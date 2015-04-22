{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}
module Semantics where

import Prelude hiding (Right)
import Control.Monad.State
import Data.Graph.Libgraph
import Data.Data hiding (Infix,Prefix)

--------------------------------------------------------------------------------
-- Expressions

data Expr = Lambda     Name Expr
          | Apply      Expr Name
          | Var        Name
          | Let        (Name,Expr) Expr
          | Constr     ConstrId [Name] Judgement
          | Case       Expr [(Expr,Expr)]

          | Observe    Label  Judgement           Expr
          | Observed   Parent Judgement           Expr
          | FunObs     Parent Judgement Name Name Expr

          | Print      Expr
          | Exception  String
          deriving (Show,Eq,Data,Typeable)

deriving instance Data Judgement
deriving instance Typeable Judgement

type Label    = String

data ConstrId = ConstrId Int 
              deriving (Eq,Ord,Data,Typeable)

instance Show ConstrId where show (ConstrId i) = "c_" ++ show i

--------------------------------------------------------------------------------
-- The state

data Context = Context { trace          :: !Trace
                       , uniq           :: !UID
                       , heap           :: !Heap
                       , depth          :: !Int
                       , reductionCount :: !Int
                       , reduceLog      :: ![String]
                       , freshVarNames  :: ![Int]
                       , stdout         :: String
                       }

doLog :: String -> State Context ()
doLog msg = do
  d <- gets depth
  modify $ \cxt -> cxt{reduceLog = (showd d ++ msg ++ "\n") : reduceLog cxt}
  where showd 0 = " "
        showd n = '|' : showd (n-1)

doPrint :: String -> State Context ()
doPrint s = do
    modify $ \cxt -> cxt{stdout = stdout cxt ++ s}

evaluate' :: Expr -> (Expr,Trace,String)
evaluate' redex = ( reduct
                  , trace cxt
                  , (foldl (++) "" . reverse . reduceLog $ cxt)
                    ++ "\nProgram output: " ++ stdout cxt
                  )
  where (reduct,cxt) = runState (eval redex) state0

evaluate :: Expr -> (Expr,Trace)
evaluate redex = (reduct, trace cxt)
  where (reduct,cxt) = runState (eval redex) state0

state0 :: Context
state0 = Context{trace=[], uniq=0, heap=[], depth=0, reductionCount=1, reduceLog=[], freshVarNames=[1..], stdout=""}

eval :: (Expr -> State Context Expr)
eval expr = do 
  n <- gets reductionCount
  modify $ \s -> s {reductionCount = n+1}
  if n > 1000
    then return (Exception "Giving up after 1000 reductions.")
    else do
        d <- gets depth
        modify $ \cxt -> cxt{depth=d+1}
        doLog (show n ++ ": " ++ show expr)
        -- h <- gets heap
        -- doLog ("* with heap" ++ show (map fst h))
        reduct <- reduce expr
        modify $ \cxt -> cxt{depth=d}
        return reduct

--------------------------------------------------------------------------------
-- Manipulating the heap

type Name = String
type Heap = [(Name,Expr)]

insertHeap :: Name -> Expr -> State Context ()
insertHeap _ (Exception _) = return ()
insertHeap x e = do
  modify $ \s -> s{heap = (x,e) : (heap s)}
  doLog ("* added " ++ (show (x,e)) ++ " to heap")

deleteHeap :: Name -> State Context ()
deleteHeap x = modify $ \s -> s{heap = filter ((/= x) . fst) (heap s)}

updateHeap :: Name -> Expr -> State Context ()
updateHeap x e = do
  deleteHeap x
  insertHeap x e

lookupHeap :: Name -> State Context Expr
lookupHeap x = do 
  me <- fmap (lookup x . heap) get
  case me of
    Just e -> return e
    _      -> return $ Exception ("Lookup '" ++ x ++ "' failed in heap ")

--------------------------------------------------------------------------------
-- Reduction rules

reduce :: Expr -> State Context Expr

reduce (Lambda x e) = 
  return (Lambda x e)

reduce (Let (x,e1) e2) = do
  insertHeap x e1
  eval e2

reduce (Apply f x) = do
  e <- eval f
  case e of 
    (Lambda y e')  -> eval (subst y x e')
    Exception msg -> return (Exception msg)
    _             -> do doLog "Attempt to apply non-Lambda!"
                        doLog (show e)
                        return (Exception "Apply non-Lambda?")

reduce (Var x) = do
  e' <- lookupHeap x
  e  <- eval e'
  updateHeap x e
  fresh e

reduce (Observe l jmt e) = do
  uid <- getUniq
  doTrace (RootEvent uid l)
  eval (Observed (Parent uid 1) jmt e)

reduce (Observed q jmt e) = do

  j <- getUniq
  doTrace (EnterEvent j q)
  let p = Parent j 1

  w <- eval e
  case w of
    Exception msg ->
      return (Exception msg)

    -- ObsC rule in paper
    (Constr s ns jmt_c) -> do
      let jmt' = case (jmt,jmt_c) of (Right,Right) -> Right; _ -> Wrong
      i <- getUniq
      doTrace (ConstEvent i p s (length ns) jmt')
      ms <- mapM getFreshVar ns
      eval $ foldl (\e' (m,n,k) -> Let (m, Observed (Parent i k) jmt (Var n)) e')
                   (Constr s ms jmt') (zip3 ms ns [1..])

    -- ObsL rule in paper
    (Lambda x e') -> do
      i <- getUniq
      doTrace (LamEvent i p)
      x1 <- getFreshVar x
      return (Lambda x1 (FunObs (Parent i 1) jmt x x1 e'))

    e' -> 
      return (Exception $ "Observe undefined: " ++ show e')

-- Obs_lambda rule in paper
-- Note how the Judgement is only passed on to the result, not the argument.
reduce (FunObs p jmt x x1 e) = do
      i  <- getUniq
      doTrace (AppEvent i p)
      x2 <- getFreshVar x
      eval $ Let    (x2,Observed (Parent i 1) Right (Var x1))
             {-in-} (   Observed (Parent i 2) jmt   (Apply (Lambda x e) x2))


reduce (Case e1 alts) = do
  e1' <- eval e1
  case e1' of
    (Constr i ys _) -> case myLookup i alts of
                          (Just alt) -> red ys alt
                          Nothing    -> return $ non_exh i
    _ -> return $ Exception "Case on a non-Constr expression"
    
    where non_exh n                  = Exception $ "Non-exhaustive patterns in Case: " ++ show n
          myLookup n                 = (lookup n) . (map $ \(Constr t ys j,e)->(t,(Constr t ys j,e)))
          red ys (Constr _ xs _, e2) = eval $ foldl (\e (x,y) -> subst x y e) e2 (zip xs ys)
          red _  _                   = error "Substitute in reduce Case alternative went wrong"

reduce (Constr i xs jmt) = return $ Constr i xs jmt

reduce (Print e) = do
  e' <- eval e
  case e' of
        (Constr i ns _) -> do -- MF TODO should we print the constructors judgment here?
          doPrint $ show i
          mapM_ printField ns
          return e'
        (Exception s) -> do
          doPrint $ "Exception: " ++ s
          return e'
        f -> return $ Exception ("Print non-constant " ++ show f)
  where printField n = do
          doPrint " ("
          eval (Print (Var n))
          doPrint ")"


reduce (Exception msg) = return (Exception msg)

--------------------------------------------------------------------------------
-- Substituting variable names

subst :: Name -> Name -> Expr -> Expr
subst n m (Lambda n' e)         = Lambda (sub n m n') (subst n m e)
subst n m (Apply e n')          = Apply (subst n m e) (sub n m n')
subst n m (Var n')              = Var (sub n m n')
subst n m (Let (n',e1) e2)      = Let ((sub n m n'),(subst n m e1)) (subst n m e2)
subst n m (Observe l j e)       = Observe l j (subst n m e)
subst n m (Observed p j e)      = Observed p j (subst n m e)
subst n m (FunObs p j n' n'' e) = FunObs p j (sub n m n') (sub n m n'') (subst n m e)
subst n m (Case e1 alts)        = Case (subst n m e1) 
                                $ map (\(e2,e3) -> (subst n m e2, subst n m e3)) alts
subst n m (Constr s ns jmt)     = Constr s (map (sub n m) ns) jmt
subst n m (Print e)             = Print (subst n m e)
subst _ _ e@Exception{}         = e

sub :: Name -> Name -> Name -> Name
sub n m n' = if n == n' then m else n'

--------------------------------------------------------------------------------
-- Fresh variable names

fresh :: Expr -> State Context Expr

fresh (Lambda x e) = do 
  y <- getFreshVar x
  e' <- (fresh . subst x y) e
  return (Lambda y e')

fresh (Let (x,e1) e2) = do 
  y <- getFreshVar x
  e1' <- (fresh . subst x y) e1
  e2' <- (fresh . subst x y) e2
  return $ Let (y,e1') e2'

fresh (Apply f x) = do 
  f' <- fresh f
  return $ Apply f' x

fresh (Var x) =
  return (Var x)

fresh (Observe l jmt e) = do
  e' <- fresh e
  return (Observe l jmt e')

fresh (Observed p jmt e) = do
  e' <- fresh e
  return (Observed p jmt e')

fresh (FunObs p j x x1 e) = do
  y <- getFreshVar x
  e' <- (fresh . subst x y) e
  return (FunObs p j y x1 e')

fresh (Exception msg) = return (Exception msg)

fresh (Constr s ns jmt) =
  return (Constr s ns jmt)

fresh (Case e1 alts) = do
  let (e2s,e3s) = unzip alts
  e1'  <- fresh e1
  e3s' <- mapM fresh e3s
  return $ Case e1' (zip e2s e3s')

fresh (Print e) = do
  e' <- fresh e
  return (Print e')

getFreshVar :: Name -> State Context Name
getFreshVar n = do
  (x:xs) <- gets freshVarNames
  modify $ \cxt -> cxt {freshVarNames=xs}
  return (n ++ show x)

--------------------------------------------------------------------------------
-- Tracing

type Trace = [Event]

data Event
  = RootEvent  { eventUID :: UID, eventLabel  :: Label }
  | EnterEvent { eventUID :: UID, eventParent :: Parent}
  | ConstEvent { eventUID :: UID, eventParent :: Parent, eventRepr :: ConstrId
               , eventLength :: Int, eventJudgement :: Judgement}
  | LamEvent   { eventUID :: UID, eventParent :: Parent}
  | AppEvent   { eventUID :: UID, eventParent :: Parent}
  deriving (Show,Eq,Ord)

type UID = Int
type ParentPosition = Int

data Parent = Parent {parentUID :: UID,  parentPosition :: ParentPosition} 
              deriving (Show,Eq,Ord,Data,Typeable)

getUniq :: State Context UID
getUniq = do
  i <- gets uniq
  modify $ \cxt -> cxt { uniq = i + 1 }
  return i

doTrace :: Event -> State Context ()
doTrace rec = do
  doLog $ "* " ++ show rec
  modify $ \cxt -> cxt{trace = rec : trace cxt}


