module Semantics where

import Control.Monad.State
import Data.Graph.Libgraph
import Data.List (sort,partition,permutations,nub)
import qualified Debug.Trace as Debug

--------------------------------------------------------------------------------
-- Examples

plus1Traced = Let ("plus1", Lambda "x" 
                          $ Apply ( Push "plus1" 
                                  $ Lambda "x'" (Apply (Apply (Var "plus") "1") "x'")
                                  ) "x")

ex1 = prelude
    $ plus1Traced
    $ Print $ Apply (Var "plus1") "1"

--------------------------------------------------------------------------------
-- Expressions

data Expr = Lambda     Name Expr
          | Apply      Expr Name
          | Var        Name
          | Let        (Name,Expr) Expr
          | Constr     String [Name]
          | Case       Expr [(Expr,Expr)]

          | Push       Label Expr
          | Observed   Parent Expr
          | FunObs     Name Name Parent Expr
          | ConsrObs   

          | Const      Int
          | Plus       Expr Expr

          | Print      Expr

          | Exception  String
          deriving (Show,Eq)

--------------------------------------------------------------------------------
-- Prelude, with:
--
-- N | S Expr
--
-- plus = \x y -> case x of N      -> y
--                          (S x') -> plus x' (S y)
--
-- Nil | Con Expr Expr
--
-- map = \f xs -> case xs of (Constr "Nil" [])    -> xs
--                           (Constr "Con" [h,t]) -> let h' = f h, t' = map f t
--                                                  in Constr "Con" [h', t']
--

prelude :: Expr -> Expr
prelude e = Let ("plus", Lambda "x" $ Lambda "y"
                       $ Case (Var "x")
                              [ (Constr "N" [],     Var "y")
                              , (Constr "S" ["m"], Let ("n", Constr "S" ["y"])
                                                        $ Apply (Apply (Var "plus") "m") "n")
                              ])
          $ Let ("0", Constr "N" [])
          $ Let ("1", Constr "S" ["0"])
          $ Let ("2", Constr "S" ["1"])
          $ Let ("map", Lambda "f" $ Lambda "xs" 
                      $ Case (Var "xs")
                             [ (Constr "Nil" [], Var "xs")
                             , ( Constr "Con" ["h","t"]
                               , Let ("h'", Apply (Var "f") "h")
                               $ Let ("t'", Apply (Apply (Var "map") "f") "t")
                               $ Constr "Con" ["h'","t'"]
                               )
                             ])
          $ e

--------------------------------------------------------------------------------
-- The state

data Context = Context { trace          :: !Trace
                       , uniq           :: !UID
                       , stack          :: !Stack
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

state0 = Context [] 0 [] [] 0 1 [] [1..] ""

eval :: (Expr -> State Context Expr)
eval expr = do 
  n <- gets reductionCount
  modify $ \s -> s {reductionCount = n+1}
  if n > 500
    then return (Exception "Giving up after 500 reductions.")
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
type Heap = [(Name,(Stack,Expr))]

insertHeap :: Name -> (Stack,Expr) -> State Context ()
insertHeap x (_,Exception _) = return ()
insertHeap x e = do
  modify $ \s -> s{heap = (x,e) : (heap s)}
  doLog ("* added " ++ (show (x,e)) ++ " to heap")

deleteHeap :: Name -> State Context ()
deleteHeap x = modify $ \s -> s{heap = filter ((/= x) . fst) (heap s)}

updateHeap x e = do
  deleteHeap x
  insertHeap x e

lookupHeap :: Name -> State Context (Stack,Expr)
lookupHeap x = do 
  me <- fmap (lookup x . heap) get
  case me of
    Just (stk,e) -> return (stk,e)
    _            -> return ([],Exception ("Lookup '" ++ x ++ "' failed in heap "))

--------------------------------------------------------------------------------
-- Stack handling: push and call

type Label = String
type Stack = [Label]

stackIsNow msg = do
  stk <- gets stack
  doLog ("* " ++ msg ++ ": stack is now " ++ show stk)

setStack :: Stack -> State Context ()
setStack stk = do
  modify $ \s -> s {stack = stk}
  stackIsNow "Restore stack from heap"

doPush :: Label -> State Context ()
doPush l = do
  modify $ \s -> s {stack = push l (stack s)}
  stackIsNow $ "Push " ++ l

push :: Label -> Stack -> Stack
push l s
  | l `elem` s = dropWhile (/= l) s
  | otherwise  = l : s

doCall :: Stack -> State Context ()
doCall sLam = do
  stk <- gets stack
  modify $ \s -> s {stack = call (stack s) sLam}
  stackIsNow $ "Call " ++ show stk ++ " " ++ show sLam

-- call sApp sLam ∉ {sApp, SLam} when sLam is not a prefix of sApp.
call :: Stack -> Stack -> Stack
call sApp sLam = sLam' ++ sApp
  where (sPre,sApp',sLam') = commonPrefix sApp sLam

commonPrefix :: Stack -> Stack -> (Stack, Stack, Stack)
commonPrefix sApp sLam
  = let (sPre,sApp',sLam') = span2 (==) (reverse sApp) (reverse sLam)
    in (sPre, reverse sApp', reverse sLam') 

span2 :: (a -> a -> Bool) -> [a] -> [a] -> ([a], [a], [a])
span2 f = s f []
  where s _ pre [] ys = (pre,[],ys)
        s _ pre xs [] = (pre,xs,[])
        s f pre xs@(x:xs') ys@(y:ys') 
          | f x y     = s f (x:pre) xs' ys'
          | otherwise = (pre,xs,ys)

--------------------------------------------------------------------------------
-- Reduction rules

reduce :: Expr -> State Context Expr

reduce (Const v) = 
  return (Const v)

reduce (Lambda x e) = 
  return (Lambda x e)

reduce (Let (x,e1) e2) = do
  stk <- gets stack
  insertHeap x (stk,e1)
  eval e2

reduce (Apply f x) = do
  e <- eval f
  case e of 
    (Lambda y e)  -> eval (subst y x e)
    Exception msg -> return (Exception msg)
    _             -> do doLog "Attempt to apply non-Lambda!"
                        doLog (show e)
                        return (Exception "Apply non-Lambda?")

reduce (Var x) = do
  stk       <- gets stack
  (xStk,e') <- lookupHeap x
  setStack xStk                      -- Restore stack as saved on heap
  e         <- eval e'
  xStk'     <- gets stack
  updateHeap x (xStk',e)             -- Update stack (and expression) on heap
  setStack stk                       -- Restore stack as before evaluating
  case e of
     (Lambda _ _) -> do doCall xStk' -- For functions: the current stack is the
                                     -- call-site stack, xStk' is the "lambda"
                                     -- stack. Here we combine the two as Marlow,
                                     -- Solving An Old Problem.
                        fresh e
     _            -> do fresh e

reduce (Push l e) = do
  stk <- gets stack
  doPush l
  uid <- getUniq
  doTrace (RootEvent l stk uid)
  eval (Observed (Parent uid 1) e)

reduce (Observed p e) = do
  stk <- gets stack
  e' <- eval e
  case e' of
    Exception msg ->
      return (Exception msg)

    -- ObsC rule in PLDI paper
    (Const v) -> do
      uid <- getUniq
      doTrace (ConstEvent uid p (show v) 0)
      return e'

    (Constr s ns) -> do
      i <- getUniq
      doTrace (ConstEvent i p s (length ns))
      ms <- mapM getFreshVar ns
      eval $ foldl (\e (m,n,j) -> Let (m, Observed (Parent i j) (Var n)) e)
                   (Constr s ms) (zip3 ms ns [1..])

    -- ObsL rule in PLDI paper
    (Lambda x e) -> do
      i <- getUniq
      doTrace (LamEvent i p)
      x1 <- getFreshVar x
      return (Lambda x1 (FunObs x x1 (Parent i 1) e))

    e -> 
      return (Exception $ "Observe undefined: " ++ show e)

-- ObsF rule in paper
reduce (FunObs x x1 p e) = do
      i  <- getUniq
      doTrace (AppEvent i p)
      x2 <- getFreshVar x
      eval $ Let    (x2,Observed (Parent i 1) (Var x1)) 
             {-in-} (Observed (Parent i 2) (Apply (Lambda x e) x2))


reduce (Case e1 alts) = do
  e1' <- eval e1
  case e1' of
    (Constr s ys) -> case lookup s alts of
                       (Just alt) -> red ys alt
                       Nothing    -> return $ non_exh s
    _ -> return $ Exception "Case on a non-Constr expression"
    
    where non_exh s                = Exception $ "Non-exhaustive patterns in Case :" ++ s
          lookup s                 = (Prelude.lookup s) 
                                   . (map $ \(Constr t ys,e)->(t,(Constr t ys,e)))
          red ys (Constr s xs, e2) = eval $ foldl (\e (x,y) -> subst x y e) e2 (zip xs ys)

reduce (Constr s xs) = return $ Constr s xs

reduce (Print e) = do
  e' <- eval e
  case e' of
        (Constr s ns) -> do
          doPrint s
          mapM_ printField ns
          return e'
        (Const i) -> do
          doPrint (show i)
          return e'
        f -> return $ Exception ("Print non-constant " ++ show f)
  where printField n = do
          doPrint " ("
          eval (Print (Var n))
          doPrint ")"

reduce (Plus e1 e2) = do
  e1' <- eval e1
  e2' <- eval e2
  case (e1',e2') of
        (Const v1, Const v2) -> return $ Const (v1 + v2)
        (l,r)                -> return (Exception $ "Attempt to sum non-constant values: "
                                                  ++ show l ++ " + " ++ show r)

reduce (Exception msg) = return (Exception msg)

--------------------------------------------------------------------------------
-- Substituting variable names

subst :: Name -> Name -> Expr -> Expr
subst n m (Const v)           = Const v
subst n m (Lambda n' e)       = Lambda (sub n m n') (subst n m e)
subst n m (Apply e n')        = Apply (subst n m e) (sub n m n')
subst n m (Var n')            = Var (sub n m n')
subst n m (Let (n',e1) e2)    = Let ((sub n m n'),(subst n m e1)) (subst n m e2)
subst n m (Push l e)          = Push l (subst n m e)
subst n m (Observed p e)      = Observed p (subst n m e)
subst n m (FunObs n' n'' p e) = FunObs (sub n m n') (sub n m n'') p (subst n m e)
subst n m (Plus e1 e2)        = Plus (subst n m e1) (subst n m e2)
subst n m (Case e1 alts)      = Case (subst n m e1) 
                              $ map (\(e2,e3) -> (subst n m e2, subst n m e3)) alts
subst n m (Constr s ns)       = Constr s $ map (sub n m) ns
subst n m (Print e)           = Print (subst n m e)

sub :: Name -> Name -> Name -> Name
sub n m n' = if n == n' then m else n'

--------------------------------------------------------------------------------
-- Fresh variable names

fresh :: Expr -> State Context Expr

fresh (Const v) = do
  return (Const v)

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

fresh (Push l e) = do
  e' <- fresh e
  return (Push l e')

fresh (Observed p e) = do
  e' <- fresh e
  return (Observed p e')

fresh (FunObs x x1 p e) = do
  y <- getFreshVar x
  e' <- (fresh . subst x y) e
  return (FunObs y x1 p e')

fresh (Exception msg) = return (Exception msg)

fresh (Plus e1 e2) = do
  e1' <- fresh e1
  e2' <- fresh e2
  return (Plus e1' e2')

fresh (Constr s ns) =
  return (Constr s ns)

fresh (Case e1 alts) = do
  let (e2s,e3s) = unzip alts
  e1'  <- fresh e1
  -- e2s' <- mapM fresh e2s ???                           <--- MF TODO, is this ok?
  e3s' <- mapM fresh e3s
  return $ Case e1 (zip e2s e3s')

  where freshAlt (Constr s xs, e) = do
          ys <- mapM getFreshVar xs
          e' <- fresh $ foldl (\v (x,y) -> subst x y v) e (zip xs ys)
          return (Constr s ys, e')

fresh (Print e) = do
  e' <- fresh e
  return (Print e)

getFreshVar :: Name -> State Context Name
getFreshVar n = do
  (x:xs) <- gets freshVarNames
  modify $ \cxt -> cxt {freshVarNames=xs}
  return (n ++ show x)

--------------------------------------------------------------------------------
-- Tracing

type Trace = [Event]

data Event
  = RootEvent
    { eventLabel  :: Label
    , eventStack  :: Stack
    , eventUID    :: UID
    } 
  | ConstEvent
    { eventUID    :: UID
    , eventParent :: Parent
    , eventRepr   :: String
    , eventLength :: Int
    }
  | LamEvent
    { eventUID    :: UID
    , eventParent :: Parent
    }
  | AppEvent
    { eventUID    :: UID
    , eventParent :: Parent
    }    
  deriving (Show,Eq,Ord)

data CompStmt
 = CompStmt
    { stmtLabel  :: Label
    , stmtStack  :: Stack
    , stmtUID    :: UID
    , stmtRepr   :: String
    }
 | IntermediateStmt
    { stmtParent :: Parent
    , stmtUID    :: UID
    , stmtRepr   :: String
    }
  deriving (Show,Eq,Ord)

type UID = Int

data Parent = Parent {parentUID :: UID,  parentPosition :: Int} 
              deriving (Show,Eq,Ord)

getUniq :: State Context UID
getUniq = do
  i <- gets uniq
  modify $ \cxt -> cxt { uniq = i + 1 }
  return i

doTrace :: Event -> State Context ()
doTrace rec = do
  doLog $ "* " ++ show rec
  modify $ \cxt -> cxt{trace = rec : trace cxt}

--------------------------------------------------------------------------------
-- Trace post processing

-- Searchable mapping from UID of the parent and position in list of siblings
-- to a child event.
type EventTree = [(UID, [(Int, Event)])]

mkStmts :: (Expr,Trace) -> (Expr,[CompStmt])
mkStmts (reduct,trc) = (reduct,map (mkStmt events) roots)

  where isRoot (RootEvent _ _ _) = True
        isRoot _                 = False
        (roots,chds) = partition isRoot trc

        events :: EventTree
        events = map children trc
        children e = let j = eventUID e
                     in (j, map    (\c -> (parentPosition . eventParent $ c, c))
                          $ filter (\e -> j == (parentUID . eventParent) e) chds)

mkStmt :: EventTree -> Event -> CompStmt
mkStmt tree (e@(RootEvent l s i)) = CompStmt l s i r
        where r = dfsFold pre post "" (Just e) tree
              pre Nothing                     = (++" _")
              pre (Just (RootEvent l _ _))    = (++l)
              pre (Just (ConstEvent _ _ r _)) = (++" ("++r)
              pre (Just (LamEvent _ _))       = (++" {")
              pre (Just (AppEvent _ _))       = (++" ->")
              post Nothing                     = id
              post (Just (RootEvent l _ _))    = id
              post (Just (ConstEvent _ _ r _)) = (++")")
              post (Just (LamEvent _ _))       = (++" }")
              post (Just (AppEvent _ _))       = id


dfsFold :: (Maybe Event -> a -> a) -> (Maybe Event -> a -> a) -> a 
        -> (Maybe Event) -> EventTree -> a
dfsFold pre post z me tree 
  = let z'     = pre me z
        cs     = case me of (Just e) -> case lookup (eventUID e) tree of (Just cs) -> cs
                                                                         Nothing   -> []
                            Nothing  -> []
        csFold = foldl(\z'' d -> dfsFold pre post z'' (lookup d cs) tree) z' 
  in post me $ case me of
    Nothing                     -> z'
    (Just (RootEvent _ _ i))    -> csFold [1]
    (Just (ConstEvent i _ _ l)) -> csFold [1..l]
    (Just (LamEvent i _))       -> csFold [1]
    (Just (AppEvent i _))       -> let z1 = dfsFold pre post z (lookup 1 cs) tree
                                       z2 = pre me z1 -- infix
                                   in       dfsFold pre post z2 (lookup 2 cs) tree
{-
successors :: Bool -> Trace -> Event -> CompStmt
successors root trc rec = case rec of
        (AppEvent _ _)    -> merge root rec $ (suc ArgOf) ++ (suc ResOf)
        (LamEvent _ _)    -> merge root rec (suc $ flip Parent 0)
        (RootEvent l s _) -> merge root rec (suc $ flip Parent 0)

  where childEvents = map    (\c -> (parentUID . eventParent $ c, c))
                    $ filter (\c -> eventUID rec == parentUID . eventParent $ c) trc

        repr j = case lookup j childEvents of
                        Nothing -> "_"
                        
                     

        -- TODO: some kind of root detection for -> vs = ?
        -- mkStmt (ConstEvent uid p repr _) = case rec of
        --   (RootEvent _ _ _) -> IntermediateStmt p uid ("= " ++ repr)
        --   _            -> IntermediateStmt p uid repr
	-- mkStmt chd                     = (successors root' trc chd)
	-- root' = case rec of (AppEvent _ _) -> False; _ -> root
-}

oldestUID :: [UID] -> UID
oldestUID = head . sort

{-
merge :: Bool -> Event -> [CompStmt] -> CompStmt

merge _ (RootEvent lbl stk i) []    = CompStmt lbl stk i (lbl ++ " = _")
merge _ (RootEvent lbl stk _) [chd] = CompStmt lbl stk i (lbl ++ " " ++ r)
  where r = stmtRepr chd
        i = stmtUID  chd
merge _ (RootEvent lbl stk i) _     = error "merge: Root with multiple children?"

merge _ (LamEvent i p) []   = IntermediateStmt p i "_"
merge _ (LamEvent _ p) [a]  = IntermediateStmt p (stmtUID a) (stmtRepr a)
merge _ (LamEvent _ p) apps = IntermediateStmt p i r
  where (a:pps)     = map stmtRepr apps
        r           = (foldl and ("{" ++ a) pps) ++ "}"
        i           = head . sort . (map stmtUID) $ apps
        and acc app = acc ++ "; " ++ app

merge t (AppEvent appUID p) chds = case (length chds) of
  0 -> IntermediateStmt p appUID (mkStmt "_" "_")
  1 -> let res = head chds
           r   = mkStmt "_" (stmtRepr res)
           i   = stmtUID  res
       in IntermediateStmt p i r
  2 -> let [arg,res] = chds
           r   = mkStmt (stmtRepr arg) (stmtRepr res)
           i   = stmtUID res
       in IntermediateStmt p i r
  _ -> error "merge: Application with multiple arguments?"
  where mkStmt arg res = pre ++ arg ++ inf ++ res ++ post
        pre  = if t then "" else "(\\"
        inf  = if t then " = " else " -> "
        post = if t then "" else ")"
-}

--------------------------------------------------------------------------------
-- Debug

data Vertex = RootVertex | Vertex [CompStmt] deriving (Eq)
type CompGraph = Graph Vertex ()

mkGraph :: (Expr,[CompStmt]) -> (Expr,CompGraph)
mkGraph (reduct,trc) = let (Graph _ vs as) = mapGraph mkVertex (mkGraph' trc)
                           rs              = filter (\(Vertex [c]) -> stmtStack c == []) vs
                           as'             = map (\r -> Arc RootVertex r ()) rs
                       in (reduct, Graph RootVertex (RootVertex:vs) (as' ++ as))

mkGraph' :: [CompStmt] -> Graph CompStmt ()
mkGraph' trace
  | length trace < 1 = error "mkGraph: empty trace"
  | otherwise = Graph (head trace) -- doesn't really matter, replaced above
                       trace
                       (nub $ mkArcs trace)

mkVertex :: CompStmt -> Vertex
mkVertex c = Vertex [c]

-- Implementation of combinations function taken from http://stackoverflow.com/a/22577148/2424911
combinations :: Int -> [a] -> [[a]]
combinations k xs = combinations' (length xs) k xs
  where combinations' n k' l@(y:ys)
          | k' == 0   = [[]]
          | k' >= n   = [l]
          | null l    = []
          | otherwise = map (y :) (combinations' (n - 1) (k' - 1) ys) 
                        ++ combinations' (n - 1) k' ys


permutationsOfLength :: Int -> [a] -> [[a]]
permutationsOfLength x = (foldl (++) []) . (map permutations) . (combinations x)

mkArcs :: [CompStmt] -> [Arc CompStmt ()]
mkArcs cs = callArcs ++ pushArcs
  where pushArcs = map (\[c1,c2]    -> Arc c1 c2 ()) ps 
        callArcs = foldl (\as [c1,c2,c3] -> (Arc c1 c2 ()) 
                                            : ((Arc c2 c3 ()) : as)) [] ts 
        ps = filter f2 (permutationsOfLength 2 cs)
        ts = filter f3 (permutationsOfLength 3 cs)

        f3 [c1,c2,c3] = callDependency c1 c2 c3
        f3 _          = False -- less than 3 statements

        f2 [c1,c2]    = pushDependency c1 c2
        f2 _          = False


arcsFrom :: CompStmt -> [CompStmt] -> [Arc CompStmt ()]
arcsFrom src trc =  ((map (\tgt -> Arc src tgt ())) . (filter isPushArc) $ trc)
                 ++ ((map (\tgt -> Arc src tgt ())) . (filter isCall1Arc) $ trc)

  where isPushArc = pushDependency src
        
        isCall1Arc = anyOf $ map (flip callDependency src) trc

        isCall2Arc = anyOf $  apmap (map (callDependency2 src) trc) trc
                           ++ apmap (map (callDependency2' src) trc) trc

        anyOf :: [a->Bool] -> a -> Bool
        anyOf ps x = or (map (\p -> p x) ps)

        apmap :: [a->b] -> [a] -> [b]
        apmap fs xs = foldl (\acc f -> acc ++ (map f xs)) [] fs

nextStack :: CompStmt -> Stack
nextStack rec = push (stmtLabel rec) (stmtStack rec)

pushDependency :: CompStmt -> CompStmt -> Bool
pushDependency p c = nextStack p == stmtStack c

callDependency :: CompStmt -> CompStmt -> CompStmt -> Bool
callDependency pApp pLam c = 
  stmtStack c == call (nextStack pApp) (nextStack pLam)

callDependency2 :: CompStmt -> CompStmt -> CompStmt -> CompStmt -> Bool
callDependency2 pApp pApp' pLam' c = call (nextStack pApp) pLam == stmtStack c
  where pLam = call (nextStack pApp') (nextStack pLam')

callDependency2' :: CompStmt -> CompStmt -> CompStmt -> CompStmt -> Bool
callDependency2' pApp1 pApp2 pLam c = call pApp (nextStack pLam) == stmtStack c
  where pApp = call (nextStack pApp1) (nextStack pApp2)

--------------------------------------------------------------------------------
-- Evaluate and display.

-- tracedEval :: Expr -> (Expr,CompGraph)
-- tracedEval = mkGraph . mkStmts . evaluate

dispTxt :: Expr -> IO ()  
dispTxt = disp' (putStrLn . shw)
  where shw :: CompGraph -> String
        shw g = "\nComputation statements:\n" ++ unlines (map showVertex' $ vertices g)

-- Requires Imagemagick to be installed.
disp :: Expr -> IO ()
disp = disp' (display shw)
  where shw :: CompGraph -> String
        shw g = showWith g showVertex showArc

showVertex :: Vertex -> (String,String)
showVertex v = (showVertex' v, "")

showVertex' :: Vertex -> String
showVertex' RootVertex  = "Root"
showVertex' (Vertex cs) = (foldl (++) "") . (map showCompStmt) $ cs

showCompStmt :: CompStmt -> String
showCompStmt (CompStmt l s i r) = r -- ++ " (with stack " ++ show s ++ ")"

showArc _  = ""

disp' f expr = do
  putStrLn (messages ++ strc)
  -- Uncomment the next line to write all reduction steps to file (for off-line analysis).
  writeFile "log" (messages ++ strc)
  f . snd . mkGraph . mkStmts $ (reduct,trc)
  where (reduct,trc,messages) = evaluate' expr
        strc = "\n\nReduct: " ++ show reduct
               ++ foldl (\acc s -> acc ++ "\n" ++ s) "\n\nEvent trace:" (map show $ reverse trc)
