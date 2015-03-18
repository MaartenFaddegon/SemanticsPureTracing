module Semantics where

import Control.Monad.State
import Data.Graph.Libgraph
import Data.List (sort,partition,permutations,nub,minimum,maximum,(\\),find)
import qualified Debug.Trace as Debug

--------------------------------------------------------------------------------
-- Examples

plus1Traced = Let ("plus1", Lambda "x" 
                          $ Apply ( Push "plus1" 
                                  $ Lambda "x'" (Apply (Apply (Var "plus") "1") "x'")
                                  ) "x")

-- NOTE: this only traces the top, subsequent (recursive) calls to plus are not traced
plusTraced = Let ("p", Lambda "x" $ Lambda "y"
                     $ Apply (Apply (Push "p" 
                         (Lambda "a" (Lambda "b" 
                           (Apply (Apply (Var "plus") "a") "b")))
                       ) "x") "y")


-- NOTE: this only traces the top, subsequent (recursive) calls to foldl are not traced
foldlTraced = Let ("foldlT", Lambda "f" $ Lambda "xs"  $ Lambda "z"
                           $ Apply (Apply (Apply (Push "foldl" 
                             (Var "foldl")) "f") "xs" ) "z")

sumTraced = Let ("sum", Lambda "xs" (Apply (Push "sum" (Lambda "xs'" 
                        (Apply (Apply (Apply (Var "foldl") "p") "0" )"xs'"))) "xs"))

mapTraced = Let ("mapT", Lambda "f" $ Lambda "xs"
                       $ Apply (Apply (Push "map" (Var "map")) "f") "xs" )

-- data B = T | F
-- n :: B -> B
myNot     = Let ("n", Lambda "b" $ Case (Var "b")
                    [ (Constr "T" [], Constr "F" [])
                    , (Constr "F" [], Constr "T" [])
                    ])

notTraced = Let ("n", Lambda "b'" $ Apply (Push "n" $ Lambda "b"
                      $ Case (Var "b")
                             [ (Constr "T" [], Constr "F" [])
                             , (Constr "F" [], Constr "T" [])
                             ]) "b'")


-- x :: B -> B -> B
myXor = Let ("x", Lambda "a1" $ Lambda "a2" $ Apply (Apply (Push "x" $ Lambda "b1" $ Lambda "b2"
                      $ Case (Var "b1")
                             [ (Constr "T" [], Case (Var "b2")[ (Constr "T" [], Constr "F" [])
                                                              , (Constr "F" [], Constr "T" [])])
                             , (Constr "F" [], Case (Var "b2")[ (Constr "T" [], Constr "T" [])
                                                              , (Constr "F" [], Constr "T" [])])
                             ]
                             ) "a1") "a2")


ex1 = {- import -} prelude
    $ {- import -} notTraced
    $ Let ("b", (Constr "F" []))
    $ Print $ Apply (Var "n") "b"

-- Example 2: Function h and n are traced, h maps over a list and n is
-- applied to all elements.
--
--   a) without reverse
--   b) reverse before printing (but outside traced code)

ex2a = {- import -} prelude
     $ {- import -} notTraced
     $ Let ("xs", Let ("a", Constr "T" [])
                $ Let ("b", Constr "F" [])
                $ Let ("c2", Constr "Nil" [])
                $ Let ("c1", Constr "Con" ["b", "c2"])
                $            Constr "Con" ["a","c1"])
     $ Let ("h", Lambda "xs" (Apply (Push "h" (Apply (Var "map") "n")) "xs"))
     $ Print $ Apply (Var "h") "xs"

ex2b = {- import -} prelude
     $ {- import -} notTraced
     $ Let ("xs", Let ("a", Constr "T" [])
                $ Let ("b", Constr "F" [])
                $ Let ("c2", Constr "Nil" [])
                $ Let ("c1", Constr "Con" ["b", "c2"])
                $            Constr "Con" ["a","c1"])
     $ Let ("h", Lambda "xs" (Apply (Push "h" (Apply (Var "map") "n")) "xs"))
     $ Print $ Let ("ys", Apply (Var "h") "xs") 
             $ Apply (Var "reverse") "ys"

-- Example 3: Trace map and its callees, reverse result before printing
-- but outside traced code

ex3a = {- import -} prelude
     $ {- import -} myNot
     $ {- import -} mapTraced
     $ Let ("xs", Let ("a", Constr "T" [])
                $ Let ("b", Constr "F" [])
                $ Let ("c2", Constr "Nil" [])
                $ Let ("c1", Constr "Con" ["b", "c2"])
                $            Constr "Con" ["a","c1"])
     $ Print $ Let ("ys", Apply (Apply (Var "mapT") "n") "xs")
             $ Var "ys"

ex3b = {- import -} prelude
     $ {- import -} notTraced
     $ {- import -} mapTraced
     $ Let ("xs", Let ("a", Constr "T" [])
                $ Let ("b", Constr "F" [])
                $ Let ("c2", Constr "Nil" [])
                $ Let ("c1", Constr "Con" ["b", "c2"])
                $            Constr "Con" ["a","c1"])
     $ Print $ Let ("ys", Apply (Apply (Var "mapT") "n") "xs")
             $ Apply (Var "reverse") "ys"

-- Example 4: Trace foldl and its callees in a simple checksum program

ex4 = {- import -} prelude
    $ {- import -} foldlTraced
    $ {- import -} myXor
     $ Let ("bs", Let ("a", Constr "T" [])
                $ Let ("b", Constr "F" [])
                $ Let ("c2", Constr "Nil" [])
                $ Let ("c1", Constr "Con" ["b", "c2"])
                $            Constr "Con" ["a","c1"])
     $ Let ("z", Constr "F" [])
     $ Print $ Apply (Apply (Apply (Var "foldlT") "x") "z") "bs"

-- Example 5: 
--      a) f -> g -> h
--      b) f -> g, f -> h

ex5a = Let ("h", Lambda "x" (Apply (Push "h" (Lambda "y" $ Var "y")) "x"))
     $ Let ("g", Lambda "x" (Apply (Push "g" (Lambda "y" $ Apply (Var "h") "y")) "x"))
     $ Let ("f", Lambda "x" (Apply (Push "f" (Lambda "y" $ Apply (Var "g") "y")) "x"))
     $ Let ("k", Constr "1" [])
     $ Print $ Apply (Var "f") "k"

ex5b = Let ("h", Lambda "x" (Apply (Push "h" (Lambda "y" $ Var "y")) "x"))
     $ Let ("g", Lambda "x" (Apply (Push "g" (Lambda "y" $ Var "y")) "x"))
     $ Let ("f", Lambda "x" (Apply (Push "f" (Lambda "y" $ Let ("z", Apply (Var "g") "y")
                                                               (Apply (Var "h") "z")
                                             )) "x"))
     $ Let ("k", Constr "1" [])
     $ Print $ Apply (Var "f") "k"


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
--                                                   in Constr "Con" [h', t']
--
-- foldl = \f z xs -> case xs of (Constr "Nil" [])    -> z
--                               (Constr "Con" [h,t]) -> let z' = f z h
--                                                       in foldl f z' t
-- reverse = \xs -> let f = \z x -> Constr "Con" [x,z]
--                      z = Constr "Nil" []
--                  in foldl f z xs


prelude :: Expr -> Expr
prelude e = Let ("plus", Lambda "x" $ Lambda "y"
                       $ Case (Var "x")
                              [ (Constr "O" [],     Var "y")
                              , (Constr "S" ["m"], Let ("n", Constr "S" ["y"])
                                                        $ Apply (Apply (Var "plus") "m") "n")
                              ])
          $ Let ("0", Constr "O" [])
          $ Let ("1", Constr "S" ["0"])
          $ Let ("2", Constr "S" ["1"])
          $ Let ("3", Constr "S" ["2"])
          $ Let ("4", Constr "S" ["3"])
          $ Let ("5", Constr "S" ["4"])
          $ Let ("map", Lambda "f" $ Lambda "xs" 
                      $ Case (Var "xs")
                             [ (Constr "Nil" [], Var "xs")
                             , ( Constr "Con" ["h","t"]
                               , Let ("h'", Apply (Var "f") "h")
                               $ Let ("t'", Apply (Apply (Var "map") "f") "t")
                               $ Constr "Con" ["h'","t'"]
                               )
                             ])
          $ Let ("foldl", Lambda "f" $ Lambda "z"  $ Lambda "xs"
                        $ Case (Var "xs")
                             [ (Constr "Nil" [], Var "z")
                             , ( Constr "Con" ["h","t"]
                               , Let ("z'", Apply (Apply (Var "f") "z") "h")
                               $ Apply (Apply (Apply (Var "foldl") "f") "z'") "t"
                               )
                             ])
          $ Let ("reverse", Lambda "xs"
                          $ Let ("f", Lambda "z" $ Lambda "x"
                                    $ Constr "Con" ["x","z"])
                          $ Let ("z", Constr "Nil" [])
                          $ Apply (Apply (Apply (Var "foldl") "f") "z") "xs")
          $ e



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
    
    where non_exh s                = Exception $ "Non-exhaustive patterns in Case: " ++ s
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
        (Exception s) -> do
          doPrint $ "Exception: " ++ s
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
    , stmtUID    :: [UID]
    , stmtRepr   :: String
    , stmtHoles  :: [Hole]
    }
  deriving (Show,Eq,Ord)

type UID = Int
type ParentPosition = Int

data Parent = Parent {parentUID :: UID,  parentPosition :: ParentPosition} 
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
type EventForest = [(UID, [(Int, Event)])]

mkEventForest :: Trace -> EventForest
mkEventForest trc = map children trc
  where children e = let j = eventUID e
                     in (j, map    (\c -> (parentPosition . eventParent $ c, c))
                          $ filter (\e -> j == (parentUID . eventParent) e) chds)

        (roots,chds) = partition isRoot trc
        isRoot (RootEvent _ _ _) = True
        isRoot _                 = False


mkStmts :: (Expr,Trace) -> (Expr,Trace,[CompStmt])
mkStmts (reduct,trc) = (reduct,trc, map (mkStmt forest) roots)

  where isRoot (RootEvent _ _ _) = True
        isRoot _                 = False
        (roots,chds) = partition isRoot trc

        forest :: EventForest
        forest = mkEventForest trc

mkStmt :: EventForest -> Event -> CompStmt
mkStmt forest (e@(RootEvent l s _)) = CompStmt l s i r h
        where r = dfsFold Infix pre post "" Trunk (Just e) forest
              pre Nothing                      _ = (++" _")
              pre (Just (RootEvent l _ _))     _ = (++l)
              pre (Just (ConstEvent _ _ r _))  _ = (++" ("++r)
              pre (Just (LamEvent _ _))        _ = (++" {")
              pre (Just (AppEvent _ _))        _ = (++" ->")
              post Nothing                     _ = id
              post (Just (RootEvent l _ _))    _ = id
              post (Just (ConstEvent _ _ r _)) _ = (++")")
              post (Just (LamEvent _ _))       _ = (++"}")
              post (Just (AppEvent _ _))       _ = id

              i = reverse $ dfsFold Prefix addUID nop [] Trunk (Just e) forest
              addUID Nothing                      _ is = is
              addUID (Just (RootEvent _ _ i))     _ is = i : is
              addUID (Just (ConstEvent i _ _ _))  _ is = i : is
              addUID (Just (LamEvent i _))        _ is = i : is
              addUID (Just (AppEvent i _))        _ is = i : is
              nop    _                            _ is = is

              h :: [Hole]
              h = holes forest e

treeUIDs :: EventForest -> Event -> [UID]
treeUIDs forest root = reverse $ dfsFold Prefix addUID nop [] Trunk (Just root) forest
  where addUID Nothing                      _ is = is
        addUID (Just (RootEvent _ _ i))     _ is = i : is
        addUID (Just (ConstEvent i _ _ _))  _ is = i : is
        addUID (Just (LamEvent i _))        _ is = i : is
        addUID (Just (AppEvent i _))        _ is = i : is
        nop    _                            _ is = is

data InfixOrPrefix = Infix | Prefix

data Location = Trunk | ArgumentOf Location | ResultOf Location deriving Eq

data ArgOrRes = Arg | Res

-- Is the first location in the argument, or result subtree of the second location?
argOrRes :: Location -> Location -> ArgOrRes
argOrRes (ArgumentOf loc') loc = if loc == loc' then Arg else argOrRes loc' loc
argOrRes (ResultOf loc')   loc = if loc == loc' then Res else argOrRes loc' loc
argOrRes Trunk             _   = error $ "argOrRes: Second location is not on the path"
                                       ++ "between root and the first location."

-- 
argNum :: Location -> Int
argNum (ResultOf loc)   = 1 + (argNum loc)
argNum (ArgumentOf loc) = argNum loc
argNum Trunk            = 1

type Visit a = Maybe Event -> Location -> a -> a

-- Given an event, return the list of (expected) children in depth-first order.
--
-- Nothing indicates that we expect an event (e.g. the argument of an application-
-- event) but it was not there.
--
-- An abstraction (LamEvent) can have more than one application. There is no
-- particular ordering and we just return the applications (AppEvents) in the
-- order we find them in the trace (i.e. evaluation order).

dfsChildren :: EventForest -> Event -> [Maybe Event]
dfsChildren forest e = case e of
    (RootEvent _ _ i)    -> byPosition [1]
    (ConstEvent i _ _ l) -> byPosition [1..l]
    (LamEvent i _)       -> map (Just . snd) cs
    (AppEvent i _)       -> byPosition [1,2]

  where -- Find list of events by position
        byPosition :: [ParentPosition] -> [Maybe Event]
        byPosition = map (\pos -> lookup pos cs)

        -- Events in the forest that list our event as parent (in no particular order).
        cs :: [(ParentPosition,Event)]
        cs = case lookup (eventUID e) forest of (Just cs') -> cs'; _ -> []

        
dfsFold :: InfixOrPrefix -> Visit a -> Visit a -> a 
        -> Location -> (Maybe Event) -> EventForest -> a

dfsFold ip pre post z w me forest 
  = post me w $ case me of
      Nothing -> z'

      (Just (AppEvent _ _)) -> let [arg,res] = cs
        in case ip of
          Prefix -> csFold $ zip cs [ArgumentOf w,ResultOf w]
          Infix  -> let z1 = dfsFold ip pre post z (ArgumentOf w) arg forest
                        z2 = pre me w z1
                    in  dfsFold ip pre post z2 (ResultOf w) res forest

      _ -> csFold $ zip cs (repeat w)

  where z'  = pre me w z

        cs :: [Maybe Event]
        cs = case me of (Just e) -> dfsChildren forest e

        csFold = foldl (\z'' (c,w') -> dfsFold ip pre post z'' w' c forest) z'

--------------------------------------------------------------------------------
-- Pegs and holes in event trees

data Hole = Hole { holeIds :: [UID] } deriving (Eq,Ord,Show)

delIds :: Hole -> [UID] -> Hole
delIds (Hole is) js = Hole (is \\ js)
-- delIds (ArgHole i is) js = ArgHole i (is \\ js)
-- delIds (ResHole i is) js = ResHole i (is \\ js)

(\\\) :: Hole -> Hole -> Hole
h \\\ k = delIds h (holeIds k)

(\\\\) :: [Hole] -> [Hole] -> [Hole]
hs \\\\ ks = map (\h -> foldl (\h' k -> h' \\\ k) h ks) hs


rmEmpty :: [Hole] -> [Hole]
rmEmpty = filter (\h -> holeIds h /= [])

data AppScope = Scope { appLocation :: Location 
                      , argIds      :: [Int]
                      , resIds      :: [Int]
                      }

newScope :: Location -> AppScope
newScope l = Scope l [] []

addToScopes :: [AppScope] -> Location -> Int -> [AppScope]
addToScopes ss l i  = map add ss
  where add s = case argOrRes l (appLocation s) of
                  Arg -> s{argIds=i:argIds s}
                  Res -> s{resIds=i:resIds s}

holes :: EventForest -> Event -> [Hole]
holes forest root = snd $ dfsFold Prefix pre post z Trunk (Just root) forest

  where z :: ([AppScope], [Hole])
        z = ([],[])

        uids = treeUIDs forest root

        -- On dfs previsit collect ids per subtree
        pre :: Visit ([AppScope],[Hole])
        pre Nothing                     l x       = x
        pre (Just (ConstEvent i _ _ _)) l (ss,hs) = (addToScopes ss l i, hs)
        pre (Just (RootEvent _ _ i))    l x       = x
        pre (Just (LamEvent i _))       l (ss,hs) = (addToScopes ss l i, hs)
        pre (Just e@(AppEvent i _))     l (ss,hs)
          | hasFinalRes e = (newScope l:ss,hs)
          | otherwise     = (addToScopes ss l i, hs)
   
        -- On dfs postvisit calculate holes using collected ids
        post :: Visit ([AppScope],[Hole])
        post Nothing                     _ x = x
        post (Just (ConstEvent _ _ _ _)) _ x = x
        post (Just (RootEvent _ _ _))    _ x = x
        post (Just (LamEvent _ _))       _ x = x
        post (Just e@(AppEvent i _))     l x
          | hasFinalRes e  = let ((Scope _ as rs):ss,hs)  = x
                                 m = minimum [(maximum as) + 1, minimum rs]
                                 h = Hole [j | j <- [m .. maximum rs], j `notElem` uids]
                             in (ss, h:hs)
          | otherwise      = x

        hasFinalRes :: Event -> Bool
        hasFinalRes e = let [arg,res] = dfsChildren forest e in case res of
          (Just (ConstEvent _ _ _ _)) -> True
          _                           -> False

-- Infering dependencies from events

type Dependency = (UID,UID,UID)              -- Parent-root UID, Child-root UID, hole/peg UID
type TreeDescr  = (Event  -- Root event
                  ,[UID]  -- UIDs of events in this tree
                  ,[Hole] -- Holes in the event UIDs
                  ,[UID]) -- Inherited UIDs (of child events)

dependencies :: EventForest -> Trace -> [Dependency]
dependencies forest rs = loop ts0 []

  where ts0 :: [TreeDescr]
        ts0 = map (\r -> let is = treeUIDs forest r in (r, is, holes forest r, is)) rs

        loop :: [TreeDescr] -> [Dependency] -> [Dependency]
        loop ts as = let ts' = map (\(e,is,hs,js) -> (e,is,rmEmpty hs,js)) ts
                     in if all (\(_,_,hs,_) -> case hs of [] -> True; _ -> False) ts'
                        then as
                        else let (ts'',a) = oneDependency ts' 
                             in  if ts'' == ts' then error "dependencies got stuck"
                                                else loop ts'' (a:as)

-- Find a list of holes between arguments and result
-- resHoles :: EventForest -> Event -> [Hole]
-- resHoles forest = (filter $ \h -> case h of (ResHole _ _) -> True; _ -> False) . (holes forest)


-- Resolve the first dependency for which we find a matching hole/peg pair, and remove
-- the hole and any overlapping holes between parent/child from the parent.
oneDependency :: [TreeDescr] -> ([TreeDescr], Dependency)
oneDependency ts = (rmOverlap ts (e,is,hs,js) (e_p,is_p,hs_p,js_p), (eventUID e, eventUID e_p, h))
       
  where -- The first TreeDescr with a hole left
        (e,is,hs,js) = case find (\(_,_,hs,_) -> hs /= []) ts of
                         (Just t) -> t
                         Nothing  -> error "oneDependency: No more holes left?"

        -- The last hole in the TreeDescr
        h :: UID
        h = case (last hs) of (Hole xs) -> last xs

        -- The TreeDescr with the peg that fits the hole
        (e_p,is_p,hs_p,js_p) = dependency ts h

rmOverlap :: [TreeDescr] -> TreeDescr -> TreeDescr -> [TreeDescr]
rmOverlap ts t_h t_p = map (\t -> if t == t_h then rmOverlap1 t_h t_p else t) ts

rmOverlap1 :: TreeDescr -> TreeDescr -> TreeDescr
rmOverlap1 (e,is,hs,js) (e',is',hs',js') = (e,is,new_hs,new_js)
  where new_hs = map (flip delIds $ is' ++ js') hs \\\\ hs'
        new_js = nub (js ++ js')

-- Given a hole, find TreeDescr with mathing peg
dependency :: [TreeDescr] -> UID -> TreeDescr
dependency ts h = case filter (\(_,pegs,_,_) -> h `elem` pegs) ts of
                     []    -> error "dependency: A UID disappeared!"
                     (t:_) -> t

--------------------------------------------------------------------------------
-- Debug

data Vertex = RootVertex | Vertex [CompStmt] deriving (Eq)
type CompGraph = Graph Vertex PegIndex
type PegIndex = Int

mkGraph :: (Expr,Trace,[CompStmt]) -> (Expr,CompGraph)
mkGraph (reduct,trc,cs) = let (Graph _ vs as) = mapGraph mkVertex (mkGraph' trc cs)
                              rs              = filter (\(Vertex [c]) -> stmtStack c == []) vs
                              as'             = map (\r -> Arc RootVertex r 0) rs
                          in (reduct, Graph RootVertex (RootVertex:vs) (as' ++ as))

mkGraph' :: Trace -> [CompStmt] -> Graph CompStmt PegIndex
mkGraph' trc cs
  | length cs < 1 = error "mkGraph: no computation statements?"
  | otherwise = Graph (head cs) -- doesn't really matter, replaced above
                      cs
                      (mkArcs trc cs)

mkVertex :: CompStmt -> Vertex
mkVertex c = Vertex [c]

mkArcs :: Trace -> [CompStmt] -> [Arc CompStmt PegIndex]
mkArcs trc cs = map (\(i,j,h) -> Arc (findC i) (findC j) h) ds
  where forest  = mkEventForest trc
        ds      = dependencies forest roots
        findC i = case find (\c -> i `elem` stmtUID c) cs of Just c -> c

        (roots,chds) = partition isRoot trc
        isRoot (RootEvent _ _ _) = True
        isRoot _                 = False

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
showCompStmt (CompStmt l s i r h) = r
        ++ "\n with stack " ++ show s
        ++ "\n with UIDs "  ++ show i
        ++ "\n with holes " ++ show h

showArc :: Arc Vertex PegIndex -> String
showArc (Arc _ _ i)  = show i

disp' f expr = do
  putStrLn (messages ++ strc)
  -- Uncomment the next line to write all reduction steps to file (for off-line analysis).
  writeFile "log" (messages ++ strc)
  f . snd . mkGraph . mkStmts $ (reduct,trc)
  where (reduct,trc,messages) = evaluate' expr
        strc = "\n\nReduct: " ++ show reduct
               ++ foldl (\acc s -> acc ++ "\n" ++ s) "\n\nEvent trace:" (map show $ reverse trc)
