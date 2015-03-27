{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}
module Semantics where

import Prelude hiding (Right)
import Control.Monad.State
import Data.Graph.Libgraph
import Data.List (nub,(\\),find)
import Test.QuickCheck
import Data.Data hiding (Infix,Prefix)
import Data.Generics.Schemes(listify)

--------------------------------------------------------------------------------
-- Expressions

data Expr = Lambda     Name Expr
          | Apply      Expr Name
          | Var        Name
          | Let        (Name,Expr) Expr
          | Constr     ConstrId [Name]
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

data ConstrId = WrongConstr 
              | ConstrId Int 
              deriving (Eq,Ord,Data,Typeable)

instance Show ConstrId where show WrongConstr  = ":("
                             show (ConstrId i) = "c_" ++ show i

--------------------------------------------------------------------------------
-- Examples

-- We will use the following constructor encoding in the examples:
c_0 :: [Name] -> Expr
c_0 = Constr (ConstrId 0) -- False

c_1 :: [Name] -> Expr
c_1 = Constr (ConstrId 1) -- True

c_2 :: [Name] -> Expr
c_2 = Constr (ConstrId 2) -- the empty list []

c_3 :: [Name] -> Expr
c_3 = Constr (ConstrId 3) -- the list constructor (:)


-- NOTE: this only traces the top, subsequent (recursive) calls to foldl are not traced
foldlTraced :: Expr -> Expr
foldlTraced = Let ("foldlT", Lambda "f" $ Lambda "xs"  $ Lambda "z"
                           $ Apply (Apply (Apply (Observe "foldl" Right
                             (Var "foldl")) "f") "xs" ) "z")

sumTraced :: Expr -> Expr
sumTraced = Let ("sum", Lambda "xs" (Apply (Observe "sum" Right (Lambda "xs'" 
                        (Apply (Apply (Apply (Var "foldl") "p") "0" )"xs'"))) "xs"))

mapTraced :: Expr -> Expr
mapTraced = Let ("mapT", Lambda "f" $ Lambda "xs"
                       $ Apply (Apply (Observe "map" Right (Var "map")) "f") "xs" )

-- data B = T | F
-- n :: B -> B
myNot :: Expr -> Expr
myNot     = Let ("n", Lambda "b" $ Case (Var "b")
                    [ (c_1 [], c_0 [])
                    , (c_0 [], c_1 [])
                    ])

notTraced :: Expr -> Expr
notTraced = Let ("n", Lambda "b'" $ Apply (Observe "n" Right $ Lambda "b"
                      $ Case (Var "b")
                             [ (c_1 [], c_0 [])
                             , (c_0 [], c_1 [])
                             ]) "b'")


-- x :: B -> B -> B
myXor :: Expr -> Expr
myXor = Let ("x", Lambda "a1" $ Lambda "a2" $ Apply (Apply (Observe "x" Right $ Lambda "b1" $ Lambda "b2"
                      $ Case (Var "b1")
                             [ (c_1 [], Case (Var "b2")[ (c_1 [], c_0 [])
                                                              , (c_0 [], c_1 [])])
                             , (c_0 [], Case (Var "b2")[ (c_1 [], c_1 [])
                                                              , (c_0 [], c_1 [])])
                             ]
                             ) "a1") "a2")


ex1 :: Expr
ex1 = {- import -} prelude
    $ {- import -} notTraced
    $ Let ("b", (c_0 []))
    $ Print $ Apply (Var "n") "b"

-- Example 2: Function h and n are traced, h maps over a list and n is
-- applied to all elements.
--
--   a) without reverse
--   b) reverse before printing (but outside traced code)
ex2a :: Expr
ex2a = {- import -} prelude
     $ {- import -} notTraced
     $ Let ("xs", Let ("a", c_1 [])
                $ Let ("b", c_0 [])
                $ Let ("c2", c_2 [])
                $ Let ("c1", c_3 ["b", "c2"])
                $            c_3 ["a","c1"])
     $ Let ("h", Lambda "xs" (Apply (Observe "h" Right (Apply (Var "map") "n")) "xs"))
     $ Print $ Apply (Var "h") "xs"

ex2b :: Expr
ex2b = {- import -} prelude
     $ {- import -} notTraced
     $ Let ("xs", Let ("a", c_1 [])
                $ Let ("b", c_0 [])
                $ Let ("c2", c_2 [])
                $ Let ("c1", c_3 ["b", "c2"])
                $            c_3 ["a","c1"])
     $ Let ("h", Lambda "xs" (Apply (Observe "h" Right (Apply (Var "map") "n")) "xs"))
     $ Print $ Let ("ys", Apply (Var "h") "xs") 
             $ Apply (Var "reverse") "ys"

-- Example 3: Trace map and its callees, reverse result before printing
-- but outside traced code
ex3a :: Expr
ex3a = {- import -} prelude
     $ {- import -} myNot
     $ {- import -} mapTraced
     $ Let ("xs", Let ("a", c_1 [])
                $ Let ("b", c_0 [])
                $ Let ("c2", c_2 [])
                $ Let ("c1", c_3 ["b", "c2"])
                $            c_3 ["a","c1"])
     $ Print $ Let ("ys", Apply (Apply (Var "mapT") "n") "xs")
             $ Var "ys"

ex3b :: Expr
ex3b = {- import -} prelude
     $ {- import -} notTraced
     $ {- import -} mapTraced
     $ Let ("xs", Let ("a", c_1 [])
                $ Let ("b", c_0 [])
                $ Let ("c2", c_2 [])
                $ Let ("c1", c_3 ["b", "c2"])
                $            c_3 ["a","c1"])
     $ Print $ Let ("ys", Apply (Apply (Var "mapT") "n") "xs")
             $ Apply (Var "reverse") "ys"

-- Example 4: Trace foldl and its callees in a simple checksum program
ex4 :: Expr
ex4 = {- import -} prelude
    $ {- import -} foldlTraced
    $ {- import -} myXor
     $ Let ("bs", Let ("a", c_1 [])
                $ Let ("b", c_0 [])
                $ Let ("c2", c_2 [])
                $ Let ("c1", c_3 ["b", "c2"])
                $            c_3 ["a","c1"])
     $ Let ("z", c_0 [])
     $ Print $ Apply (Apply (Apply (Var "foldlT") "x") "z") "bs"

-- Example 5: 
--      a) f -> g -> h
--      b) f -> g, f -> h
ex5a :: Expr
ex5a = Let ("h", Observe "h" Wrong $ Lambda "y" $ Var "y")
     $ Let ("g", Observe "g" Right $ Lambda "y" $ Apply (Var "h") "y")
     $ Let ("f", Observe "f" Right $ Lambda "y" $ Apply (Var "g") "y")
     $ Let ("k", c_1 [])
     $ Print $ Apply (Var "f") "k"

ex5b :: Expr
ex5b = Let ("h", Observe "h" Wrong (Lambda "y" $ Var "y"))
     $ Let ("g", Observe "g" Right (Lambda "y" $ Var "y"))
     $ Let ("f", Observe "f" Right (Lambda "y" $ Let ("z", Apply (Var "g") "y")
                                                               (Apply (Var "h") "z")
                                             ))
     $ Let ("k", c_1 [])
     $ Print $ Apply (Var "f") "k"


--------------------------------------------------------------------------------
-- Prelude, with:
--
-- map = \f xs -> case xs of (c_2 [])    -> xs
--                           (c_3 [h,t]) -> let h' = f h, t' = map f t
--                                                   in c_3 [h', t']
--
-- foldl = \f z xs -> case xs of (c_2 [])    -> z
--                               (c_3 [h,t]) -> let z' = f z h
--                                                       in foldl f z' t
-- reverse = \xs -> let f = \z x -> c_3 [x,z]
--                      z = c_2 []
--                  in foldl f z xs


prelude :: Expr -> Expr
prelude e = Let ("map", Lambda "f" $ Lambda "xs" 
                      $ Case (Var "xs")
                             [ (c_2 [], Var "xs")
                             , ( c_3 ["h","t"]
                               , Let ("h'", Apply (Var "f") "h")
                               $ Let ("t'", Apply (Apply (Var "map") "f") "t")
                               $ c_3 ["h'","t'"]
                               )
                             ])
          $ Let ("foldl", Lambda "f" $ Lambda "z"  $ Lambda "xs"
                        $ Case (Var "xs")
                             [ (c_2 [], Var "z")
                             , ( c_3 ["h","t"]
                               , Let ("z'", Apply (Apply (Var "f") "z") "h")
                               $ Apply (Apply (Apply (Var "foldl") "f") "z'") "t"
                               )
                             ])
          $ Let ("reverse", Lambda "xs"
                          $ Let ("f", Lambda "z" $ Lambda "x"
                                    $ c_3 ["x","z"])
                          $ Let ("z", c_2 [])
                          $ Apply (Apply (Apply (Var "foldl") "f") "z") "xs")
          $ e



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
  doTrace (RootEvent l uid)
  eval (Observed (Parent uid 1) jmt e)

reduce (Observed p jmt e) = do
  w <- eval e
  case w of
    Exception msg ->
      return (Exception msg)

    -- ObsC rule in paper
    (Constr s ns) -> do
      let t = case jmt of Right -> s; Wrong -> WrongConstr
                          Unassessed -> error "Unassessed judgement in ObsC rule"
      i <- getUniq
      doTrace (ConstEvent i p t (length ns))
      ms <- mapM getFreshVar ns
      eval $ foldl (\e' (m,n,j) -> Let (m, Observed (Parent i j) jmt (Var n)) e')
                   (Constr t ms) (zip3 ms ns [1..])

    -- ObsL rule in paper
    (Lambda x e') -> do
      i <- getUniq
      doTrace (LamEvent i p)
      x1 <- getFreshVar x
      return (Lambda x1 (FunObs (Parent i 1) jmt x x1 e'))

    e' -> 
      return (Exception $ "Observe undefined: " ++ show e')

-- ObsF rule in paper
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
    (Constr i ys) -> case myLookup i alts of
                       (Just alt) -> red ys alt
                       Nothing    -> return $ non_exh i
    _ -> return $ Exception "Case on a non-Constr expression"
    
    where non_exh n                = Exception $ "Non-exhaustive patterns in Case: " ++ show n
          myLookup n               = (lookup n) . (map $ \(Constr t ys,e)->(t,(Constr t ys,e)))
          red ys (Constr _ xs, e2) = eval $ foldl (\e (x,y) -> subst x y e) e2 (zip xs ys)
          red _  _                 = error "Substitute in reduce Case alternative went wrong"

reduce (Constr i xs) = return $ Constr i xs

reduce (Print e) = do
  e' <- eval e
  case e' of
        (Constr i ns) -> do
          doPrint (show i)
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
subst n m (Constr s ns)         = Constr s $ map (sub n m) ns
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

fresh (Constr s ns) =
  return (Constr s ns)

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
  = RootEvent
    { eventLabel     :: Label
    , eventUID       :: UID
    } 
  | ConstEvent
    { eventUID       :: UID
    , eventParent    :: Parent
    , eventRepr      :: ConstrId
    , eventLength    :: Int
    }
  | LamEvent
    { eventUID       :: UID
    , eventParent    :: Parent
    }
  | AppEvent
    { eventUID       :: UID
    , eventParent    :: Parent
    }    
  deriving (Show,Eq,Ord)

data CompStmt
 = CompStmt
    { stmtLabel     :: Label
    , stmtUID       :: [UID]
    , stmtRepr      :: String
    , stmtHoles     :: [Hole]
    , stmtJudgement :: Judgement
    }
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

--------------------------------------------------------------------------------
-- Trace post processing

-- Searchable mapping from UID of the parent and position in list of siblings
-- to a child event.
type EventForest = [(UID, [(Int, Event)])]

isRoot :: Event -> Bool
isRoot (RootEvent _ _) = True
isRoot _               = False

mkEventForest :: Trace -> EventForest
mkEventForest trc = map children trc
  where children e = let j = eventUID e
                     in (j, map    (\c -> (parentPosition . eventParent $ c, c))
                          $ filter (\e' -> j == (parentUID . eventParent) e') chds)
        chds = filter (not . isRoot) trc

mkStmts :: (Expr,Trace) -> (Expr,Trace,[CompStmt])
mkStmts (reduct,trc) = (reduct,trc, map (mkStmt forest) roots)

  where roots = filter isRoot trc
        forest = mkEventForest trc

mkStmt :: EventForest -> Event -> CompStmt
mkStmt forest (e@(RootEvent lbl _)) = CompStmt lbl i repr h j

        where i :: [UID]
              i = treeUIDs forest e

              repr :: String
              repr = dfsFold Infix pre post "" Trunk (Just e) forest
              pre Nothing                         _ = (++" _")
              pre (Just RootEvent{eventLabel=l})  _ = (++l)
              pre (Just ConstEvent{eventRepr=r})  _ = (++" ("++show r)
              pre (Just LamEvent{})               _ = (++" {")
              pre (Just AppEvent{})               _ = (++" ->")
              post Nothing                        _ = id
              post (Just RootEvent{})             _ = id
              post (Just ConstEvent{})            _ = (++")")
              post (Just LamEvent{})              _ = (++"}")
              post (Just AppEvent{})              _ = id

              h :: [Hole]
              h = holes forest e

              j :: Judgement
              j = judgeTree forest e
mkStmt _ e = error $ "mkStmt should be given RootEvent, was given " ++ show e

judgeTree :: EventForest -> Event -> Judgement
judgeTree forest e@AppEvent{} 
  = let [arg,res] = dfsChildren forest e
    in case (judgeEventList forest [arg],judgeEventList forest [res]) of
         (Right,jmt)     -> jmt
         (Wrong,_  )     -> Right
         (Unassessed, _) -> error "judgeTree expected Right or Wrong, got Unassessed"
judgeTree _ ConstEvent{eventRepr=WrongConstr} = Wrong
judgeTree forest e = judgeEventList forest (dfsChildren forest e)

judgeEventList :: EventForest -> [Maybe Event] -> Judgement
judgeEventList forest = bool2jmt . (all isRight) . (map judgeME)
  where judgeME Nothing  = Right
        judgeME (Just e) = judgeTree forest e
        isRight Right    = True
        isRight _        = False
        bool2jmt True    = Right
        bool2jmt _       = Wrong


treeUIDs :: EventForest -> Event -> [UID]
treeUIDs forest r = reverse $ dfsFold Prefix addUID nop [] Trunk (Just r) forest
  where addUID (Just e) _ is = eventUID e : is
        addUID Nothing  _ is = is
        nop    _        _ is = is

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
    RootEvent{}               -> byPosition [1]
    ConstEvent{eventLength=l} -> byPosition [1..l]
    LamEvent{}                -> map (Just . snd) cs
    AppEvent{}                -> byPosition [1,2]

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
        cs = case me of (Just e) -> dfsChildren forest e; Nothing -> error "dfsFold filter failed"

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
holes forest rootEvent = snd $ dfsFold Prefix pre post z Trunk (Just rootEvent) forest

  where z :: ([AppScope], [Hole])
        z = ([],[])

        uids = treeUIDs forest rootEvent

        -- On dfs previsit collect ids per subtree
        pre :: Visit ([AppScope],[Hole])
        pre Nothing                        _ x       = x
        pre (Just ConstEvent{eventUID=i})  l (ss,hs) = (addToScopes ss l i, hs)
        pre (Just RootEvent{})             _ x       = x
        pre (Just LamEvent{eventUID=i})    l (ss,hs) = (addToScopes ss l i, hs)
        pre (Just e@AppEvent{eventUID=i})  l (ss,hs)
          | hasFinalRes e = (newScope l:ss,hs)
          | otherwise     = (addToScopes ss l i, hs)
   
        -- On dfs postvisit calculate holes using collected ids
        post :: Visit ([AppScope],[Hole])
        post Nothing                        _ x = x
        post (Just ConstEvent{})            _ x = x
        post (Just RootEvent{})             _ x = x
        post (Just LamEvent{})              _ x = x
        post (Just e@AppEvent{})            _ x
          | hasFinalRes e  = let ((Scope _ as rs):ss,hs)  = x
                                 m = minimum [(maximum as) + 1, minimum rs]
                                 h = Hole [j | j <- [m .. maximum rs], j `notElem` uids]
                             in (ss, h:hs)
          | otherwise      = x

        hasFinalRes :: Event -> Bool
        hasFinalRes e = let [_,res] = dfsChildren forest e in case res of
          (Just ConstEvent{}) -> True
          _                   -> False

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
        (e,is,hs,js) = case find (\(_,_,hs',_) -> hs' /= []) ts of
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
rmOverlap1 (e,is,hs,js) (_,is',hs',js') = (e,is,new_hs,new_js)
  where new_hs = map (flip delIds $ is' ++ js') hs \\\\ hs'
        new_js = nub (js ++ js')

-- Given a hole, find TreeDescr with mathing peg
dependency :: [TreeDescr] -> UID -> TreeDescr
dependency ts h = case filter (\(_,pegs,_,_) -> h `elem` pegs) ts of
                     []    -> error "dependency: A UID disappeared!"
                     (t:_) -> t

--------------------------------------------------------------------------------
-- Constructing a computation graph

data Vertex = RootVertex | Vertex CompStmt deriving (Eq,Show,Ord)
type CompGraph = Graph Vertex PegIndex
type PegIndex = Int

mkGraph :: (Expr,Trace,[CompStmt]) -> (Expr,CompGraph)
mkGraph (reduct,trc,cs) = let (Graph _ vs as) = mapGraph mkVertex (mkGraph' trc cs)
                              rs              = [last vs] -- TODO: used to be vs with [] as stack
                              as'             = map (\r -> Arc RootVertex r 0) rs
                          in (reduct, Graph RootVertex (RootVertex:vs) (as' ++ as))

mkGraph' :: Trace -> [CompStmt] -> Graph CompStmt PegIndex
mkGraph' trc cs
  | length cs < 1 = error "mkGraph: no computation statements?"
  | otherwise = Graph (head cs) -- Doesn't really matter, is replaced above
                      cs
                      (mkArcs trc cs)

mkVertex :: CompStmt -> Vertex
mkVertex c = Vertex c

mkArcs :: Trace -> [CompStmt] -> [Arc CompStmt PegIndex]
mkArcs trc cs = map (\(i,j,h) -> Arc (findC i) (findC j) h) ds
  where forest  = mkEventForest trc
        ds      = dependencies forest roots
        findC i = case find (\c -> i `elem` stmtUID c) cs of Just c -> c; Nothing -> error "mkArcs: non-existant peg?"
        roots   = filter isRoot trc

--------------------------------------------------------------------------------
-- Evaluate and display.

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
showVertex' (Vertex c) = showCompStmt c

showCompStmt :: CompStmt -> String
showCompStmt (CompStmt _ i r h j) = r
        ++ "\n with UIDs "     ++ show i
        ++ "\n with holes "    ++ show h
        ++ "\n with judgment " ++ show j

showArc :: Arc Vertex PegIndex -> String
showArc (Arc _ _ i)  = show i

disp' :: (CompGraph -> IO a) -> Expr -> IO a
disp' f expr = do
  putStrLn (messages ++ strc)
  -- Uncomment the next line to write all reduction steps to file (for off-line analysis).
  -- writeFile "log" (messages ++ strc)
  f . snd . mkGraph . mkStmts $ (reduct,trc)
  where (reduct,trc,messages) = evaluate' expr
        strc = "\n\nReduct: " ++ show reduct
               ++ foldl (\acc s -> acc ++ "\n" ++ s) "\n\nEvent trace:" (map show $ reverse trc)


--------------------------------------------------------------------------------
-- Finding faulty program slices

-- Evaluate, and use algorithmic debugging on result
algoDebug :: Expr -> [Label]
algoDebug = map getLbl . findFaulty_dag j . snd . mkGraph . mkStmts . evaluate
  where j RootVertex = Right
        j (Vertex c) = stmtJudgement c
        getLbl (Vertex c) = stmtLabel c
        getLbl RootVertex = error "Algorithmic debugging marked root as faulty!"

-- Extract program slices we marked as faulty
markedFaulty :: Expr -> [Label]
markedFaulty = map getLabel . listify isMarked

  where isMarked :: Expr -> Bool
        isMarked (Observe _ Wrong _) = True
        isMarked _                   = False

        getLabel :: Expr -> Label
        getLabel (Observe l Wrong _) = l
        getLabel _                   = "Filtered wrong Expr in markedFaulty!"
 
        -- MF TODO: rather than map over listify results do something with gfoldl here?
        -- addF :: [Label] -> Expr -> [Label]
        -- addF ls (Observe l Wrong _) = l : ls
        -- addF ls _                   = ls

--------------------------------------------------------------------------------
-- Generating random expressions

gen_varName :: Gen String
gen_varName = elements $ map (:[]) ['a'..'i']

gen_var :: Gen Expr
gen_var = liftM Var gen_varName

gen_constr :: Gen Expr
gen_constr = oneof [ elements [c_0 [], c_1 [], c_2 []]
                     , liftM2 (\v1 v2 -> c_3 [v1,v2]) gen_varName gen_varName
                     ]

gen_case :: Int -> Gen Expr
gen_case n = return mkCase `ap` gen_expr' `ap` gen_expr' `ap` gen_expr' `ap` gen_expr' `ap` gen_expr' 
                           `ap` gen_varName `ap` gen_varName
  where mkCase e e0 e1 e2 e3 n1 n2 = Case e [(c_0 [],e0),(c_1 [],e1),(c_2 [],e2),(c_3 [n1,n2],e3)]
        gen_expr' = gen_expr $ (n `div` 7) - 1

gen_expr :: Int -> Gen Expr
gen_expr 0 = gen_constr
gen_expr n = oneof [ gen_constr
                   , gen_var
                   , gen_case n
                   , liftM2 Lambda gen_varName (gen_expr $ n-1)
                   , liftM2 Apply  (gen_expr $ n-1) gen_varName
                   , liftM3 mkLet  gen_varName (gen_expr $ n-1 `div` 2) (gen_expr $ n-1 `div` 2)
                   , liftM3 Observe gen_label gen_jmt (gen_expr $ n-1)
                   ]
  where gen_label         = elements $ map (:[]) ['A'..'Z']
        gen_jmt           = elements [Right, Wrong]
        mkLet a e1 e2     = Let (a,e1) e2

uniqueLabels :: Expr -> Expr
uniqueLabels e = snd (uniqueLabels' lbls e)
  where lbls = zipWith (++) (cycle ["CC"]) (map show' [1..])
        show' = show :: Integer -> String

uniqueLabels' :: [Label] -> Expr -> ([Label], Expr)
uniqueLabels' []   _                     = error "uniqueLabels' exhausted available labels"
uniqueLabels' lbls (Constr n fs)         = (lbls,Constr n fs)
uniqueLabels' lbls (Lambda n e)          = let (lbls',e') = uniqueLabels' lbls e
                                           in (lbls',Lambda n e')
uniqueLabels' lbls (Apply e n)           = let (lbls',e') = uniqueLabels' lbls e
                                           in (lbls',Apply e' n)
uniqueLabels' lbls (Var n)               = (lbls,Var n)
uniqueLabels' lbls (Let (n,e1) e2)       = let (lbls1,e1') = uniqueLabels' lbls  e1
                                               (lbls2,e2') = uniqueLabels' lbls1 e2
                                           in (lbls2,Let (n,e1') e2')
uniqueLabels' (l:lbls) (Observe _ j e)   = let (lbls',e') = uniqueLabels' lbls e
                                           in (lbls',Observe l j e')
uniqueLabels' lbls     (Case e alts)     = let (lbls',alts') = foldl (\(ls,as) alt -> let (ls',a) = uniqueLabels'_tuple ls alt 
                                                                                      in (ls',a:as)) (lbls,[]) alts
                                               (lbls'',e')   = uniqueLabels' lbls' e
                                           in (lbls'',Case e' alts') 
uniqueLabels' _ expr                      = error $ "Unexpected expr '" ++ show expr ++ "' in uniqueLabels'."

uniqueLabels'_tuple :: [Label] -> (Expr,Expr) -> ([Label], (Expr,Expr))
uniqueLabels'_tuple ls (e1,e2) = let (ls', e1') = uniqueLabels' ls  e1
                                     (ls'',e2') = uniqueLabels' ls' e2
                                 in (ls'', (e1',e2'))

instance Arbitrary Expr where

  arbitrary = sized gen_expr

  shrink (Constr _ _)      = []
  shrink (Observe l j e)   = e : (map (Observe l j) (shrink e))
  shrink (Lambda n e)      = e : (map (Lambda n) (shrink e))
  shrink (Apply e n)       = let alts = e : (map (flip Apply n) (shrink e))
                             in case e of
                               (Lambda _ e') -> e' : alts
                               _             -> alts
  shrink (Let (n,e1) e2)   = e2 : e1
                             :    (map (Let (n,e1)) (shrink e2))
                             ++   (map (\e-> Let (n,e) e2) (shrink e1))
  shrink _                 = [c_0 []]

