{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}
module Semantics where

import Prelude hiding (Right)
import Control.Monad.State
import Data.Graph.Libgraph
import Data.List (nub,(\\),find,sortBy)
import Data.Ord (comparing)
import Data.Data hiding (Infix,Prefix)
import Data.Generics.Schemes(listify)
import Data.Maybe(mapMaybe)

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
    (Constr s ns) -> do
      let t = case jmt of Right -> s; Wrong -> WrongConstr
                          Unassessed -> error "Unassessed judgement in ObsC rule"
      i <- getUniq
      doTrace (ConstEvent i p t (length ns))
      ms <- mapM getFreshVar ns
      eval $ foldl (\e' (m,n,k) -> Let (m, Observed (Parent i k) jmt (Var n)) e')
                   (Constr t ms) (zip3 ms ns [1..])

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
  = RootEvent  { eventUID :: UID, eventLabel  :: Label }
  | EnterEvent { eventUID :: UID, eventParent :: Parent}
  | ConstEvent { eventUID :: UID, eventParent :: Parent, eventRepr :: ConstrId , eventLength :: Int}
  | LamEvent   { eventUID :: UID, eventParent :: Parent}
  | AppEvent   { eventUID :: UID, eventParent :: Parent}
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
-- Constant Values 

data ConstantValue = ConstantValue { valStmt :: UID, valLoc :: Location
                                   , valMin :: UID,  valMax :: UID }
                   | CVRoot
                  deriving Eq

type ConstantTree = Graph ConstantValue ()
type CVArc = Arc ConstantValue ()

instance Show ConstantValue where
  show CVRoot = "Root"
  show v = "Stmt-" ++ (show . valStmt $ v)
         ++ "-"    ++ (show . valLoc  $ v) 
         ++ ": "   ++ (show . valMin  $ v) 
         ++ "-"    ++ (show . valMax  $ v) 

constants :: EventForest -> Event -> [ConstantValue]
constants frt r = dfsFold Prefix pre idVisit [] Trunk (Just r) frt
  where pre :: Visit [ConstantValue]
        pre (Just ent) loc vs
          | isConstantTree frt ent = mkConstantValue ent loc : vs
          | otherwise              = vs
        pre _          _   vs      = vs

        mkConstantValue :: Event -> Location -> ConstantValue
        mkConstantValue e loc = let us = treeUIDs frt e
                          in ConstantValue (eventUID r) loc (minimum us) (maximum us)


-- Is given event the root of a (sub)tree describing a constant value?
-- Note that root must be an EnterEvent.
isConstantTree :: EventForest -> Event -> Bool
isConstantTree frt ent = case ent of 
  EnterEvent{} -> case head $ dfsChildren frt ent of
    (Just ConstEvent{}) -> True
    _                   -> False
  _            -> False
--------------------------------------------------------------------------------
-- Dynamic Data Dependency Tree

mkDDDT :: [ConstantValue] -> ConstantTree
mkDDDT vs = Graph CVRoot (CVRoot : vs) (as ++ as')
  where as  = mapMaybe (maybeDepends vs) vs
        as' = map (\r -> Arc CVRoot r()) rs
        rs  = filter (notEnclosed vs) vs

notEnclosed :: [ConstantValue] -> ConstantValue -> Bool
notEnclosed vs v = all (not . (flip encloses) v) vs

maybeDepends :: [ConstantValue] -> ConstantValue -> Maybe (CVArc)
maybeDepends vs v = do
  w <- closestEnclosing v vs
  return $ Arc w v ()

encloses :: ConstantValue -> ConstantValue -> Bool
encloses v w = valMin v < valMin w && valMax v > valMax w

closestEnclosing :: ConstantValue -> [ConstantValue] -> Maybe ConstantValue
closestEnclosing v vs = case filter (flip encloses $ v) vs of
  [] -> Nothing
  ws -> Just . head . sortBy (comparing minMaxDiff) $ ws

minMaxDiff :: ConstantValue -> Int
minMaxDiff v = (valMax v) - (valMin v)

--------------------------------------------------------------------------------
-- Last Open Result Dependency Tree

mkResDepTree :: ConstantTree -> ConstantTree
mkResDepTree ddt = Graph (root ddt) 
                         (filter resOrRoot $ vertices ddt) 
                         (visit [CVRoot] (succs ddt $ root ddt) [])

  where -- visit list of children
        visit :: CVStack -> [ConstantValue] -> [CVArc] -> [CVArc]
        visit cvs vs as = foldl (\as' v -> visit' cvs v as') as vs

        -- visit one child
        visit' :: CVStack -> ConstantValue -> [CVArc] -> [CVArc]
        visit' cvs v as
          | (isResult . valLoc) v = let as' = Arc (peekCVS cvs v) v () : as
                                    in  visit (pushCVS cvs v) (succs ddt v) as'
          | otherwise             =     visit (popCVS cvs)    (succs ddt v) as

        resOrRoot :: ConstantValue -> Bool
        resOrRoot CVRoot = True
        resOrRoot v = isResult . valLoc $ v
        
        isResult :: Location -> Bool
        isResult Trunk          = True
        isResult (ResultOf l)   = isResult l
        isResult (ArgumentOf _) = False



type CVStack = [ConstantValue]

pushCVS :: CVStack -> ConstantValue -> CVStack
pushCVS cvs r = r : cvs

popCVS :: CVStack -> CVStack
popCVS []      = []
popCVS (_:cvs) = cvs

popMatchCVS :: CVStack -> ConstantValue -> CVStack
popMatchCVS []      _ = error "Pop empty Constant Value Stack!"
popMatchCVS (r:cvs) a = case (valLoc r, valLoc a) of 
  (ResultOf rloc, ArgumentOf aloc) -> if rloc == aloc then cvs else err
  _                                -> err
  where err = error "Constant Value Stack mismatch on pop!"

peekCVS :: CVStack -> ConstantValue -> ConstantValue
peekCVS []     v = error $ (fst . shwCV) v ++ ": peek on empty Constant Value Stack!"
peekCVS (cv:_) _ = cv


--------------------------------------------------------------------------------
-- Trace post processing

analyseTrace :: Trace -> IO()
analyseTrace trc = do
  let rs   = filter isRoot trc
      frt  = mkEventForest trc
      cs   = map (mkStmt frt) rs
      -- vs= reverse . sortBy (comparing valMax) . foldl (\z r -> z ++ constants frt r) [] $ rs
      vs   =           sortBy (comparing valMin) . foldl (\z r -> z ++ constants frt r) [] $ rs
  putStrLn $ "Trace has " ++ (show . length $ trc) ++ " events."
  putStrLn $ "Trace has " ++ (show . length $ rs)  ++ " root events: " ++ (commaList . (map eventUID) $ rs)
  -- print statement representations
  mapM_ (\(r,c) -> putStrLn $ "Stmt-" ++ (show . eventUID $ r) ++ ": " ++ stmtRepr c) $ zip rs cs
  -- print constants
  putStrLn "Constants:"
  mapM_ print vs
  -- Dynamic data dependency tree
  putStrLn "Data dependencies:"
  let (Graph _ _ dds) = mkDDDT vs
  mapM_ (\dd -> putStrLn $ show (source dd) ++ " -> " ++ show (target dd)) dds



analyseDependency :: Trace -> [UID] -> IO ()
analyseDependency trc hs = loop hs 
  where rs   = filter isRoot trc
        frt  = mkEventForest trc

        r2us :: [(UID,[UID])]
        r2us = map (\r -> (eventUID r,treeUIDs frt r)) rs

        u2r :: [(UID,UID)]
        u2r  = foldl (\z (r,us) -> z ++ (map (\u -> (u,r)) us)) [] r2us

        loop :: [UID] -> IO ()
        loop [] = putStrLn "Done."
        loop xs = do putStrLn $ "Holes: " ++ show xs
                     let (Just r)  = lookup (last xs) u2r
                         (Just us) = lookup r r2us
                     putStrLn $ "Depends on Stmt-" ++ show r
                     loop (xs \\ us)

commaList :: Show a => [a] -> String
commaList xs = case xs of
  []  -> "-"
  [x] -> show x
  _   -> let (h:ys) = init xs
         in (foldl (\s x -> s ++ ", " ++ show x) (show h) ys) ++ " and " ++ show (last xs)

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
mkStmts (reduct,trc) = (reduct,trc, map (mkStmt frt) roots)

  where roots = filter isRoot trc
        frt = mkEventForest trc

mkStmt :: EventForest -> Event -> CompStmt
mkStmt frt (e@(RootEvent{eventLabel=lbl})) = CompStmt lbl i repr h j

        where i :: [UID]
              i = treeUIDs frt e

              repr :: String
              repr = dfsFold Infix pre post "" Trunk (Just e) frt
              pre Nothing                         _ = (++" _")
              pre (Just EnterEvent{})             _ = id
              pre (Just RootEvent{eventLabel=l})  _ = (++l)
              pre (Just ConstEvent{eventRepr=r})  _ = (++" ("++show r)
              pre (Just LamEvent{})               _ = (++" {")
              pre (Just AppEvent{})               _ = (++" ->")
              post Nothing                        _ = id
              post (Just EnterEvent{})            _ = id
              post (Just RootEvent{})             _ = id
              post (Just ConstEvent{})            _ = (++")")
              post (Just LamEvent{})              _ = (++"}")
              post (Just AppEvent{})              _ = id

              h :: [Hole]
              h = holes frt e

              j :: Judgement
              j = judgeTree frt e
mkStmt _ e = error $ "mkStmt should be given RootEvent, was given " ++ show e

judgeTree :: EventForest -> Event -> Judgement
judgeTree frt e@AppEvent{} 
  = let [arg,res] = dfsChildren frt e
    in case (judgeEventList frt [arg],judgeEventList frt [res]) of
         (Right,jmt)     -> jmt
         (Wrong,_  )     -> Right
         (Unassessed, _) -> error "judgeTree expected Right or Wrong, got Unassessed"
judgeTree _ ConstEvent{eventRepr=WrongConstr} = Wrong
judgeTree frt e = judgeEventList frt (dfsChildren frt e)

judgeEventList :: EventForest -> [Maybe Event] -> Judgement
judgeEventList frt = bool2jmt . (all isRight) . (map judgeME)
  where judgeME Nothing  = Right
        judgeME (Just e) = judgeTree frt e
        isRight Right    = True
        isRight _        = False
        bool2jmt True    = Right
        bool2jmt _       = Wrong


data InfixOrPrefix = Infix | Prefix

data Location = Trunk | ArgumentOf Location | ResultOf Location deriving Eq

instance Show Location where 
   show Trunk            = ""
   show (ArgumentOf loc) = 'a' : show loc
   show (ResultOf   loc) = 'r' : show loc

data ArgOrRes = Arg | Res

-- Is the first location in the argument, or result subtree of the second location?
argOrRes :: Location -> Location -> ArgOrRes
argOrRes (ArgumentOf loc') loc = if loc == loc' then Arg else argOrRes loc' loc
argOrRes (ResultOf loc')   loc = if loc == loc' then Res else argOrRes loc' loc
argOrRes Trunk             _   = error $ "argOrRes: Second location is not on the path"
                                       ++ "between root and the first location."

type Visit a = Maybe Event -> Location -> a -> a

idVisit :: Visit a
idVisit _ _ z = z

-- Given an event, return the list of (expected) children in depth-first order.
--
-- Nothing indicates that we expect an event (e.g. the argument of an application-
-- event) but it was not there.
--
-- An abstraction (LamEvent) can have more than one application. There is no
-- particular ordering and we just return the applications (AppEvents) in the
-- order we find them in the trace (i.e. evaluation order).

dfsChildren :: EventForest -> Event -> [Maybe Event]
dfsChildren frt e = case e of
    EnterEvent{}              -> byPosition [1]
    RootEvent{}               -> byPosition [1]
    ConstEvent{eventLength=l} -> byPosition [1..l]
    LamEvent{}                -> map (Just . snd) cs
    AppEvent{}                -> byPosition [1,2]

  where -- Find list of events by position
        byPosition :: [ParentPosition] -> [Maybe Event]
        byPosition = map (\pos -> lookup pos cs)

        -- Events in the frt that list our event as parent (in no particular order).
        cs :: [(ParentPosition,Event)]
        cs = case lookup (eventUID e) frt of (Just cs') -> cs'; _ -> []

        
dfsFold :: InfixOrPrefix -> Visit a -> Visit a -> a 
        -> Location -> (Maybe Event) -> EventForest -> a

dfsFold ip pre post z w me frt 
  = post me w $ case me of
      Nothing -> z'

      (Just (AppEvent _ _)) -> let [arg,res] = cs
        in case ip of
          Prefix -> csFold $ zip cs [ArgumentOf w,ResultOf w]
          Infix  -> let z1 = dfsFold ip pre post z (ArgumentOf w) arg frt
                        z2 = pre me w z1
                    in  dfsFold ip pre post z2 (ResultOf w) res frt

      _ -> csFold $ zip cs (repeat w)

  where z'  = pre me w z

        cs :: [Maybe Event]
        cs = case me of (Just e) -> dfsChildren frt e; Nothing -> error "dfsFold filter failed"

        csFold = foldl (\z'' (c,w') -> dfsFold ip pre post z'' w' c frt) z'

--------------------------------------------------------------------------------
-- Pegs and holes in event trees

data Hole = Hole { holeIds :: [UID] } deriving (Eq,Ord,Show)

delIds :: Hole -> [UID] -> Hole
delIds (Hole is) js = Hole (is \\ js)

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
holes frt r = map hole rs
  where rs = resultPair frt r
        js = treeUIDs frt r
        hole (ent,_) = let is = treeUIDs frt ent
                       in Hole [i | i <- [minimum is .. maximum is], i `notElem` js]

argEvents :: EventForest -> Event -> [[Event]]
argEvents frt r = dfsFold Prefix pre idVisit [] Trunk (Just r) frt
  where pre :: Visit [[Event]]
        pre (Just app@AppEvent{}) _ es = case dfsChildren frt app of
                [(Just ent),_] -> (eventsInTree frt ent) : es
                _              -> es
        pre _                     _ es = es

-- An event tree can have multiple applications. An application can have a function
-- map as argument or as result with more applications in it. In this function we
-- are interested in finding the results of applications that are a constant value.
-- For each constant value we return a depth first ordered list of events that describe
-- the constant value.
resultEvents :: EventForest -> Event -> [[Event]]
resultEvents frt r = dfsFold Prefix pre idVisit [] Trunk (Just r) frt
  where pre :: Visit [[Event]]
        pre (Just app@AppEvent{}) _ es = case dfsChildren frt app of
                [_,(Just ent)] -> if isConstantTree frt ent then (eventsInTree frt ent) : es else es
                _              -> es
        pre _                     _ es = es


-- Given an event r, return depth first ordered list of events in the (sub)tree starting from r.
eventsInTree :: EventForest -> Event -> [Event]
eventsInTree frt r = reverse $ dfsFold Prefix add idVisit [] Trunk (Just r) frt
  where add (Just e) _ es = e : es
        add Nothing  _ es = es

treeUIDs :: EventForest -> Event -> [UID]
treeUIDs frt = (map eventUID) . eventsInTree frt
-- treeUIDs frt r = reverse $ dfsFold Prefix addUID idVisit [] Trunk (Just r) frt
--   where addUID (Just e) _ is = eventUID e : is
--         addUID Nothing  _ is = is

-- Given the root of a tree in the frt, return for all final-result subtrees
-- the pair of (EnterEvent,ConstEvent) from the root the subtree.
resultPair :: EventForest -> Event -> [(Event,Event)]
resultPair frt r = dfsFold Prefix pre idVisit [] Trunk (Just r) frt
  where pre :: Visit [(Event,Event)]
        pre (Just app@AppEvent{}) _ es = let [_,res] = dfsChildren frt app
                                         in case res of
                                              (Just ent@EnterEvent{}) -> case head $ dfsChildren frt ent of
                                                                           (Just con@ConstEvent{}) -> (ent,con) : es
                                                                           _                       -> es
                                              _                       -> es
        pre _                   _ es   = es

-- Infering dependencies from events

type Dependency = (UID,UID,UID)              -- Parent-root UID, Child-root UID, hole/peg UID
type TreeDescr  = (Event  -- Root event
                  ,[UID]  -- UIDs of events in this tree
                  ,[Hole] -- Holes in the event UIDs
                  ,[UID]) -- Inherited UIDs (of child events)

dependencies :: EventForest -> Trace -> [Dependency]
dependencies frt rs = loop ts0 []

  where ts0 :: [TreeDescr]
        ts0 = map (\r -> let is = treeUIDs frt r in (r, is, holes frt r, is)) rs

        loop :: [TreeDescr] -> [Dependency] -> [Dependency]
        loop ts as = let ts' = map (\(e,is,hs,js) -> (e,is,rmEmpty hs,js)) ts
                     in if all (\(_,_,hs,_) -> case hs of [] -> True; _ -> False) ts'
                        then as
                        else let (ts'',a) = oneDependency ts' 
                             in  if ts'' == ts' then error "dependencies got stuck"
                                                else loop ts'' (a:as)

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
  where frt     = mkEventForest trc
        ds      = dependencies frt roots
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

dispDataDep :: Expr -> IO ()
dispDataDep e = display shwCT (evalDDT e)

dispResDep :: Expr -> IO ()
dispResDep e = display shwCT (mkResDepTree $ evalDDT e)

evalDDT :: Expr -> ConstantTree
evalDDT e = mkDDDT vs
  where trc = snd . evaluate $ e
        frt = mkEventForest trc
        rs  = filter isRoot trc
        vs  = sortBy (comparing valMin) . foldl (\z r -> z ++ constants frt r) [] $ rs

shwCT :: ConstantTree -> String
shwCT g = showWith g shwCV (\_ -> "")

shwCV :: ConstantValue -> (String,String)
shwCV v = (show (valLoc v) ++ "_" ++ show (valStmt v), "")

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


