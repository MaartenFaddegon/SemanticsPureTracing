import Semantics
import Examples
import DataDep
import EventForest

import Prelude hiding (Right)
import Data.List(isPrefixOf,sort)
import Test.QuickCheck
import Control.Monad.State
import Data.Graph.Libgraph
import Data.List (nub,(\\),find,sortBy)
import Data.Generics.Schemes(listify)
import Data.Ord (comparing)

--------------------------------------------------------------------------------
-- QuickCheck soundness property

subsetOf :: Ord a => [a] -> [a] -> Bool
subsetOf xs ys = isPrefixOf (sort xs) (sort ys)

nonEmptyTrace :: Expr -> Bool
nonEmptyTrace = not . null . snd . evaluate

prop_actuallyFaulty :: Expr -> Property
prop_actuallyFaulty e = nonEmptyTrace e ==> property $ algoDebug e `subsetOf` markedFaulty e

--------------------------------------------------------------------------------
-- Generating random expressions with observed abstractions

gen_expr :: Int -> Gen Expr
gen_expr 0 = gen_constr
gen_expr n = oneof [ gen_constr
                   , gen_var
                   , gen_case n
                   , liftM2 Lambda gen_varName (gen_expr $ n-1)
                   , liftM2 Apply  (gen_expr $ n-1) gen_varName
                   , liftM3 mkLet  gen_varName (gen_expr $ (n-1) `div` 2) (gen_expr $ (n-1) `div` 2)
                   , gen_observedLam n
                   ]
        where mkLet a e1 e2 = Let (a,e1) e2

gen_label :: Gen Label
gen_label = elements $ map (:[]) ['A'..'Z']

gen_jmt :: Gen Judgement
gen_jmt = elements [Right, Wrong]

gen_observedLam :: Int -> Gen Expr
gen_observedLam n = return oLam `ap` gen_label `ap` gen_jmt `ap` gen_varName `ap` (gen_expr $ n-2)
  where oLam l j v e = Observe l j (Lambda v e)

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
        gen_expr' = gen_expr $ (n - 1) `div` 7

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

--------------------------------------------------------------------------------
-- Main

main :: IO ()
main = quickCheckWith args prop_actuallyFaulty
  where args = Args { replay          = Nothing
                    , maxSuccess      = 1000  -- number of tests
                    , maxDiscardRatio = 100
                    , maxSize         = 8   -- max subexpressions
                    , chatty          = True
                    }


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

data CompStmt
 = CompStmt
    { stmtLabel     :: Label
    , stmtUID       :: [UID]
    , stmtRepr      :: String
    , stmtHoles     :: [Hole]
    , stmtJudgement :: Judgement
    }
  deriving (Show,Eq,Ord)

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


