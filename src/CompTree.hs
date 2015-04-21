module CompTree where
import Prelude hiding (Right)
import Semantics
import EventForest

import DataDep
import Data.Graph.Libgraph

data CompStmt
 = CompStmt
    { stmtLabel     :: Label
    , stmtUID       :: [UID]
    , stmtRepr      :: String
    , stmtJudgement :: Judgement
    }
  deriving (Show,Eq,Ord)
data Vertex = RootVertex | Vertex CompStmt deriving (Eq,Show,Ord)

type CompTree = Graph Vertex ()

--------------------------------------------------------------------------------
-- Computation Tree

mkCompTree :: [CompStmt] -> ConstantTree -> CompTree
mkCompTree cs = mapGraph findVertex
  where findVertex :: ConstantValue -> Vertex
        findVertex CVRoot = RootVertex
        findVertex v      = Vertex (findCompStmt cs v)

findCompStmt :: [CompStmt] -> ConstantValue -> CompStmt
findCompStmt cs v = case filter (\c -> valStmt v `elem` stmtUID c) cs of
  []    -> error $ "findCompStmt: cannot find " ++ show v
  (c:_) -> c

--------------------------------------------------------------------------------
-- Computation Statements

mkStmts :: Trace -> [CompStmt]
mkStmts trc = map (mkStmt frt) (filter isRoot trc)
  where frt = mkEventForest trc

mkStmt :: EventForest -> Event -> CompStmt
mkStmt frt (e@(RootEvent{eventLabel=lbl})) = CompStmt lbl i repr j

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


