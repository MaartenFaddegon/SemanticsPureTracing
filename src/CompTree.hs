module CompTree where
import Prelude hiding (Right)
import Semantics
import EventForest

import DataDep
import Data.Graph.Libgraph
import Data.List(nub)

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

-- One computation statement can have multiple result-events. Sometime these add
-- new information, often the information is just a duplicate of what we already
-- know. With nub we remove the duplicates.
mkCompTree :: [CompStmt] -> ConstantTree -> CompTree
mkCompTree cs ddt = Graph r (nub vs) (nub as)
  where Graph r vs as = mapGraph findVertex ddt

        findVertex :: ConstantValue -> Vertex
        findVertex CVRoot = RootVertex
        findVertex v      = Vertex (findCompStmt cs v)

findCompStmt :: [CompStmt] -> ConstantValue -> CompStmt
findCompStmt cs v = case filter (\c -> valStmt v `elem` stmtUID c) cs of
  []    -> error $ "findCompStmt: cannot find " ++ show v
  (c:_) -> c

--------------------------------------------------------------------------------
-- Computation Statements

mkStmts :: Trace -> [CompStmt]
mkStmts trc = foldl (\cs r -> cs ++ (map (mkStmt frt r) (topLevelApps frt r))) [] 
                    (filter isRoot trc)
  where frt = mkEventForest trc

mkStmt :: EventForest -> Event -> Event -> CompStmt
mkStmt frt (e@(RootEvent{eventLabel=lbl})) a@AppEvent{} = CompStmt lbl i' repr' j
  where (CompStmt _ i repr j) = mkStmt' frt a
        repr'                 = lbl ++ " = " ++ repr
        i'                    = eventUID e : eventUID lam : i
        [Just lam]            = dfsChildren frt e
mkStmt _ e e' = error $ "mkStmt should be given RootEvent and AppEvent, was given " 
                      ++ show e ++ " and " ++ show e'

mkStmt' :: EventForest -> Event -> CompStmt
mkStmt' frt (e@(AppEvent{})) = CompStmt "??" i repr j
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
              j = judgeApp frt e

judgeApp :: EventForest -> Event -> Judgement
judgeApp frt a@AppEvent{} = case (allRight arg, allRight res) of
        (True, False) -> Wrong
        (False,_)     -> Right
        (True, True)  -> Right

  where [arg,res] = dfsChildren frt a

        allRight :: Maybe Event -> Bool
        allRight = (all (\e -> Right == eventJudgement e)) . (constList frt)

constList :: EventForest -> Maybe Event -> [Event]
constList _   Nothing  = []
constList frt (Just e) = filter isConst (eventsInTree frt e)
  where isConst ConstEvent{} = True
        isConst _            = False
