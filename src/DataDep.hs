module DataDep where
import Semantics
import EventForest
import Data.Graph.Libgraph
import Data.Maybe(mapMaybe)
import Data.List(sortBy)
import Data.Ord (comparing)

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

shwCT :: ConstantTree -> String
shwCT g = showWith g shwCV (\_ -> "")

shwCV :: ConstantValue -> (String,String)
shwCV v = (show (valLoc v) ++ "_" ++ show (valStmt v), "")

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


