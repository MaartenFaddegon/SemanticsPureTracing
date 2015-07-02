module Run where

import Semantics
import CompTree
import DataDep
import EventForest

import Prelude hiding (Right)
import Data.Graph.Libgraph
import Data.Generics.Schemes(listify)
import Data.List(sortBy)
import Data.Ord (comparing)

-- Evaluate, and apply algorithmic debugging to resulting trace to obtain a list
-- of faulty labels.
algoDebug :: Expr -> [Label]
algoDebug expr = map getLbl . findFaulty_dag getJmt $ ct

  where ct = getCompTree . red $ expr

        getJmt :: Vertex -> Judgement
        getJmt RootVertex = Right
        getJmt (Vertex c) = stmtJudgement c

        getLbl :: Vertex -> Label
        getLbl (Vertex c) = stmtLabel c
        getLbl RootVertex = error "Algorithmic debugging marked root as faulty!"

-- Extract program slices we marked as faulty from expression without evaluating.
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
-- Evaluate and display.

data Reduct = Reduct { getReduct      :: Expr
                     , getLog         :: String
                     , getTrace       :: Trace
                     , getDataDepTree :: ConstantTree
                     , getResDepTree  :: ConstantTree
                     , getCompTree    :: CompTree
                     }

red :: Expr -> Reduct
red expr = Reduct reduct str trc ddt rdt ct
  where (reduct,trc,messages) = evaluate' expr
        str = messages 
            ++ "\n\nReduct: " ++ show reduct
            ++ foldl (\acc s -> acc ++ "\n" ++ s) "\n\nEvent trace:" (map show $ reverse trc)
        ddt = mkDDDT (mkConstants trc)
        rdt = mkResDepTree ddt
        ct  = mkCompTree (mkStmts trc) rdt

mkConstants :: Trace -> [ConstantValue]
mkConstants trc = sortBy (comparing valMin) . foldl (\z r -> z ++ constants frt r) [] 
                $ filter isRoot trc
        where frt = mkEventForest trc

dispTxt :: Expr -> IO ()  
dispTxt expr = putStrLn $ getLog r ++ shw (getCompTree r)
  where shw :: CompTree -> String
        shw g = "\nComputation statements:\n" ++ unlines (map showVertex' $ vertices g)
        r = red expr

-- Requires Imagemagick to be installed.
dispCompTree :: Expr -> IO ()
dispCompTree expr = (display shw) (getCompTree . red $ expr)
  where shw :: CompTree -> String
        shw g = showWith g showVertex showArc

dispDataDep :: Expr -> IO ()
dispDataDep expr = display shwCT (getDataDepTree . red $ expr)

dispResDep :: Expr -> IO ()
dispResDep expr = display shwCT (getResDepTree . red $ expr)

showVertex :: Vertex -> (String,String)
showVertex v = (showVertex' v, "")

showVertex' :: Vertex -> String
showVertex' RootVertex  = "Root"
showVertex' (Vertex c) = "\"" ++ stmtRepr c ++ "\""

showCompStmt :: CompStmt -> String
showCompStmt (CompStmt _ i r j) = r
        ++ "\n with UIDs "     ++ show i
        ++ "\n with judgment " ++ show j

showArc :: Arc Vertex () -> String
showArc _ = ""

--------------------------------------------------------------------------------

type TraceGraph  = Graph EventVertex ParentPosition
data EventVertex = EventVertex Event | TraceGraphRoot
  deriving Eq

mkTraceGraph :: Trace -> TraceGraph
mkTraceGraph trc = Graph TraceGraphRoot vs as
  where vs = TraceGraphRoot : (map EventVertex trc)
        as = map mkArc trc

        mkArc :: Event -> Arc EventVertex ParentPosition
        mkArc tgt@RootEvent{} = Arc TraceGraphRoot    (EventVertex tgt) 0
        mkArc tgt = case lookup (parentUID . eventParent $ tgt) es of 
          (Just src) -> Arc (EventVertex src) (EventVertex tgt) 
                            (parentPosition . eventParent $ tgt)

        es = map (\e -> (eventUID e, e)) trc


dispTrace :: Expr -> IO ()
dispTrace = (display shw) . mkTraceGraph . getTrace . red
  where shw :: TraceGraph -> String
        shw g = showWith g shwEvent shwEventArc

        shwEvent (EventVertex (RootEvent i lbl)     ) = (show i ++ ": " ++ lbl   , "")
        shwEvent (EventVertex (EnterEvent i _)      ) = (show i ++ ": Ent"       , "")
        shwEvent (EventVertex (ConstEvent i _ c _ _)) = (show i ++ ": " ++ show c, "")
        shwEvent (EventVertex (LamEvent i _)        ) = (show i ++ ": Lam"       , "")
        shwEvent (EventVertex (AppEvent i _)        ) = (show i ++ ": @"         , "")

        shwEventArc (Arc _ _ pos) = show pos
