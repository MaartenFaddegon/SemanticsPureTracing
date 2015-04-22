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

  where (_,_,_,ct) = red expr

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

red :: Expr -> (String, ConstantTree, ConstantTree, CompTree)
red expr = (str, ddt, rdt, ct)
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
dispTxt expr = putStrLn $ str ++ shw ct
  where shw :: CompTree -> String
        shw g = "\nComputation statements:\n" ++ unlines (map showVertex' $ vertices g)
        (str,_,_,ct) = red expr

-- Requires Imagemagick to be installed.
dispCompTree :: Expr -> IO ()
dispCompTree expr = (display shw) ct
  where shw :: CompTree -> String
        shw g = showWith g showVertex showArc
        (_,_,_,ct) = red expr

dispDataDep :: Expr -> IO ()
dispDataDep expr = display shwCT ddt
  where (_,ddt,_,_) = red expr

dispResDep :: Expr -> IO ()
dispResDep expr = display shwCT rdt
  where (_,_,rdt,_) = red expr

showVertex :: Vertex -> (String,String)
showVertex v = (showVertex' v, "")

showVertex' :: Vertex -> String
showVertex' RootVertex  = "Root"
showVertex' (Vertex c) = showCompStmt c

showCompStmt :: CompStmt -> String
showCompStmt (CompStmt _ i r j) = r
        ++ "\n with UIDs "     ++ show i
        ++ "\n with judgment " ++ show j

showArc :: Arc Vertex () -> String
showArc _ = ""

