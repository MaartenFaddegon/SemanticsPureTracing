import Semantics
import Examples
import Run
import FreeVar
import CompTree

import Prelude hiding (Right)
import Data.Graph.Libgraph
import Test.QuickCheck
import Control.Monad.State

--------------------------------------------------------------------------------
-- QuickCheck soundness property

--------------------------------------------------

-- For every request event there is exactly one response event and vice versa.
prop_eventSpans e = wellFormed e ==> lbl_trcLen trc $ all (formsSpan trc) trc
 where trc = getTrace (red e)

formsSpan trc e | isReq  e  = length es == 2 && isResp (es !! 0)
                | isResp e  = length es == 2 && isReq  (es !! 1)
                | otherwise = True -- other events (e.g. RootEvent) don't form spans
 where es = filter (hasParent (eventParent e)) trc

isReq EnterEvent{} = True
isReq _            = False

isResp ConstEvent{} = True
isResp LamEvent{}   = True
isResp _            = False

hasParent p RootEvent{} = False
hasParent p e           = eventParent e == p

--------------------------------------------------
-- Request and response events are like the language of balanced parentheses.
-- Automata and Computability, Chapter: Balanced Parentheses, Dexter C. Kozen
-- http://link.springer.com/chapter/10.1007/978-1-4612-1844-9_24#page-1

prop_balanced e = 
 wellFormed e ==> lbl_trcLen trc $ numLeft trc == numRight trc 
                  && all (\prefix -> numLeft prefix >= numRight prefix) (prefixes trc)
 where trc = reverse $ getTrace (red e)

prefixes :: [a] -> [[a]]
prefixes [] = []
prefixes xs = ys : prefixes ys 
 where ys = init xs

numLeft,numRight :: [Event] -> Int
numLeft  = length . (filter isReq)
numRight = length . (filter isResp)

--------------------------------------------------
-- A labelled expression that algorithmic debugging finds faulty 
-- actually contains a defect.

prop_actuallyFaulty :: Expr -> Property
prop_actuallyFaulty e = 
 hasNoFreeVars e && wellFormed e ==> lbl_tree tree $ algoDebug e `subsetOf` markedFaulty e
 where
 tree = getCompTree (red e)

subsetOf :: Ord a => [a] -> [a] -> Bool
subsetOf xs ys = all (flip elem ys) xs

--------------------------------------------------
-- A computation tree has no surplus edges: every statement has a unique parent.

prop_minimal :: Expr -> Property
prop_minimal e =
 wellFormed e ==> lbl_tree tree $ all (\c -> length (parent c) <= 1) (statements tree)
 where
 tree = getCompTree (red e)
 parent = predCache tree
 statements = vertices

--------------------------------------------------
-- All computation statements are reachable from the root.

prop_connected :: Expr -> Property
prop_connected e =
 wellFormed e ==> lbl_tree tree $ all hasParent (filter (/= RootVertex) (statements tree))
 where
 tree = getCompTree (red e)
 hasParent = (not . null . parent)
 parent = predCache tree
 statements = vertices

--------------------------------------------------
-- A wrong statement is reachable from the special root statement * 
-- via a chain of wrong statements.
prop_reachable :: Expr -> Property
prop_reachable e =
 wellFormed e ==> lbl_tree tree $ all parentWrong (filter isWrong (statements tree))
 where
 parentWrong c = case parent c of
  []  -> True
  [p] -> isWrong p
 tree = getCompTree (red e)
 parent = predCache tree
 statements = vertices
 isWrong RootVertex = True
 isWrong (Vertex c) = stmtJudgement c == Wrong

--------------------------------------------------

lbl_trcLen trc = label $ (show . length $ trc) ++ " events in the trace"

lbl_tree tree = lbl_treeDepth tree . lbl_statements tree

lbl_treeDepth tree = label $ "computation tree has depth " ++ (show . treeDepth $ tree)

lbl_statements tree = label $ (show . length . vertices $ tree) ++ " computation statements"

--------------------------------------------------
-- preconditions

hasNoFreeVars :: Expr -> Bool
hasNoFreeVars expr = freeVars expr == NoFreeVar

wellFormed :: Expr -> Bool
wellFormed expr = reducesToConstr r && nonEmptyTrace r
  where r = red expr

nonEmptyTrace :: Reduct -> Bool
nonEmptyTrace = not . null . getTrace

reducesToConstr :: Reduct -> Bool
reducesToConstr r = case getReduct r of (Constr _ _ _) -> True; _ -> False

--------------------------------------------------------------------------------
-- Generating random expressions with observed abstractions

gen_expr :: [String] -> Int -> Gen Expr
gen_expr [] 0 = gen_constr []
gen_expr xs 0 = oneof [gen_constr xs, liftM Var (elements xs)]
gen_expr [] n = oneof (noVarGens [] n)
gen_expr xs n = oneof (noVarGens xs n ++ varGens xs n)

varGens,noVarGens :: [String] -> Int -> [Gen Expr]

noVarGens xs n = 
  [ gen_constr xs
  , gen_case xs n
  , gen_lam xs n
  , gen_let xs n
  , gen_observedLam xs n
  ]

varGens xs n | xs /= [] = 
  [ liftM2 Apply  (gen_expr xs $ n-1) (elements xs)
  , liftM Var (elements xs)
  ]

gen_let :: [String] -> Int -> Gen Expr
gen_let xs n = do
  x   <- gen_varName
  liftM2 (mkLet x) (gen_expr (x:xs) $ (n-1) `div` 2) (gen_expr (x:xs) $ (n-1) `div` 2)
  where
  mkLet a e1 e2 = Let (a,e1) e2

gen_observedLam :: [String] -> Int -> Gen Expr
gen_observedLam xs n = liftM3 Observe gen_label gen_jmt (gen_lam xs n)

gen_jmt :: Gen Judgement
gen_jmt = elements [Right, Wrong]

gen_lam :: [String] -> Int -> Gen Expr
gen_lam xs n = do
  x   <- gen_varName
  liftM (Lambda x) (gen_expr (x:xs) (n-1))

gen_label :: Gen Label
gen_label = elements $ map (:[]) ['A'..'Z']

gen_varName :: Gen String
gen_varName = elements $ map (:[]) ['a'..'z']

-- Note that when generated constants always are judged as Right.
gen_constr :: [String] -> Gen Expr
gen_constr [] = elements [c_0 [] Right, c_1 [] Right, c_2 [] Right]
gen_constr xs = oneof [ gen_constr []
                      , liftM2 (\v1 v2 -> c_3 [v1,v2] Right)
                               (elements xs) (elements xs)
                      ]

gen_case :: [String] -> Int -> Gen Expr
gen_case xs n = return mkCase `ap` gen_expr' `ap` gen_expr' `ap` gen_expr' `ap` gen_expr' `ap` gen_expr' 
                           `ap` gen_varName `ap` gen_varName
  where mkCase e e0 e1 e2 e3 n1 n2 = Case e [(c_0 [] Right,e0),(c_1 [] Right,e1),
                                             (c_2 [] Right,e2),(c_3 [n1,n2] Right,e3)]
        gen_expr' = gen_expr xs $ (n - 1) `div` 7

instance Arbitrary Expr where

  arbitrary = sized (gen_expr [])

  shrink (Constr _ _ _)    = []
  shrink (Observe l j e)   = e : (map (Observe l j) (shrink e))
  shrink (Lambda n e)      = e : (map (Lambda n) (shrink e))
  shrink (Apply e n)       = let alts = e : (map (flip Apply n) (shrink e))
                             in case e of
                               (Lambda _ e') -> e' : alts
                               _             -> alts
  shrink (Let (n,e1) e2)   = e2 : e1
                             :    (map (Let (n,e1)) (shrink e2))
                             ++   (map (\e-> Let (n,e) e2) (shrink e1))
  shrink _                 = [c_0 [] Right]

--------------------------------------------------------------------------------
-- Main

main :: IO ()
main = (flip mapM_) tests (\(prop,description) -> do
 putStrLn description
 check 5 300 prop
 putStrLn "")
 

-- check 10000 300 prop_actuallyFaulty

 where 
 tests = [(prop_eventSpans, "For every request event there is exactly one response event and vice versa."),
  (prop_balanced, "Request and response events are like the language of balanced parentheses."),
  (prop_actuallyFaulty, "A labelled expression that algorithmic debugging finds faulty actually contains a defect."),
  (prop_reachable, "A wrong statement is reachable from the special root statement * via a chain of wrong statements."),
  (prop_connected, "All computation statements are reachable from the root."),
  (prop_minimal, "Our computation tree has no surplus edges: every statement has a unique parent.")
  ]

check n m prop = quickCheckWith args prop
  where args = Args { replay          = Nothing
                    , maxSuccess      = n        -- number of tests
                    , maxDiscardRatio = 1000000  -- many random exprs will not be valid
                    , maxSize         = m        -- max subexpressions
                    , chatty          = True
                    }
