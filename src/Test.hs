import Semantics
import Examples
import Run
import FreeVar

import Prelude hiding (Right)
import Data.Graph.Libgraph
import Test.QuickCheck
import Control.Monad.State

--------------------------------------------------------------------------------
-- QuickCheck soundness property

subsetOf :: Ord a => [a] -> [a] -> Bool
subsetOf xs ys = all (flip elem ys) xs

nonEmptyTrace :: Reduct -> Bool
nonEmptyTrace = not . null . getTrace

reducesToConstr :: Reduct -> Bool
reducesToConstr r = case getReduct r of (Constr _ _ _) -> True; _ -> False

hasNoFreeVars :: Expr -> Bool
hasNoFreeVars expr = freeVars expr == NoFreeVar

validExpr :: Expr -> Bool
validExpr expr = hasNoFreeVars expr && reducesToConstr r && nonEmptyTrace r
  where r = red expr

prop_actuallyFaulty :: Expr -> Property
prop_actuallyFaulty e = 
  validExpr e ==>
   property (actuallyFaulty e) 

actuallyFaulty :: Expr -> Bool
actuallyFaulty e = algoDebug e `subsetOf` markedFaulty e

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
main = quickCheckWith args prop_actuallyFaulty

  where args = Args { replay          = Nothing
                    , maxSuccess      = 10000    -- number of tests
                    , maxDiscardRatio = 1000000  -- many random exprs will not be valid
                    , maxSize         = 300       -- max subexpressions
                    , chatty          = True
                    }
