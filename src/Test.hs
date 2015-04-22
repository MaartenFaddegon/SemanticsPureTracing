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
prop_actuallyFaulty e = validExpr e ==> property $ algoDebug e `subsetOf` markedFaulty e

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
gen_observedLam n = return oLam `ap` gen_label `ap` gen_jmt `ap` gen_varName `ap` (gen_expr $ n-1)
  where oLam l j v e = Observe l j (Lambda v e)

gen_varName :: Gen String
gen_varName = elements $ map (:[]) ['a'..'i']

gen_var :: Gen Expr
gen_var = liftM Var gen_varName

-- Note that when generated constants always are judged as Right.
gen_constr :: Gen Expr
gen_constr = oneof [ elements [c_0 [] Right, c_1 [] Right, c_2 [] Right]
                   , liftM2 (\v1 v2 -> c_3 [v1,v2] Right) gen_varName gen_varName
                   ]

gen_case :: Int -> Gen Expr
gen_case n = return mkCase `ap` gen_expr' `ap` gen_expr' `ap` gen_expr' `ap` gen_expr' `ap` gen_expr' 
                           `ap` gen_varName `ap` gen_varName
  where mkCase e e0 e1 e2 e3 n1 n2 = Case e [(c_0 [] Right,e0),(c_1 [] Right,e1),
                                             (c_2 [] Right,e2),(c_3 [n1,n2] Right,e3)]
        gen_expr' = gen_expr $ (n - 1) `div` 7

instance Arbitrary Expr where

  arbitrary = sized gen_expr

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
                    , maxSuccess      = 10000  -- number of tests
                    , maxDiscardRatio = 500    -- many random exprs will not be valid
                    , maxSize         = 100    -- max subexpressions
                    , chatty          = True
                    }
