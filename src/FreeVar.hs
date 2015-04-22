module FreeVar where
import Semantics
import Prelude hiding ((||),any,Right)
import Data.Graph.Libgraph

data FreeVar = NoFreeVar | FreeVar String 
  deriving (Show, Eq)

freeVars :: Expr -> FreeVar
freeVars = freeVars' [] []

freeVars' :: [String] -> [String] -> Expr -> FreeVar
freeVars' fs _  (Observe    _ _ e)     = freeVars' fs [] e
freeVars' fs vs (Lambda     n e)       = freeVars' fs (n:vs) e
freeVars' fs vs (Apply      e n)       = if n `elem` (fs++vs) then freeVars' fs vs e 
                                                              else (FreeVar n)
freeVars' fs vs (Var        n)         = if n `elem` (fs++vs) then NoFreeVar    
                                                              else (FreeVar n)
freeVars' fs vs (Let        (n,e1) e2)
  | isFun e1                          = freeVars' (n:fs) vs     e1 || freeVars' (n:fs) vs     e2
  | otherwise                         = freeVars' fs     (n:vs) e1 || freeVars' fs     (n:vs) e2
freeVars' fs vs (Constr     _ _ _)     = NoFreeVar
freeVars' fs vs (Case       e es)      = freeVars' fs vs e || any (caseFreeVar fs vs) es
freeVars' fs vs (Print      e)         = freeVars' fs vs e

(||) :: FreeVar -> FreeVar -> FreeVar
(FreeVar v)  || _            = FreeVar v
_            || (FreeVar v)  = FreeVar v
_            || _            = NoFreeVar

any :: (a->FreeVar) -> [a] -> FreeVar
any f = foldl (\z x -> z || f x) NoFreeVar

isFun :: Expr -> Bool
isFun Lambda{}               = True
isFun (Observe _ _ Lambda{}) = True
isFun _                      = False

caseFreeVar :: [String] -> [String] -> (Expr,Expr) -> FreeVar
caseFreeVar fs vs (Constr _ ns _,e) = freeVars' fs (vs ++ ns) e
caseFreeVar _  _  (e,_)             = error $ "caseHasFreeVar: attempt to match a non-contr:"
                                             ++ show e


--------------------------------------------------------------------------------

test1 :: Bool
test1  = NoFreeVar == test1'
test1' = freeVars $ Lambda "y" (Let ("x", c) (Var "x"))

test2 :: Bool
test2  = FreeVar "k1" == test2'
test2' = freeVars $ Let ("k1", c) 
                  $ Let ("k2", c) 
                  $ Let ("f", Observe "f" Right $ Lambda "x" (Var "k1"))
                  $ Apply (Var "f") "k2"

test3 :: Bool
test3  = NoFreeVar == test3'
test3' = freeVars $ Let ("k1", c) 
                  $ Let ("k2", c) 
                  $ Let ("f", Observe "f" Right $ Lambda "x" (Var "x"))
                  $ Apply (Var "f") "k2"

c :: Expr
c = Constr (ConstrId 1) [] Right
