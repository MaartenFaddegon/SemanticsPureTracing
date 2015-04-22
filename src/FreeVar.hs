module FreeVar where
import Semantics
import Prelude hiding ((||),any)

data FreeVar = NoFreeVar | FreeVar String 
  deriving Show

freeVars :: [String] -> Expr -> FreeVar
freeVars bs (Lambda     n e)       = freeVars (n:bs) e
freeVars bs (Apply      e n)       = if n `elem` bs then freeVars bs e else (FreeVar n)
freeVars bs (Var        n)         = if n `elem` bs then NoFreeVar    else (FreeVar n)
freeVars bs (Let        (n,e1) e2)
  | isFun e1                          = freeVars (n:bs) e1 || freeVars (n:bs) e2
  | otherwise                         = freeVars bs     e1 || freeVars bs     e2
freeVars bs (Constr     _ _ _)     = NoFreeVar
freeVars bs (Case       e es)      = freeVars bs e || any (caseFreeVar bs) es
freeVars bs (Observe    _ _ e)     = freeVars bs e
freeVars bs (Print      e)         = freeVars bs e

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

caseFreeVar :: [String] -> (Expr,Expr) -> FreeVar
caseFreeVar bs (Constr _ ns _,e) = freeVars (ns ++ bs) e
caseFreeVar bs (e,_)             = error $ "caseHasFreeVar: attempt to match a non-contr:"
                                             ++ show e
