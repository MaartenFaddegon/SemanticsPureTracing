module Examples where

import Semantics
import CompTree
import DataDep
import EventForest

import Prelude hiding (Right)
import Data.Graph.Libgraph
import Data.List(sortBy)
import Data.Ord (comparing)

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
dispTxt expr = putStrLn . shw $ ct
  where shw :: CompTree -> String
        shw g = "\nComputation statements:\n" ++ unlines (map showVertex' $ vertices g)
        (_,_,_,ct) = red expr

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

--------------------------------------------------------------------------------
-- Examples

-- We use the following constructor encoding in the examples:
c_0 :: [Name] -> Judgement -> Expr
c_0 = Constr (ConstrId 0) -- False

c_1 :: [Name] -> Judgement -> Expr
c_1 = Constr (ConstrId 1) -- True

c_2 :: [Name] -> Judgement -> Expr
c_2 = Constr (ConstrId 2) -- the empty list []

c_3 :: [Name] -> Judgement -> Expr
c_3 = Constr (ConstrId 3) -- the list constructor (:)


-- NOTE: this only traces the top, subsequent (recursive) calls to foldl are not traced
foldlTraced :: Expr -> Expr
foldlTraced = Let ("foldlT", Lambda "f" $ Lambda "xs"  $ Lambda "z"
                           $ Apply (Apply (Apply (Observe "foldl" Right
                             (Var "foldl")) "f") "xs" ) "z")

sumTraced :: Expr -> Expr
sumTraced = Let ("sum", Lambda "xs" (Apply (Observe "sum" Right (Lambda "xs'" 
                        (Apply (Apply (Apply (Var "foldl") "p") "0" )"xs'"))) "xs"))

mapTraced :: Expr -> Expr
mapTraced = Let ("mapT", Lambda "f" $ Lambda "xs"
                       $ Apply (Apply (Observe "map" Right (Var "map")) "f") "xs" )

-- data B = T | F
-- n :: B -> B
myNot :: Expr -> Expr
myNot     = Let ("n", Lambda "b" $ Case (Var "b")
                    [ (c_1 [] Right, c_0 [] Right)
                    , (c_0 [] Right, c_1 [] Right)
                    ])

notTraced :: Expr -> Expr
notTraced = Let ("n", Lambda "b'" $ Apply (Observe "n" Right $ Lambda "b"
                      $ Case (Var "b")
                             [ (c_1 [] Right, c_0 [] Right)
                             , (c_0 [] Right, c_1 [] Right)
                             ]) "b'")


-- x :: B -> B -> B
myXor :: Expr -> Expr
myXor = Let ("x", Lambda "a1" $ Lambda "a2" $ Apply (Apply (Observe "x" Right $ Lambda "b1" $ Lambda "b2"
                      $ Case (Var "b1")
                             [ (c_1 [] Right, Case (Var "b2")[ (c_1 [] Right, c_0 [] Right)
                                                             , (c_0 [] Right, c_1 [] Right)])
                             , (c_0 [] Right, Case (Var "b2")[ (c_1 [] Right, c_1 [] Right)
                                                             , (c_0 [] Right, c_1 [] Right)])
                             ]
                             ) "a1") "a2")


ex1 :: Expr
ex1 = {- import -} prelude
    $ {- import -} notTraced
    $ Let ("b", (c_0 [] Right))
    $ Print $ Apply (Var "n") "b"

-- Example 2: Function h and n are traced, h maps over a list and n is
-- applied to all elements.
--
--   a) without reverse
--   b) reverse before printing (but outside traced code)
ex2a :: Expr
ex2a = {- import -} prelude
     $ {- import -} notTraced
     $ Let ("xs", Let ("a", c_1 [] Right)
                $ Let ("b", c_0 [] Right)
                $ Let ("c2", c_2 [] Right)
                $ Let ("c1", c_3 ["b", "c2"] Right)
                $            c_3 ["a","c1"] Right)
     $ Let ("h", Lambda "xs" (Apply (Observe "h" Right (Apply (Var "map") "n")) "xs"))
     $ Print $ Apply (Var "h") "xs"

ex2b :: Expr
ex2b = {- import -} prelude
     $ {- import -} notTraced
     $ Let ("xs", Let ("a", c_1 [] Right)
                $ Let ("b", c_0 [] Right)
                $ Let ("c2", c_2 [] Right)
                $ Let ("c1", c_3 ["b", "c2"] Right)
                $            c_3 ["a","c1"] Right)
     $ Let ("h", Lambda "xs" (Apply (Observe "h" Right (Apply (Var "map") "n")) "xs"))
     $ Print $ Let ("ys", Apply (Var "h") "xs") 
             $ Apply (Var "reverse") "ys"

-- Example 3: Trace map and its callees, reverse result before printing
-- but outside traced code
ex3a :: Expr
ex3a = {- import -} prelude
     $ {- import -} myNot
     $ {- import -} mapTraced
     $ Let ("xs", Let ("a", c_1 [] Right)
                $ Let ("b", c_0 [] Right)
                $ Let ("c2", c_2 [] Right)
                $ Let ("c1", c_3 ["b", "c2"] Right)
                $            c_3 ["a","c1"] Right)
     $ Print $ Let ("ys", Apply (Apply (Var "mapT") "n") "xs")
             $ Var "ys"

ex3b :: Expr
ex3b = {- import -} prelude
     $ {- import -} notTraced
     $ {- import -} mapTraced
     $ Let ("xs", Let ("a", c_1 [] Right)
                $ Let ("b", c_0 [] Right)
                $ Let ("c2", c_2 [] Right)
                $ Let ("c1", c_3 ["b", "c2"] Right)
                $            c_3 ["a","c1"] Right)
     $ Print $ Let ("ys", Apply (Apply (Var "mapT") "n") "xs")
             $ Apply (Var "reverse") "ys"

-- Example 4: Trace foldl and its callees in a simple checksum program
ex4 :: Expr
ex4 = {- import -} prelude
    $ {- import -} foldlTraced
    $ {- import -} myXor
    $ Let ("bs", Let ("a", c_1 [] Right)
               $ Let ("b", c_0 [] Right)
               $ Let ("c2", c_2 [] Right)
               $ Let ("c1", c_3 ["b", "c2"] Right)
               $            c_3 ["a","c1"] Right)
    $ Let ("z", c_0 [] Right)
    $ Print $ Apply (Apply (Apply (Var "foldlT") "x") "z") "bs"

-- Example 5: 
--      a) f -> g -> h
--      b) f -> g, f -> h
--      c) a -> b, a -> c, c -> d
ex5a :: Expr
ex5a = Let ("h", Observe "h" Wrong $ Lambda "y" $ Var "y")
     $ Let ("g", Observe "g" Right $ Lambda "y" $ Apply (Var "h") "y")
     $ Let ("f", Observe "f" Right $ Lambda "y" $ Apply (Var "g") "y")
     $ Let ("k", c_1 [] Right)
     $ Print $ Apply (Var "f") "k"

traceEx5a :: Trace
traceEx5a = reverse . snd . evaluate $ ex5a

ex5b :: Expr
ex5b = Let ("h", Observe "h" Right (Lambda "y" $ Var "y"))
     $ Let ("g", Observe "g" Right (Lambda "y" $ Var "y"))
     $ Let ("f", Observe "f" Right (Lambda "y" $ Let ("z", Apply (Var "g") "y")
                                                               (Apply (Var "h") "z")
                                             ))
     $ Let ("k", c_1 [] Right)
     $ Print $ Apply (Var "f") "k"

traceEx5b :: Trace
traceEx5b = reverse . snd . evaluate $ ex5b

ex5c :: Expr
ex5c = Let ("mod2",    Observe "mod2"    Right (Lambda "x" $ Var "x"))
     $ Let ("isEven",  Observe "isEven"  Right (Lambda "x" $ Apply (Var "mod2") "x"))
     $ Let ("plusOne", Observe "plusOne" Right (Lambda "x" $ Var "x"))
     $ Let ("isOdd",   Observe "isOdd"   Right (Lambda "x" $ Let ("y", Apply (Var "plusOne") "x")
                                                                 (Apply (Var "isEven") "y")
                                               ))
     $ Let ("k", c_1 [] Right)
     $ Print $ Apply (Var "isOdd") "k"


traceEx5c :: Trace
traceEx5c = reverse . snd . evaluate $ ex5c

-- Example 6:
--  There are different computation trees that are sound for algorithmic
--  debugging. Functions as arguments can be represented in different ways
--  but that also means that different dependencies are needed for a tree
--  to be sound. We represent functions as a finite mapping thus we should
--  create the dependencies that fit that.

ex6 :: Expr
ex6 = Let ("not",  Observe "not"  Wrong (Lambda "b" $ Case (Var "b") 
                   [(c_1 [] Right, c_0 [] Right), (c_0 [] Right, c_1 [] Right)]))
    $ Let ("app",  Observe "app"  Right (Lambda "f" $ Lambda "x" $ Apply (Var "f") "x"))
    $ Let ("main", Observe "main" Right (Lambda "x" $ Apply (Apply (Var "app") "not") "x"))
    $ Let ("y",    c_1 [] Right)
    $ {-in-} Apply (Var "main") "y"

-- ex7a:
--   app f x = f (not x)
--   main = app not True
ex7a :: Expr
ex7a = Let ("not",  Lambda "a" $ Apply (Observe "not"  Right 
                    (Lambda "b" $ Case (Var "b") [(c_1 [] Right, c_0 [] Right), (c_0 [] Right, c_1 [] Right)])) "a")
     $ Let ("app",  Observe "app"  Right (Lambda "f" $ Lambda "x" $ Let ("y",Apply (Var "not") "x") 
                                                                  $ Apply (Var "f") "y"))
     $ Let ("main", Observe "main" Right (Lambda "x" $ Apply (Apply (Var "app") "not") "x"))
     $ Let ("y",    c_1 [] Right)
     $ {-in-} Apply (Var "main") "y"

traceEx7a :: Trace
traceEx7a = reverse . snd . evaluate $ ex7a

-- ex7b:
--   app f x = not (f x)
--   main = app not True
ex7b :: Expr
ex7b = Let ("not",  Lambda "a" $ Apply (Observe "not"  Right (Lambda "b" $ Case (Var "b") [(c_1 [] Right, c_0 [] Right), (c_0 [] Right, c_1 [] Right)])) "a")
     $ Let ("app",  Observe "app"  Right (Lambda "f" $ Lambda "x" $ Let ("y",Apply (Var "f") "x") 
                                                                  $ Apply (Var "not") "y"))
     $ Let ("main", Observe "main" Right (Lambda "x" $ Apply (Apply (Var "app") "not") "x"))
     $ Let ("y",    c_1 [] Right)
     $ {-in-} Apply (Var "main") "y"


traceEx7b :: Trace
traceEx7b = reverse . snd . evaluate $ ex7b

-- ex7c:
--   app f x = f x
--   main = app (app not) True
ex7c :: Expr
ex7c = Let ("not",  Lambda "a" $ Apply (Observe "not"  Right (Lambda "b" $ Case (Var "b") [(c_1 [] Right, c_0 [] Right), (c_0 [] Right, c_1 [] Right)])) "a")
     $ Let ("app", Lambda "g" $ Lambda "y" $ Apply (Apply
                   (Observe "app"  Right (Lambda "f" $ Lambda "x" $ Apply (Var "f") "x"))
                   "g" ) "y"
           )
     $ Let ("main", Observe "main" Right (Lambda "x" $ Let ("app1", Apply (Var "app") "not") 
                                                $ Apply (Apply (Var "app") "app1") "x"))
     $ Let ("y",    c_1 [] Right)
     $ {-in-} Apply (Var "main") "y"


traceEx7c :: Trace
traceEx7c = reverse . snd . evaluate $ ex7c

-- Example 8: How does our technique handle sharing?

-- How does re-use of the result of "f" affect our dependence inference?
ex8 :: Expr
ex8 = genId "f"
    $ genId "g"
    $ genId "h"
    -- p a1 a2 = case a1 of False -> (case a2 of False -> False)
    $ Let ("p", Lambda "a1" $ Lambda "a2" 
              $ Apply (Apply (Observe "p" Right
              $ Lambda "b1" $ Lambda "b2" 
              $ Case (Var "b1") [(c_0 [] Right, Case (Var "b2") [(c_0 [] Right, c_0 [] Right)])]
              ) "a1") "a2")
    -- m a = let k = f a in p (g k) (h k) 
    $ Let ("m", Lambda "a" (Apply (Observe "m" Right
          $ Lambda "b"
          $ Let ("k",  Apply (Var "f") "b")
          $ Let ("k_g", Apply (Var "g") "k")
          $ Let ("k_h", Apply (Var "h") "k")
          $ Apply (Apply (Var "p") "k_g") "k_h"
          ) "a"))
    -- main = m False
    $ Let ("c", c_0 [] Right) $ Apply (Var "m") "c"

  where genId :: String -> Expr -> Expr
        genId funName = Let (funName, Lambda "x"
                                    $ Apply 
                                    ( Observe funName Right
                                    $ Lambda "y" (Var "y")
                                    ) "x")
                                                        
traceEx8 :: Trace
traceEx8 = reverse . snd . evaluate $ ex8

-- ex8b is as ex8, but p is not observed
ex8b :: Expr
ex8b = genId "f"
     $ genId "g"
     $ genId "h"
     -- p a1 a2 = case a1 of False -> (case a2 of False -> False)
     $ Let ("p", Lambda "b1" $ Lambda "b2" 
               $ Case (Var "b1") [(c_0 [] Right, Case (Var "b2") [(c_0 [] Right, c_0 [] Right)])]
               )
     -- m a = let k = f a in p (g k) (h k) 
     $ Let ("m", Lambda "a" (Apply (Observe "m" Right
           $ Lambda "b"
           $ Let ("k",  Apply (Var "f") "b")
           $ Let ("k_g", Apply (Var "g") "k")
           $ Let ("k_h", Apply (Var "h") "k")
           $ Apply (Apply (Var "p") "k_g") "k_h"
           ) "a"))
     -- main = m False
     $ Let ("c", c_0 [] Right) $ Apply (Var "m") "c"

  where genId :: String -> Expr -> Expr
        genId funName = Let (funName, Lambda "x"
                                    $ Apply 
                                    ( Observe funName Right
                                    $ Lambda "y" (Var "y")
                                    ) "x")

traceEx8b :: Trace
traceEx8b = reverse . snd . evaluate $ ex8b

-- Example 8c: sharing an argument
--   f x = x
--   g x = x
--   m x = f x + g x

ex8c :: Expr
ex8c = genId "f"
     $ genId "g"
     -- p a1 a2 = case a1 of False -> (case a2 of False -> False)
     $ Let ("p", Lambda "b1" $ Lambda "b2" 
               $ Case (Var "b1") [(c_0 [] Right, Case (Var "b2") [(c_0 [] Right, c_0 [] Right)])]
               )
     -- m a = let k_f = f a; k_g = g a in p k_f k_g
     $ Let ("m", Lambda "a" (Apply (Observe "m" Right
           $ Lambda "b"
           $ Let ("k_g", Apply (Var "g") "b")
           $ Let ("k_f", Apply (Var "f") "b")
           $ Apply (Apply (Var "p") "k_f") "k_g"
           ) "a"))
     -- main = m False
     $ Let ("c", c_0 [] Right) $ Apply (Var "m") "c"

  where genId :: String -> Expr -> Expr
        genId funName = Let (funName, Lambda "x"
                                    $ Apply 
                                    ( Observe funName Right
                                    $ Lambda "y" (Var "y")
                                    ) "x")

--------------------------------------------------------------------------------
-- Prelude, with:
--
-- map = \f xs -> case xs of (c_2 [])    -> xs
--                           (c_3 [h,t]) -> let h' = f h, t' = map f t
--                                                   in c_3 [h', t']
--
-- foldl = \f z xs -> case xs of (c_2 [])    -> z
--                               (c_3 [h,t]) -> let z' = f z h
--                                                       in foldl f z' t
-- reverse = \xs -> let f = \z x -> c_3 [x,z]
--                      z = c_2 []
--                  in foldl f z xs


prelude :: Expr -> Expr
prelude e = Let ("map", Lambda "f" $ Lambda "xs" 
                      $ Case (Var "xs")
                             [ (c_2 [] Right, Var "xs")
                             , ( c_3 ["h","t"] Right
                               , Let ("h'", Apply (Var "f") "h")
                               $ Let ("t'", Apply (Apply (Var "map") "f") "t")
                               $ c_3 ["h'","t'"] Right
                               )
                             ])
          $ Let ("foldl", Lambda "f" $ Lambda "z"  $ Lambda "xs"
                        $ Case (Var "xs")
                             [ (c_2 [] Right, Var "z")
                             , ( c_3 ["h","t"] Right
                               , Let ("z'", Apply (Apply (Var "f") "z") "h")
                               $ Apply (Apply (Apply (Var "foldl") "f") "z'") "t"
                               )
                             ])
          $ Let ("reverse", Lambda "xs"
                          $ Let ("f", Lambda "z" $ Lambda "x"
                                    $ c_3 ["x","z"] Right)
                          $ Let ("z", c_2 [] Right)
                          $ Apply (Apply (Apply (Var "foldl") "f") "z") "xs")
          $ e


