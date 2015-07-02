module Examples where

import Semantics
import Run
import FreeVar

import Prelude hiding (Right)
import Data.Graph.Libgraph

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

-- mapTraced' is as mapTraced, but with 
mapTraced' :: Expr -> Expr
mapTraced' = Let ("mapT", Observe "mapT" Right $ Lambda "f" $ Lambda "xs" 
                       $ Case (Var "xs")
                              [ (c_2 [] Right, Var "xs")
                              , ( c_3 ["h","t"] Right
                                , Let ("h'", Apply (Var "f") "h")
                                $ Let ("t'", Apply (Apply (Var "mapT") "f") "t")
                                $ c_3 ["h'","t'"] Right
                                )
                              ])

-- data B = T | F
-- n :: B -> B
myNot :: Expr -> Expr
myNot     = Let ("n", Lambda "b" $ Case (Var "b")
                    [ (c_1 [] Right, c_0 [] Right)
                    , (c_0 [] Right, c_1 [] Right)
                    ])

-- and :: B -> B -> B
myAnd :: Expr -> Expr
myAnd     = Let ("and", Lambda "p" $ Lambda "q" $ Case (Var "p")
                    [ (c_0 [] Right, c_0 [] Right)
                    , (c_1 [] Right, Case (Var "q")
                        [ (c_0 [] Right, c_0 [] Right)
                        , (c_1 [] Right, c_1 [] Right)
                        ])
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

-- ex7d:
--   app f x = f x
--   main = (app not) True
ex7d :: Expr
ex7d = Let ("not",  Observe "not"  Right $ Lambda "b" $ Case (Var "b") 
               [(c_1 [] Right, c_0 [] Right)
               , (c_0 [] Right, c_1 [] Right)]
           )
     $ Let ("app", Observe "app" Right $ Lambda "f" $ Lambda "x" $ 
                Apply (Var "f") "x"
           )
     $ Let ("main", Observe "main" Right $ Lambda "x" $ 
                Apply (Apply (Var "app") "not") "x")
     $ Let ("y",    c_1 [] Right)
     $ {-in-} Apply (Var "main") "y"

-- ex7e:
--   not True = False
--   not False = True
--   appT f = f True
--   neg b = (appT not)
ex7e :: Expr
ex7e = Let ("true",  c_1 [] Right)
     $ Let ("false", c_0 [] Right)
     $ Let ("not",  Observe "not"  Right $ Lambda "b" $ Case (Var "b") 
               [(c_1 [] Right, c_0 [] Right)
               , (c_0 [] Right, c_1 [] Right)]
           )
     $ Let ("appT", Observe "appT" Right $ Lambda "f" $ Apply (Var "f") "true")
     $ Let ("neg", Observe "neg" Right $ Lambda "b" (Apply (Var "appT") "not"))
     $ {-in-} Apply (Var "neg") "false"

-- ex7f: more higher order functions, or
-- a function taking as argument a function taking as argument a function
--
-- appN = observe "appN" appN'
-- appN' g = g not
--
-- appT = observe "appT" appT'
-- appT' f = f True
-- 
-- not = observe "not" not'
-- not' True  = False
-- not' False = True

ex7f :: Expr
ex7f = Let ("true",  c_1 [] Right)
     $ Let ("false", c_0 [] Right)
     $ Let ("not",  Observe "not"  Right $ Lambda "b" $ Case (Var "b") 
               [(c_1 [] Right, c_0 [] Right)
               , (c_0 [] Right, c_1 [] Right)]
           )
     $ Let ("appT", Observe "appT" Right $ Lambda "f" $ Apply (Var "f") "true")
     $ Let ("appN", Observe "appN" Right $ Lambda "g" $ Apply (Var "g") "not")
     $ Let ("neg", Observe "neg" Right $ Lambda "b" $ (Apply (Var "appN") "appT"))
     $ {-in-} Apply (Var "neg") "false"


-- As ex7f, but appN is not observed
ex7g :: Expr
ex7g = Let ("true",  c_1 [] Right)
     $ Let ("false", c_0 [] Right)
     $ Let ("not",  Observe "not"  Right $ Lambda "b" $ Case (Var "b") 
               [(c_1 [] Right, c_0 [] Right)
               , (c_0 [] Right, c_1 [] Right)]
           )
     $ Let ("appT", Observe "appT" Right $ Lambda "f" $ Apply (Var "f") "true")
     $ Let ("appN", Lambda "g" $ Apply (Var "g") "not")
     $ Let ("neg", Observe "neg" Right $ Lambda "b" $ (Apply (Var "appN") "appT"))
     $ {-in-} Apply (Var "neg") "false"


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


-- Example 9: 
--
--
-- mapNot = map not
-- all    = foldl and True
-- main   = all (mapNot [False, False, True])

ex9 :: Expr
ex9 = {- import -} prelude
    $ {- import -} myNot
    $ {- import -} myAnd
    $ Let ("true", c_1 [] Right)
    $ Let ("false", c_0 [] Right)
    $ Let ("mapNot", Observe "mapNot" Right $ Lambda "xs" $ Apply (Apply (Var "map") "n") "xs")
    $ Let ("all", Observe "all" Right $ Apply (Apply (Var "foldl") "and") "true")
    $ Let ("k0", c_2 [] Right)
    $ Let ("k1", c_3 ["true", "k0"] Right)
    $ Let ("k2", c_3 ["false", "k1"] Right)
    $ Let ("k3", c_3 ["false", "k2"] Right)
    $ {- main= -} Let ("ys", Apply (Var "mapNot") "k3") $ Apply (Var "all") "ys"

-- as ex9 but with function not also traced
ex9b :: Expr
ex9b = {- import -} prelude
     $ {- import -} notTraced
     $ {- import -} myAnd
     $ Let ("true", c_1 [] Right)
     $ Let ("false", c_0 [] Right)
     $ Let ("mapNot", Observe "mapNot" Right $ Lambda "xs" $ Apply (Apply (Var "map") "n") "xs")
     $ Let ("all", Observe "all" Right $ Apply (Apply (Var "foldl") "and") "true")
     $ Let ("k0", c_2 [] Right)
     $ Let ("k1", c_3 ["true", "k0"] Right)
     $ Let ("k2", c_3 ["false", "k1"] Right)
     $ {- main= -} Let ("ys", Apply (Var "mapNot") "k2") $ Apply (Var "all") "ys"

-- as ex9b but with map also traced
ex9c :: Expr
ex9c = {- import -} prelude
     $ {- import -} notTraced
     $ {- import -} mapTraced
     $ {- import -} myAnd
     $ Let ("true", c_1 [] Right)
     $ Let ("false", c_0 [] Right)
     $ Let ("mapNot", Observe "mapNot" Right $ Lambda "xs" $ Apply (Apply (Var "mapT") "n") "xs")
     $ Let ("all", Observe "all" Right $ Apply (Apply (Var "foldl") "and") "true")
     $ Let ("k0", c_2 [] Right)
     $ Let ("k1", c_3 ["true", "k0"] Right)
     $ Let ("k2", c_3 ["false", "k1"] Right)
     $ {- main= -} Let ("ys", Apply (Var "mapNot") "k2") $ Apply (Var "all") "ys"

-- map and not observed
ex9d :: Expr
ex9d = {- import -} prelude
     $ {- import -} mapTraced'
     $ {- import -} myAnd
     $ Let ("true", c_1 [] Right)
     $ Let ("false", c_0 [] Right)
     $ Let ("not", Observe "not" Right $ Lambda "b"$ Case (Var "b")
                             [ (c_1 [] Right, c_0 [] Right)
                             , (c_0 [] Right, c_1 [] Right)
                             ])
     $ Let ("mapNot", Lambda "xs" $ Apply (Apply (Var "mapT") "not") "xs")
     $ Let ("all", Apply (Apply (Var "foldl") "and") "true")
     $ Let ("k0", c_2 [] Right)
     $ Let ("k1", c_3 ["true", "k0"] Right)
     $ Let ("k2", c_3 ["false", "k1"] Right)
     $ {- main= -} Let ("ys", Apply (Var "mapNot") "k2") $ Apply (Var "all") "ys"

-- program with multi-argument functions:
--   not = observe "not" not'
--   not' True  = False
--   not' False = True
--   
--   and True True = True
--   and _    _    = False
--   
--   nand = observe "nand" nand'
--   nand' b d = and (not b) (not d)
ex10a :: Expr
ex10a = {- import -} prelude
     $ Let ("true", c_1 [] Right)
     $ Let ("false", c_0 [] Right)
      $ Let ("not", Observe "not" Right $ Lambda "b"$ Case (Var "b")
                      [ (c_1 [] Right, c_0 [] Right)
                      , (c_0 [] Right, c_1 [] Right)
                      ])
      $ Let ("and", Lambda "b"$ Lambda "d" $ Case (Var "b")
                      [ (c_0 [] Right, c_0 [] Right)
                      , (c_1 [] Right, Case (Var "d")
                        [ (c_0 [] Right, c_0 [] Right)
                        , (c_1 [] Right, c_1 [] Right)
                        ])
                      ])
      $ Let ("nand", Observe "nand" Wrong $ Lambda "b"$ Lambda "d"
                $ Let ("nb",Apply (Var "not") "b")
                $ Let ("nd",Apply (Var "not") "d")
                $ Apply (Apply (Var "and") "nb") "nd")
      $ Apply (Apply (Var "nand") "false") "true"

-- as 10a but with and also observed
ex10b :: Expr
ex10b = {- import -} prelude
     $ Let ("true", c_1 [] Right)
     $ Let ("false", c_0 [] Right)
      $ Let ("not", Observe "not" Right $ Lambda "b"$ Case (Var "b")
                      [ (c_1 [] Right, c_0 [] Right)
                      , (c_0 [] Right, c_1 [] Right)
                      ])
      $ Let ("and", Observe "and" Right $ Lambda "b"$ Lambda "d"
                  $ Case (Var "b")
                      [ (c_0 [] Right, c_0 [] Right)
                      , (c_1 [] Right, Case (Var "d")
                        [ (c_0 [] Right, c_0 [] Right)
                        , (c_1 [] Right, c_1 [] Right)
                        ])
                      ])
      $ Let ("nand", Observe "nand" Right $ Lambda "b"$ Lambda "d"
                $ Let ("nb",Apply (Var "not") "b")
                $ Let ("nd",Apply (Var "not") "d")
                $ Apply (Apply (Var "and") "nb") "nd")
      $ Apply (Apply (Var "nand") "false") "true"

-- program with multi-argument functions:
--   not = observe "not" not'
--   not' True  = False
--   not' False = True
--   
--   and = observe "and" and
--   and' b True  = not b
--   and' b False = False
--   
--   nand = observe "nand" nand'
--   nand' b d = and b (not d)
ex10c :: Expr
ex10c = {- import -} prelude
     $ Let ("true", c_1 [] Right)
     $ Let ("false", c_0 [] Right)
      $ Let ("not", Observe "not" Right $ Lambda "b"$ Case (Var "b")
                      [ (c_1 [] Right, c_0 [] Right)
                      , (c_0 [] Right, c_1 [] Right)
                      ])
      $ Let ("and", Observe "and" Right $ Lambda "b"$ Lambda "d"
                  $ Case (Var "d")
                      [ (c_0 [] Right, c_0 [] Right)
                      , (c_1 [] Right, Apply (Var "not") "b")
                      ])
      $ Let ("nand", Observe "nand" Right $ Lambda "b"$ Lambda "d"
                $ Let ("nd",Apply (Var "not") "d")
                $ Apply (Apply (Var "and") "b") "nd")
      $ Apply (Apply (Var "nand") "true") "false"


-- program with non nullary constructors
--
-- data D = D Bool Bool
--
-- not = observe "not" not'
-- not' True  = False
-- not' False = True
-- 
-- and True True = True
-- and _    _    = False
-- 
-- nandD = observe "nand" nand'
-- nandD' (D b d) = and (not b) (not d)
--
ex11a = {- import -} prelude
     $ Let ("true", c_1 [] Right)
     $ Let ("false", c_0 [] Right)
      $ Let ("not", Observe "not" Right $ Lambda "b"$ Case (Var "b")
                      [ (c_1 [] Right, c_0 [] Right)
                      , (c_0 [] Right, c_1 [] Right)
                      ])
      $ Let ("and", Lambda "b" $ Lambda "d" $ Case (Var "b")
                      [ (c_0 [] Right, c_0 [] Right)
                      , (c_1 [] Right, Case (Var "d")
                        [ (c_0 [] Right, c_0 [] Right)
                        , (c_1 [] Right, c_1 [] Right)
                        ])
                      ])
      $ Let ("nandD", Observe "nandD" Wrong $ Lambda "d" $ Case (Var "d")
                [ ( c_3 ["p","q"] Right
                  , Let ("nb",Apply (Var "not") "p")
                  $ Let ("nd",Apply (Var "not") "q")
                  $ Apply (Apply (Var "and") "nb") "nd")])
      $ Let ("x", c_3 ["false", "true"] Right)
      $ Apply (Var "nandD") "x"

-- Simpler program with non nullary constructors
--
-- data D = D Bool
--
-- not = observe "not" not'
-- not' True  = False
-- not' False = True
-- 
-- notD = observe "notD" notD'
-- notD' (D b) = D (not b)
--
ex11b = {- import -} prelude
      $ Let ("true", c_1 [] Right)
      $ Let ("false", c_0 [] Right)
      $ Let ("not", Observe "not" Right $ Lambda "b"$ Case (Var "b")
                      [ (c_1 [] Right, c_0 [] Right)
                      , (c_0 [] Right, c_1 [] Right)
                      ])
      $ Let ("notD", Observe "notD" Wrong $ Lambda "d" $ Case (Var "d")
                [ ( c_3 ["b"] Right
                  , Let ("nb",Apply (Var "not") "b")
                  $ c_3 ["nb"] Right)])
      $ Let ("k", c_3 ["false"] Right)
      $ Print $ Apply (Var "notD") "k"



-- Examples with exceptions.

-- ex12a: a simple example
ex12a = {- import -} prelude
      $ Let ("true", c_1 [] Right)
      $ Let ("false", c_0 [] Right)
      $ Let ("not", Observe "not" Right $ Lambda "b"$ Case (Var "b")
                      [ (c_1 [] Right, c_0 [] Right)
                         -- no definition for "not False" --> throws exception
                      ])
      $ Print $ Apply (Var "not") "false"

-- and = observe "and" and'
-- and' True  True  = True
-- and' True  False = False
-- -- No definition for False b -> throws exception!
--
-- foldl = observe "foldl" foldl'
-- foldl' f z []    = z
-- foldl' f z (h:t) = let z' = f z h in foldl f z' t
--
-- all = foldl and True []
--
-- main = all [False, True]
{-
ex12b = Let ("foldl", Observe "not" Right (Var "foldl'"))
      $ Let ("foldl'", Lambda "f" $ Lambda "z"  $ Lambda "xs"
                    $ Case (Var "xs")
                         [ (c_2 [] Right, Var "z")
                         , ( c_3 ["h","t"] Right
                           , Let ("z'", Apply (Apply (Var "f") "z") "h")
                           $ Apply (Apply (Apply (Var "foldl") "f") "z'") "t"
                           )
                         ])
      $ Let ("and", Lambda "b" $ Lambda "d" $ Case (Var "b")
                      [ (c_0 [] Right, c_0 [] Right)
                      , (c_1 [] Right, Case (Var "d")
-}

--------------------------------------------------------------------------------
-- Counter examples found with QuickCheck

-- Counter example 1: use of free variables in an observed function
--
-- Solution: add static analysis to quickcheck that rejects testing of
-- generated expressions with free variables.

cex1 :: Expr
cex1 = Case (Apply (Let ("d",Apply (Let ("h",Apply (Let ("h",c_3 ["h","i"] Right) (c_1 [] Right)) "b") (Observe "M" Wrong (Lambda "d" (Let ("e",c_3 ["b","b"] Right) (c_1 [] Right))))) "g") (Lambda "a" (Let ("h",Lambda "f" (Case (c_1 [] Right) [(c_0 [] Right,c_3 ["e","c"] Right),(c_1 [] Right,c_3 ["a","b"] Right),(c_2 [] Right,c_3 ["h","a"] Right),(c_3 ["e","f"] Right,c_3 ["g","f"] Right)])) (Var "d")))) "i") [(c_0 [] Right,Let ("g",c_1 [] Right) (c_3 ["e","g"] Right)),(c_1 [] Right,Apply (Observe "G" Right (Lambda "i" (Var "d"))) "e"),(c_2 [] Right,Lambda "c" (Let ("h",Lambda "h" (Let ("i",c_2 [] Right) (Observe "N" Right (Lambda "b" (c_3 ["b","i"] Right))))) (Var "g"))),(c_3 ["a","e"] Right,Observe "I" Right (Lambda "d" (Lambda "h" (Let ("e",Case (c_1 [] Right) [(c_0 [] Right,c_3 ["f","a"] Right),(c_1 [] Right,c_3 ["h","h"] Right),(c_2 [] Right,c_3 ["e","c"] Right),(c_3 ["c","e"] Right,c_3 ["a","i"] Right)]) (Let ("g",c_3 ["h","i"] Right) (Case (c_1 [] Right) [(c_0 [] Right,c_2 [] Right),(c_1 [] Right,c_3 ["f","a"] Right),(c_2 [] Right,c_2 [] Right),(c_3 ["b","c"] Right,c_0 [] Right)]))))))]

-- A manual variation on cex1 where the problem is easier to spot:
cex1a :: Expr
cex1a = Let ("f", (Observe "f" Wrong (Lambda "x" (Var "x"))))    -- defective fun
      $ Let ("v", Let ("y", c_1 [] Right) (Apply (Var "f") "y")) -- free var v
      $ Let ("g", (Observe "g" Wrong (Lambda "x" (Var "v"))))    -- use of free var
      -- In the main function, we first force the evaluation of the free variable
      -- and thus add events of the defective function f to the trace.
      $ Case (Var "v") 
         -- After that we apply the function g with the free variable in the body,
         -- while g itself is correct, it returns the wrong result due to contamination
         -- from the defective function f.
         [(c_1 [] Right, Let ("z", c_1 [] Right) (Apply (Var "g") "z"))]

cex1b :: Expr
cex1b = Let ("f", (Observe "f" Wrong (Lambda "x" (Var "x"))))    -- defective fun
      $ Let ("v", Let ("y", c_1 [] Right) (Apply (Var "f") "y")) -- free var v
      $ Let ("g", (Observe "g" Wrong (Lambda "x" (Var "x"))))
      -- In the main function, we first force the evaluation of the free variable
      -- and thus add events of the defective function f to the trace.
      $ Case (Var "v") 
         -- After that we apply the function g to the free variable in the body,
         -- this is not a problem because now we see that function g gets a wrong
         -- value as argument.
         [(c_1 [] Right, Apply (Var "g") "v")]

-- Counter example 2
--
-- s3:  h =  { { _ -> (c_1)} -> (c_1)} -> (c_1)
--       with UIDs [0,1,3,5,6,7,12,16,20,21,25,8,28,4,29]
--       with judgment Wrong
-- s9:  h =  { _ -> (c_1)} -> (c_1)
--       with UIDs [0,1,9,11,17,18,19,26,10,27]
--       with judgment Right
-- s22: g =  _ -> (c_1)
--       with UIDs [13,14,22,23,24]
--       with judgment Wrong
-- 
cex2 :: Expr
cex2 = Let ("h",Observe "h" Right 
                (Lambda "f" (Let ("g",Observe "g" Wrong 
                                      (Lambda "a" ( c_1 [] Right))
                                 ) (Apply (Var "f") "g")
                            )
                )
           ) (Apply (Var "h") "h")

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


