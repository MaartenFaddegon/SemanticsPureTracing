import Semantics
import Test.QuickCheck

main :: IO ()
main = quickCheckWith args prop_actuallyFaulty
  where args = Args { replay          = Nothing
                    , maxSuccess      = 1000  -- number of tests
                    , maxDiscardRatio = 100
                    , maxSize         = 1000   -- max subexpressions
                    , chatty          = True
                    }
