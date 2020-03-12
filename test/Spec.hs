-- test/LibTests.hs
module Main where

import           Test.Tasty
import           Test.Tasty.HUnit

import           AlloyOperators
import           Alloy
import           Smt
import           SmtLibPrinter
import           Translator
import           Optimizer
import           System.Environment


main :: IO ()
main = defaultMain (testGroup "Project tests" [test1, test2])

test1 :: TestTree
test1 = testGroup
  "Optimize LetExpr"
  [ testCase
    "test1"
    (assertEqual "test1" optimizedLetExpr1 (SmtLet [(y, SmtVar y)] (SmtVar y)))
  , testCase
    "test2"
    (assertEqual "test2" optimizedLetExpr2 (SmtLet [(x, SmtVar x)] (SmtVar x)))
  , testCase "test3" (assertEqual "test3" optimizedLetExpr3 (SmtIntConstant 0))
  ]
 where
  x = SmtVariable "x" SmtInt False []
  y = SmtVariable "y" SmtInt False []
  letExpr1 = SmtLet [(x, SmtVar x), (y, SmtVar y)] (SmtVar y)
  letExpr2 = SmtLet [(x, SmtVar x), (y, SmtVar y)] (SmtVar x)
  letExpr3 = SmtLet [(x, SmtVar x), (y, SmtVar y)] (SmtIntConstant 0)
  (optimizedLetExpr1, changed1) = optimize letExpr1
  (optimizedLetExpr2, changed2) = optimize letExpr2
  (optimizedLetExpr3, changed3) = optimize letExpr3

test2 :: TestTree
test2 = testCase "test2" (assertEqual "10 = 5 + 5" (SmtVar x) (SmtVar y))
 where
  x = SmtVariable "x" SmtInt False []
  y = SmtVariable "y" SmtInt False []

