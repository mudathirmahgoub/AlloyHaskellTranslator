-- test/LibTests.hs
module Main where

import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main = do
  defaultMain (testGroup "Project tests" [test1, test2])

test1 :: TestTree
test1 = testCase "test1"
  (assertEqual "test1" "Hello world" "Hello world")

test2 :: TestTree
test2 = testCase "test2"
  (assertEqual "10 = 5 + 5" 10 (5 + 5))