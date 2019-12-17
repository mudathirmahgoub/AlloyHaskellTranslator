module Main where

import Expressions
import Translator


printTranslation :: IO ()
printTranslation = print (translate (AlloyBinary Plus AlloyUnary AlloyUnary ))

main :: IO ()
main = printTranslation
