module Utils where

excludeLast :: [a] -> [a]
excludeLast []       = error "Empty list"
excludeLast (_ : []) = []
excludeLast (x : xs) = x : excludeLast xs

excludeFirst :: [a] -> [a]
excludeFirst []       = error "Empty list"
excludeFirst (_ : xs) = xs


