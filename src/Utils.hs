module Utils where

excludeLast :: [a] -> [a]
excludeLast []       = error "Empty list"
excludeLast (x : []) = []
excludeLast (x : xs) = x : excludeLast xs

excludeFirst :: [a] -> [a]
excludeFirst []       = error "Empty list"
excludeFirst (x : xs) = xs


