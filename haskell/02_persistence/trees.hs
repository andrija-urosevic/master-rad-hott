module Set(Set(..)) where

class Set s where
    empty   :: s a
    insert  :: (Ord a) => a -> s a -> s a
    member  :: (Ord a) => a -> s a -> Bool

data Tree a = E 
            | T (Tree a) a (Tree a)
            deriving (Eq, Ord, Read, Show)

instance Set Tree where
    empty               = E
    insert x E          = T E x E
    insert x (T l y r)  = if x < y then T (insert x l) y r
                          else if x > y then T l y (insert x r)
                          else T l x r
    member x E          = False
    member x (T l y r)  = if x < y then member x l
                          else if x > y then member x r
                          else True
