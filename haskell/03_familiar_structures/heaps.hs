module Heap(Heap(...)) where

class Heap h where
    empty       :: h a
    isEmpty     :: h a -> Bool
    insert      :: (Ord a) => a -> h a -> h a
    merge       :: (Ord a) => h a -> h a -> h a
    findMin     :: (Ord a) => h a -> a
    deleteMin   :: (Ord a) => h a -> h a

data LeftistHeap a = E
                   | T (rank :: Int) a (LeftistHeap a) (LeftistHeap a)
                   deriving (Eq, Ord, Read, Show)

instance Heap LeftistHeap where
    empty = E
    isEmpty E = True
    isEmpty _ = False
    merge h E = h
    merge E h = h
    merge h1@(T _ x1 l1 r1) h2@(T _ x2 l2 r2) = 
        if x1 <= x2 then makeT x1 l1 (merge r1 h2)
        else makeT x2 l2 (merge h1 r2)
        where makeT x h1 h2 = 
                if rank h1 >= rank h2 then T (rank h2 + 1) x h1 h2
                else T (rank h1 + 1) x h2 h1
    insert x h = merge (T 1 x E E) h
    findMin (T _ x _ _) = x
    deleteMin (T _ _ h1 h2) = merge h1 h2

