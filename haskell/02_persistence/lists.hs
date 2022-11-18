module Stack(Stack(..)) where

class Stack s where
    empty   :: s a
    isEmpty :: s a -> Bool
    cons    :: a -> s a -> s a
    head    :: s a -> a
    tail    :: s a -> s a

instance Stack [] where
    empty   = []
    isEmpty = null
    cons    = (:)
    head    = Prelude.head
    tail    = Prelude.tail

data MyStack a = Nil 
               | Cons a (MyStack a)
               deriving (Read, Show)

instance Stack MyStack where
    empty               = Nil
    isEmpty Nil         = True
    isEmpty (Cons x _)  = False
    cons x s            = Cons x s
    head Nil            = error "Empty Stack"
    head (Cons x _)     = x
    tail Nil            = error "Empty Stack" 
    tail (Cons _ xs)    = xs

append :: Stack s => s a -> s a -> s a
append xs ys = if isEmpty xs 
               then ys 
               else cons (Stack.head xs) (append (Stack.tail xs) ys)

update :: [a] -> Int -> a -> [a]
update [] i y     = error "Indexing"
update (x:xs) 0 y = y : xs
update (x:xs) i y = update xs (i - 1) y

suffixes :: [a] -> [[a]]
suffixes []     = [[]]
suffixes (x:xs) = (x:xs) : (suffixes xs)
