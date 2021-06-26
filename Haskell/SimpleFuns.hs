module SimpleFuns(swap, pair_up, kth, equalLs, quicksort, fst_T, snd_T, thd_T, mapT, applyPToP, allButLast, toIdxC) where

--inverts the pair
swap (x, y) = (y, x)

pair_up::a->b->(a,b)
pair_up x y = (x, y)

-- Projection functions for triples
fst_T (x, _, _) = x
snd_T (_, y, _) = y
thd_T (_, _, z) = z

-- Maps a function onto a triple
mapT f (x, y, z) = (f x, f y, f z)

-- Does the indexing within  a list
kth k (x:xs) = if k == 0 then x else kth (k-1) xs

equalLs [][] = True
equalLs _ [] = False
equalLs [] _ = False
equalLs (x:xs) (y:ys) 
   | x == y = (equalLs xs ys) 
   | otherwise = False

quicksort :: (Ord a) => [a] -> [a]    
quicksort [] = []    
quicksort (x:xs) =     
    let smallerSorted = quicksort (filter (<=x) xs)  
        biggerSorted = quicksort (filter (>x) xs)   
    in  smallerSorted ++ [x] ++ biggerSorted 

applyPToP (f, g)(x, y)= (f x, g y) 

allButLast l = take ((length l) - 1) l

toIdxC::Eq a=>[a]->[(a, Int)]
toIdxC xs = toIdxC' xs 0
    where  toIdxC' [] _ = []
           toIdxC' (x:xs) k = (x, k):toIdxC' xs (k+1)