module LsFuns (theL, appl, applM, subseteq, equalLs, eq_contents, substitute, find_multi_map_xs, functional, eq_singleton, 
   intersec, disjoint, combine_if, diff, union, insert, gunion, quicksort, no_dups, acyclic, id_on, rcomp, pfcomp, implies,
   trancl, rtrancl, rtrancl_on, total, injective, surjective, inj_surj_fun, inj_pfun, inj_fun, total_fun_surj, fun_bij, override, 
   getTransversalOfTree, toMaybe, eq_rel, fst_T, snd_T, thd_T, mapT, butLast, pair_up) where

pair_up::a->b->(a,b)
pair_up x y = (x, y)

fst_T (x, _, _) = x
snd_T (_, y, _) = y
thd_T (_, _, z) = z

mapT f (x, y, z) = (f x, f y, f z)

theL [x] = x

toMaybe [] = Nothing
toMaybe (n:ns) = Just n

equalLs [][] = True
equalLs _ [] = False
equalLs [] _ = False
equalLs (x:xs) (y:ys) 
   | x == y = (equalLs xs ys) 
   | otherwise = False


butLast [] = []
butLast (_:[]) = []
butLast (x:xs) = x:(butLast xs)

substitute xs rs = foldl (\xs' r-> (substitute_m xs' r)) xs rs

substitute_m [] _ = []
substitute_m (x:xs) p@(y, z) = if x == y then z:(substitute_m xs p) else x:(substitute_m xs p)

--subseteq s1 s2 = all (\x -> x `elem` s2) s1

--eq_contents l1 l2 = (subseteq l1 l2) && (subseteq l2 l1) 

--Checks whether two singletons are equal
--eq_singleton (x:xs) (y:ys)
--   | x == y && (null xs) && (null ys) = True
--   | otherwise = False

--find_fst_map_of x [] = Nothing
--find_fst_map_of x (p:xs) = if fst p == x then Just (snd p) else find_fst_map_of x xs




-- checks whether a relation is injective
--injective [] = True
--injective ((x, y):r) 
--   | null (img (inv r) [y]) = injective r
--   | otherwise              = False 


-- intersection
--intersec _ [] = []
--intersec [] _ = []
--intersec (x:xs) lb 
--   | x `elem` lb  = x:(intersec xs lb)
--   | otherwise    = (intersec xs lb)

-- generalised intersection
gintersec ss = foldr (intersec) [] ss

--disjointness as a generelised intersection
disjoint ss = null $ gintersec ss

 -- combines into pairs when some pair condition is met
combine_if_elem p e [] = []
combine_if_elem p e (x:xs) 
   | p (e, x)  = (e, x):combine_if_elem p e xs
   | otherwise = combine_if_elem p e xs

combine_if p [] lb = []
combine_if p la [] = []
combine_if p (x:xs) lb = combine_if_elem p x lb ++ combine_if p xs lb



quicksort :: (Ord a) => [a] -> [a]    
quicksort [] = []    
quicksort (x:xs) =     
    let smallerSorted = quicksort (filter (<=x) xs)  
        biggerSorted = quicksort (filter (>x) xs)   
    in  smallerSorted ++ [x] ++ biggerSorted 

--checks whether a relation has cycles
--cyclic [] = False
--cyclic ((x,y):r) =
--   let cyclic' r [] lv = False -- cyclic (dsub r lv) 
--       cyclic' r (v:vs) lv  
--          | v `elem` lv = True
--          | otherwise   = (cyclic' r vs lv) || (cyclic' r (img r [v]) (v:lv))  
--   in cyclic' r (y:(img r [x])) [x]

data Lookup a = Done| Looking a

carryIfNotFound Done _  = Done
carryIfNotFound (Looking lv) op  = op lv

carryConclude Done _  _ = True
carryConclude (Looking lv) op lv'  = op (lv' `diff` lv)

cyclic r = 
   let cyclic' r [] = False
       cyclic' r (v:vs) =
          let cyclic'' r [] lv = Looking lv
              cyclic'' r (v:vs) lv 
                 | v `elem` lv = Done
                 | otherwise =  carryIfNotFound (cyclic'' r (img r [v]) (v:lv)) (cyclic'' r vs)
          in carryConclude (cyclic'' r (img r [v]) [v]) (cyclic' r) vs
   in cyclic' r (dom_of r)

acyclic r = not (cyclic r)

-- pairs a element with a 'maybe'
--pairWith _ Nothing = []
--pairWith x (Just z) = [(x, z)]

--
--   (pairWith x (lookup y r2))++(rcomp ps r2)

--composition of partial functions
--pfcomp::Eq a=>Eq b=>[(b,c)]->[(a,b)]->a->Maybe c
pfcomp r s = (flip lookup_) r . (flip lookup s)
   where lookup_ Nothing _  = Nothing
         lookup_ (Just x) r  = lookup x r

-- transitive closure
--trancl r = let r' = r `union` (rcomp r r) in if r' == r then r else trancl r'
--rtrancl r = (trancl r) `union` (id_on ((dom_of r) `union` (ran_of r)))
--rtrancl_on r es= (trancl r) `union` (id_on es)

--tree r = acyclic r && functional r

--An equivalence relation over r
--eq_rel r = rtrancl_on (r `union` (inv r)) ((dom_of r) `union` (ran_of r))

--connected r = all (\x -> (all (\y -> (x, y) `elem` (trancl r)) (ran_of r))) (dom_of r)
--forest r = acyclic r

-- gets a particular transversal of a tree (a relation) by starting from a particular element
getTransversalOfTree r x = 
   let succs = img r [x] in
   succs ++ (foldr (\x xs-> getTransversalOfTree r x ++ xs) [] succs)