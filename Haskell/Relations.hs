module Relations (dom_of, ran_of, img, inv, dres, rres, dsub, rsub, override, id_on, rcomp, bcomp, functional, total, fun_total, 
    fun_total_seq, pfun, fun_total', fun_pinj, fun_inj, fun_bij, inj_surj_fun, injective, relation, cl_override, mktotal_in, 
    appl, find_monces, acyclic, trancl, rtrancl_on, antireflexive, cross, flatten) where

import SimpleFuns
import Sets

dom_of r = map fst r
ran_of r = map snd r

--inverts a relation (as a list of pairs)
inv r = map swap r

--domain restriction
dres r xs = filter ((\x -> elem x xs) . fst) r

--range restriction
rres r ys = filter ((\x -> elem x ys) . snd) r

-- domain subtraction
dsub r xs = filter ((\x -> not $ x `elem` xs) . fst) r

-- range subtraction
rsub r ys = filter ((\y -> not $ y `elem` ys) . snd) r

--relation image
img r xs = ran_of (dres r xs)

--takes first element of image (appropriate when doing function application)
appl r x = head $ img r [x] 

-- relational overriding
override [] s = s
override ((x,y):r) s 
   | x `elem` (dom_of s) = override r s
   | otherwise =  (x,y):(override r s)

-- Identity on a given set
id_on s = zip s s

-- forwards relation composition
--rcomp0 [] _ = []
--rcomp0 _ [] = []
--rcomp0 ((x, y):r1) r2 = 
--   (map (pair_up x) (img r2 [y]))`union` (rcomp0 r1 r2)

rcomp r1 r2 = foldr (\(x, y) r'-> map (pair_up x) (img r2 [y]) `union` r') [] r1
--rcomp0 r1 r2 

-- backwards relation composition
bcomp r1 r2 = rcomp r2 r1
--foldr (\(x, y) r'->map (pair_up x) (img r1 [y]) `union` r') [] r2


functional [] = True
functional ((x, _):r) 
   | x `elem` dom_of r = False
   | otherwise        = functional r

total r xs = (dom_of r) `seteq`  xs

range_ok r ys = (ran_of r) `subseteq` ys
fun_total f xs ys = functional f && total f xs && range_ok f ys
fun_total_seq f xs ys = functional f && total f xs && (gunion . ran_of $ f) `subseteq` ys

fun_total' r xs = functional r && total r xs

injective r = (functional . inv) r

surjective r ys = ys `seteq` (ran_of r)

relation r xs ys = dom_of r `subseteq` xs && range_ok r ys
pfun f xs ys = functional f && relation f xs ys

-- A partial injection (pinj)
fun_pinj f xs ys = injective f && pfun f xs ys
fun_inj f xs ys = injective f && fun_total f xs ys

inj_fun r xs ys = injective r && fun_total r xs ys
inj_surj_fun r xs ys = injective r && surjective r ys && fun_total r xs ys

total_fun_surj r xs ys = fun_total r xs ys && surjective r ys
fun_bij r xs ys = fun_total r xs ys && injective r && surjective r ys

-- Checks that a relation is anti-reflexive
antireflexive r = all (\(x,y)-> x /= y) r

-- transitive closure
trancl r = let r' = r `union` (r `rcomp` r) in if r' == r then r else trancl r'
rtrancl r = (trancl r) `union` (id_on ((dom_of r) `union` (ran_of r)))
rtrancl_on r es= (trancl r) `union` (id_on es)

tree r = acyclic r && functional r

-- An equivalence relation over r
eq_rel r = rtrancl_on (r `union` (inv r)) ((dom_of r) `union` (ran_of r))

-- Says whether a relation is acyclic
acyclic r = null $ trancl r `intersec` (id_on $ dom_of r `union` ran_of r)

-- closure of a relation ovveride
cl_override r = let r' = r `override` (rcomp r r) in if r' == r then r else cl_override r'

-- Totalises a relation within a set by using identity to stand for undefinedness
mktotal_in r s = (id_on s) `override` r

-- Those domain elements which are mapped more than once in a relation
find_monces r = foldr (\x xs->if length (img r [x]) > 1 then insert x xs else xs) [] (dom_of r)

--find_multi_map_xs [] = []
--find_multi_map_xs ((x, y):r)
--   | not (null (img r [x])) = x:(find_multi_map_xs r)
--   | otherwise              = find_multi_map_xs r

cross [] _ = []
cross (x:xs) ys = (map (pair_up x) ys) `union` (cross xs ys)

flatten [] = []
flatten ((x, ys):ps) = (map (pair_up x) ys) `union` (flatten ps)