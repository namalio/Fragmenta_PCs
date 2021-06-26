module Composition (eq_rel_eq_map, quotient_set_eq_map, calc_g_po, norm_after_po) where

import Grs
import SGrs
import Sets
import Relations
import SimpleFuns

--A relation giving function applications of a certain elefEnt (equivalence kernel): (f(a), g(a))
rel_eq_map [] _ = [] 
rel_eq_map ((x,y):f) g = (y, appl g x):(rel_eq_map f g)

eq_rel_eq_map f g a b = 
   let r = rel_eq_map f g in
   rtrancl_on (r `union` (inv r)) (a `union` b)

--gives quotient set of equivalence kernel
quotient_set_eq_map f g a b =
   let r =  eq_rel_eq_map f g a b in
   no_dups $ map (\x->quicksort (img r [x]))(a `union` b)

--gives projection function over equivalence class
pi_of_eq_map f g a b = 
   let r = eq_rel_eq_map f g a b in
   no_dups $ map (\x->(x, quicksort (img r [x])))(a `union` b)

pi_commutes f g a b = 
   let pi =  pi_of_eq_map f g a b in
   (g `rcomp` pi)  `seteq` (f `rcomp` pi) 

gm_eq_map gm1 gm2 =cons_gm (rel_eq_map (fV gm1) (fV gm2)) (rel_eq_map (fE gm1) (fE gm2))

gm_eq_rel_eq_map gm1 gm2 ga gb = cons_gm (eq_rel_eq_map (fV gm1) (fV gm2) (ns ga) (ns gb)) (eq_rel_eq_map (fE gm1) (fE gm2) (es ga) (es gb))

calc_g_po gm1 gm2 gb gc = 
   let pi_V =  pi_of_eq_map (fV gm1) (fV gm2) (ns gb) (ns gc) in
   let pi_E =  pi_of_eq_map (fE gm1) (fE gm2) (es gb) (es gc) in
   let ns' = quotient_set_eq_map (fV gm1) (fV gm2) (ns gb) (ns gc) in
   let es' = quotient_set_eq_map (fE gm1) (fE gm2) (es gb) (es gc) in
   let s = ((inv $ pi_E) `rcomp` ((src gb) `union` (src gc))) `rcomp` pi_V in
   let t = ((inv $ pi_E) `rcomp` ((tgt gb) `union` (tgt gc))) `rcomp` pi_V in
   cons_g ns' es' s t

norm_after_po g nt = 
   cons_g (map pickNode $ ns g) (map head $ es g) (map (\(x, y)-> (head x, pickNode y)) (src g)) (map (\(x, y)-> (head x, pickNode y)) (tgt g))
   where pickNode [n] = n
         pickNode (n:ns) = if appl nt n /= Nprxy then n else pickNode ns