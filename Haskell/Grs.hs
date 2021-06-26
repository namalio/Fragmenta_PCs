{-# LANGUAGE MultiParamTypeClasses #-}

module Grs (Gr, GrM, TK(..), MK(..), isKTotal, ns_g, es_g, src_g, tgt_g, cons_g, empty_g, cons_gm, empty_gm, fV, fE, restrict, replace, 
    adjacent, successors, predecessors, getAdjacent, relOfG, esIncident, acyclicG, disj_gs, union_g, union_gs, union_gm, gid, ogm,
    union_gms, is_wf_gm_g, subsume_g, invertg) where

import Gr_Cls
import Sets
import Relations
import ErrorAnalysis 
import Utils

data Gr a = Gr {
   ns_ :: [a], 
   es_ ::  [a],
   src_ :: [(a, a)],
   tgt_ :: [(a, a)]} 
   deriving(Eq, Show) 

-- constructor
cons_g ns' es' s t =  Gr {ns_ = ns', es_ = es', src_ = s, tgt_ = t}

-- projection functions
ns_g Gr {ns_ = ns', es_ = _, src_ = _, tgt_ = _} = ns'
es_g Gr {ns_ = _, es_ = es', src_ = _, tgt_ = _} = es'
src_g Gr {ns_ = _, es_ = _, src_ = s, tgt_ = _} = s
tgt_g Gr {ns_ = _, es_ = _, src_ = _, tgt_ = t} = t

-- empty element
empty_g = cons_g [] [] [] []

instance GR Gr where
   ns = ns_g
   es = es_g
   src = src_g
   tgt = tgt_g
   empty = empty_g

is_wf_g:: (Eq a, GR g) => g a -> Bool
is_wf_g g = fun_total (src g) (es g) (ns g) && fun_total (tgt g) (es g) (ns g)


errors_wf_g:: (GR g, Eq a, Show a) => g a -> [ErrorTree]
errors_wf_g g =
   let errs1 = if fun_total (src g) (es g) (ns g) then nile else cons_et ("Function 'src' is ill defined.") [check_fun_total (src g) (es g) (ns g)] in
   let errs2 = if fun_total (tgt g) (es g) (ns g) then nile else cons_et ("Function 'tgt' is ill defined.") [check_fun_total (tgt g) (es g) (ns g)] in
   [errs1, errs2]

check_wf_g id g = check_wf_of g id (is_wf_g) errors_wf_g

-- Builds a new graph by restricting to a set of edges
--rst_ns g le = no_dups $ union (ran_of (dres (src g)  le))  (ran_of (dres (tgt g)  le))

-- Restricts a graph to a list of edges
restrict g le = 
   let es' = (es g) `intersec` le in
   let s = dres (src g) le in
   let t = dres (tgt g) le in
   cons_g (ns g) es' s t

-- Replaces nodes in a graph according to a substitution mapping
-- NOT SURE IT IS NEEDED
replace g subst = 
   let ns' = ns g `union` (ran_of subst) in
   let s = (src g) `rcomp` ((id_on . ran_of . src $ g) `override` subst) in
   let t = (tgt g) `rcomp` ((id_on . ran_of . tgt $ g) `override` subst) in
   cons_g ns' (es g) s t

--function that yields the map of a source function
--esId_g g = filter (\e-> appl (src g) e == appl (tgt g) e)(es g)

-- Gives all successor nodes of a given node in a given graph
successors g v = img (tgt g) $ filter (\e-> appl (src g) e == v) (es g)

-- Gives all predecessor nodes of a given node in a given graph
predecessors g v = img (src g) $ filter (\e-> appl (tgt g) e == v) (es g)

--Gives all nodes adjacent to a particular node (sucessors and predecessors)
getAdjacent g v = (successors g v) `union` (predecessors g v)

-- defines graph notion of adjency
adjacent g v1 v2 = 
   (not . null) $ filter (\e-> (img (src g) [e]) `seteq` [v1] && (img (tgt g) [e]) `seteq`  [v2]) (es g)

-- Inverts a graph
invertg g = cons_g (ns g) (es g) (tgt g) (src g)
 
-- gets adjacency relation induced by graph
relOfG g = foldr (\e r-> (appl (src g) e, appl (tgt g) e):r) [] (es g)

-- All incident edges of a set of nodes
esIncident g vs = img (inv $ src g) vs `union` img (inv $ tgt g) vs

-- checks whether a graph is acyclic
acyclicG::(Eq a, GR g) => g a->Bool
acyclicG = acyclic . relOfG 

-- Total function check on 'fV'
fun_total_fV (gs, m, gt) = fun_total (fV m) (ns gs) (ns gt)

-- Total function check on 'fE'
fun_total_fE (gs, m, gt) = fun_total (fE m) (es gs) (es gt)

-- Checks whether the source function commutes
morphism_gm_commutes_src (gs, m, gt) = ((fV m) `bcomp` (src gs))  `seteq` ((src gt) `bcomp` (fE m) ) 
morphism_gm_commutes_tgt (gs, m, gt) = ((fV m) `bcomp` (tgt gs))  `seteq` ((tgt gt) `bcomp` (fE m) ) 

is_wf_gm_g:: (Eq a, GR g) => (g a, GrM a, g a) -> Bool
is_wf_gm_g (gs, m, gt) = fun_total_fV (gs, m, gt) && fun_total_fE (gs, m, gt)
   && morphism_gm_commutes_src (gs, m, gt)
   && morphism_gm_commutes_tgt (gs, m, gt)

is_wf_g' _ = is_wf_g

is_wf_gm_g' _ (g, gm, gt) = is_wf_gm_g (g, gm, gt)

check_wf_g' id _ = check_wf_g id

instance G_WF_CHK Gr where
   is_wf = is_wf_g'
   check_wf = check_wf_g'

instance GM_CHK Gr Gr where
   is_wf_gm = is_wf_gm_g'
   check_wf_gm = check_wf_gm_g'

--check_gr_wf:: (GR g, Eq a, Show a) => String -> g a -> IO () 
--check_gr_wf g_id g = 
--   let errs = check_wf_g g_id g in
--   if null errs 
--      then putStrLn $ "Graph " ++ g_id ++ " is well forfEd" 
--      else putStrLn $ "Graph " ++ g_id ++ " is not well-forfEd. " ++ (show errs) 

errors_gm_g:: (GR g, Eq a, Show a) => (g a, GrM a, g a) -> [ErrorTree]
errors_gm_g (gs, m, gt) =
   let err1 = if fun_total_fV (gs, m, gt) then nile else cons_et "Function 'fV' is ill defined." [check_fun_total (fV m) (ns gs) (ns gt)] in
   let err2 = if fun_total_fE (gs, m, gt) then nile else cons_et "Function 'fE' is ill defined." [check_fun_total (fE m) (es gs) (es gt)] in
   let err3 = if morphism_gm_commutes_src (gs, m, gt) then nile else cons_se "Problems in the commuting of the source functions" in
   let err4 = if morphism_gm_commutes_tgt (gs, m, gt) then nile else cons_se "Problems in the commuting of the target functions" in
   [err1,err2,err3,err4]

check_wf_gm_g:: (GR g, Eq a, Show a) => String-> (g a, GrM a, g a) -> ErrorTree
check_wf_gm_g nm (gs, gm, gt) = 
   check_wf_of (gs, gm, gt) nm (is_wf_gm_g) (errors_gm_g)

check_wf_gm_g' nm Nothing = check_wf_gm_g nm 

disj_gs gs = disjoint (map ns gs) && disjoint (map es gs)

-- graph union
union_g g1 g2 = 
   let ns' = (ns g1) `union` (ns g2) in
   let es' = (es g1) `union` (es g2) in
   let s = (src g1) `union` (src g2) in
   let t = (tgt g1) `union` (tgt g2) in
   cons_g ns' es' s t

-- generalised graph union
union_gs gs = foldl (\gacc g-> gacc `union_g` g) empty_g gs

-- graph subsumption: takes a graph and a substituion mapping
subsume_g g sub 
   | pfun sub (ns g) (ns g) && antireflexive sub = cons_g (ns g `diff` dom_of sub) (es g) (total_ns `bcomp` src g) (total_ns `bcomp` tgt g)
   where total_ns = sub `mktotal_in` ns g
-- Identity morphism over a graph
gid g = cons_gm (id_on $ ns g) (id_on $ es g)

-- Union on graph morphisms
union_gm gm1 gm2 = cons_gm ((fV gm1) `union` (fV gm2)) ((fE gm1) `union` (fE gm2))

-- Generalised union for graph morphisms 
union_gms gms = foldl (\gmacc gm-> gmacc `union_gm` gm) empty_gm gms

-- Morphism composition
ogm g f = cons_gm (fV g `bcomp` fV f) (fE g `bcomp` fE f)

--replace_in_gm gm subs_ns_dom subs_ns_ran =
--   let ns_dom' = substitute (map fst (fV gm)) subs_ns_dom in
--   let ns_ran' = substitute (map snd (fV gm)) subs_ns_ran in
--   cons_gm (zip ns_dom' ns_ran') (fE gm)

-- Registricts an instance graph to a set of edge types given a morphism
--REMOVE LATER IF UNNECESSARY
restrictGToTyEdges m g tes = restrict g (img (inv . fE $ m) tes)
