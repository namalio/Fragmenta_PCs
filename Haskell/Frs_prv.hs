{-# LANGUAGE MultiParamTypeClasses #-}
module Frs(Fr, sg, esr, sr, tr, cons_fr, empty_fr, is_wf_fr, withRsG, esF, disj_frs, union_frs, noHangingProxies, check_wf_fr, refs, is_wf_ftym, check_wf_ftym, is_wf_gm_frs, 
   inhstF, resolveProxiesFM, consSeamlessCompFs, consSeamlessCompF) where

import Gr_Cls
import Grs
import SGrs
import Sets
import Relations
import Utils
import Composition
import MyMaybe
import ErrorAnalysis
import ShowUtils

data Fr a = Fr {
   sg_ :: (SGr a), 
   esr_ :: [a],
   sr_  :: [(a, a)],
   tr_ :: [(a, a)]
} deriving (Show)

sg Fr {sg_ = sg, esr_ = _, sr_ = _, tr_ = _} = sg
esr Fr {sg_ = _, esr_ = es, sr_ = _, tr_ = _} = es
sr Fr {sg_ = _, esr_ = _, sr_ = s, tr_ = _} = s
tr Fr {sg_ = _, esr_ = _, sr_ = _, tr_ = t} = t

cons_fr sg es s t = Fr {sg_ = sg, esr_ = es, sr_ = s, tr_ = t} 

empty_fr = cons_fr (empty_sg) [] [] []

-- Graph with actual references
withRsG::Eq a=>Fr a -> Gr a
withRsG f =
   cons_g ((ns $ sg f) `union` (ran_of $ tr f)) ((es $ sg f) `union` (esr f)) ((src $ sg f) `union` (sr f)) ((tgt $ sg f) `union` (tr f))

--Gets all edges of a fragment
esF f = (es $ sg f) `union` (esr f)

-- Gets a graph with proxies
refsG f = restrict (withRsG f) (esr f)
refs f = relOfG $ refsG f
acyclicIR f = acyclic $ ((refs f) `union` (inh $ sg f)) 

refsOf f n = let r = refs f in img (trancl r) [n]

--nonPRefs f n = 
--   let nsP' = (nsP $ sg f) in
--   filter (\v -> not $ v `elem` nsP') (refsOf f n)

-- the representatives relation
reps f = (refs f) `union` (inv $ refs f)
repsst f = rtrancl_on (reps f) ((ns $ sg f) `union` (ran_of $ tr f))

--Total well-formedness
referencesAreValid f = (ran_of $ tr f) `subseteq` (ns $ sg f)

--No hanging proxies. Proxies must eventually refer to a non-proy node of a fragment.
noHangingProxies f = 
   let nsp = (nsP $ sg f) in
   all (\s -> not $  null s) (map (\n -> filter (\v -> not $ v `elem` nsp) (refsOf f n)) nsp) 

inheritedNodes f = ran_of $ filter (\(x, y)-> x/=y)(inhstF f)

-- Function 'nsTys' which takes proxies into account
nsTysF f nts = img (repsst f) (nsTys (sg f) nts)

-- Virtual and abstract nodes or any of its representatives must be inherited
virtAndAbstAreInheritedF f = (nsTysF f [Nvirt, Nabst]) `subseteq` (inheritedNodes f)

--not . null $ diff(img (inv . tgt . sg $ f) (img (repsst f) (nsTys (sg f) [Nvirt, Nabst])), (esId . sg $ f))

-- Checks whether a fragment is well-formed either totally or partially
is_wf_fr tk f = 
   is_wf Nothing (sg f)
   && disjoint [es $ sg f, esr f]
   && fun_bij (sr f) (esr f) (nsP $ sg f) 
   && total_fun' (tr f) (esr f) 
   && (acyclicIR f) 
   && if (isKTotal tk) then referencesAreValid f && noHangingProxies f && virtAndAbstAreInheritedF f else True

disj_frs fs = disj_sgs (map sg fs) && disjoint (map esr fs)

union_frs fs = cons_fr (union_sgs $ map sg fs) (gunion $ map esr fs) (gunion $ map sr fs) (gunion $ map tr fs)

-- Builds seamless (or colimit/pushout) composition by resolving the proxies that can be resolved
consSeamlessCompF f = 
   let p_res = resProxySubs f in
   let p_res_tot = p_res `union` id_on (diff (ns . sg $ f) (dom_of p_res)) in
   let ns' = diff (ns . sg $ f) (dom_of p_res) in -- the new set of nodes removes the proxies that are resolved
   let src' = (src . sg $ f) `rcomp` p_res_tot in
   let tgt' = (tgt . sg $ f) `rcomp` p_res_tot in
   let esr' = diff (esr f) (img (inv . sr $ f) (dom_of p_res)) in
   let sr' = rsub (sr f) (img (inv . sr $ f) (dom_of p_res)) in
   let tr' = rsub (tr f) (img (inv . sr $ f) (dom_of p_res)) in
   let g = cons_g ns' (es . sg $ f) src' tgt' in
   let sg' = cons_sg g (dres (nty . sg $ f) ns') (ety . sg $ f) ((srcm . sg) $ f) ((tgtm . sg) $ f) in
   cons_fr sg' esr' sr' tr'

-- Builds the colimin/pushout composition of a given collection of fragments by resolving the proxies
consSeamlessCompFs fs = 
   let ufs = union_frs fs in
   let pg = cons_g (nsTys (sg ufs) [Nprxy]) [] [] [] in
   let g = g_sg $ sg ufs in
   let gm1 = cons_gm (refs ufs) [] in
   let gm2 = gid pg in
   let g_comp = norm_after_po (calc_g_po gm1 gm2 g pg) (nty $ sg ufs) in
   let sg' = cons_sg g_comp (dres (nty $ sg ufs) (ns g_comp)) (dres (ety $ sg ufs) (es g_comp)) (dres (srcm $ sg ufs) (es g_comp)) (dres (tgtm $ sg ufs) (es g_comp)) in
   cons_fr sg' [] [] []

errors_fr::(Eq a, Show a)=>TK -> Fr a -> [ErrorTree]
errors_fr tk f  = 
   let errs1 = check_wf "SG " (Just tk) (sg f) in
   let errs2 = if disjoint [es $ sg f, esr f] then nile else cons_se "Sets of SG edges and reference edges are not disjoint" in 
   let errs3 = if fun_bij (sr f) (esr f) (nsP $ sg f) then nile else cons_et "Function 'sr' is not a bijection. " [check_bij (sr f) (esr f) (nsP . sg $ f)] in
   let errs4 = if (not (isKTotal tk)) || (ran_of $ tr f) `subseteq` (ns $ sg f) 
               then nile 
               else cons_se $ "The following proxy references are invalid:" ++ showElems' (diff (ran_of . tr $ f) (ns . sg $ f)) in
   let errs5 = if total_fun' (tr f) (esr f) then nile else cons_et "Function 'tr' is not total" [check_tfun' (tr f) (esr f)] in
   let errs6 = if acyclicIR f then nile else cons_se "The graph of inheritance with references is acyclic" in
   let errs7 = if (isKTotal tk) && referencesAreValid f 
               then nile 
               else cons_se $ "Invalid proxy references:"++ (showElems' (diff (ran_of . tr $ f) (ns . sg $ f))) in
   let errs8 = if (isKTotal tk) && noHangingProxies f then nile else cons_se "Certain proxies are hanging" in
   let errs9 = if (isKTotal tk) && virtAndAbstAreInheritedF f then nile else cons_se "Certain virtual and abstract nodes are not inherited." in
   [errs1, errs2,errs3,errs4,errs5,errs6,errs7,errs8,errs9]

check_wf_fr nm t f   = 
   check_wf_of f nm (is_wf_fr t) (errors_fr t)
   --if is_wf_fr f t then [] else ("Fragment " ++ (str_of_ostr onm) ++ " is malformed"):(spot_errors_fr f t)

-- Checks that a typing morphism is well-formed (for those fragments accompanied by a typing morphism)
is_wf_ftym f ty = total_fun' (fV ty) (ns . sg $ f) && total_fun' (fE ty) (es . sg $ f)


errors_ftym f ty = 
   let errs1 = if total_fun' (fV ty) (ns . sg $ f) then nile else cons_et "Function 'fV' is not total. " [check_tfun' (fV ty) (ns . sg $ f)] in
   let errs2 = if total_fun' (fE ty) (es . sg $ f) then nile else cons_et "Function 'fE' is not total. " [check_tfun' (fE ty) (es . sg $ f)] in
   [errs1, errs2]

check_wf_ftym f ty onm = 
   --check_wf_of f (str_of_ostr onm) (is_wf_ftym f ty) (errors_ftym f ty)
   if is_wf_ftym f ty then nile else cons_et ("Typing morphism of fragment " ++ (str_of_ostr onm) ++ " is malformed") $ errors_ftym f ty

-- The extended inheritance relation 
inhF f = (inh . sg $ f) `union` (reps f)

-- Gets the reflexive transitive closure of the inheritence relation
inhstF f = rtrancl_on (inhF f) (ns . sg $ f)

-- Extension of src* relation for fragments
src_tgt_stwF f =
   (dres (src . sg $ f) (esW . sg $ f) `rcomp` inv (inhstF f)) `union` (dres (tgt . sg $ f) (esW . sg $ f) `rcomp` inv (inhstF f))

srcstF f = dres (src . sg $ f) (esA . sg $ f) `rcomp` inv (inhstF f) `union` (src_tgt_stwF f)

-- Extension of tgt* relation for fragments
tgtstF f = dres (tgt . sg $ f) (esA . sg $ f) `rcomp` inv (inhstF f) `union` (src_tgt_stwF f)

-- Totalises function
totalise_mv mv f = mv `union` ((inv . refs $ f) `rcomp` mv)

-- Checks if edge kinds are preserved
--edges_kinds_preserved gm fs ft = 
--all (\e-> appl (ety . sg $ fs) e `eq_ety_kind` appl ((fE gm) `rcomp` (ety . sg $ ft)) e) (es . sg $ fs)
--((fE gm) `rcomp` (ety . sg $ ft)) `eq_contents` (ety . sg $ fs)


-- Fragment morphisms
is_wf_gm_frs:: (Eq a) => TK -> (GrM a, Fr a, Fr a) -> Bool
is_wf_gm_frs tk (gm, fs, ft) = 
   let mvT = totalise_mv (fV gm) fs in
   is_wf_fr tk fs && is_wf_fr tk ft
   && total_fun (fV gm) (ns . sg $ fs) (ns . sg $ ft) 
   && total_fun (fE gm) (es . sg $ fs) (es . sg $ ft)
   && ((srcstF fs) `rcomp` (fV gm))  `subseteq` ((fE gm) `rcomp` (srcstF ft))
   && ((tgtstF fs) `rcomp` (fV gm))  `subseteq` ((fE gm) `rcomp` (tgtstF ft))
   && gm_edge_typing_preserved (gm, (sg fs), (sg ft))
   && ((inhstF fs) `rcomp` mvT) `subseteq` (mvT `rcomp` (inhstF ft))

errors_gm_frs tk (gm, fs, ft) = 
   let mvT = totalise_mv (fV gm) fs in
   let errs1 = if is_wf_fr tk fs then nile else check_wf_fr "Source fragment" tk fs in
   let errs2 = if is_wf_fr tk ft then nile else check_wf_fr "Target fragment" tk ft in
   let errs3 = if total_fun (fV gm) (ns . sg $ fs) (ns . sg $ ft) then nile else cons_et "Function 'fV' is not total." [check_tfun (fV gm) (ns . sg $ fs) (ns . sg $ ft)] in
   let errs4 = if total_fun (fE gm) (es . sg $ fs) (es . sg $ ft) then nile else cons_et "Function 'fE' is not total." [check_tfun (fE gm) (es . sg $ fs) (es . sg $ ft)] in
   let errs5 = if ((srcstF fs) `rcomp` (fV gm))  `subseteq` ((fE gm) `rcomp` (srcstF ft)) then nile else cons_se "Problems in commuting of source functions" in
   let errs6 = if ((tgtstF fs) `rcomp` (fV gm))  `subseteq` ((fE gm) `rcomp` (tgtstF ft)) then nile else cons_se "Problems in commuting of target functions" in
   let npes = filter (\e->not $ appl (ety . sg $ fs) e `eq_ety_kind` appl ((fE gm) `rcomp` (ety . sg $ ft)) e)(es . sg $ fs) in
   let errs7 = if gm_edge_typing_preserved (gm, sg fs, sg ft) then nile else cons_se $ "Edge kinds not preserved for edges:" ++ (showElems' npes) in
   let errs8 = if ((inhstF fs) `rcomp` mvT) `subseteq` (mvT `rcomp` (inhstF ft)) then nile else cons_se "Problems in commuting of inheritance relation" in
   [errs1, errs2, errs3, errs4, errs5, errs6, errs7, errs8]

check_wf_gm_frs nm tk (gm, fs, ft) = 
   check_wf_of (gm, fs, ft) nm (is_wf_gm_frs tk) (errors_gm_frs tk)

--if is_wf_gm_frs tk gm fs ft then [] else ("Morphism "++nm++" is mal-formed"):(spot_errors_gm_frs tk gm fs ft)

-- Checks that 'abstract' and 'enum' metamodel nodes have no direct nodes in instance graph
--no_instances_of_abstract_tnodes m f = null (img (inv $ fV m) $ nsTysF f [Nabst, Nenum])

--node_types_preserved gm fs ft = all (\n -> appl (nty sgs) n <= appl ((fV gm) `rcomp` (nty sgt)) n) (ns sgs)

-- Checks that instances of composites are not shared
--composites_not_shared m fs ft =
--   let g' = restrictGrToEdgeTy m (g_sg . sg $ fs) (esTys (sg ft) [Ecomp Bi, Ecomp Uni]) in 
--   injective (relOfGr g')

--multsOk gm fs ft = all (null . multOfGraphToFTEOk gm fs ft) (esTys (sg ft) [Ecomp Bi, Ecomp Uni, Erel Bi, Erel Uni])

-- Typing constraints of Fragment morphisms
is_wf_ty_frs tk (gm, fs, ft)  = 
   let fsc = consSeamlessCompF fs in 
   let ftc = consSeamlessCompF ft in 
   let gmc = resolveProxiesFM gm fs ft in
   is_wf_gm_frs tk (gm, fs, ft)
   && node_types_preserved gm (sg fs) (sg ft)
   && mults_respected gm (srcm . sg $ fs) (srcm . sg $ ft) 
   && mults_respected gm (tgtm . sg $ fs) (tgtm . sg $ ft) 
   -- && no_instances_of_abstract_tnodes gm ft
   -- && composites_not_shared gm fs ft 
   && if (isKTotal tk) then instSGMultsOk gmc (sg fsc) (sg ftc) else True

all_normal_nodes_mapped gm ft = 
   --let is_mapped n = n `elem`  (ran_of $ fV gm) in
   --let inv_refsst = trancl (inv $ refs ft) in
   --all(\n->is_mapped n || (any (\n'->is_mapped n') (img inv_refsst [n]))) (nsTys (sg ft) [Nnrml]) 
   ((nsTys (sg ft) [Nnrml]) `subseteq` ran_of ((fV gm) `rcomp` (inhstF ft)))

is_wf_ty_frs_ref (gm, fs, ft) = 
   is_wf_ty_frs Total (gm, fs, ft) 
    -- every normal node is mapped at least once directly or though proxies
   && all_normal_nodes_mapped gm ft

--checkMultsOk gm fs ft = 
--   let m_checks = map (\te-> (te, multOfGraphToFTEOk gm fs ft te) ) (esTys (sg ft) [Ecomp Bi, Ecomp Uni, Erel Bi, Erel Uni]) in
--   let mult_err_msg te errs = "Multiplicity of type edge " ++ (show te) ++ " is not satisfied in instance graph:" ++ (unlines errs) in
--   map (\(te, errs)-> mult_err_msg te errs) (filter (\(_, errs)-> not (null errs)) m_checks)

--check_composites gm fs ft = 
--   let g' = restrictGrToEdgeTy gm (g_sg . sg $ fs) (esTys (sg ft) [Ecomp Bi, Ecomp Uni]) in 
--   if composites_not_shared gm fs ft then [] else ["Parts are being shared by compounds:"] ++ (analyse_inj_err $ relOfGr g')

errors_ty_frs tk (gm, fs, ft) = 
   let fsc = consSeamlessCompF fs in 
   let ftc = consSeamlessCompF ft in 
   let gmc = resolveProxiesFM gm fs ft in
   let errs1 = errors_gm_frs tk (gm, fs, ft) in
   let npns = non_preserving_nodes gm (sg fs) (sg ft) in
   let errs2 = if node_types_preserved gm  (sg fs) (sg ft) then nile else cons_se $ "Instance nodes fail to preserve their type kinds: " ++ (showElems' npns) in
   let errs3 = check_mults_respected gm (srcm . sg $ fs) (srcm . sg $ ft) "Source" in
   let errs4 = check_mults_respected gm (tgtm . sg $ fs) (tgtm . sg $ ft) "Target" in
   let errs5 = if (isKTotal tk) then checkInstSGMults gmc (sg fsc) (sg ftc) else [] in
   errs1++[errs2, errs3, errs4] ++ errs5

errors_ty_frs_ref (gm, fs, ft) = 
   let errs1 = errors_ty_frs Total (gm, fs, ft) in
   let errs2 = if all_normal_nodes_mapped gm ft then nile else cons_se "Not all normal nodes are being mapped to in the type morphism:" in
   errs1++ [errs2]

check_wf_ty_frs nm WeakM (gm, fs, ft)  = check_wf_of (gm, fs, ft) nm (is_wf_gm_frs Partial) (errors_gm_frs Partial)
check_wf_ty_frs nm PartialM (gm, fs, ft)  = check_wf_of (gm, fs, ft) nm (is_wf_ty_frs Partial) (errors_ty_frs Partial)
check_wf_ty_frs nm FullM (gm, fs, ft) = check_wf_of (gm, fs, ft) nm (is_wf_ty_frs Total) (errors_ty_frs Total)
--check_wf_ty_frs nm (FullM Total) (gm, fs, ft) = check_wf_of (gm, fs, ft) nm (is_wf_ty_frs_ref) (errors_ty_frs_ref)

--Gets instance nodes of particular node type given a morphism
--ns_of_ntyF m f ns = img (inv $ fV m) (img (inv $ inhstF f) ns)

-- Function that gives a non-proxy reference of a node (resolves proxy if proxy)
refOfNode n f = the_or_x (refOfPrxy (Just n) f) n 
    where
      refOfPrxy Nothing _ = Nothing
      refOfPrxy (Just n) f = if n `elem` (nsP . sg $ f) then refOfPrxy (applM (refs f) n) f else (Just n)
      the_or_x Nothing x = x  
      the_or_x (Just y) _ = y


-- Builds a list of substitions for the proxies of the fragment (a relation)
proxySubs f = map (\p->(p, refOfNode p f)) (nsP . sg $ f)

-- Gives the restricted relation to only those proxies that can be resolved
resProxySubs f = filter (\p->fst p /= snd p) (proxySubs f)

-- replaces the proxies in the domain of the nodes function of a morphism
replaceProxies_dom gm f =   
   let subs = proxySubs f `union` id_on (diff (ns . sg $ f) (nsP . sg $ f)) in
   cons_gm ((inv subs) `rcomp` fV gm) (fE gm)

-- replaces the proxies in the range of the nodes function of a morphism
replaceProxies_ran gm f =   
   let subs = proxySubs f `union` id_on (diff (ns . sg $ f) (nsP . sg $ f)) in
   cons_gm ((fV gm) `rcomp` subs) (fE gm)

resolveProxiesFM gm fs ft = 
   let gm' = (replaceProxies_dom gm fs) in
   replaceProxies_ran gm' ft

-- Gets a relation giving the non proxy representatives 
--nonPReps f = rres (repsst f) (nsTys (sg f) (diff sgnty_set [Nprxy]))

--multOfGraphToFTEOk m fs ft te = 
--   let r = relOfGr $ restrictGrToEdgeTy m (g_sg . sg $ fs) [te] in
--   let r' = ((inhstF fs) `rcomp` r) `rcomp` (inv $ inhstF fs) in
--   let r_nonPRep = nonPReps fs in
--   let r'' = no_dups $ ((inv r_nonPRep) `rcomp` r') `rcomp` r_nonPRep  in
--   let ns_s = ns_of_ntyF m ft (img (srcstF ft) [te]) in
--   let ns_s' = img r_nonPRep ns_s in
--   let ns_t = ns_of_ntyF m ft (img (tgtstF ft) [te]) in
--   let ns_t' = img r_nonPRep ns_t in
--   let e_srcm = 
--         if (img (ety . sg $ ft) [te]) `subseteq` [Erel Bi, Ecomp Bi] then appl (srcm . sg $ ft) te else Sm (Val 1) in
--   multGrOk r'' e_srcm (appl (tgtm . sg $ ft) te) ns_s' ns_t'


is_wf_fr' (Just tk) = is_wf_fr tk 
is_wf_fr' Nothing = is_wf_fr Partial 
check_wf_fr' nm (Just tk) = check_wf_fr nm tk
check_wf_fr' nm Nothing = check_wf_fr nm Partial

check_wf_ty_frs' id (Just tk) = check_wf_ty_frs id tk
check_wf_ty_frs' id (Nothing) = check_wf_ty_frs id PartialM


is_wf_ty_frs' Nothing = is_wf_gm_frs Partial 
is_wf_ty_frs' (Just WeakM) = is_wf_gm_frs Partial 
is_wf_ty_frs' (Just PartialM) = is_wf_ty_frs Partial
is_wf_ty_frs' (Just FullM) = is_wf_ty_frs Total
--is_wf_ty_frs' (Just (FullM Total)) = is_wf_ty_frs_ref

instance GR Fr where
   ns = ns . withRsG
   es = es . withRsG
   src = src . withRsG
   tgt = tgt . withRsG
   empty = empty_fr

instance G_CHK Fr where
   is_wf = is_wf_fr'
   check_wf = check_wf_fr'
   
instance GM_CHK Fr Fr where
   is_wf_gm = is_wf_ty_frs'
   check_wf_gm = check_wf_ty_frs'

