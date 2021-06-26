------------------
-- Project: PCs/Fragmenta
-- Module: 'SGrs'
-- Description: Module dedicated to Fragmenta's structural graphs (SGs)
-- Author: Nuno Amálio
-----------------
{-# LANGUAGE MultiParamTypeClasses #-}

module SGrs(SGr, is_wf_sg, inhG, cons_sg, g_sg, nty, ety, srcm, tgtm, empty_sg, nsTys, nsP, esTys, esA, esI, esW, esC, srcst, tgtst, inh, inhst,  
   disj_sgs, union_sg, union_sgs, subsume_sg, sg_refinesz, errs_sg_refinesz, tsg_refinesz, errs_tsg_refinesz, ns_of_ntys, es_of_ety)  where

import Sets
import Relations
import Gr_Cls
import Grs
import ErrorAnalysis
import Utils
import ShowUtils
import SGElemTys
import Mult
import MyMaybe
import GrswT

-- Structural graphs (SGs)
data SGr a = SGr {
   g_sg_ :: (Gr a)
   , nty_ :: [(a, SGNTy)]
   , ety_ :: [(a, SGETy)]
   , srcm_ :: [(a, Mult)]
   , tgtm_ :: [(a, Mult)]
} deriving (Show, Eq)

g_sg SGr {g_sg_ = g, nty_ = _, ety_ = _, srcm_ = _, tgtm_ = _} = g
nty SGr {g_sg_ = _, nty_ = nt, ety_ = _, srcm_ = _, tgtm_ = _} = nt
ety SGr {g_sg_ = _, nty_ = _, ety_ = et, srcm_ = _, tgtm_ = _} = et
srcm SGr {g_sg_ = _, nty_ = _, ety_ = _, srcm_ = sm, tgtm_ = _} = sm
tgtm SGr {g_sg_ = _, nty_ = _, ety_ = _, srcm_ = _, tgtm_ = tm} = tm

-- A SG constructor
cons_sg g nt et sm tm = SGr {g_sg_ = g, nty_ = nt, ety_ = et, srcm_ = sm, tgtm_ = tm}

-- The empty SG
empty_sg :: SGr a
empty_sg = cons_sg empty_g [] [] [] [] 

instance GR SGr where
   ns = ns . g_sg
   es = es . g_sg
   src = src . g_sg
   tgt = tgt . g_sg
   empty = empty_sg

-- Gets edges of certain types
esTys sg ets = img (inv $ ety sg) ets

-- Gets nodes of certain types
nsTys sg nts = img (inv $ nty sg) nts

-- Gets proxy nodes
nsP = (flip nsTys) [Nprxy]

-- Gets optional nodes
nsO = (flip nsTys) [Nopt]

-- Gets ethereal nodes
nsEther = (flip nsTys) [Nabst, Nvirt, Nenum]

-- Gets the inheritance edges
esI = (flip esTys) [Einh]

-- Gets the association edges
esA::Eq a=>SGr a->[a]
esA = (flip esTys) [et d | et<-[Ecomp, Erel], d<-[Dbi, Duni]]

-- Gets the wander edges
esW::Eq a=>SGr a->[a]
esW = (flip esTys) [Ewander]

-- Gets connection edges (association + wander)
esC sg = (esA sg) `union` (esW sg)

-- Inheritence graph: SG is restricted to inheritance edges only
inhG sg = restrict sg $ esI sg

-- Inheritence relation buillt from inheritance graph
inh::Eq a=>SGr a->[(a, a)]
inh = relOfG . inhG 

-- Reflexive transitive closure of inheritence relation
inhst sg = rtrancl_on (inh sg) (ns sg)

-- totalises 'srcm' by providing multiplicities of uni-directional composition and relation edges
srcma sg = (srcm sg) `override` ((esTys sg [Ecomp Duni] `cross` [msole_k 1]) `override` (esTys sg [Erel Duni] `cross` [msole_many]))

-- Checks whether edges comply with their type multiplicity allowances
edge_mult_ok::Eq a =>SGr a->a->Bool
edge_mult_ok sg e = (appl (ety sg) e) `allowedm` (appl (srcma sg) e, appl (tgtm sg) e)

mult_etys_ok::Eq a =>SGr a->Bool
mult_etys_ok sg = all (\e->edge_mult_ok sg e) (esC sg)

-- Checks whether inheritance relations between nodes comply with the inheritance restrictions of their types
inh_nty_ok sg (v, v') = (appl(nty sg) v) < (appl(nty sg) v')
inh_ntys_ok::Eq a =>SGr a->Bool
inh_ntys_ok sg = all (inh_nty_ok sg) (inh sg)

-- Checks whether
nodeopt_ok::Eq a =>SGr a->a->Bool
nodeopt_ok sg n = img (ety sg) (esIncident (g_sg sg) [n]) `subseteq` [Ewander]

optsVoluntary::Eq a =>SGr a->Bool
optsVoluntary sg = all (\n->nodeopt_ok sg n) $ nsO sg

-- Function that checks that a list of multiplicies are well-formed
mults_wf = all multwf

acyclicI::Eq a =>SGr a->Bool
acyclicI = acyclicG . inhG

-- Checks whether a SG is well-forfEd either totally or partially
is_wf_sg::Eq a =>SGr a->Bool
is_wf_sg sg = is_wf Nothing (g_sg sg)
   && fun_total (nty sg) (ns sg) (sgnty_set) 
   && fun_total (ety sg) (es sg) (sgety_set)
   && mults_wf (ran_of $ srcm sg) && mults_wf (ran_of $ tgtm sg) 
   && fun_total' (srcma sg) (esC sg) && fun_total' (tgtm sg) (esC sg)
   && mult_etys_ok sg && optsVoluntary sg 
   && inh_ntys_ok sg && acyclicI sg

-- Ethereal nodes must be inherited
etherealInherited::Eq a =>SGr a->Bool
etherealInherited sg = (nsEther sg) `subseteq` (ran_of $ inh sg)

-- Condition for total SGs
is_wf_tsg::Eq a =>SGr a->Bool
is_wf_tsg sg = is_wf_sg sg && etherealInherited sg

check_mult_etys_ok sg = 
   if mult_etys_ok sg then nile else cons_se $ "The following edges have incorrect multiplicities:"++ (showElems' err_es)
   where err_es = foldr (\e es->if edge_mult_ok sg e then es else (e:es)) [] (esC sg)

check_optsVoluntary::(Eq a, Show a) =>SGr a->ErrorTree
check_optsVoluntary sg = 
   if optsVoluntary sg then nile else cons_se $ "The following optional nodes are engaged in compulsory relations:" ++ (showElems' err_opts)
   where err_opts = foldr (\n ns-> if nodeopt_ok sg n then ns else n:ns) [] (nsO sg)

check_inh_ntys_ok::(Eq a, Show a) =>SGr a->ErrorTree
check_inh_ntys_ok sg = 
   if inh_ntys_ok sg then nile else cons_se $ "The following inheritance relations are not compliant with the node type restrictions:" ++ (showElems' err_inh_pairs)
   where err_inh_pairs = filter (not . (inh_nty_ok sg)) (inh sg)

-- Handles errors related to multiplicity 
-- err_multiplicity_maps s_set t_set = 
--    let err2 = if null (diff s_set t_set) then nile else cons_se $ "the following elements should not have a multiplicity mapping :" ++ showElems' (diff s_set r_set) in
--    let err3 = if null (diff t_set s_set) then nile else cons_se $ "no multiplicity mappings for the following edges :" ++ showElems' (diff r_set s_set) in
--    if s_set `seteq` r_set then nile else cons_et "multiplicity mappings are incorrect." [err2, err3]

-- multiplicities_src sg = 
--    let errt = multiplicities_src_tgt (dom_of (srcm sg)) (esTys sg $ [Ewander] ++ [e d | e<-[Erel, Ecomp],d<-[Dbi]])  in
--    err_prepend "Source " errt

-- multiplicities_tgt sg = 
--    let errt = multiplicities_src_tgt (dom_of (tgtm sg)) (esC sg) in
--    err_prepend "Target " errt

errors_sg::(Eq a, Show a)=>SGr a-> [ErrorTree]
errors_sg sg = 
   let err1 = err_prepend "The underlying graph is malformed." (check_wf "SG" Nothing $ g_sg sg) in
   let err2 = err_prepend "Function 'nty' is not total. " $ check_fun_total (nty sg) (ns sg) (sgnty_set) in
   let err3 = err_prepend "Function 'ety' is not total. " $ check_fun_total (ety sg) (es sg) (sgety_set) in
   let err4 = if mults_wf (ran_of $ srcm sg) then nile else cons_se "Well-formedness errors in edge source multiplicities." in
   let err5 = if mults_wf (ran_of $ tgtm sg) then nile else cons_se "Well-formedness errors in edge target multiplicities." in
   let err6 = err_prepend "Source multplicity function is not total" $ check_fun_total' (srcma sg) (esC sg) in
   let err7 = err_prepend "Target multplicity function is not total" $ check_fun_total' (tgtm sg) (esC sg) in
   let err8 = check_mult_etys_ok sg in
   let err9 = check_optsVoluntary sg in
   let err10 = check_inh_ntys_ok sg in
   let err11 = if acyclicI sg then nile else cons_se "The inheritance hierarchy has cycles." in
   [err1, err2, err3, err4, err5, err6, err7, err8, err9, err10, err11]

check_wf_sg::(Eq a, Show a)=>String->SGr a-> ErrorTree
check_wf_sg nm sg = check_wf_of sg nm is_wf_sg errors_sg

check_etherealInherited sg = 
   if etherealInherited sg then nile else cons_se $ "The following ethereal nodes are not inherited:"++ (showElems' ens_n_inh)
   where isInherited n = n `elem` (ran_of $ inh sg)
         ens_n_inh = filter (not . isInherited)(nsEther sg) 
errors_tsg::(Eq a, Show a)=>SGr a-> [ErrorTree]
errors_tsg sg = 
   let err1 = check_wf "SG" Nothing sg in
   let err2 = check_etherealInherited sg in
   [err1, err2]

check_wf_tsg::(Eq a, Show a)=>String->SGr a-> ErrorTree
check_wf_tsg nm sg = check_wf_of sg nm is_wf_tsg errors_tsg

is_wf_sg' (Just Total) = is_wf_tsg 
is_wf_sg' _ = is_wf_sg

check_wf_sg' id (Just Total) = check_wf_tsg id
check_wf_sg' id _            = check_wf_sg id  

instance G_WF_CHK SGr where
   is_wf = is_wf_sg'
   check_wf = check_wf_sg'

-- src relation which takes wander edges into account
srcr::Eq a=>SGr a->[(a, a)]
srcr sg = src sg `union` (dres (tgt sg) (esW sg))

-- tgt relation which takes wander edges into account
tgtr::Eq a=>SGr a->[(a, a)]
tgtr sg = tgt sg `union` (dres (src sg) (esW sg))

-- src* relations: base and final definitions
srcst_0 sg = dres (srcr sg) (esC sg) 
srcst sg = (srcst_0 sg) `rcomp` (inv . inhst $ sg)

-- tgt* relations: base and final definitions
tgtst_0 sg = dres (tgtr sg) (esC sg)
tgtst sg = (tgtst_0 sg) `rcomp` (inv $ inhst sg)

-- Checs whether SGs are disjoint
disj_sgs sgs = disj_gs (map g_sg sgs) 

-- Union of SGs
union_sg sg1 sg2 = 
   let ug = (g_sg sg1) `union_g` (g_sg sg2) in
   let u_nty = (nty sg1) `union` (nty sg2) in
   let u_ety = (ety sg1) `union` (ety sg2) in
   let u_srcm = (srcm sg1) `union` (srcm sg2) in
   let u_tgtm = (tgtm sg1) `union` (tgtm sg2) in
   cons_sg ug u_nty u_ety u_srcm u_tgtm

union_sgs sgs = 
   cons_sg (union_gs $ map g_sg sgs) (gunion $ map nty sgs) (gunion $ map ety sgs) (gunion $ map srcm sgs) (gunion $ map tgtm sgs)

-- SG subsumption
subsume_sg sg sub 
   | pfun sub (nsP sg) (ns sg) && antireflexive sub = cons_sg s_g (dsub (nty sg) (dom_of sub)) (ety sg) (srcm sg) (tgtm sg)
   where s_g = subsume_g (g_sg sg) sub 

-- Notion of allowed edge refinefEnts
-- allow_edge_ref::SGETy->SGETy->Bool
-- allow_edge_ref (Ecomp Dbi) (Ecomp Dbi) = True
-- allow_edge_ref (Ecomp Dbi) (Ecomp Duni) = True
-- allow_edge_ref (Erel Dbi) (Erel d) = d `elem` [Dbi, Duni]
-- allow_edge_ref (Erel Dbi) (Ewander) = True
-- allow_edge_ref (Erel Dbi) (Erel Duni) = True
-- allow_edge_ref (Ewander) b = is_val_edge_ref_of_wander b
-- allow_edge_ref a b = a == b

-- is_val_edge_ref_of_wander b = b `elem` ([e d | e<-[Erel, Ecomp], d<-[Dbi, Duni]] ++ [Ewander])
-- --[Erel Dbi, Erel Duni, Erel Duni,Ecomp Dbi, Ecomp DUni, E wander]


-- allowed_edge_refs::[(SGETy,SGETy)]
-- allowed_edge_refs = [(x, y) | x<-sgety_set, y<-sgety_set, allow_edge_ref x y]
--zip [Einh] [Einh]
--allowed_edge_refs @ekv(Ecomp _) = [Ecomp Bi, Ecomp Uni]
--allowed_edge_refs (Erel _) = [Erel Bi, Erel Uni]
--allowed_edge_refs (Ewander) = [Erel Bi, Erel Uni,Ecomp Bi, Ecomp Uni,Ewander]

commute_sgm_src (sgs, m, sgt) = 
   let lhs = (fV m) `bcomp` (srcst sgs) in  
   let rhs = (srcst sgt) `bcomp` (fE m) in
   (lhs, rhs)

-- Checks whether the source function commutes for morphisms between SGs
morphism_sgm_commutes_src (sgs, m, sgt) = 
   let (lhs, rhs) = commute_sgm_src (sgs, m, sgt) in
   lhs  `subseteq` rhs

commute_sgm_tgt (sgs, m, sgt) = 
   let lhs = (fV m) `bcomp` (tgtst sgs) in  
   let rhs = (tgtst sgt) `bcomp` (fE m) in
   (lhs, rhs)

-- Checks whether the target function commutes for morphisms between SGs
morphism_sgm_commutes_tgt (sgs, m, sgt) = 
   let (lhs, rhs) = commute_sgm_tgt (sgs, m, sgt) in
   lhs  `subseteq` rhs

-- Checks whether the inheritance is preserved
ihh_sgm_ok (sgs, m, sgt) = ((fV m) `bcomp` (inhst sgs)) `subseteq` ((inhst sgt) `bcomp` (fV m))

-- Common aspects of both graph morphism settings which involve SGs
is_wf_gm_common (gs, m, gt) = 
   -- is_wf Nothing gs && is_wf Nothing gt 
   fun_total (fV m) (ns gs) (ns gt)  

-- checks whether a morphisms between SGs is well-formed
is_wf_sgm::Eq a => (SGr a, GrM a,  SGr a) -> Bool
is_wf_sgm (sgs, m, sgt) = is_wf_gm_common (sgs, m, sgt)
   && fun_total (fE m) (esC sgs) (esC sgt)
   && morphism_sgm_commutes_src (sgs, m, sgt)
   && morphism_sgm_commutes_tgt (sgs, m, sgt)
   && ihh_sgm_ok (sgs, m, sgt)

errors_sgm_common (gs, m, gt) =
   let err1 = check_wf "Source graph" Nothing gs in
   let err2 = check_wf "Target Graph" Nothing gt in
   let err3 = if fun_total (fV m) (ns gs) (ns gt) then nile else cons_et "Function 'fV' is ill defined." [check_fun_total (fV m) (ns gs) (ns gt)] in
   [err1, err2, err3]

errors_commuting (r1, r2) ty = 
   if  r1 `subseteq` r2 then nile else cons_et ("Problems in commuting of " ++ ty ++ " functions") [check_subseteq r1 r2]

errors_wf_sgm (gs, m, gt) = 
   let errs1 = errors_sgm_common (gs, m, gt) in
   let err2 = if fun_total (fE m) (esC gs) (esC gt) then nile else cons_et "Function 'fE' is ill defined." [check_fun_total (fE m) (esC gs) (esC gt)] in
   let err3 = if morphism_sgm_commutes_src (gs, m, gt) then nile else errors_commuting (commute_sgm_src (gs, m, gt)) "source" in
   let err4 = if morphism_sgm_commutes_tgt (gs, m, gt) then nile else errors_commuting (commute_sgm_tgt (gs, m, gt)) "target" in
   let err5 = if ihh_sgm_ok (gs, m, gt) then nile else cons_se "Problems in the commuting of the inheritance relation" in
   errs1 ++ [err2, err3, err4, err5]

check_wf_sgm::(Eq a, Show a)=>String->SGr a-> GrM a->SGr a->ErrorTree
check_wf_sgm nm sgs gm sgt = check_wf_of (sgs, gm, sgt) nm (is_wf_sgm) (errors_wf_sgm)

commute_gm_src::Eq a => (GrwT a, SGr a) ->([(a, a)], [(a, a)])
commute_gm_src (gwt, sg) = 
   let lhs = (fV gwt) `bcomp` (src gwt) in  
   let rhs = (srcst sg) `bcomp` (fE  gwt) in
   (lhs, rhs)

-- Checks whether the source function commutes for morphisms from Gs to SGs
morphism_gm_commutes_src::Eq a => (GrwT a, SGr a) -> Bool
morphism_gm_commutes_src (gwt, sg) = 
   let (lhs, rhs) = commute_gm_src (gwt, sg) in
   lhs  `subseteq` rhs

commute_gm_tgt::Eq a => (GrwT a, SGr a) ->([(a, a)], [(a, a)])
commute_gm_tgt (gwt, sg) = 
   let lhs = (fV gwt) `bcomp` (tgt gwt) in  
   let rhs = (tgtst sg) `bcomp` (fE gwt) in
   (lhs, rhs)

-- Checks whether the target function commutes for morphisms from Gs to SGs
morphism_gm_commutes_tgt::Eq a => (GrwT a, SGr a) -> Bool
morphism_gm_commutes_tgt (gwt, sg) = 
   let (lhs, rhs) = commute_gm_tgt (gwt, sg) in
   lhs  `subseteq` rhs

is_wf_gwt_sg:: Eq a => (GrwT a, SGr a) -> Bool
is_wf_gwt_sg (gwt, sg) = is_wf_gm_common (gOf gwt, ty gwt, sg)
   && fun_total (fE gwt) (es gwt) (esC sg)
   && morphism_gm_commutes_src (gwt, sg)
   && morphism_gm_commutes_tgt (gwt, sg)

errors_gwt_sg::(Eq a, Show a) => (GrwT a, SGr a) -> [ErrorTree]
errors_gwt_sg (gwt, sg) =
   let errs1 = errors_sgm_common (gOf gwt, ty gwt, sg) in
   let err2 = if fun_total (fE gwt) (es gwt) (esC sg) then nile else cons_et "Function 'fE' is ill defined." [check_fun_total (fE gwt) (es gwt) (esC sg)] in
   let err3 = if morphism_gm_commutes_src (gwt, sg) then nile else errors_commuting (commute_gm_src (gwt, sg)) "source" in
   let err4 = if morphism_gm_commutes_tgt (gwt, sg) then nile else errors_commuting (commute_gm_tgt (gwt, sg)) "target" in 
   errs1 ++ [err2, err3, err4]

check_wf_gwt_sg nm gwt sg = check_wf_of (gwt, sg) nm (is_wf_gwt_sg) (errors_gwt_sg)

-- Gets instance nodes of a particular set of meta-nodes type given a morphism
insOf::(Eq a, GRM gm)=>gm a->SGr a->[a]->[a]
insOf m sg mns = img (inv . fV $ m) (img (inv . inhst $ sg) mns)

-- Gets instance edges of particular set of meta-edges given a morphism
iesOf::(Eq a, GRM gm)=>gm a->[a]->[a]
iesOf m mes = img (inv . fE $ m) mes

-- A function obtains the instance graph restricted to a set of meta-edges
igRMEs::Eq a=>GrwT a->[a]->Gr a
igRMEs gwt mes = (gOf gwt) `restrict` (iesOf (ty gwt) mes)

-- Checks that 'abstract' and 'enum' fEtamodel nodes have no direct nodes in instance graph
no_instances_of_abstract_tnodes m sgt = null (img (inv $ fV m) $ nsTys sgt [Nabst, Nenum])

-- Checks whether an edge is instantiated invertedly, which is permitted for wander edges
inverted_ie gwt sg e = applM ((tgt sg) `bcomp` (fE . ty $ gwt)) e == applM ((fV . ty $ gwt) `bcomp` (src sg)) e

-- Gets the instance graph restricted to a wander edge
gOfwei gwt sg e = 
   let g' = gOf gwt in
   if inverted_ie gwt sg e then invertg g' else g'

-- Gets the instance graph restricted to a set of wander edges
gOfweis gwt sg [] = empty_g
gOfweis gwt sg (e:es) = gOfwei gwt sg e `union_g` gOfweis gwt sg es

-- Gets an instance graph restricted to a set of meta-edges
igRMEsW::Eq a=>GrwT a->SGr a->a->Gr a
igRMEsW gwt sg me = if me `elem` esW sg then gOfweis gwt sg (img (inv $ (fE . ty $ gwt)) [me]) else igRMEs gwt [me]

-- SG multiplicity refinement
sgs_mult_leq sgc m sga e  = appl (srcma sgc) e <= appl ((srcma sga) `bcomp` (fE m)) e
sg_refines_m (sgc, m) sga = all (\e-> sgs_mult_leq sgc m sga e) (esC sgc)

-- SG refinement of edge types
sgs_ety_leq sgc m sga e  = appl (ety sgc) e <= appl ((ety sga) `bcomp` (fE m)) e
sg_refines_ety (sgc, m) sga = all (\e-> sgs_ety_leq sgc m sga e) (esC sgc)

-- SG refinement of node types
sgs_nty_leq sgc m sga n  = appl (nty sgc) n <= appl ((nty sga) `bcomp` (fV m)) n
sg_refines_nty (sgc, m) sga = all (\n-> sgs_nty_leq sgc m sga n) (ns sgc)

-- SG refinement conditions
sg_refinesz (sgc, m) sga = (sgc, m) `sg_refines_nty` sga && (sgc, m) `sg_refines_ety`  sga 
   && (sgc, m) `sg_refines_m` sga

-- SG refinement 
sg_refines (sgc, m) sga = is_wf_sgm (sgc, m, sga) &&  (sgc, m) `sg_refinesz` sga

-- Error checking
check_sg_refines_m (sgc, m) sga = 
   if (sgc, m) `sg_refines_m` sga then nile else cons_se $ "Issues with multiplicity refinement for the following edges:" ++ (showElems' es_n_ref)
   where es_n_ref = filter (\e-> not $ sgs_mult_leq sgc m sga e) (esC sgc)

check_sg_refines_ety (sgc, m) sga = 
   if (sgc, m) `sg_refines_ety` sga then nile else cons_se $ "Issues with edge type refinement for the following edges:" ++ (showElems' es_n_ref)
   where es_n_ref = filter (\e-> not $ sgs_nty_leq  sgc m sga e) (esC sgc)

check_sg_refines_nty (sgc, m) sga = 
   if (sgc, m) `sg_refines_nty` sga then nile else cons_se $ "The following instance nodes fail to preserve their type kinds: " ++ (showElems' ns_n_ref)
   where ns_n_ref = filter (\n-> not $ sgs_nty_leq sgc m sga n) (ns sgc)

errs_sg_refinesz (sgc, m) sga = 
   let err1 = check_sg_refines_nty (sgc, m) sga in
   let err2 = check_sg_refines_ety (sgc, m) sga in
   let err3 = check_sg_refines_m (sgc, m) sga in
   [err1, err2, err3]

-- errors of SG refinement
errs_sg_refines id (sgc, m, sga) = 
   let err1 = check_wf_sgm id sgc m sga in
   let errs2 = errs_sg_refinesz (sgc, m) sga in
   (err1:errs2)

check_sg_refines id (sgc, m) sga = check_wf_of (sgc, m, sga) id (sg_refines') (errs_sg_refines id)
   where sg_refines' (sgc, m, sga) = (sgc, m) `sg_refines` sga

-- Total SG refinement of abstract nodes
is_refined m sga n = not . null $ (img (inhst sga) [n]) `intersec` (ran_of  $ fV m)
tsg_refines_ans m sga = all (\nn-> is_refined m sga nn) (nsTys sga [Nnrml])

-- Total SG refinement of abstract edges
tsg_refines_aes::Eq a=>(SGr a, GrM a)->SGr a->Bool
tsg_refines_aes (sgc, m) sga = all (\me->(sga, me) `okRefinedIn` (sgc, m)) (esA sga)

-- Checks if the instance relation is refined correctly
okRefinedIn::Eq a=>(SGr a, a)->(SGr a, GrM a)->Bool
okRefinedIn (sga, me) (sgc, m) = 
   let r = (inhst sgc) `rcomp` (relOfG $ igRMEsW (cons_gwt (g_sg sgc) m) sga me) `rcomp` (inv . inhst $ sgc) in
   let s = (insOf m sga $ img (src sga) [me]) `diff`  (nsEther sgc `diff` dom_of r) in
   let t = (insOf m sga $ img (tgt sga) [me]) `diff` (nsEther sgc `diff` ran_of r) in
   (relation r s t) && (not . null $ r) 

-- Total SG refinement conditions
tsg_refinesz::Eq a=>(SGr a, GrM a)->SGr a->Bool
tsg_refinesz (sgc, m) sga = 
   (sgc, m) `sg_refinesz` sga && (sgc, m) `tsg_refines_aes` sga && m `tsg_refines_ans` sga

-- Total SG refinement
tsg_refines::Eq a=>(SGr a, GrM a)->SGr a->Bool
tsg_refines (sgc, m) sga = is_wf_sgm (sgc, m, sga) && (sgc, m) `tsg_refinesz` sga 

-- Errors checking
-- errors of SG refinement of abstract nodes
check_tsg_refines_ans m sga = 
   if m `tsg_refines_ans` sga then nile else cons_se $ "The following normal nodes are not being refined: " ++ (showElems' nns_n_ref)
   where nns_n_ref = filter (\nn-> not $ is_refined m sga nn) (nsTys sga [Nnrml])

check_tsg_refines_aes::(Eq a, Show a)=>(SGr a, GrM a)->SGr a->ErrorTree
check_tsg_refines_aes (sgc, m) sga =
   if (sgc, m) `tsg_refines_aes` sga then nile else cons_se $ "Certain association edges are not correctly refined: " ++ (showElems' aes_nref)
   where aes_nref = filter (\me-> not $ (sga, me) `okRefinedIn` (sgc, m)) (esA sga)

errs_tsg_refinesz::(Eq a, Show a)=>(SGr a, GrM a)->SGr a->[ErrorTree]
errs_tsg_refinesz (sgc, m) sga =
   let errs1 = errs_sg_refinesz (sgc, m) sga in
   let err2 = check_tsg_refines_ans m sga in
   let err3 = check_tsg_refines_aes (sgc, m) sga in
   errs1 ++ [err2, err3]

check_tsg_refines::(Eq a, Show a)=>String->(SGr a, GrM a)->SGr a->ErrorTree
check_tsg_refines id (sgc, m) sga = 
   let err1 = check_wf_sgm id sgc m sga in
   let errs2 = errs_tsg_refinesz (sgc, m) sga in
   if (sgc, m) `tsg_refines` sga then nile else cons_et "Errors in total SG refinement" (err1:errs2)

is_wf_sgm'::Eq a=>Maybe MK->(SGr a, GrM a, SGr a)->Bool
is_wf_sgm' Nothing = is_wf_sgm
is_wf_sgm' (Just WeakM) = is_wf_sgm
is_wf_sgm' (Just PartialM) = (\(sgc, m, sga)->(sgc, m) `sg_refines` sga)
is_wf_sgm' (Just TotalM) = (\(sgc, m, sga)->(sgc, m) `tsg_refines` sga)

check_wf_gm_g'::(Eq a, Show a)=>String->Maybe MK->(SGr a, GrM a, SGr a)->ErrorTree
check_wf_gm_g' id Nothing (sgc, m, sga)= check_wf_sgm id sgc m sga
check_wf_gm_g' id (Just WeakM) (sgc, m, sga) = check_wf_sgm id sgc m sga
check_wf_gm_g' id (Just  PartialM) (sgc, m, sga) = check_sg_refines id (sgc, m) sga
check_wf_gm_g' id (Just TotalM) (sgc, m, sga) = check_tsg_refines id (sgc, m) sga

instance GM_CHK SGr SGr where
   is_wf_gm = is_wf_sgm'
   check_wf_gm = check_wf_gm_g'

--
-- SG Type conformance

-- Instances of compounds are not allowed to share parts
ty_complies_pns::Eq a=>GrwT a->SGr a->Bool
ty_complies_pns gwt sg = injective $ relOfG (igRMEs gwt (esTys sg [Ecomp Dbi, Ecomp Duni]))

check_ty_complies_pns::(Eq a, Show a)=>GrwT a->SGr a->ErrorTree
check_ty_complies_pns gwt sg = 
   let r = relOfG $ igRMEs gwt (esTys sg [Ecomp Dbi, Ecomp Duni]) in
   if gwt `ty_complies_pns` sg then nile else cons_et "Parts are being shared by compounds:" [check_inj r]

-- Instances of ethereal nodes are not allowed
insEther gwt sg = img ((inv. fV) $ gwt) (nsEther sg)
ty_complies_fi::Eq a=>GrwT a->SGr a->Bool
ty_complies_fi gwt sg = null $ insEther gwt sg

check_ty_complies_fi gwt sg = 
   if ty_complies_fi gwt sg then nile else cons_se $ "Error! There are the following ethereal nodes instances:" ++ (showElems' (insEther gwt sg))

-- Checks whether the appropriate instances of a SG comply to the meta-edges's multiplicity constraints
me_mult_ok::Eq a=>SGr a->a->GrwT a->Bool
me_mult_ok sg me gwt = 
   let r = relOfG $ igRMEsW gwt sg me in
   let s = insOf gwt sg $ img (src sg) [me] in
   let t = insOf gwt sg $ img (tgt sg) [me] in
   multOk r s t (appl (srcma sg) me) (appl (tgtm sg) me)

check_me_mult_ok::(Eq a, Show a)=>SGr a->a->GrwT a->ErrorTree
check_me_mult_ok sg me gwt = 
   let r = relOfG $ igRMEsW gwt sg me in
   let s = insOf gwt sg $ img (src sg) [me] in
   let t = insOf gwt sg $ img (tgt sg) [me] in
   check_multOk me r s t (appl (srcma sg) me) (appl (tgtm sg) me)

-- Multiplicity compliance
ty_complies_mult::Eq a=>GrwT a->SGr a->Bool
ty_complies_mult gwt sg = all (\me->me_mult_ok sg me gwt) (esC sg)

check_ty_complies_mult gwt sg = 
   if ty_complies_mult gwt sg then nile else cons_et "Multiplicity constraints are breached in the instance model." errs
   where errs = foldr (\me errs ->(check_me_mult_ok sg me gwt):errs) [] (esC sg)

ty_complies::Eq a=>GrwT a->SGr a->Bool
ty_complies gwt sg = is_wf_gwt_sg (gwt, sg) && gwt `ty_complies_mult` sg &&  gwt `ty_complies_fi` sg && gwt `ty_complies_pns` sg 

check_ty_complies::(Eq a, Show a)=>String->GrwT a->SGr a->ErrorTree
check_ty_complies id gwt sg =
   let err1 = check_wf_gwt_sg id gwt sg in
   let err2 = check_ty_complies_mult gwt sg in
   let err3 = check_ty_complies_fi gwt sg in
   let err4 = check_ty_complies_pns gwt sg in
   if gwt `ty_complies` sg then nile else cons_et "Errors in compliance of graph to its SG type" [err1, err2, err3, err4]

is_wf_ty::(Eq a)=>(Maybe MK)->(GrwT a, SGr a)->Bool
is_wf_ty Nothing          = is_wf_gwt_sg 
is_wf_ty (Just WeakM)     = is_wf_gwt_sg 
is_wf_ty (Just PartialM)  = (\(gwt, sg)->gwt `ty_complies` sg)
is_wf_ty (Just TotalM)    = (\(gwt, sg)->gwt  `ty_complies` sg)

check_wf_ty id Nothing (gwt, sg) =check_wf_gwt_sg id gwt sg
check_wf_ty id (Just WeakM) (gwt, sg) = check_wf_gwt_sg id gwt sg
check_wf_ty id (Just PartialM) (gwt, sg) = check_ty_complies id gwt sg
check_wf_ty id (Just TotalM) (gwt, sg) = check_ty_complies id gwt sg

instance GM_CHK' GrwT SGr where
   is_wf_gm' = is_wf_ty
   check_wf_gm' = check_wf_ty

--is_wf_gwtss_sg:: Eq a => (GrwTSs a, SGr a) -> Bool
--is_wf_gwtss_sg (g, sg) = fun_total (fV g) (ans g) (ns sg)  
--   && fun_total (fE g) (es g) (esC sg)
--   && img (fE g) (ses g) `subseteq` (esSeq sg) 
--   && ((fV g) `bcomp` (src g)) `subseteq` ((srcst sg) `bcomp` (fE  g))
--   && ((fV g) `bcomp` (tgtext g)) `subseteq` ((tgtst sg) `bcomp` (fE  g))


-- Checks whether the target function commutes for morphisms from Gs to SGs
-- morphism_gm_commutes_tgt_ss::Eq a => (GrwTSs a, SGr a) -> Bool
-- morphism_gm_commutes_tgt_ss (g, sg) = 
--    let lhs = (fV g) `bcomp` (tgtext g) in  
--    let rhs = (tgtst sg) `bcomp` (fE g) in
--    lhs  `subseteq` rhs

-- commute_gm_tgt_ss::Eq a => (GrwTSs a, SGr a) ->([(a, a)], [(a, a)])
-- commute_gm_tgt_ss (g, sg) = 
--    let lhs = (fV g) `bcomp` (tgtext g) in  
--    let rhs = (tgtst sg) `bcomp` (fE g) in
--    (lhs, rhs)

-- errors_gwtss_sg::(Eq a, Show a) => (GrwTSs a, SGr a) -> [ErrorTree]
-- errors_gwtss_sg (g, sg) =
--    let err1 = if fun_total (fV g) (ans g) (ns sg) then nile else cons_et "Function 'fV' is ill defined." [check_fun_total (fV g) (ans g) (ns sg)] in
--    let err2 = if fun_total (fE g) (es g) (esC sg) then nile else cons_et "Function 'fE' is ill defined." [check_fun_total (fE g) (es g) (esC sg)] in
--    let err3 = if morphism_gm_commutes_src (gwt g, sg) then nile else errors_commuting (commute_gm_src (gwt g, sg)) "source" in
--    let err4 = if morphism_gm_commutes_tgt_ss (g, sg) then nile else errors_commuting (commute_gm_tgt_ss (g, sg)) "target" in 
--    [err1, err2, err3, err4]

-- check_wf_gwtss_sg nm g sg = check_wf_of (g, sg) nm (is_wf_gwtss_sg) (errors_gwtss_sg)

-- tyss_complies::Eq a=>GrwTSs a->SGr a->Bool
-- tyss_complies g sg = is_wf_gwtss_sg (g, sg) 
--     &&  (gwt g) `ty_complies_mult` sg &&  (gwt g)`ty_complies_fi` sg && (gwt g) `ty_complies_pns` sg 

-- check_tyss_complies::(Eq a, Show a)=>String->GrwTSs a->SGr a->ErrorTree
-- check_tyss_complies id g sg =
--    let err1 = check_wf_gwtss_sg id g sg in
--    let err2 = check_ty_complies_mult (gwt g) sg in
--    let err3 = check_ty_complies_fi (gwt g) sg in
--    let err4 = check_ty_complies_pns (gwt g) sg in
--    if g `tyss_complies` sg then nile else cons_et "Errors in compliance of graph to its SG type" [err1, err2, err3, err4]

-- is_wf_tyss::(Eq a)=>(Maybe MK)->(GrwTSs a, SGr a)->Bool
-- is_wf_tyss Nothing          = is_wf_gwtss_sg
-- is_wf_tyss (Just WeakM)     = is_wf_gwtss_sg
-- is_wf_tyss (Just PartialM)  = (\(g, sg)->g `tyss_complies` sg)
-- is_wf_tyss (Just TotalM)    = (\(g, sg)->g  `tyss_complies` sg)

-- check_wf_tyss id Nothing (g, sg) =check_wf_gwtss_sg id g sg
-- check_wf_tyss id (Just WeakM) (g, sg) = check_wf_gwtss_sg id g sg
-- check_wf_tyss id (Just PartialM) (g, sg) = check_tyss_complies id g sg
-- check_wf_tyss id (Just TotalM) (g, sg) = check_tyss_complies id g sg

-- instance GM_CHK' GrwTSs SGr where
--    is_wf_gm' = is_wf_tyss
--    check_wf_gm' = check_wf_tyss

--Gets instance nodes of particular node type given a type sg and a morphism
ns_of_ntys m sg ns = img (inv . fV $ m) (img (inv . inhst $ sg) ns)

--Gets instance edges of particular node type given a morphism
es_of_ety m e = img (inv . fE $ m) [e]

-- is_wf_ty_sgs_strong:: (Eq a, Show a) => (GrM a, SGr a, SGr a) -> Bool
-- is_wf_ty_sgs_strong (gm, sgc, sga) = 
--    is_wf_ty_sgs_weak (gm, sgc, sga)
--    && (nsTys sga [Nnrml]) `subseteq` (ran_of $ fV gm)

-- -- The typing notion between a graph and a SG
-- is_wf_ty_g_sg:: (Eq a, Show a) => (GrM a, Gr a, SGr a) -> Bool
-- is_wf_ty_g_sg (m, g, sg) = 
--    is_wf_gm_g_sg (m, g, sg)
--    && no_instances_of_abstract_tnodes m sg 
--    && composites_not_shared m g sg
--    && instMultsOk m g sg

-- non_preserving_nodes gm sgs sgt = filter (\n->not $ appl (nty sgs) n <= appl ((fV gm) `rcomp` (nty sgt)) n) (ns sgs)

-- errors_ty_sgs_partial::(Eq a, Show a)=>String -> (GrM a, SGr a, SGr a) -> [ErrorTree]
-- errors_ty_sgs_partial nm (gm, sgs, sgt) = 
--    let errs1 = check_wf_gm_sgs nm gm sgs sgt in
--    let npns = non_preserving_nodes gm sgs sgt in
--    let errs2 = if node_types_preserved gm sgs sgt then nile else cons_se $ "Instance nodes fail to preserve their type kinds: " ++ (showElems' npns) in
--    let errs3 = check_mults_respected gm (srcm sgs) (srcm sgt) "Source" in
--    let errs4 = check_mults_respected gm (tgtm sgs) (tgtm sgt) "Target" in
--    [errs1, errs2,errs3, errs4]


-- errors_ty_sgs_weak nm (gm, sgs, sgt) = 
--    let errs1 = errors_ty_sgs_partial nm (gm, sgs, sgt) in
--    let errs2 = checkInstSGMults gm sgs sgt in --if (esA sgt) `subseteq` ran_of (fE gm) then [] else ["Not all association edges of the type graph are being mapped."] in
--    errs1++errs2

-- errors_ty_sgs_strong nm (gm, sgs, sgt) = 
--    let errs1 = errors_ty_sgs_weak nm (gm, sgs, sgt) in
--    let errs2 = if ((nsTys sgt [Nnrml]) `subseteq` ran_of ((fV gm) `rcomp` (inhst sgt))) 
--                then nile 
--                else cons_se $ "Not all normal nodes are being mapped to in the type morphism: " ++ (show (diff (nsTys sgt [Nnrml]) (ran_of ((fV gm) `rcomp` (inhst sgt))))) in
--    errs1++[errs2]

-- errors_ty_sgs::(Eq a, Show a)=>String -> MK -> (GrM a, SGr a, SGr a) -> [ErrorTree]
-- errors_ty_sgs nm PartialM = errors_ty_sgs_partial nm
-- errors_ty_sgs nm FullM = errors_ty_sgs_strong nm
-- errors_ty_sgs nm PartialM = errors_ty_sgs_weak nm
-- errors_ty_sgs nm WeakM = errors_gm_sgs 

-- errors_ty_g_sg::(Eq a, Show a)=>String ->(GrM a, Gr a, SGr a) -> [ErrorTree]
-- errors_ty_g_sg nm (gm, g, sg) = 
--    let errs1 = check_wf_gm_g_sg nm gm g sg in
--    let abstract_nodes_msg ns = "Type nodes " ++ (show ns) ++ ", either abstract or enufEration, cannot have direct instances." in
--    let errs2 = if no_instances_of_abstract_tnodes gm sg then nile else cons_se (abstract_nodes_msg $ (nsTys sg [Nabst, Nenum])) in
--    let errs3 = checkInstMults gm g sg in
--    let errs4 = check_composites gm g sg in
--    [errs1, errs2] ++ errs3 ++ [errs4]


-- is_wf_ty_sgs PartialM = is_wf_ty_sgs_partial 
-- is_wf_ty_sgs FullM = is_wf_ty_sgs_strong 
-- is_wf_ty_sgs PartialM = is_wf_ty_sgs_weak 
-- is_wf_ty_sgs WeakM = is_wf_gm_sgs 

-- check_wf_ty_g_sg::(Eq a, Show a)=>String -> (GrM a, Gr a, SGr a) -> ErrorTree
-- check_wf_ty_g_sg nm (gm, g, sg) = 
--    check_wf_of (gm, g, sg) nm (is_wf_ty_g_sg) (errors_ty_g_sg nm)

-- check_wf_ty_sgs::(Eq a, Show a)=>String -> MK -> (GrM a, SGr a, SGr a) -> ErrorTree
-- check_wf_ty_sgs nm mk (gm, sgs, sgt) = 
--    check_wf_of (gm, sgs, sgt) nm (is_wf_ty_sgs mk) (errors_ty_sgs nm mk)

--check_wf_gm_sg nm PartialM (gm, sg, sgt) = check_wf_ty_sgs_partial nm gm sg sgt
--check_wf_gm_sg nm (TotalM Strong) (gm, sg, sgt) = check_wf_ty_sgs_strong nm gm sg sgt
--check_wf_gm_sg nm (TotalM Weak) (gm, sg, sgt) = check_wf_ty_sgs_weak nm gm sg sgt


