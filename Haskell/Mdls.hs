-------------------------
-- Project: PCs/Fragmenta
-- Module: 'Mdls'
-- Description: Fragmenta's models (Mdls)
-- Author: Nuno Amálio
---------------------------
{-# LANGUAGE MultiParamTypeClasses #-}
module Mdls (Mdl, cons_mdl, mgfg, mfd, mufs, from, reso_m)
where

import Gr_Cls
import Grs 
import SGrs 
import GFGrs 
import Frs 
import GrswT
import Relations
import ErrorAnalysis 
import Utils
import ShowUtils

data Mdl a = Mdl {
    gfg_ :: GFGr a,
    fd_ :: [(a, Fr a)]
} deriving (Eq, Show)

mgfg Mdl {gfg_ = gfg, fd_ = _} = gfg
mfd Mdl {gfg_ = _, fd_ = fd} = fd

cons_mdl gfg fd = Mdl {gfg_ = gfg, fd_ = fd} 

mufs::Eq a=>Mdl a->Fr a
mufs = union_fs . ran_of . mfd

from' n ((gf, f):mf) 
   | n `elem` (ns .fsg $ f) = gf
   | otherwise = from' n mf

from::Eq a=>Mdl a->a->a
from m n = from' n (mfd m)

is_ref_ok m p = (from m p, from m (appl (refs (mufs m)) p)) `elem` (refsOf . mgfg $ m)
complyGFG m = all (\p->is_ref_ok m p) (nsP . fsg . mufs $ m)

errs_complyGFG m = if complyGFG m then nile else cons_se ("The following proxies are not complying with the referencing of the model's GFG: " ++ (showElems' ps))
    where ps = filter (not . is_ref_ok m)(nsP . fsg . mufs $ m)

is_wf_mdl m = is_wf (Nothing) (mgfg m)  && fun_total' (mfd m) (ns . mgfg $ m) && disj_fs (ran_of . mfd $ m)
    && is_wf (Just Total) (mufs m) && complyGFG m

errs_wf_mdl id m = 
    let err1 = check_wf id (Nothing) (mgfg m) in
    let err2 = if fun_total' (mfd m) (ns . mgfg $ m) then nile else cons_et "Not all GFG fragment nodes have a corresponding fragment." [check_fun_total' (mfd m) (ns . mgfg $ m)] in
    let err3 = if disj_fs (ran_of . mfd $ m) then nile else cons_se "The fragments are not disjoint" in
    let err4 = check_wf id (Just Total) (mufs m) in
    let err5 = errs_complyGFG m in
    [err1, err2, err3, err4, err5]

check_wf_mdl nm m = check_wf_of m nm is_wf_mdl (errs_wf_mdl nm)

is_wf_f' _ = is_wf_mdl

check_wf_f' id _   = check_wf_mdl id  

instance G_WF_CHK Mdl where
   is_wf = is_wf_f'
   check_wf = check_wf_f'

reso_m::Eq a=>Mdl a->Fr a
reso_m = reso_f . mufs

-- Checks that a morphism between models is well-formed 
is_wf_mgm (mdls, m, mdlt) = is_wf_gm Nothing (mufs mdls, m, mufs mdlt)

-- Checks that a source model accompanied by a set of morphisms is model-morphism compliant to another model
complies_fgm (mdls, ms) mdlt = is_wf_mgm (mdls, union_gms ms, mdlt)

errors_wf_mgm nm (mdls, m, mdlt) = 
    let err = check_wf_gm nm (Just WeakM) (mufs mdls, m, mufs mdlt) in
    [err]

check_wf_mgm nm (mdls, m, mdlt) = check_wf_of (mdls, m, mdlt) nm is_wf_mgm (errors_wf_mgm nm)

-- Checks that one model refines another
mrefines (mdls, ms) mdlt = is_wf_gm (Just TotalM) (mufs mdls, union_gms ms, mufs mdlt) 

errors_mrefines nm (mdls, ms, mdlt) = 
    let err = check_wf_gm nm (Just TotalM) (mufs mdls, union_gms ms, mufs mdlt)  in
    [err]

check_mrefines nm (mdls, ms, mdlt) = check_wf_of (mdls, ms, mdlt) nm (appl mrefines) (errors_mrefines nm)
    where appl f = (\(fc, m, fa)->f (fc, m) fa)

is_wf_mgm' Nothing         = is_wf_mgm  
is_wf_mgm' (Just WeakM)    = is_wf_mgm 
is_wf_mgm' (Just PartialM) = (\(mdlc, m, mdla)-> (mdlc, [m]) `mrefines` mdla)
is_wf_mgm' (Just TotalM)   = (\(mdlc, m, mdla)-> (mdlc, [m]) `mrefines` mdla)

check_wf_mgm' id Nothing         = check_wf_mgm id
check_wf_mgm' id (Just WeakM)    = check_wf_mgm id
check_wf_mgm' id (Just PartialM) = (\(mdlc, m, mdla)-> check_mrefines id (mdlc, [m], mdla))
check_wf_mgm' id (Just TotalM)   = (\(mdlc, m, mdla)-> check_mrefines id (mdlc, [m], mdla))

instance GM_CHK Mdl Mdl where
   is_wf_gm = is_wf_mgm'
   check_wf_gm = check_wf_mgm'

ty_compliesm::Eq a=>GrwT a->Mdl a->Bool
ty_compliesm gwt mdl = is_wf_gm' (Just PartialM) (gwt, mufs mdl) 

check_ty_compliesm::(Eq a, Show a)=>String->GrwT a->Mdl a->ErrorTree
check_ty_compliesm id gwt mdl = check_wf_gm' id (Just PartialM) (gwt,  mufs mdl)

is_wf_ty Nothing (gwt, mdl)         = is_wf_gm' Nothing (gwt, mufs mdl)
is_wf_ty (Just WeakM) (gwt, mdl)    = is_wf_gm' (Just WeakM) (gwt,  mufs mdl) 
is_wf_ty (Just PartialM) (gwt, mdl) = gwt `ty_compliesm` mdl
is_wf_ty (Just TotalM) (gwt, mdl)   = gwt  `ty_compliesm` mdl

check_wf_ty id Nothing (gwt, mdl)         = check_wf_gm' id Nothing (gwt,  mufs mdl)
check_wf_ty id (Just WeakM) (gwt, mdl)    = check_wf_gm' id  (Just WeakM) (gwt,  mufs mdl)
check_wf_ty id (Just PartialM) (gwt, mdl) = check_ty_compliesm id gwt mdl
check_wf_ty id (Just TotalM) (gwt, mdl)   = check_ty_compliesm id gwt mdl

instance GM_CHK' GrwT Mdl where
   is_wf_gm' = is_wf_ty
   check_wf_gm' = check_wf_ty
