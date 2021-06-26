-------------------------
-- Project: PCs/Fragmenta
-- Module: 'GrswT'
-- Description: Fragmenta's graphs with typing (GrswT)
-- Author: Nuno Amálio
---------------------------
module GrswT (cons_gwt, gOf, ty, is_wf_gwt, GrwT, empty_gwt, union_gwt) where

import Sets
import Relations
import Grs
import Gr_Cls
import ErrorAnalysis

data GrwT a = GrwT {
    g_ :: Gr a
    , t_ :: GrM a
    } deriving(Eq, Show) 

cons_gwt g t = GrwT  {g_ = g, t_ = t}

gOf GrwT  {g_ = g, t_ = _} = g
ty GrwT  {g_ = _, t_ = t} = t

empty_gwt = cons_gwt empty_g empty_gm 

instance GR GrwT where
   ns = ns . gOf
   es = es . gOf
   src = src . gOf
   tgt = tgt . gOf
   empty = empty_gwt


instance GRM GrwT where
    fV = fV . ty
    fE = fE . ty

-- well-formedness
is_wf_gwt gwt = (is_wf Nothing $ gOf gwt) && (dom_of . fV $ gwt) `seteq` ns gwt && (dom_of . fE $ gwt) `seteq` es gwt

errs_wf_gwt id gwt = 
    let err1 = check_wf id Nothing $ gOf gwt in
    let err2 = if (dom_of . fV $ gwt) `seteq` ns gwt then nile else check_seteq (dom_of . fV $ gwt) (ns gwt) in
    let err3 = if (dom_of . fE $ gwt) `seteq` es gwt then nile else check_seteq (dom_of . fE $ gwt) (es gwt) in
    add_to_err err1 [err2, err3]

check_wf_gwt id gwt = (check_wf id Nothing $ gOf gwt)

is_wf' _ = is_wf_gwt
check_wf' id _ = check_wf_gwt id

union_gwt gwt1 gwt2 = cons_gwt (gwt1 `union_g` gwt2) (gwt1 `union_gm` gwt2)

instance G_WF_CHK GrwT where
   is_wf = is_wf'
   check_wf = check_wf'