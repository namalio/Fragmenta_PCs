
module PCs(PC, MMInfo, isNodeOfTys, getAtoms, getPCStart, load_mm_info, pc_cmm, pc_amm, pc_rm, pc_sg_cmm, startCompound, getPCDef, 
  srcOf, tgtOf, afterCRel, paramsOf, nmOfNamed, guardOf, pc_ns_of_nty, nmOfRef, nmOfRefF, paramsOfRef, anyExpOfAt, renamingsOf,
  opValOfOp, nextNode, nextNodes, successorsOf, compoundStart, withinRel, importsOf, nextAfterC, nextNodesAfter, nextNodeAfter, 
  branchesOfOp, innerKs, innerRefKs, commonInnerKs, hidden_RC, inner_Ref, openAC, guardOfOp) 
where

import Gr_Cls
import Grs
import GrswT
import Mdls 
import LoadCheckDraw
import Relations
import Sets
import SGrs
import Frs
import Grs
import The_Nil
import MyMaybe
import ParseUtils
import SimpleFuns
import PCs_MM_Names
import Control.Monad(when)

type PC a = GrwT a

data MMInfo a = MMInfo {cmm_ :: Mdl a, amm_ :: Mdl a, rm_:: GrM a, sg_cmm_ :: SGr a}
  deriving (Show)

cons_mm_info cmm amm rm sgcmm = MMInfo {cmm_ = cmm, amm_ = amm, rm_ = rm, sg_cmm_ = sgcmm}

pc_cmm MMInfo {cmm_ = cmm, amm_ = _, rm_ = _, sg_cmm_ = _} = cmm
pc_amm MMInfo {cmm_ = _, amm_ = amm, rm_ = _, sg_cmm_ = _} = amm
pc_rm MMInfo {cmm_ = _, amm_ = _, rm_ = rm, sg_cmm_ = _} = rm
pc_sg_cmm MMInfo {cmm_ = _, amm_ = _, rm_ = _ , sg_cmm_ = sgcmm} = sgcmm

load_pcs_amm def_path = do
  mdl<-load_mdl_def def_path "PCs_AMM"
  return mdl

load_pcs_cmm def_path = do
  mdl <- load_mdl_def def_path "PCs_MM"
  return mdl

load_pcs_rm def_path = do
    rm<-load_rm_cmdl_def def_path "PCs_MM"
    return rm

load_mm_info def_path = do
  amm<-load_pcs_amm def_path
  cmm<-load_pcs_cmm def_path
  rm<-load_pcs_rm def_path
  return (cons_mm_info cmm amm rm (fsg . reso_m $ cmm))

--isNodeOfTy n ty sg_mm pc = 
--    let t = str_of_ostr $ tyOfNM n pc in
--    t `elem` img (inv $ inhst sg_mm) [show_cmm_n sty]

isNodeOfTys n tys sg_mm pc = 
    let t = str_of_ostr $ tyOfNM n pc in
    t `elem`  (img (inv $ inhst sg_mm) [show_cmm_n sty | sty<-tys])

pc_ns_of_nty::SGr String->GrwT String -> PCs_CMM_Ns -> [String]
pc_ns_of_nty sg_mm pc nt = ns_of_ntys pc sg_mm [show_cmm_n nt]

getAtoms::SGr String->GrwT String-> [String]
getAtoms sg_mm pc = foldr (\a as->(extAtoms (nmOfNamed pc a) (anyExpOfAt pc a))++as) [] (pc_ns_of_nty sg_mm pc CMM_Atom)
    where extAtoms nm Nothing = [nm]
          extAtoms _ (Just (_, ats)) = 
            if head ats == '{' && last ats == '}' then words' (== ',') (drop 1 (take ((length ats) - 1) ats)) else []

-- Gets starting node of  PC 
getPCStart sg_mm pc = the $ pc_ns_of_nty sg_mm pc CMM_StartN

-- Get's PCs starting compound
startCompound mmi pc = the $ (nextNodes mmi pc $ getPCStart (pc_sg_cmm mmi) pc) `intersec`  (pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_Compound)


compoundStart mmi pc n = 
   let defC = (successorsOf mmi pc n) `intersec` (img (inv $ fV pc) [show_cmm_n CMM_DefinesC]) in
   the $ successorsOf mmi pc (the $ defC)

-- Obtains the two level morphism from PCs to the abstract layer 
twolm mmi pc =  (pc_rm mmi) `ogm` pc  

-- Successors of a connector node
successorsOfC mmi pc nc = 
    img (tgt pc) $ img (inv . fE $ twolm mmi pc) [show_amm_e AMM_EConnector_tgt] `intersec` dom_of (rres (src pc) [nc])

-- Successors of any node
successorsOf mmi pc n =
   let succsOfN = img (src pc) $ img (inv . fE $ twolm mmi pc) [show_amm_e AMM_EConnector_src]  `intersec` dom_of (rres (tgt pc) [n]) in
   if (isNodeOfTys n [CMM_Node] (pc_sg_cmm mmi) pc) then succsOfN else if (isNodeOfTys n [CMM_Connector] (pc_sg_cmm mmi) pc) then successorsOfC mmi pc n else []

-- Gets the predecessors of a connector
predecessorsOfC mmi pc nc = 
    img (tgt pc) $ img (inv . fE $ twolm mmi pc) [show_amm_e AMM_EConnector_src] `intersec` dom_of (rres (src pc) [nc])

nextNode mmi pc n = 
  let n' = toMaybeFrLs $ successorsOf mmi pc n in
  let next' = n' /= Nothing && (not $ isNodeOfTys (the n') [CMM_Node] (pc_sg_cmm mmi) pc) in
  if not next' then n' else toMaybeFrLs $ successorsOf mmi pc (the n')

nextNodes mmi pc n = 
  let ns' = successorsOf mmi pc n in
  let next' = not $ null ns' && (not $ isNodeOfTys (head ns') [CMM_Node] (pc_sg_cmm mmi) pc) in
  if not next' then ns' else (foldr (\x xs-> (successorsOf mmi pc x) ++ xs) [] ns')


nextAfterC mmi pc n = (successorsOf mmi pc n) `intersec` (pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_AfterC)

branchesOfOp mmi pc n = 
    let ns = successorsOf mmi pc n in
    (filter (\n->the (tyOfNM n pc) == show_cmm_n CMM_BranchC) ns)
    ++ (filter (\n->the (tyOfNM n pc) == show_cmm_n CMM_BMainIfC) ns)
    ++ (filter (\n->the (tyOfNM n pc) == show_cmm_n CMM_BElseC) ns)
    ++ (filter (\n->the (tyOfNM n pc) == show_cmm_n CMM_BJumpC) ns)

nextNodesAfter mmi pc n = let after = nextAfterC mmi pc n in 
    if isNil after then [] else successorsOf mmi pc (the after)

guardOfOp mmi pc n = 
    let ns = successorsOf mmi pc n in
    let n_if_b = filter (\n->the (tyOfNM n pc) == show_cmm_n CMM_BMainIfC) ns in
    if isNil n_if_b then Nothing else guardOf pc (the n_if_b)

nextNodeAfter mmi pc n = toMaybeFrLs $ nextNodesAfter mmi pc n

-- Gets PC's definitional node 
getPCDef pc = appl (inv . fV $ pc) (show_cmm_n CMM_PCDef)

srcOf mmi pc c = the $ predecessorsOfC mmi pc c
tgtOf mmi pc c = the $ successorsOfC mmi pc c

-- Relation induced by 'AfterC' connector
afterCRel mmi pc = 
  let ns_e = pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_AfterC in
  foldr (\ne r-> (srcOf mmi pc ne, tgtOf mmi pc ne):r) [] ns_e

pparams ps = foldr (\p ps'->(snd $ splitAtStr "_param_" p):ps') [] ps
pair_of_rename ren = 
  splitAtStr "_" (snd $ splitAtStr "_renaming_" ren)

prenamings rs = foldr (\r ps'->(pair_of_rename r):ps') [] rs

paramsOf pc n = 
   let ps = img (tgt pc) $ (img (inv $ src pc) [n]) `intersec`  (es_of_ety pc $ show_cmm_e CMM_EHasParams) in
   pparams ps

anyExpOfAt pc n = 
   let ps = img (tgt pc) $ (img (inv $ src pc) [n ++ "_anyExp"]) `intersec`  (es_of_ety pc $ show_cmm_e CMM_EAnyExp_atv) in
   let ps'= img (tgt pc) $ (img (inv $ src pc) [n ++ "_anyExp"]) `intersec`  (es_of_ety pc $ show_cmm_e CMM_EAnyExp_atSet) in
   if isNil ps' then Nothing else Just (head $ pparams ps, head $ pparams ps')

renamingsOf pc n = 
   let rs = img (tgt pc) $ (img (inv $ src pc) [n]) `intersec`  (es_of_ety pc $ show_cmm_e CMM_ERenamings) in
   prenamings rs   

inner_Ref pc n = 
   let is = img (tgt pc) $ (img (inv $ src pc) [n]) `intersec`  (es_of_ety pc $ show_cmm_e CMM_EReference_inner) in
   if isSomething is then (the is) == "YesV" else False

hidden_RC pc c = 
   let hs = img (tgt pc) $ (img (inv $ src pc) [c]) `intersec`  (es_of_ety pc $ show_cmm_e CMM_EReferenceC_hidden) in
   if isSomething hs then (the hs) == "YesV" else False

openAC pc c = 
   let os = img (tgt pc) $ (img (inv $ src pc) [c]) `intersec`  (es_of_ety pc $ show_cmm_e CMM_EAfterC_copen) in
   if isSomething os then (the os) == "YesV" else False

nmOfNamed pc n = 
  allButLast $ appl (tgt pc) (the $ img (inv . src $ pc) [n] `intersec`  (es_of_ety pc $ show_cmm_e CMM_ENamedNode_name))

guardOf pc n =
   let p = img (tgt pc) $ (img (inv . src $ pc) [n])  `intersec`  (es_of_ety pc $ show_cmm_e CMM_EHasGuard) in
   if null p then Nothing else Just (snd $ splitAtStr "_guard_" (the p))

nmOfRef pc n = 
  let rn = img (tgt pc) $ img (inv . src $ pc) [n] `intersec`  (es_of_ety pc $ show_cmm_e CMM_EReference_name) in
  if null rn then "" else allButLast . the $ rn

nmOfRefF mmi pc n = 
  let rn = nmOfRef pc n in
  let rc = the $ (successorsOf mmi pc n) `intersec` (pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_ReferenceC) in
  if null rn then the $ successorsOf mmi pc rc else rn 

paramsOfRef mmi pc n =
  let rn = nmOfRef pc n in
  let rc = the $ (successorsOf mmi pc n) `intersec` (pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_ReferenceC) in
  if null rn then paramsOf pc rc else paramsOf pc n

opValId sg_mm pc n = 
   if isNodeOfTys n [CMM_OperatorVal] sg_mm pc then appl (fV pc) n else ""

opValOfOp sg_mm pc n =
   let nOpVal = appl (tgt pc) (the $ img (inv $ src pc) [n] `intersec` (es_of_ety pc $ show_cmm_e CMM_EOperator_op)) in
   let op = opValId sg_mm pc nOpVal in
   if isNodeOfTys n [CMM_Operator] sg_mm pc then op else ""

combinePAsC (x, y) (x', y') = (x++x', y++y') 

withinRelWiths mmi pc n ns pcs = 
  let combine (x, y, z) (x', y', z') = (x++x', y `union` y', z `union` z') in
  let to_pair (x, y, _) = (x, y) in
  let as_triple (x, y) z = (x, y, z) in
  let upd_ks k = if isNodeOfTys k [CMM_Compound] (pc_sg_cmm mmi) pc then [k] else [] in
  to_pair $ foldl (\ks k->if k `elem` (thd_T ks) then ks else (as_triple (withinRelWithAux mmi pc n k (thd_T ks)) (upd_ks k)) `combine` ks) ([], [], pcs) ns

withinRelWithAux mmi pc n n' pcs
   | isNodeOfTys n' [CMM_Atom] (pc_sg_cmm mmi) pc = ([(n, n')], []) `combinePAsC` withinRelWithOpt (nextNode mmi pc n')
   -- Here it depends on whether it is definitional or not
   | isNodeOfTys n' [CMM_Compound] (pc_sg_cmm mmi) pc = if n' `elem` (n:pcs) then nilR else ((n, n'):withinRelWith mmi pc n' (n:pcs), []) 
   | isNodeOfTys n' [CMM_Reference] (pc_sg_cmm mmi) pc = ([], []) 
   | isNodeOfTys n' [CMM_Operator] (pc_sg_cmm mmi) pc = let ns = (nextNodes mmi pc n') in withinRelWiths mmi pc n ns pcs
   | isNodeOfTys n' [CMM_Stop,CMM_Skip] (pc_sg_cmm mmi) pc = ([], []) 
   where withinRelWithOpt Nothing = nilR
         withinRelWithOpt (Just k) = if k `elem` pcs then nilR else (withinRelWithAux mmi pc n k pcs)
         nilR = ([], [])

withinRelForNs _ _ [] _ = []
withinRelForNs mmi pc (n:ns) pcs = 
  let (r, rcs) = withinRelWith' mmi pc n pcs in
  r `union` withinRelForNs mmi pc (rcs `union` ns) ((dom_of r) `union` pcs)

withinRelWith' mmi pc n pcs =
   let next_ns = nextNodes mmi pc n in
   withinRelWiths mmi pc n next_ns pcs

withinRelWith mmi pc n pcs =
   let (r, rcs) = withinRelWith' mmi pc n pcs in
   let r' = withinRelForNs mmi pc rcs ((dom_of r) `union` pcs) in
   r `union` r'

withinRel mmi pc = withinRelWith mmi pc (startCompound mmi pc) []

innerKsOf mmi pc [] _ = []
innerKsOf mmi pc (n:ns) vns
    | isNodeOfTys n [CMM_Atom] (pc_sg_cmm mmi) pc = innerKsOf mmi pc ((nextNodesAfter mmi pc n)++ns) vns
    | isNodeOfTys n [CMM_Reference] (pc_sg_cmm mmi) pc && (not $ inner_Ref pc n) = innerKsOf mmi pc ((nextNodesAfter mmi pc n)++ns) vns
    | isNodeOfTys n [CMM_Reference] (pc_sg_cmm mmi) pc && (inner_Ref pc n) = 
        innerKsOf mmi pc ([nmOfRefF mmi pc n]++(nextNodesAfter mmi pc n)++ns) vns
    | isNodeOfTys n [CMM_Compound] (pc_sg_cmm mmi) pc = let nas = nextNodesAfter mmi pc n in
        if n `elem` vns then innerKsOf mmi pc ns vns else n:(innerKsOf mmi pc ((compoundStart mmi pc n):(nas++ns)) $ n:vns)
    | isNodeOfTys n [CMM_Operator] (pc_sg_cmm mmi) pc = innerKsOf mmi pc ((nextNodes mmi pc n)++ns) vns
    | isNodeOfTys n [CMM_Stop,CMM_Skip] (pc_sg_cmm mmi) pc = innerKsOf mmi pc ns vns 
    -- | otherwise = (the (tyOfNM n pc)):innerKsOf mmi pc ns

innerKs mmi pc n = innerKsOf mmi pc [compoundStart mmi pc n] [n]

innerRefKsOf _ _ [] _ = []
innerRefKsOf mmi pc (n:ns) vns
  | isNodeOfTys n [CMM_Atom,CMM_Compound] (pc_sg_cmm mmi) pc = 
      if n `elem` vns then innerRefKsOf mmi pc ns vns else  innerRefKsOf mmi pc ((nextNodesAfter mmi pc n)++ns) vns
  | isNodeOfTys n [CMM_Operator] (pc_sg_cmm mmi) pc = 
      innerRefKsOf mmi pc ((nextNodes mmi pc n)++ns) vns
  | isNodeOfTys n [CMM_Stop,CMM_Skip] (pc_sg_cmm mmi) pc = innerRefKsOf mmi pc ns vns 
  | isNodeOfTys n [CMM_Reference] (pc_sg_cmm mmi) pc && (not $ inner_Ref pc n) = innerRefKsOf mmi pc ((nextNodesAfter mmi pc n)++ns) vns 
  | isNodeOfTys n [CMM_Reference] (pc_sg_cmm mmi) pc && (inner_Ref pc n) = let rn = nmOfRefF mmi pc n in 
      if rn `elem` vns then innerRefKsOf mmi pc ns vns else rn:(innerRefKsOf mmi pc ((nextNodesAfter mmi pc n)++ns)) (rn:vns)

innerRefKs mmi pc n = innerRefKsOf mmi pc [compoundStart mmi pc n] [n]
--commonInnerKsOf mmi pc [] _ = []
--commonInnerKsOf mmi pc (n:ns) vns 
--    | isNodeOfTys n [CMM_Atom, CMM_Reference] (pc_sg_cmm mmi) pc = commonInnerKs mmi pc ((nextNodesAfter mmi pc n)++ns) vns 
--    | isNodeOfTys n [CMM_Compound] (pc_sg_cmm mmi) pc = let nas = nextNodesAfter mmi pc n in
--        if n `elem` vns then commonInnerKsOf mmi pc ns vns else commonInnerKsOf mmi pc ((compoundStart mmi pc n):(nas++ns)) (n:vns)
--    | isNodeOfTys n [CMM_Operator] (pc_sg_cmm mmi) pc = let nns = nextNodes mmi pc n in
--      (gintersec (foldr (\n cns->(innerKsOf mmi pc [n] vns):cns) [] nns)) `intersec` (commonInnerKsOf mmi pc ns (nns++vns))
--    | isNodeOfTys n [CMM_Stop] (pc_sg_cmm mmi) pc = commonInnerKsOf mmi pc ns vns 

divergentInnerKs0 mmi pc [] _ = []
divergentInnerKs0 mmi pc (n:ns) vns
    | isNodeOfTys n [CMM_Atom] (pc_sg_cmm mmi) pc = let nns = nextNodesAfter mmi pc n in
        divergentInnerKs0 mmi pc (nns++ns) vns 
    | (isNodeOfTys n [CMM_Reference] (pc_sg_cmm mmi) pc) && (not $ inner_Ref pc n) = 
        let nns = nextNodesAfter mmi pc n in divergentInnerKs0 mmi pc (nns++ns) vns 
    | (isNodeOfTys n [CMM_Reference] (pc_sg_cmm mmi) pc) && (inner_Ref pc n) =  
        let nns = nextNodesAfter mmi pc n in let rn = nmOfRefF mmi pc n in
        divergentInnerKs0 mmi pc (rn:(nns++ns)) vns
    | isNodeOfTys n [CMM_Compound] (pc_sg_cmm mmi) pc = let nns = nextNodesAfter mmi pc n in
        if n `elem` vns then divergentInnerKs0 mmi pc ns vns else divergentInnerKs0 mmi pc ((compoundStart mmi pc n):(nns++ns)) (n:vns)
    | isNodeOfTys n [CMM_Operator] (pc_sg_cmm mmi) pc = let nns = nextNodes mmi pc n in
        (foldr (\n' dss->(innerKsOf mmi pc [n'] vns):dss) [] nns) ++ (divergentInnerKs0 mmi pc ns vns)
    | isNodeOfTys n [CMM_Stop,CMM_Skip] (pc_sg_cmm mmi) pc = divergentInnerKs0 mmi pc ns vns 

divergentInnerKs mmi pc n = divergentInnerKs0 mmi pc [compoundStart mmi pc n] [n]

commonInnerKs mmi pc n = gintersec (divergentInnerKs mmi pc n)

--getImports :: GrM a -> [String]
importsOf sg_mm pc = pc_ns_of_nty sg_mm  pc CMM_Import
