------------------
-- Project: PCs/Fragmenta
-- Module: 'CSP_AST'
-- Description: Module that represents PCs as PCTs, a recursive datatype representation of abstract syntax
-- Author: Nuno Amálio
-----------------
module PCTrees(PCT(..), TOp(..), CT(..), PCTD(..), withinRel, consPCTD, atomsOfPCTD, 
  show_pctd, isOperator, isAtom, isAtomAny, isAtomic, isSole) where

import PCs
import Gr_Cls
import Grs
import GrswT
import Sets
import Relations
import The_Nil
import MyMaybe
import PCs_MM_Names
import ShowUtils
import ParseUtils

type Id = String 
type PCExp = String 
type Guard = String
type Param = String 

data TOp = OpExtChoice | OpIntChoice | OpSeq Bool | OpParallel [Param] | OpInterleave | OpThrow [Param] | OpIf Guard deriving(Eq, Show)  
data PCT = Atom Id (Maybe Guard) (Maybe (Id, PCExp)) | OpB TOp PCT PCT | Kappa CT | Ref Id (Maybe Guard) [Param] [(Id, Id)]
   | NilT | StopT | SkipT deriving(Eq, Show)
data CT = CT Id [Param] [CT] PCT deriving(Eq, Show)

data PCTD = PCTD Id [CT] deriving(Eq, Show)

the_ct (Kappa ct) = ct 

opseqC = OpSeq False
opseqO = OpSeq True

rearrangeT (OpB opseqC (Kappa (CT k ps cts t1)) t2) = CT k ps [] (OpB opseqC (Kappa (CT (k++"0") [] cts t1)) t2)
rearrangeT (Kappa ct) = ct

show_top OpExtChoice = "◻︎"
show_top OpIntChoice = "⊓"
show_top (OpSeq o) = (if o then "O" else "") ++  "⇥"
show_top (OpParallel ps) = "∥" ++ (show ps)
show_top (OpInterleave) = "⦀"
show_top (OpThrow ps) = "𝛩" ++ (show ps)
show_top (OpIf g) = "𝜄" ++ (show g)

show_cts cts = if null cts then "" else ":" ++ foldr (\ct scts->(show_pct $ Kappa ct) ++ "∙" ++  scts) "" cts
show_params ps = if null ps then "" else "(" ++ (showStrs ps ",") ++ ")"
show_renamings rs = if null rs then "" else "⟦" ++ (showStrs (foldr (\(fr, to) rps->(fr ++ "/" ++ to):rps) [] rs) ",") ++ "⟧"
show_guard og = if isNil og then "" else " [" ++ (str_of_ostr og) ++ "]"
show_atparams op = if isNil op then "" else " (" ++ (fst . the $ op) ++ "," ++ (snd . the $ op) ++ ")"
show_pct (Atom id og op) = "𝛼" ++ id ++ (show_atparams op) ++ (show_guard og)
show_pct (Kappa (CT id ps cts pct)) = "𝜅 " ++ id ++ (show_params ps) ++ (show_cts cts)++ " @ " ++ (show_pct pct)
show_pct (OpB op pct1 pct2) = "[𝛾 " ++ show_top op ++ "]" ++ (show_pct pct1) ++ " [" ++ (show_pct pct2) ++ "]"
show_pct (Ref id og ps rs) = "𝜌" ++ id ++ (show_params ps) ++ (show_renamings rs) ++ (show_guard og)
show_pct (NilT) = "𝜑"
show_pct (StopT) = "𝛉"
show_pct (SkipT) = "𝜉"

show_pctd (PCTD id cts) = "PC " ++ id ++ (show_cts cts)

andThenO (t, rs, gcs) (t', rs', gcs') = (OpB opseqO t t', rs `union` rs', gcs `union` gcs')
andThenC (t, rs, gcs) (t', rs', gcs') = (OpB opseqC t t', rs `union` rs', gcs `union` gcs')

undThen (t, rs, gcs) (t', rs', gcs') = if t' == NilT then (t, rs, gcs) else (t, rs, gcs) `andThenC` (t', rs', gcs')

withOp (t, rs, gcs) (op, (t', rs', gcs')) = if t' == NilT then (t, rs, gcs) else (OpB op t t', rs `union` rs', gcs `union` gcs')

toTOp CMM_OpChoice _ _= OpExtChoice
toTOp CMM_OpIntChoice _ _= OpIntChoice
toTOp CMM_OpParallel _ ps = OpParallel ps
--toTreeOp CMM_OpWaitFor _ _= OpWaitFor
toTOp CMM_OpInterleave _ _ = OpInterleave
--toTreeOp CMM_OpSyncInterrupt _ ps = OpSyncInterrupt ps
toTOp CMM_OpThrow _ ps = OpThrow ps
toTOp CMM_OpIf og _ = OpIf (the og)

fillAnyExp (Just ("", ats)) = (Just ("e", ats))
fillAnyExp p = p

atLeaf::PC String->Id->(PCT, [Id], [Id])
atLeaf pc n = (Atom (nmOfNamed pc n) (guardOf pc n) (fillAnyExp $ anyExpOfAt pc n), [], [])

openACOf mmi pc n = 
  let ac = nextAfterC mmi pc n in
  isSomething ac && openAC pc (the ac)

atomBranch::MMInfo String->PC String->Id->[Id]->(PCT, [Id], [Id])
atomBranch mmi pc n gcs = 
    let t1 = atLeaf pc n in
    let t2 = consOptBranch mmi pc (nextNodeAfter mmi pc n) gcs in
    if openACOf mmi pc n then t1 `andThenO` t2 else t1 `andThenC` t2
    
compound::MMInfo String->PC String->Id->[Id]->(PCT, [Id], [Id])
compound mmi pc n gcs = 
  let (cts, rs1, gcs1) = seqCTs mmi pc ((innerRefKs mmi pc n) `union` (commonInnerKs mmi pc n)) (n:gcs) in
  let (t, rs2, gcs2) = consBranch mmi pc (compoundStart mmi pc n) (gunion [[n], gcs, gcs1]) in
  (Kappa  $ CT n (paramsOf pc n) cts t, rs1 `union` rs2, gunion [[n],gcs1, gcs2])

compoundAB::MMInfo String->PC String->Id->[Id]->(PCT, [Id], [Id])
compoundAB mmi pc n gcs = 
  (compound mmi pc n gcs) `undThen` (consOptBranch mmi pc (nextNodeAfter mmi pc n) (n:gcs))

--   let on = nextNodeAfter mmi pc n in
--   let (t1, rs) = consCompound mmi pc n gcs in
--   let combine (t2, rs', z) = (OpB OpSeq t1 t2, rs++rs', [n, the on] `union` z) in
--   if isSomething on then combine $ consBranch mmi pc (the on) Nothing (n:gcs) else (t1, rs, [n])

--consCompoundOrAtom::MMInfo String->PC String->Id->Guard->[Id]->(PCT, [Id], [Id])
--consCompoundOrAtom mmi pc n g gcs 
--    | isNodeOfTy n CMM_Atom (pc_sg_cmm mmi) pc = atomLeaf pc n g
--    | isNodeOfTy n CMM_Compound (pc_sg_cmm mmi) pc = consCompound mmi pc n gcs

--consCompoundOrAtomBranch::MMInfo String->PC String->Id->Guard->[Id]->(PCT, [Id], [Id])
--consCompoundOrAtomBranch mmi pc n g gcs = 
--    (consCompoundOrAtom mmi pc n g gcs) `andThen` (consOptBranch mmi pc (nextNodeAfter mmi pc n) Nothing gcs)

consRefOrcompound::MMInfo String->PC String->Id->[Id]->(PCT, [Id], [Id])
consRefOrcompound mmi pc n gcs 
    | n `elem` gcs = (Ref n Nothing [] [], [], [])
    | otherwise = compoundAB mmi pc n gcs

refLeaf mmi pc n gcs = 
  let rn = nmOfRefF mmi pc n in 
  let rs = if rn `elem` gcs || not (isNodeOfTys rn [CMM_Compound] (pc_sg_cmm mmi) pc) then [] else [rn] in
  (Ref rn (guardOf pc n) (paramsOfRef mmi pc n) (renamingsOf pc n), rs , [])

refBranch mmi pc n gcs =
    --let ir = inner_Ref pc n in
    --let rn = nmOfRefF mmi pc n in -- Work here
    --if ir && (not $ rn `elem` gcs) then compoundAB mmi pc rn gcs else 
    (refLeaf mmi pc n gcs) `undThen` (consOptBranch mmi pc (nextNodeAfter mmi pc n) gcs)
    --here combine rs (t, rs', gcs) = (t, rs `union` rs', gcs)
   --if isNil after then (t, rs, []) else combine rs $ generateOpTreeFor mmi pc t [the after] rs gcs

--opBGuard::MMInfo String->PC String->Id->Maybe Guard
--opBGuard mmi pc n = 
--  let cs = (successorsOf mmi pc n) `intersec` (img (inv $ fV pc) [show_cmm_n CMM_BranchC]) in
--  if isNil cs then Nothing else predMaybe (not . null) $ guardOf pc (the cs)

opTree::MMInfo String->PC String->Id->[Id]->(PCT, [Id], [Id])
opTree mmi pc n gcs = 
   opBranches mmi pc (toTOp (read_cmm $ opValOfOp (pc_sg_cmm mmi) pc n) (guardOfOp mmi pc n) (paramsOf pc n)) (branchesOfOp mmi pc n) gcs
-- let (tcs, rs, cs) = consOpBranches mmi pc (read_cmm $ opValOfOp (pc_sg_cmm mmi) pc n) (bs++bs'++bs'') gcs
--generatePCTsForBranches mmi pc (bs++bs'++bs'') gcs in
--(consOpTreeLs tcs (toTreeOp (read_cmm $ opValOfOp (pc_sg_cmm mmi) pc n) g (paramsOf pc n)), rs, cs)

consOptBranch::MMInfo String->PC String->Maybe Id->[Id]->(PCT, [Id], [Id])
consOptBranch mmi pc on gcs = if isNil on then (NilT, [], []) else consBranch mmi pc (the on) gcs

consBranch::MMInfo String->PC String->Id->[Id]->(PCT, [Id], [Id])
consBranch mmi pc n gcs 
    | isNodeOfTys n [CMM_Atom] (pc_sg_cmm mmi) pc = atomBranch mmi pc n gcs
    | isNodeOfTys n [CMM_Compound] (pc_sg_cmm mmi) pc = consRefOrcompound mmi pc n gcs
    | isNodeOfTys n [CMM_Reference] (pc_sg_cmm mmi) pc = refBranch mmi pc n gcs
    | isNodeOfTys n [CMM_Operator] (pc_sg_cmm mmi) pc = opTree mmi pc n gcs 
    | isNodeOfTys n [CMM_Stop] (pc_sg_cmm mmi) pc = (StopT, [], [])
    | isNodeOfTys n [CMM_Skip] (pc_sg_cmm mmi) pc = (SkipT, [], [])


opBranches::MMInfo String->PC String->TOp->[Id]->[Id]->(PCT, [Id], [Id])
opBranches _ _ _ [] _ = (NilT, [], [])
opBranches mmi pc op (b:bs) cs = 
   let n = the $ nextNode mmi pc b in
   let (tc, rs, cs') = consBranch mmi pc n cs in
   --let combine (tc, rs, cs) (tcs, rs', cs') = (tc:tcs, rs++rs', cs++cs') in
   (tc, rs, cs') `withOp`  (op, opBranches mmi pc op bs $ cs' `union` cs)

--followedBy t ts = if t' == NilT then t else TSeq t t'
seqCTs::MMInfo String->PC String->[Id]->[Id]->([CT], [Id], [Id])
seqCTs _ _ [] gcs = ([], [], gcs)
seqCTs mmi pc (rn:rns) gcs = 
    let (t, rns1, gcs1)  = compoundAB mmi pc rn gcs in
    let (cts, rns2, gcs2) = seqCTs mmi pc ((rns `union` rns1) `diff` gcs1) (gcs `union` gcs1) in 
    ((rearrangeT t):cts, gunion [rns, rns1, rns2], gunion [gcs, gcs1, gcs2])
--where modify_t (OpB opseqC (Kappa (CT k ps cts t1)) t2) = CT k ps [] (OpB opseqC (Kappa (CT (k++"0") [] cts t1)) t2)

consPCTD::MMInfo String->PC String->PCTD
consPCTD mmi pc = 
    let (cts, _, _) = seqCTs mmi pc [startCompound mmi pc] [] in 
    PCTD (getPCDef pc) cts

revname nm k p = if nm == k then p else nm
rename (Atom nm og oats) k p = Atom (revname nm k p) og oats
rename (OpB op t1 t2) k p = OpB op (rename t1 k p) (rename t2 k p)
rename (Kappa (CT nm ps cts t)) k p = 
  Kappa (CT (revname nm k p) ps (map the_ct $ foldr (\t' ts->(rename t' k p):ts) [] (map Kappa cts)) (rename t k p))
rename (Ref nm g ps rs) k p = Ref (revname nm k p) g ps rs 
rename NilT _ _ = NilT
rename StopT _ _ = StopT
rename SkipT _ _ = SkipT

within (Atom nm _ _) = [nm]
within (OpB _ t1 t2) = (within t1)++(within t2)
within (Kappa (CT nm _ cts t)) = (foldr (\ct wcts->(within $ Kappa ct)++wcts) [] cts)++[nm]++(within t)
within (Ref _ _ _ _) = []
within NilT = []
within StopT = []
within SkipT = []

relWithinRel_cts cts = (foldr (\ct rct->(relWithin $ Kappa ct)++rct) [] cts)
relWithinRel nc (Atom na _ _) = [(nc, na)]
relWithinRel nc (OpB _ t1 t2) =  (relWithinRel nc t1)++(relWithinRel nc t2)
relWithinRel nc (Kappa (CT nm _ cts t)) = [(nc, nm)] ++ (relWithinRel_cts cts) ++ (relWithin t)
relWithinRel _ (Ref _ _ _ _) = []
relWithinRel _ (NilT) = []
relWithinRel _ (StopT) = []
relWithinRel _ (SkipT) = []

relWithin (Kappa (CT nm _ cts t)) = (relWithinRel_cts cts) ++ relWithinRel nm t
--relWithin (TSeq t1 t2) = relWithin t1 ++ relWithin t2
relWithin _ = []

atomsOfPCTD cts = foldr (\ct ats->(atomsOfPCT (Kappa ct)) `union` ats) [] cts

atomsOfPCTs t1 t2 = (atomsOfPCT t1) `union` atomsOfPCT t2
atomsOfPCT (Atom na _ Nothing) = [na] 
atomsOfPCT (Atom _ _ (Just (_, ats))) = 
  if head ats == '{' && last ats == '}' then words' (== ',') (drop 1 (take ((length ats) - 1) ats)) else [] 
atomsOfPCT (OpB (OpThrow as) t1 t2) = as `union` atomsOfPCTs t1 t2
atomsOfPCT (OpB _ t1 t2) = atomsOfPCTs t1 t2
atomsOfPCT (Kappa (CT _ _ cts t)) = (foldr (\ct rct->(atomsOfPCT $ Kappa ct)`union` rct) [] cts) `union` (atomsOfPCT t)
atomsOfPCT (Ref _ _ _ rs) = foldr (\(_, to) as->to:as) [] rs
atomsOfPCT (NilT) = []
--atomsOfPCT (TSeq t1 t2) = (atomsOfPCT t1) `union` (atomsOfPCT t2)
atomsOfPCT  (StopT) = [] 
atomsOfPCT  (SkipT) = [] 

isOperator (OpB _ _ _) = True
isOperator _ = False

isAtomic at@(Atom _ _ _) = isAtom at
isAtomic (Kappa _) = True
isAtomic (NilT) = True
isAtomic (StopT) = True
isAtomic (SkipT) = True
isAtomic (Ref _ _ _ _) = True
isAtomic (OpB (OpSeq _) t NilT) = isAtom t
isAtomic _ = False

isSole (Atom _ _ _) = True
isSole (Kappa _) = True
isSole (OpB _ t1 _) = isAtomic t1 
isSole (NilT) = True
isSole (StopT) = True
isSole (SkipT) = True
isSole (Ref _ _ _ _) = True


isAtomAny (Atom _ _ as) = isSomething as
isAtomAny _ = False

isAtom (Atom _ _ as) = isNil as
isAtom _ = False

