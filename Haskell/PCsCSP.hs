
------------------
-- Project: PCs/Fragmenta
-- Module: 'PCsCSP'
-- Description: Module responsible for transforming PCTs into CSP
-- Author: Nuno Amálio
-----------------
module PCsCSP(findAfterAtom, toCSP) where

import PCs
import CSP_AST
import Relations
import Sets
import Grs
import Gr_Cls
import SGrs
import CSPPrint
import PCTrees
import The_Nil
import MyMaybe
import PCs_MM_Names
import GrswT
import SimpleFuns

genAfterC mmi pc n
   | tyOfN n pc == show_cmm_n CMM_Reference = ExpId (nmOfRef pc n)
   | tyOfN n pc == show_cmm_n CMM_Atom = genAtom mmi pc n
   | tyOfN n pc == show_cmm_n CMM_Compound = genCompoundDef mmi pc n
   | otherwise = SKIP

genAfterAtom _ _ _ [] = SKIP
genAfterAtom mmi pc n [n2] 
   | n2 `elem` img (inv $ fV pc) [show_cmm_n CMM_AfterC] = genAfterC mmi pc (the $ successorsOf mmi pc n2)
   | otherwise = SKIP

genAtom mmi pc n = Prfx (ExpId n) $ genAfterAtom mmi pc n (successorsOf mmi pc n)

genChoices mmi pc [] = SKIP
genChoices mmi pc (ch:chs) 
   | null chs = genAfterC mmi pc (the $ successorsOf mmi pc ch)
   | otherwise = ExtChoice (genAfterC mmi pc (the $ successorsOf mmi pc ch)) (genChoices mmi pc chs)

--genDeclsForCompounds pc m cns = (map (\cn->genCompound pc m cn) cns)
--genRelevantForAtomic pc m n cns = if (not $ null cns) 
--   then LetW (genDeclsForCompounds pc m cns) (genAtomic pc m n) 
--   else (genAtomic pc m n)

genCompoundSeqComp mmi pc n =
   let e = the $ (successorsOf mmi pc n) `intersec` (pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_AfterC) in
   let next_n = the $ successorsOf mmi pc e in
   SeqComp (ExpId n) (genAfterC mmi pc next_n) 

genCompoundDef mmi pc n 
   | tyOfN n pc == show_cmm_n CMM_Atom = genAtom mmi pc n
   -- Either a process reference or sequential composition
   | tyOfN n pc == show_cmm_n CMM_Compound = if (show_cmm_n CMM_AfterC) `elem` (img (fV pc) (successorsOf mmi pc n)) 
      then (genCompoundSeqComp mmi pc n) else ExpId n 
   -- something combined with an operator
   | tyOfN n pc == show_cmm_n CMM_Operator && (opValOfOp (pc_sg_cmm mmi) pc n) == show_cmm_n CMM_OpChoice = genChoices mmi pc (successorsOf mmi pc n)  
   | otherwise = SKIP -- INCOMPLETE
   

findAfterAtom pc m n = (predecessors pc n) `intersec` (ran_of $ rres (src pc) $ img (inv $ fV m) [show_cmm_n CMM_AfterC])

--genCompound pc m n = 
--   let cns = withinCompounds pc m n in
--   let buildExp e = if (not $ null $ cns) then LetW (genDeclsForCompounds pc m cns) e else e in 
--   EqDecl (ExpId n) $ buildExp (genCompoundDef pc m (findCompoundStart pc m n))

cspChannels pct ias = Channel $ ias `union` (atomsOfPCTD pct)
   --Channel $ foldl(\ns n-> let n' = nmOfNamed pc m n in if n' `elem` ias then ns else insert n' ns) [] (getAtoms m)

--cspPImports sg_mm pc = Include $ map (\mn->mn ++ "P") (importsOf sg_mm pc)

cspImports is = Include $ map (\mn->mn ++ "P") is

cspMainImports pc = Include [(getPCDef pc) ++ "P", (getPCDef pc) ++ "_base"]

--isOperator (OpB OpChoice _ _) = True
--isOperator (OpB (OpParallel  _) _ _) = True
--isOperator (OpB OpInterleave _ _) = True
--isOperator(Op (OpSyncInterrupt  _) _ _) = True
--isOperator (OpB (OpThrow  _) _ _) = True
--isOperator _ = False

--cspDecl (ts@(TSeq _ _)) = snd $ cspExp ts
--cspDecl (c@(Compound n ps t)) = 
--   let (e, cds) = cspExp c in
--   [LetW cds e] 
--cspDecl (OpB _ t1 t2) = cspDecl t1 ++ cspDecl t2
cspDecl cts = foldr (\ct scts->(snd $ cspExp  (Kappa ct)) ++ scts) [] cts

--cspDecls ts = foldr (\t ts'-> (cspDecl t)++ts') [] ts

--data BothOpt = Both (PCT->Bool) (PCT->Bool) | Fst (PCT->Bool) | Snd (PCT->Bool) | None 
data BothOpt = Both (Exp->Bool) (Exp->Bool) | Fst (Exp->Bool) | Snd (Exp->Bool) | None

cspExpsFor0 t1 t2 = 
    let (e1, cds1) = cspExp t1 in
    let (e2, cds2) = cspExp t2 in
    (e1, e2, cds1++cds2)

oparExp e f = if f e then ExpPar e else e
calcExp1 e (Both f _) = oparExp e f
calcExp1 e (Fst f) = oparExp e f
calcExp1 e (Snd f) = e
calcExp1 e None = e
calcExp2 e (Both _ f) = oparExp e f
calcExp2 e (Fst f) = e 
calcExp2 e (Snd f) = oparExp e f
calcExp2 e None = e
-- cspExpsFor t1 t2 (Both f f') = 
--     let (e1, e2, cds) = cspExpsFor0 t1 t2 in
--     let e1' = if f t1 then ExpPar e1 else e1 in
--     let e2' = if f' t2 then ExpPar e2 else e2 in
--     (e1', e2', cds)

-- cspExpsFor t1 t2 (Fst f) = 
--     let (e1, e2, cds) = cspExpsFor0 t1 t2 in
--     let e1' = if f t1 then ExpPar e1 else e1 in
--     (e1', e2, cds)

-- cspExpsFor t1 t2 (Snd f) = 
--     let (e1, e2, cds) = cspExpsFor0 t1 t2 in
--     let e2' = if f t2 then ExpPar e2 else e2 in
--     (e1, e2', cds)

-- cspExpsFor t1 t2 None = cspExpsFor0 t1 t2

cspExpsFor t1 t2 pfs = 
    let (e1, e2, cds) = cspExpsFor0 t1 t2 in
    (calcExp1 e1 pfs, calcExp2 e2 pfs, cds)

cspPRef n g ps rs = let e1 = if null ps then ExpId n else ExpApp n ps in
   let e2 = if null rs then e1 else ExpRen e1 rs in
   if isNil g then e2 else GExp (ExpId $ the g) e2 

cspPDef t =
   let (e, ds) = cspExp t in
   if null ds then e else LetW ds e

--cspPDefW n t =
--   let (e, ds) = cspExp t in
--   let e1 = cspPRef (n ++ "0") [] in
--   let d = EqDecl (ExpId $ n++ "0") e in
--   if null ds then LetW [d] e1 else LetW (d:ds) e1

cspExpPrfx t1 t2 = 
    let (e1, e2, cds) = cspExpsFor t1 t2 (Snd isComposite) in
    (Prfx e1 e2, cds)

cspExpSeq t1 t2 = 
    let (e1, e2, cds) = cspExpsFor t1 t2 (Snd isComposite) in
    (SeqComp e1 e2, cds)

consLetW ds (LetW ds' e) = LetW (ds++ds') e
consLetW ds e = LetW ds e


cspExpREC (Atom _ og (Just (atv, ats))) t2 = 
  let (e1, ds) = cspExp t2 in
  let e2 = ExpPar $ RExtChoice atv ats $ Prfx (ExpId atv) e1 in
  if isNil og then (e2, ds) else (GExp (ExpId $ the og) e2, ds) 

cspExp NilT = (SKIP, [])
cspExp StopT = (STOP, [])
cspExp SkipT = (SKIP, [])
cspExp (Atom a og Nothing) = 
    let e =  ExpId a in
    pair_up (if isNil og then e else (GExp (ExpId $ the og) e)) [] 
    
cspExp (Kappa (CT n ps cts t))  = let e1 = cspPRef n Nothing ps [] in
   let e2 = cspPDef t in
   let e2' = if isSomething cts then consLetW (cspDecl cts) e2 else e2 in
   (e1, [EqDecl e1 e2'])
cspExp (Ref r g ps rs) = (cspPRef r g ps rs, [])
cspExp (OpB (OpIf g) t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 None in
   (IfExp (ExpId g) e1 e2, cds) 
cspExp (OpB (OpSeq o) t1 t2) 
    | isAtomAny t1 && (o || t2 == NilT) = cspExpREC t1 t2 
    | isAtomAny t1 && (not o) = let (e1, ds1) = cspExpREC t1 NilT in let (e2, ds2) = cspExp t2 in (SeqComp e1 e2, ds1++ds2)
    | otherwise    = if (isAtom t1) then cspExpPrfx t1 t2 else cspExpSeq t1 t2 
cspExp (OpB OpExtChoice t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both isComposite (not . f)) in
   (ExtChoice e1 e2, cds)
   where f e = isAtomicExp e || isExtChoice e
cspExp (OpB OpIntChoice t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both isComposite isComposite) in
   (IntChoice e1 e2, cds)
cspExp (OpB (OpParallel evs) t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both isComposite isComposite) in
   (Parallel evs e1 e2, cds)
--genCSPExp (Op (OpSyncInterrupt evs) t1 t2) = 
--   let (e1, e2, rts) = genExpsForOps t1 t2 in
--   let e1' = if (isOperator t1) then ExpPar e1 else e1 in
--   let e2' = if (isOperator t2) then ExpPar e2 else e2 in
--   (SyncInterrupt evs e1' e2', rts)
cspExp (OpB (OpThrow evs) t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both isComposite isComposite) in
   (Throw evs e1 e2, cds)
cspExp (OpB OpInterleave t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both isComposite isComposite) in
   (Interleave e1 e2, cds)

toCSP::MMInfo String->PC String->[String]->[String]->(CSPSpec, CSPSpec, CSPSpec)
toCSP mmi pc ias is = 
   let (PCTD _ cts) = consPCTD mmi pc in
   (CSP [cspChannels cts ias], CSP $ cspDecl cts, CSP $ [cspMainImports pc] ++ [cspImports is])