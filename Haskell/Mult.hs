------------------
-- Project: PCs/Fragmenta
-- Module: 'Mult'
-- Description: Handles multiplicities of relations
-- Author: Nuno Amálio
-----------------
module Mult (MultVal(..), mval, mmany, Mult(..), mrange, msole_many, msole_k, multwf, multOk, check_multOk, mopt, allowedm) where

import SGElemTys
import Relations
import ErrorAnalysis

data MultVal = Val Int | Many deriving (Eq, Show)

-- 'MultVal' constructors
mval k = Val k
mmany = Many

-- The mutliplicity constraint
data Mult = Rm Int MultVal | Sm MultVal deriving (Eq, Show)

-- 'Mult' constructors
mrange k mv = Rm k mv
msole_many  = Sm Many
msole_k k   = Sm (mval k)
mopt        = Rm 0 (mval 1)

-- Checks that a multiplicity constraint is well-formed
multwf (Rm n Many) = n >= 0
multwf (Rm lb (Val ub)) = lb < ub && lb >=0
multwf (Sm Many) = True
multwf (Sm (Val v)) = v >= 1

mv_leq _ Many = True
mv_leq (Val k) (Val j) = k <= j
mv_leq _ _ = False

instance Ord MultVal where
   (<=) = mv_leq
   --(>=) = (\s1 s2-> (ids s1) >= (ids s2))

-- Predicate 'withinm' (≬)
withinm k (m1, m2) = m1 <= mval k && mval k <= m2

-- Function mlb, which gives the lower bound of a multplicity constraint (Mult) 
mlb (Sm Many) = mval 0
mlb (Sm (Val k)) = mval k
mlb (Rm k _) = mval k

-- Functions mub, which gives the upper bound of a multiplicity constraint (Mult)
mub (Sm m) = m
mub (Rm _ m) = m

-- Checks whether  m is a many multiplicity
isMultMany (Sm Many) = True
isMultMany (Rm 0 Many) = True
isMultMany _ = False

isMultOpt m = m `elem` [Sm (Val 1), Rm 0 (Val 1)]

-- Checks whether  m is a range or bounded multiplicity
isMultRange (Sm (Val k)) = k > 1
isMultRange m@(Rm lb ub) = lb >= 0 && (mval 2) <= ub && multwf m

-- Ordering on 'Mult'
m_leq m1 m2 = mlb m2 <= mlb m1 && mub m1 <= mub m2

instance Ord Mult where
   (<=) = m_leq

-- Predicate 'allowedm' (∝) 
allowedm (Erel Dbi) (_, _) = True
allowedm (Ecomp Duni) (Sm (Val 1), _) = True
allowedm (Erel Duni) (m1, _) = isMultMany m1
allowedm (Ecomp Dbi) (m1, _) = isMultOpt m1
allowedm (Ewander) (m1, m2) = isMultMany m1 && isMultMany m2
allowedm _ _ = False


rbounded r s m = all (\x->length(img r [x]) `withinm` (mlb m, mub m))  s

-- Predicate 'rmOk', which checks whether a multiplicity is satisfied by a given relation
multOk::Eq a=>[(a, a)]->[a]->[a]->Mult->Mult->Bool
multOk r s t m (Sm (Val 1)) 
    | m == Sm (Val 1)   = fun_bij r s t
    | m == Rm 0 (Val 1) = fun_inj r s t
    | isMultMany m      = fun_total r s t
    | isMultRange m     = fun_total r s t && rbounded (inv r) t m
multOk r s t (Sm (Val 1)) m 
    | m == Rm 0 (Val 1) = fun_inj (inv r) t s
    | isMultMany m      = fun_total (inv r) t s
    | isMultRange m     = fun_total (inv r) t s && rbounded r s m 
multOk r s t m (Rm 0 (Val 1))
    | m == Rm 0 (Val 1) = fun_pinj r s t
    | isMultMany m      = pfun r s t
    | isMultRange m     = pfun r s t && rbounded (inv r) t m
multOk r s t (Rm 0 (Val 1)) m
    | isMultMany m  = pfun (inv r) t s
    | isMultRange m = pfun (inv r) t s && rbounded r s m 
multOk r s t m1 m2 
    | all isMultMany [m1, m2]         = relation r s t
    | isMultMany m1 && isMultRange m2 = relation r s t && rbounded r s m2 
    | isMultRange m1 && isMultMany m2 = relation r s t && rbounded (inv r) t m1
    | all isMultRange [m1, m2]        = relation r s t && rbounded r s m2 && rbounded (inv r) t m1

say_mv (Val k) = if k == 1 then "one" else (show k)
say_mv (Many) = "many (*)"

say_mult (Sm mv) = say_mv mv
say_mult (Rm 0 (Val 1)) = "optional (0..1)"
say_mult (Rm 0 Many) = say_mv (Many)
say_mult (Rm lb ub) = say_mv (mval lb) ++ ".." ++ (say_mv ub) 

mult_err_msg me m1 m2 = (say_mult m1) ++ " to " ++ (say_mult m2) ++ " multiplicity constraint  of meta-edge " ++ (show me) ++ " is unsatisfied."

check_rbounded r s m = if rbounded r s m then nile else cons_se "Relation not within multiplicity bounds"

check_multOk::(Eq a, Show a)=>a->[(a, a)]->[a]->[a]->Mult->Mult->ErrorTree
check_multOk me r s t m1 m2@(Sm (Val 1)) 
    | m1 == Sm (Val 1)   = if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_fun_bij r s t]
    | m1 == Rm 0 (Val 1) = if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_fun_inj r s t]
    | isMultMany m1      = if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_fun_total r s t]
    | isMultRange m1     = 
        if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_fun_total r s t, check_rbounded (inv r) t m1] 
check_multOk me r s t m1@(Sm (Val 1)) m2 
    | m2 == Rm 0 (Val 1) = 
        if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_fun_inj (inv r) t s]
    | isMultMany m2      = 
        if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_fun_total (inv r) t s]
    | isMultRange m2     = 
        if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_fun_total (inv r) t s, check_rbounded r s m2] 
check_multOk me r s t m1 m2@(Rm 0 (Val 1))
    | m1 == Rm 0 (Val 1)  = 
        if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_fun_pinj r s t] 
    | isMultMany m1      = 
        if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_pfun r s t] 
    | isMultRange m1     = 
        if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_pfun r s t, check_rbounded (inv r) t m1]
check_multOk me r s t m1@(Rm 0 (Val 1)) m2
    | isMultMany m2  = 
        if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_pfun (inv r) t s]  
    | isMultRange m2 = 
        if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_pfun (inv r) t s, check_rbounded (inv r) t m2]
check_multOk me r s t m1 m2 
    | all isMultMany [m1, m2]         = 
        if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_relation r s t]
    | isMultMany m1 && isMultRange m2 = 
        if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_relation r s t, check_rbounded r s m2]
    | isMultRange m1 && isMultMany m2 = 
        if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_relation r s t, check_rbounded (inv r) t m1]
    | all isMultRange [m1, m2]        = 
        if (multOk r s t m1 m2) then nile else cons_et (mult_err_msg me m1 m2) [check_relation r s t, check_rbounded r s m2, check_rbounded (inv r) t m1]
