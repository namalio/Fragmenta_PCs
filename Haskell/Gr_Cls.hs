{-# LANGUAGE MultiParamTypeClasses #-}
module Gr_Cls(GR(..), TK(..), isKTotal, MK(..), GRM(..), GrM, G_WF_CHK(..), GM_CHK(..), GM_CHK'(..), cons_gm, empty_gm, tyOfN, tyOfE, 
   tyOfNM) where

import Relations
import ErrorAnalysis
import MyMaybe

data TK = Total | Partial deriving (Eq, Show)

isKTotal t = t == Total

--The three kinds of morphism: weak, partial, full (either total or partial) 
data MK = WeakM | PartialM | TotalM deriving (Eq, Show)

class GR g where
   ns ::  Eq a =>g a-> [a]
   es ::  Eq a =>g a-> [a]
   src::  Eq a =>g a-> [(a, a)]
   tgt::  Eq a =>g a-> [(a, a)]
   esId:: Eq a =>g a-> [a]
   empty:: Eq a => g a
   esId g = filter (\e-> appl (src g) e == appl (tgt g) e)(es g)

class GRM gm where
   fV :: Eq a=> gm a->[(a, a)]
   fE :: Eq a=> gm a->[(a, a)]

class G_WF_CHK g where
   is_wf::Eq a => (Maybe TK)->g a -> Bool
   check_wf::(Eq a, Show a) => String->(Maybe TK)->g a -> ErrorTree

data GrM a = GrM {mV_ :: [(a, a)], mE_:: [(a, a)]} deriving(Eq, Show) 

cons_gm vf ef = GrM {mV_ = vf, mE_ = ef}
empty_gm = cons_gm [] [] 
fV_gm GrM {mV_ = vf, mE_ = _} = vf
fE_gm GrM {mV_ = _, mE_ = ef} = ef

-- gets node type of a particular node
tyOfN n m = appl (fV m) n
tyOfNM n m = applM (fV m) n

-- gets edge type of a particular edge
tyOfE e m = appl (fE m) e

instance GRM GrM where
   fV = fV_gm
   fE = fE_gm

class GM_CHK g g' where
   is_wf_gm::(Eq a)=>(Maybe MK)->(g a, GrM a, g' a)->Bool 
   check_wf_gm::(Eq a, Show a) => String->(Maybe MK)->(g a, GrM a, g' a)->ErrorTree

class GM_CHK' g g' where
   is_wf_gm'::(Eq a)=>(Maybe MK)->(g a, g' a)->Bool 
   check_wf_gm'::(Eq a, Show a) => String->(Maybe MK)->(g a, g' a)->ErrorTree

-- data GrMSs a = GrMSs {fV_ :: [(a, a)], fE_:: [(a, Int, a)]} deriving(Eq, Show) 
-- cons_gmss fv fe = GrMSs {fV_ = fv, fE_ = fe}
-- empty_gmss = cons_gmss [] []
-- fV_gmss GrMSs {fV_ = vf, fE_ = _} = vf
-- fE_gmss GrMSs {fV_ = _, fE_ = ef} = ef

-- class GRM' gm where
--    fV' :: Eq a=> gm a->[(a, a)]
--    fE' :: Eq a=> gm a->[(a, Int, a)]

-- instance GRM' GrMSs where
--    fV' = fV_gmss
--    fE' = fE_gmss
