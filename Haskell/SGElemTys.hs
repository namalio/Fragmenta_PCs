
------------------
-- Project: PCs/Fragmenta
-- Module: 'SGElemTy'
-- Description: Definitions related to the different types of SG elements (nodes or edges)
-- Author: Nuno Amálio
-----------------
module SGElemTys (SGNTy(..), SGETy(..), SGED(..), sgnty_set, sgety_set) where

import Logic

data SGNTy = Nnrml | Nabst | Nprxy | Nenum | Nval | Nvirt | Nopt deriving (Eq, Show)

sgnty_set = [Nnrml, Nabst, Nprxy, Nenum, Nval, Nvirt, Nopt]

-- The association edge direction
data SGED = Dbi | Duni  deriving (Eq, Show)

data SGETy = Einh | Ecomp SGED | Erel SGED | Ewander deriving (Eq, Show)
sgety_set = [Einh, Ewander] ++ [e d | e<-[Ecomp, Erel], d<-[Duni, Dbi]]

-- Ordering that is used to state inheritance relations (sequence nodes can neither inherit nor be inherited)
nty_lti:: SGNTy->SGNTy->Bool
nty_lti nt1 nt2 = ((nt2 == Nenum) `iff` (nt1 == Nval)) && ((nt1 == Nvirt) `implies` (nt2 == Nvirt)) && ((nt1 == Nabst) `implies` (nt2 `elem` [Nvirt, Nabst, Nprxy]))
    &&  (not $ nt1 `elem` [Nprxy, Nenum]) && nt2 /= Nopt

-- Ordering that is used to state refinement relations
nty_leqr:: SGNTy->SGNTy->Bool
nty_leqr _ Nnrml     = True
nty_leqr _ Nopt      = True
nty_leqr Nprxy _     = True
nty_leqr Nnrml nt   = nt `elem` [Nabst, Nprxy]
nty_leqr Nvirt Nabst = True
nty_leqr nt1 nt2     = nt1 == nt2 

instance Ord SGNTy where
    (<) = nty_lti
    (<=) = nty_leqr

ety_eq (Erel _) (Erel _)   = True
ety_eq ety1 ety2           = ety1 == ety2

-- Relation used for refinement: wander edges are refined by any non-inheritance edges
ety_leq et1 Ewander   = et1 /= Einh
ety_leq et1 et2       = et1 `ety_eq` et2

instance Ord SGETy where
    (<=) = ety_leq