module MyMaybe(str_of_ostr, appl_f_M, toMaybeP, toMaybeFrLs, applM, boolMaybe, predMaybe,maybeToLs) where

import Relations
import The_Nil

str_of_ostr::(Maybe String)->String
str_of_ostr Nothing = ""
str_of_ostr (Just s) = s

--isNil::(Maybe a) -> Bool
--isNil Nothing = True
--isNil (Just _) = False

--isSomething::(Maybe a) -> Bool
--isSomething = not . isNil

--theM::(Maybe a) -> a
--theM (Just x) = x

appl_f_M::(a->b)->Maybe a->Maybe b
appl_f_M _ (Nothing) = Nothing
appl_f_M f (Just x) = Just (f x)

toMaybeP::Maybe a->Maybe b->Maybe(a,b)
toMaybeP Nothing _ = Nothing
toMaybeP _ Nothing = Nothing
toMaybeP (Just x) (Just y) = Just (x, y)

toMaybeFrLs [] = Nothing
toMaybeFrLs (n:_) = Just n

maybeToLs (Nothing) = []
maybeToLs (Just x) = [x]

applM r x = toMaybeFrLs $ img r [x] 

boolMaybe b x = if b then Just x else Nothing

predMaybe p x = if p x then Just x else Nothing

instance The Maybe where
    the (Just x) = x

instance Nil Maybe where
    nil = Nothing
    isNil Nothing = True
    isNil (Just _) = False


instance The [] where
    the (n:_) = n

instance Nil [] where
    nil = []
    isNil l = null l