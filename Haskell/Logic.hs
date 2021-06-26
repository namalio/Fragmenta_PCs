
module Logic(implies, iff) where

-- Implication
implies False _ = True
implies True True = True
implies True False = False

iff p q = p `implies` q && q`implies` p