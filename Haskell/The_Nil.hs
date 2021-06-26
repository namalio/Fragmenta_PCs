
module The_Nil(The(..), Nil(..)) where

class The f where
   the ::  Eq a =>f a-> a

class Nil f where
   nil ::  Eq a =>f a
   isNil ::  Eq a =>f a-> Bool
   isSomething ::  Eq a =>f a-> Bool
   isNil f = not $ isSomething f
   isSomething f = not $ isNil f