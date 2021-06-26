
module ParseUtils(wrSepElems, words', splitAt', splitAtStr, do_indent) where

import SimpleFuns

words' :: (Char->Bool)-> String -> [String]
words' isSep [] = []
words' isSep (xxs@(x:xs))
  | isSep x  = words' isSep xs
  | otherwise         =  ys : words' isSep rest
      where (ys, rest) = break (isSep) xxs

splitAt' p [] = ([], [])
splitAt' p (x:xs) 
   | p x = ([], xs)
   | otherwise = (x:ys, ys')
      where (ys, ys') = splitAt' p xs

splitAtStr _ [] = ([], [])
splitAtStr s xs@(x:xs') 
   | s `equalLs` (take (length s) xs) = ([], drop (length s) xs)
   | otherwise = (x:ys, ys')
      where (ys, ys') = splitAtStr s xs'

do_indent 0 = ""
do_indent n = "   " ++ do_indent(n-1)

-- Writes elements separated by some separator
-- Takes an identation level (a natural number)
wrSepElems [] _ _ _ _ = ""
wrSepElems (s:ss) sep spaced ind i
   | (null ss) = (if ind then (do_indent i) else "") ++ s
   | otherwise = 
   let spc = if spaced then " " else "" in
   let dind = if ind then do_indent i else "" in
      dind++s++sep++spc++(wrSepElems ss sep spaced False i)
