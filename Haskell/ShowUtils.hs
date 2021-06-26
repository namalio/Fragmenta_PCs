module ShowUtils(showElems, showElems', wrSepElems, showStrs) where

showStrs xs sep = foldl (\ss s->if null ss then s else ss++sep++s) "" xs

showElems xs sep = foldr (\s ss->if null ss then (show s) else (show s)++sep++ss) "" xs

showElems' xs  = showElems xs ", "

do_indent 0 = ""
do_indent n = "   " ++ do_indent(n-1)

-- Writes elements separated by some separator
-- Takes an identation level (a natural number)
wrSepElems [] _ _ _ _ = ""
wrSepElems (s:ss) sep spaced ind i
   | null ss = (if ind then (do_indent i) else "") ++ s
   | otherwise = 
   let spc = if spaced then " " else "" in
   let dind = if ind then do_indent i else "" in
      dind++s++sep++spc++(wrSepElems ss sep spaced False i)