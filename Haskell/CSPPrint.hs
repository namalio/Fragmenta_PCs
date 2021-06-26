
------------------
-- Project: PCs/Fragmenta
-- Module: 'CSPPrint'
-- Description: Module that deals with the text printing (or conversion to string) of CSP specifications
-- Author: Nuno Amálio
-----------------
module CSPPrint(wrCSP) where

import CSP_AST
import ParseUtils

--wrWaitFor = "Wait_({})= SKIP\nWait_(evs) = [] e :evs @ e->Wait_(diff(evs, {e}))"

wrDecl ind (Channel ids) = "channel " ++ (wrSepElems ids "," True False ind)
wrDecl ind (EqDecl e1 e2) = (do_indent ind) ++ (wrExp ind e1) ++ " = " ++ wrExp (ind +1) e2
wrDecl ind (Include ms) = wrSepElems (map (\m->"include \"" ++ m ++ ".csp\"") ms) "\n" False False ind

wrExp _ (ExpId id) = id 
wrExp ind (ExpPar e) = "(" ++ (wrExp ind e) ++ ")" 
wrExp ind (ExpApp id ps) = id ++ "(" ++ (wrSepElems ps ", " False False 0) ++ ")" 
wrExp ind (GExp e1 e2) = (wrExp ind e1) ++ " & " ++ (wrExp ind e2)
wrExp ind (IfExp e1 e2 e3) = 
   "if " ++ (wrExp 0 e1) ++ "\n" ++ (do_indent ind) ++ " then " ++ (wrExp ind e2) 
   ++ "\n" ++ (do_indent ind) ++ "else " ++ (wrExp (ind +1) e3)
wrExp ind (Prfx e1 e2) = (wrExp ind e1) ++ " -> " ++ (wrExp ind e2)
wrExp ind (ExtChoice e1 e2) = (wrExp ind e1) ++ "\n" ++ (do_indent (ind +1)) ++ "[] " ++ (wrExp ind e2)
wrExp ind (IntChoice e1 e2) = (wrExp ind e1) ++ "\n" ++ (do_indent (ind +1)) ++ " |~| " ++ (wrExp ind e2)
wrExp ind (RExtChoice idv ids e) =  "[] " ++ idv ++ " : " ++ ids ++ " @ " ++ (wrExp ind e)
wrExp ind (SeqComp e1 e2) = (wrExp ind e1) ++ "; " ++ (wrExp ind e2)
wrExp ind (Parallel evs e1 e2) = (wrExp ind e1) ++ "[|{" ++ (wrSepElems evs "," False False 0) ++ "}|]" ++ (wrExp ind e2)
wrExp ind (Throw evs e1 e2) = (wrExp ind e1) ++ "[|{" ++ (wrSepElems evs "," False False 0) ++ "}|>" ++ (wrExp ind e2)
--wrExp ind (SyncInterrupt evs e1 e2) = (wrExp ind e1) ++ "/+{" ++ (wrSepElems evs "," False False 0) ++ "}+\\" ++ (wrExp ind e2)
wrExp ind (Interleave e1 e2) = (wrExp ind e1) ++ " ||| " ++ (wrExp ind e2)
--wrExp ind (WaitFor ids) = "Wait_({" ++ (wrSepElems ids "," True False ind) ++ "})"
wrExp ind STOP = "STOP"
wrExp ind SKIP = "SKIP"
wrExp ind (LetW ds e) = "\n" ++ (do_indent ind) ++ "let \n" ++ (wrSepElems (map (wrDecl $ ind + 1) ds) "\n" False False (ind +2)) 
   ++ "\n" ++ (do_indent ind) ++ "within\n" ++ (do_indent (ind+1)) ++ (wrExp (ind + 1) e)
wrExp ind (ExpRen e rs) = (wrExp ind e) ++ (wrRenamings rs)
wrRenamings rs = "[[" ++ (foldr (\(fr, to) rstr->fr ++ " <- " ++ to ++ (if null rstr then "" else ",") ++ rstr) "" rs) ++ "]]"
--hasWait (WaitFor _) = True
hasWait (LetW ds e) = (hasWaitDs ds) || hasWait e
hasWait (_) = False
hasWaitD (Channel _) = False
hasWaitD (Include _) = False
hasWaitD (EqDecl _ e) = hasWait e
hasWaitDs ds = foldr (\d d'->(hasWaitD d) || d') False ds

wrCSP (CSP ds) = 
   let cspTxt = wrSepElems (map (wrDecl 0) ds) "\n\n" False False 0 in
   cspTxt
  -- if (hasWaitDs ds) then wrWaitFor ++ "\n\n" ++ cspTxt else cspTxt


