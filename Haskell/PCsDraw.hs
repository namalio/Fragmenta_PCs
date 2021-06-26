------------------
-- Project: PCs/Fragmenta
-- Module: 'PCsDraw'
-- Description: Module that deals with the drawing of PCs as graphviz ddescriptions
-- Author: Nuno Amálio
-----------------
module PCsDraw(wrPCAsGraphviz) where
 
import PCs
import SGrs
import Gr_Cls
import Grs
import Sets
import Relations
import ShowUtils
import The_Nil
import MyMaybe
import PCs_MM_Names

type Guard = Maybe String
data NodeInfo = Compound [String] | Atom String Guard (Maybe (String, String)) 
    | Reference Bool String [String] [(String, String)] Guard
    | Start | Stop | Skip | Import | Op String [String] 
    deriving(Eq, Show) 
data Node = Node String NodeInfo deriving(Eq, Show) 
data ConnectorInfo = CDef | CAfter Bool | CRef [String] Bool | CStart | CBranch | CBranchIf String | CBranchElse | CBranchJump deriving(Eq, Show) 
data Connector = Connector String ConnectorInfo String String deriving(Eq, Show) 
data PCDrawing = PCDrawing String [Node] [Connector] [[String]] deriving(Eq, Show) 

nmOfNode (Node nm _) = nm 
isNodeStart (Node _ ni) = ni == Start

in_sames x [] = False
in_sames x (l:ls) = x `elem` l || in_sames x ls

sames' _ [] ls = ls
sames' r (x:xs) ls 
   | in_sames x ls = sames' r xs ls
   | otherwise = sames' r xs $ ((x:(img (trancl r) [x])):ls)

sames r = sames' r (dom_of r) []

toNodeKind pc n CMM_Compound  = Compound $ paramsOf pc n
toNodeKind pc n CMM_Atom      = Atom (nmOfNamed pc n) (guardOf pc n) (anyExpOfAt pc n) 
toNodeKind pc n CMM_Reference = Reference (inner_Ref pc n) (nmOfRef pc n) (paramsOf pc n) (renamingsOf pc n) (guardOf pc n)
toNodeKind _ _ CMM_Skip       = Skip
toNodeKind _ _ CMM_Stop       = Stop
toNodeKind _ _ CMM_StartN     = Start
toNodeKind _ _ CMM_Import     = Import

toOp CMM_OpIf            = "If"
toOp CMM_OpChoice        = "◻︎"
toOp CMM_OpIntChoice     = "⊓"
toOp CMM_OpParallel      = "||"
toOp CMM_OpInterleave    = "|||"
toOp CMM_OpThrow         = "Θ"

consNode sg_mm pc n = 
   let nt = read_cmm $ tyOfN n pc in
   let nts = [CMM_Compound, CMM_Atom, CMM_Reference, CMM_Stop, CMM_Skip, CMM_StartN, CMM_Import] in
   if nt `elem` nts then Node n $ toNodeKind pc n nt else Node n $ Op (toOp . read_cmm $ opValOfOp sg_mm pc n) (paramsOf pc n)

toConnectorKind _ _ CMM_DefinesC     = CDef
toConnectorKind _ _ CMM_StartC       = CStart
toConnectorKind pc c CMM_AfterC      = CAfter (openAC pc c)
toConnectorKind pc c CMM_ReferenceC  = CRef (paramsOf pc c) (hidden_RC pc c)
toConnectorKind _ _ CMM_BranchC      = CBranch 
toConnectorKind pc c CMM_BMainIfC    = CBranchIf (the $ guardOf pc c)
toConnectorKind _ _ CMM_BElseC       = CBranchElse
toConnectorKind _ _ CMM_BJumpC       = CBranchJump

consNodes     sg_mm pc ns = foldr (\n ns'->(consNode sg_mm pc n):ns') [] ns

consConnectors mmi pc cs = foldr (\c cs'->(Connector c (toConnectorKind pc c (read_cmm $ tyOfN c pc)) (srcOf mmi pc c) (tgtOf mmi pc c)):cs') [] cs

--getStartName nm = "start_" ++ nm 

--consCStart pc m = let c = (getPCDef m) in
--   Connector c CStart c (getPCStart pc m)

drawPC mmi pc = 
   let nodes = consNodes (pc_sg_cmm mmi) pc (pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_Node)  in
   let cs = consConnectors mmi pc (pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_Connector)  in
   let r_after = afterCRel mmi pc in
   let freeFromSameRefs = filter (\n->(length (img (inv $ r_after) [n])>1)) (pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_Reference)  in
   let ss_r = diff (rsub r_after freeFromSameRefs) (inv $ trancl $ withinRel mmi pc) in
   let ss' = ([getPCStart (pc_sg_cmm mmi) pc, startCompound mmi pc]):(sames ss_r) in
   PCDrawing (getPCDef pc) nodes cs ss'

wrParamsLabel nm ps = 
   let lps = if null ps then "" else "(" ++ (showStrs ps ",") ++ ")" in
   "\"" ++ nm ++ " " ++ lps ++ "\""

wrGuard Nothing _ = ""
wrGuard (Just g) html = " {" ++ g ++ "}" ++ (if html then "<br/>" else "\n")

wrRefLabelPsRens nm ps rs g b = 
   let lps = if null ps then "" else "(" ++ (showStrs ps ",") ++ ")" in
   let st_lrs = if null lps then "" else "\n" in
   let lrs = if null rs then "" else st_lrs ++ "⟦" ++ (showStrs (foldr (\(fr, to) rps->(fr ++ "/" ++ to):rps) [] rs) ",") ++ "⟧" in
   "\"" ++ (wrGuard g False) ++ nm ++ " " ++ lps ++ lrs ++ inner ++ "\""
   where inner = if b then "\n(Inner)" else ""

wrOperatorLabel [] = ""
wrOperatorLabel ps = (wrSepElems ps "," False False 0) 

wrParamatersOfOp nm [] = ""
wrParamatersOfOp nm ps = "\n"++ nm ++ "_ps" ++  "[shape=rect,fillcolor=yellow,style=\"filled,dotted\",label=\"" ++ (wrOperatorLabel ps) ++ "\"];\n" 
   ++ nm ++"->" ++ nm ++ "_ps [dir=none,color=\"black:invis:black\"];\n" ++ "{rank=same;" ++ nm ++ "," ++ nm ++ "_ps}"


wrAtomCommon nm = nm ++ " [shape=ellipse,fillcolor=greenyellow,style = filled,label=" 
wrAtomAny0 g = "<" ++ (wrGuard g True)
wrAtomAny "" g = (wrAtomAny0 g) ++ "<I>anyof</I> " 
wrAtomAny atv g = (wrAtomAny0 g) ++ "<I>any</I> " ++ atv ++ ":"
wrNode (Node nm (Compound ps)) =  nm ++ " [shape=box,fillcolor=deepskyblue,style = filled,label=" ++ (wrParamsLabel nm ps) ++ "];" 
wrNode (Node nm (Atom rnm g Nothing)) =  (wrAtomCommon nm) ++ "\"" ++ (wrGuard g False) ++ rnm ++ "\"];"
wrNode (Node nm (Atom rnm g (Just (atv, atS)))) = (wrAtomCommon nm) ++ (wrAtomAny atv g) ++ atS  
    ++ "<br/>[" ++ rnm ++ "]>];"
wrNode (Node nm (Reference b rnm ps rs g)) = nm 
    ++ " [shape=rectangle,fillcolor=" ++ fillColor 
    ++ ",style=\"rounded,filled,dashed\",label="++ (wrRefLabelPsRens rnm ps rs g b) ++"];"
    where fillColor = if b then "\"#CBD7EB\"" else "gray"
wrNode (Node nm (Op op ps)) = nm ++ " [shape=diamond,fillcolor=yellow,style = filled,label=\"" ++ op ++ "\"];" 
   ++ wrParamatersOfOp nm ps
wrNode (Node nm Stop) = nm ++ " [shape=box,fillcolor=mistyrose2,style = filled,label=\"STOP\"];"
wrNode (Node nm Skip) = nm ++ " [shape=box,fillcolor=\"#B9E0A5\",style = filled,label=\"SKIP\"];"
wrNode (Node nm Import) = nm ++ " [shape=hexagon,fillcolor=orangered,style=filled,label =" ++  nm ++ "];" 

wrConnectorSettings CDef = "[arrowhead=\"onormal\",dir=both,arrowtail=obox,penwidth=2,label=\"=\"];"
wrConnectorSettings CBranch = "[arrowhead=\"vee\",fillcolor=white];"
wrConnectorSettings (CBranchIf g) = "[arrowhead=\"vee\",fillcolor=white,label=\""++g ++"\"];"
wrConnectorSettings CBranchElse = "[arrowhead=\"vee\",label=\"Else\"];"
wrConnectorSettings CBranchJump = "[arrowhead=\"vee\",label=\"Jump\"];"
wrConnectorSettings (CAfter o) =  "[arrowtail=" ++ (if o then "odot" else "dot") ++ ",dir=both,label=\"after\"];"
wrConnectorSettings (CRef ps _) = "[arrowhead=\"normalnormal\",label=" ++ (wrParamsLabel "" ps) ++ "];"
wrConnectorSettings CStart = "[arrowhead=\"open\",arrowtail=diamond,dir=both,label=\"starts\"];"
wrConnector (Connector _ (CRef _ True) _ _) = ""
wrConnector (Connector nm ek s t) = s ++ "->" ++ t ++ (wrConnectorSettings ek)

wrNodes ns  = foldr (\n ns'-> (wrNode n)++ "\n" ++ns') "" ns
wrConnectors cs  = foldr (\c cs'-> (wrConnector c)++ "\n" ++cs') "" cs 

wrSamesLs ls = (foldr (\n ns-> if null ns then n else n ++ "," ++ ns) "" ls) ++ "}"
wrSameRank ls = "{rank=same;" ++ wrSamesLs ls
wrMinRank ls = "{rank=min;" ++ wrSamesLs ls

wrSames' [] = ""
wrSames' (l:ls) = (wrSameRank l) ++ "\n" ++ (wrSames' ls)

wrSames ls = wrMinRank (head ls) ++ "\n" ++ wrSames' (tail ls)

startNode ns = nmOfNode . the $ filter (isNodeStart) ns
wrStartNode snm nm = snm ++  " [shape = cds,color=burlywood2,style=filled,height=.2,width=.2, label =" ++  nm ++ "];" 
wrPCDrawing (PCDrawing nm ns cs ss) = "digraph {\n" ++ (wrStartNode (startNode ns) nm) ++ "\n" 
   ++ (wrNodes $ filter (not . isNodeStart) ns) ++ "\n" ++ (wrSames ss) ++ "\n" ++ (wrConnectors cs) ++ "}"

wrPCAsGraphviz mmi pc = wrPCDrawing $ drawPC mmi pc