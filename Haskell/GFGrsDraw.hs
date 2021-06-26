module GFGrsDraw(wrGFGAsGraphviz) where

import Gr_Cls
import GFGrs
import Relations

data GFGEdge = GFGEdge String String  
   deriving(Show)
data GFGNode = GFGNode String 
   deriving(Show) 
data GFGDrawing = GFGDrawing [GFGNode] [GFGEdge] 
   deriving(Show) 

--node_name::GNode->String
--node_name (GNode nm _) = nm

--ls_of_node_names::GDrawing->[String]
--ls_of_node_names (GDrawing ns es) = map node_name ns
consGFGEdge g e = GFGEdge (appl (src g) e) (appl (tgt g) e)
consGFGEdges g = foldr (\e es'->(consGFGEdge g e):es') [] (es g)

consGFGNode n = GFGNode n 
consGFGNodes g = foldr (\n ns'->(consGFGNode n):ns') [] (ns g)
consGFGDrawingDesc g = GFGDrawing (consGFGNodes g) (consGFGEdges g)

wrEdge (GFGEdge s t) = "\"" ++ s ++ "\"->\"" ++ t ++ "\"[label=®,dir=both,arrowtail=obox,arrowhead=emptyempty];"
wrEdges es  = foldr (\e es'-> (wrEdge e)++ "\n" ++es') "" es 

wrNode (GFGNode nm) =  "\"" ++ nm ++ "\"" ++"[shape=oval,fillcolor=\"#FFCCCC\",style =\"filled,dotted\",label=\""++nm++"\"];"
wrNodes ns  = foldr (\n ns'-> (wrNode n)++ "\n" ++ns') "" ns

wrGFGGraphvizDesc::String->GFGDrawing->String
wrGFGGraphvizDesc nm (GFGDrawing ns es) = 
   let intro = "digraph {graph[label=" ++ nm ++ ",labelloc=tl,labelfontsize=12];\n" in
   let end = "}" in
   intro ++ (wrNodes ns) ++ "\n" ++ (wrEdges es) ++ end


wrGFGAsGraphviz nm g = wrGFGGraphvizDesc nm $ consGFGDrawingDesc g