module GrsDraw(wrGAsGraphviz) where

import Gr_Cls
import Grs
import Relations

data GEdge = GEdge String String String 
   deriving(Show)
data GNode = GNode String 
   deriving(Show) 
data GDrawing = GDrawing [GNode] [GEdge] 
   deriving(Show) 

--node_name::GNode->String
--node_name (GNode nm _) = nm

--ls_of_node_names::GDrawing->[String]
--ls_of_node_names (GDrawing ns es) = map node_name ns

consEdge g e = GEdge e (appl (src g) e) (appl (tgt g) e)
consEdges g = foldr (\e es'->(consEdge g e):es') [] (es g)

consNode n = GNode n 
consNodes g = foldr (\n ns'->(consNode n):ns') [] (ns g)
consGDrawingDesc g = GDrawing (consNodes g) (consEdges g)

wrEdgeSettings nm = "[" ++ (wrEdgeSettings' $ tail nm) ++ "];"
wrEdgeSettings' enm = "label=\""++enm++"▼\",arrowhead=vee"
wrEdge (GEdge nm s t) = "\"" ++ s ++ "\"->\"" ++ t ++ "\"" ++ (wrEdgeSettings nm)
wrEdges es  = foldr (\e es'-> (wrEdge e)++ "\n" ++es') "" es 

wrNode (GNode nm) =  "\"" ++ nm ++ "\"" ++"[shape=box,fillcolor=lightskyblue1,style = filled,label=\""++nm++"\"];"
wrNodes ns  = foldr (\n ns'-> (wrNode n)++ "\n" ++ns') "" ns

wrGGraphvizDesc::String->GDrawing->String
wrGGraphvizDesc nm (GDrawing ns es) = 
   let intro = "digraph {graph[label=" ++ nm ++ ",labelloc=tl,labelfontsize=12];\n" in
   let end = "}" in
   intro ++ (wrNodes ns) ++ "\n" ++ (wrEdges es) ++ end


wrGAsGraphviz nm g = wrGGraphvizDesc nm $ consGDrawingDesc g