module GwTDraw(wrGwTAsGraphviz) where

import Gr_Cls
import Grs
import GrswT
import Relations

data GwTEdge = GwTEdge String String String String
   deriving(Show)
data GwTNode = GwTNode String String
   deriving(Show) 
data GwTDrawing = GwTDrawing [GwTNode] [GwTEdge] 
   deriving(Show) 

--node_name::GNode->String
--node_name (GNode nm _) = nm

--ls_of_node_names::GDrawing->[String]
--ls_of_node_names (GDrawing ns es) = map node_name ns

consEdge gwt e = GwTEdge e (appl (src gwt) e) (appl (tgt gwt) e) (appl (fE gwt) e)
consEdges gwt = foldr (\e es'->(consEdge gwt e):es') [] (es gwt)

consNode n nty = GwTNode n nty
consNodes gwt = foldr (\n ns'->(consNode n (appl (fV gwt) n)):ns') [] (ns gwt)
consGwTDrawingDesc gwt = GwTDrawing (consNodes gwt) (consEdges gwt)

wrEdgeSettings nm ety = "[" ++ (wrEdgeSettings' (tail nm) ety) ++ "];"
wrEdgeSettings' enm ety = "label=\""++enm++ " :" ++ ety ++ "▼\",arrowhead=vee"
wrEdge (GwTEdge nm s t ety) = "\"" ++ s ++ "\"->\"" ++ t ++ "\"" ++ (wrEdgeSettings nm ety)
wrEdges es  = foldr (\e es'-> (wrEdge e)++ "\n" ++es') "" es 

wrNode (GwTNode nm nty) =  "\"" ++ nm ++ "\"" ++"[shape=box,fillcolor=lightskyblue1,style = filled,label=\""++nm++" : " ++ nty ++ "\"];"
wrNodes ns  = foldr (\n ns'-> (wrNode n)++ "\n" ++ns') "" ns

wrGwTGraphvizDesc::String->GwTDrawing->String
wrGwTGraphvizDesc nm (GwTDrawing ns es) = 
   let intro = "digraph {graph[label=" ++ nm ++ ",labelloc=tl,labelfontsize=12];\n" in
   let end = "}" in
   intro ++ (wrNodes ns) ++ "\n" ++ (wrEdges es) ++ end

wrGwTAsGraphviz nm gwt = wrGwTGraphvizDesc nm $ consGwTDrawingDesc gwt