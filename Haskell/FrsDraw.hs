
module FrsDraw (wrFrGraphvizDesc, consFrDrawingDesc, FrDrawing) where

import Relations
import SGsDraw
import Frs

data FrEdge = FrREdge String String String deriving(Show)
data FrDrawing = FrDrawing String SGDrawing [FrEdge] deriving(Show) 

consEdge f e = FrREdge e (appl (srcR f) e) (appl (tgtR f) e)
consEdges f = foldr (\e es'->(consEdge f e):es') [] (esR f)
consFrDrawingDesc nm f = FrDrawing nm (consSGDrawingDesc $ fsg f) (consEdges f)


wrPrxEdge (FrREdge nm s t) ns = if t `elem` ns then  "\"" ++ s ++ "\"->\"" ++ t ++ "\"" ++ "[arrowhead=normalnormal];" else ""
wrPrxEdges es ns  = foldr (\e es'-> (wrPrxEdge e ns)++ "\n" ++es') "" es 

wrFrGraphvizDesc::DrawPartKind->FrDrawing->String
wrFrGraphvizDesc dpk (FrDrawing nm sgd esr)  = 
   let stCluster = "subgraph cluster_" ++ nm ++ "{style=dashed;label="++nm++";\n" in
   let endCluster = "\n}\n" in
   let wrGrStart = "digraph {graph[label=" ++ nm ++ ",labelloc=tl,labelfontsize=12];\n" in
   let nodes = ls_of_node_names sgd in 
   (if is_so dpk then wrGrStart else "") ++ stCluster ++ (wrSGGraphvizDesc "" PartOf sgd) ++ endCluster ++ (wrPrxEdges esr nodes) ++ (if is_so dpk then "}" else "")