
module FrsDraw (wrFrGraphvizDesc, buildFrDrawingDesc) where

import SGsDraw
import Frs

data FrREdge = FrREdge String String String deriving(Show)
data FrDrawing = FrDrawing String SGDrawing [SGEdge] deriving(Show) 

consEdge f e = FrREdge e (appl (sr f) e) (appl (tr f) e)
consEdges f = foldr (\e es'->(consEdge f e):es') [] (esr f)
buildFrDrawingDesc nm f = FrDrawing nm (buildSGDrawingDesc $ sg f) (consEdges f)


wrEdge (FrREdge nm s t) = "\"" ++ s ++ "\"->\"" ++ t ++ "\"" ++ "[arrowhead=normalnormal];"
wrEdges es  = foldr (\e es'-> (wrEdge e)++ "\n" ++es') "" es 
wrFrGraphvizDesc (FrDrawing nm sgd esr) = 
   let stCluster = "subgraph{style=dashed,label="++nm++"; in
   let endCluster = "\n}" in
   "digraph {graph[label=" ++ nm ++ ",labelloc=tl,labelfontsize=12];\n" ++ stCluster ++ (wrSGGraphvizDesc sgd False) ++ "\n" ++ (wrEdges esr) ++ endCluster ++ "}"