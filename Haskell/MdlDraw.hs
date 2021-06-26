
module MdlDraw (wrMdlAsGraphviz) where

import Mdls
import FrsDraw
import SGsDraw

data MdlDrawing = MdlDrawing String [FrDrawing] deriving(Show) 

consMdlDrawingDesc nm mdl = MdlDrawing nm (map (\(fnm, f)-> consFrDrawingDesc fnm f) (mfd mdl))

wrMdlGraphvizDesc (MdlDrawing nm fds) = 
   "digraph {graph[label=" ++ nm ++ ",labelloc=tl,labelfontsize=12];\n" ++ (foldr (\fd ds-> (wrFrGraphvizDesc PartOf fd) ++ ds) "" fds) ++ "}"

wrMdlAsGraphviz nm mdl = wrMdlGraphvizDesc . consMdlDrawingDesc nm $ mdl