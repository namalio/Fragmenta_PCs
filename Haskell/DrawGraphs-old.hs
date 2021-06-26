
module DrawGraphs(checkAndSaveSGDraw, saveSGDrawing, saveFrDrawing, saveGDrawing, saveGwTDrawing, saveGFGrawing) where

import Gr_Cls
import SGrs
import SGsDraw
import GrsDraw
import GwTDraw
import FrsDraw
import Utils
import ErrorAnalysis

saveSGDrawing path nm sg = do
   putStrLn "Writing the GraphViz file" 
   let draw_src = wrSGGraphvizDesc nm StandAlone (consSGDrawingDesc sg)
   writeFile (path ++ nm ++ ".gv") draw_src

-- checkAndSaveSGDraw path nm sg t = do
--    let errs = check_wf nm (Just t) sg
--    if errs == nile
--      then saveSGDrawing path nm sg
--      else putStrLn $ show_err errs

saveFrDrawing path nm f = do
   putStrLn "Writing GraphViz file" 
   let draw_src = wrFrGraphvizDesc StandAlone (consFrDrawingDesc nm f) 
   writeFile (path ++ nm ++ ".gv") draw_src

saveGDrawing path nm g = do
   putStrLn "Writing the graph's GraphViz file..." 
   let draw_src = wrGAsGraphviz nm g
   writeFile (path ++ nm ++ ".gv") draw_src

saveGwTDrawing path nm gwt = do
   putStrLn "Writing the graph's GraphViz file..." 
   let draw_src = wrGwTAsGraphviz nm gwt
   writeFile (path ++ nm ++ ".gv") draw_src

saveGFGrawing path nm f = do
   putStrLn "Writing GraphViz file" 
   let draw_src = wrGFGAsGraphviz nm f 
   writeFile (path ++ nm ++ ".gv") draw_src