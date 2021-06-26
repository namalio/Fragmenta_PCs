
module LoadCheckDraw(load_def, draw_to_file, wrapSG, wrapG, unwrapG, unwrapSG, unwrapSGWithinP, draw_def, draw_mdl, load_sg_def,
    load_g_def, load_gwt_def, load_fr_def, load_morphism_def, load_gfg_def, load_mdl_def, load_rm_cmdl_def, saveSGDrawing, saveFrDrawing, 
    saveGDrawing, saveGwTDrawing, saveGFGDrawing, saveDrawingWithMdlFrs) 
where

import Gr_Cls
import GrParsing
import GwTParsing
import GFGrParsing
import GrsDraw
import SGsDraw
import FrsDraw
import GwTDraw
import GFGrsDraw
import Grs 
import GFGrs 
import Frs 
import GrswT
import SGrs
import ParseUtils
import The_Nil
import MyMaybe
import FrParsing
import Control.Monad(forM, forM_, when)
import MorphismParsing
import MdlDraw
import Mdls
import Relations

data GKind = Graph | SG | GwT | Fr | GFG
    deriving (Eq, Show)

type PossibleG a = Either (Gr a) (Either (SGr a) (Either (GrwT a) (Either (Fr a) (GFGr a))))
--    deriving (Eq, Show)

wrapG g = Left g
wrapSG g = Right $ Left g
wrapGwT g = Right (Right $ Left g)
wrapFr g = Right (Right (Right $ Left g))
wrapGFG g = Right (Right (Right $ Right g))

pg_kind (Left _) = Graph
pg_kind (Right (Left _)) = SG
pg_kind (Right (Right (Left _))) = GwT
pg_kind (Right (Right (Right (Left _)))) = Fr
pg_kind (Right (Right (Right (Right _)))) = GFG

unwrapG (Left g) = g
unwrapSG (Right (Left sg)) = sg
unwrapGwT (Right (Right (Left gwt))) = gwt
unwrapFr (Right (Right (Right (Left fr)))) = fr
unwrapGFG (Right (Right (Right (Right gfg)))) = gfg

unwrapGWithinP (Just (nm, pg)) = (nm, unwrapG pg)
unwrapSGWithinP (Just (nm, pg)) = (nm, unwrapSG pg)
unwrapGwTWithinP (Just (nm, pg)) = (nm, unwrapGwT pg)
unwrapFrWithinP (Just (nm, pg)) = (nm, unwrapFr pg)
unwrapGFGWithinP (Just (nm, pg)) = (nm, unwrapGFG pg)

load_gen path fnm load wrap = do 
    o_g<-load $ path ++ fnm 
    if isSomething o_g
      then do 
        let Just (nm_g, g) = o_g
        return $ Just (nm_g, wrap g)
      else return Nothing

def_kind fnm =
    let (_, ext) = splitAtStr "." fnm in
    case ext of
        "g" -> Graph
        "sg" -> SG
        "gwt" -> GwT
        "fr" -> Fr
        "gfg" -> GFG

load_def path fnm = do
    d<-case (def_kind fnm) of
        Graph -> load_gen path fnm loadGraph wrapG
        SG -> load_gen path fnm loadSG wrapSG
        GwT -> load_gen path fnm loadGwT wrapGwT
        Fr -> load_gen path fnm loadFragment wrapFr
        GFG -> load_gen path fnm loadGFG wrapGFG
    return d

load_sg_def path fnm = do 
    d<- load_def path fnm
    let (nm, sg) = unwrapSGWithinP d
    return (nm, sg)

load_g_def path fnm = do 
    d<- load_def path fnm
    let (nm, g) = unwrapGWithinP d
    return (nm, g)

load_gwt_def path fnm = do 
    d<- load_def path fnm
    let (nm, g) = unwrapGwTWithinP d
    return (nm, g)

load_fr_def path fnm = do 
    d<- load_def path fnm
    let (nm, g) = unwrapFrWithinP d
    return (nm, g)

load_gfg_def path fnm = do 
    d<- load_def path fnm
    return (unwrapGFGWithinP d)

load_mdl_def path nm = do 
    (_, gfg)<-load_gfg_def path (nm ++ ".gfg")
    fd <- forM (ns gfg) (\fn-> do
        (_, f)<-load_fr_def path (fn ++ ".fr")
        return (fn, f))
    return $ cons_mdl gfg fd

load_rm_cmdl_def path nm = do 
    (_, gfg)<-load_gfg_def path (nm ++ ".gfg")
    mds <- forM (ns gfg) (\fn-> do
        (_,m)<-load_morphism_def path (fn ++ ".gm")
        return m)
    return $ union_gms mds

load_morphism_def path fnm = do
    om1<-loadMorphism $ path ++ fnm
    return (the om1)

draw_def dpath ipath fnm = do
    d<-load_def dpath fnm 
    when (isSomething d) $ do
        let (nm, pg) = the $ d
        draw_to_file ipath nm pg

draw_to_file::String->String->PossibleG String->IO()
draw_to_file path nm pg = do
    case (pg_kind pg) of
        Graph->saveGDrawing path nm $ unwrapG pg
        SG ->saveSGDrawing path nm $ unwrapSG pg
        GwT->saveGwTDrawing path nm $ unwrapGwT pg
        Fr -> saveFrDrawing path nm $ unwrapFr pg
        GFG -> saveGFGDrawing path nm $ unwrapGFG pg

draw_mdl dpath ipath mnm = do
    mdl<-load_mdl_def dpath mnm
    saveGFGDrawing ipath (mnm ++ "_gfg") (mgfg mdl)
    forM_ (ns . mgfg $ mdl) (\fn-> do 
        saveFrDrawing ipath (fn) $ appl (mfd mdl) fn)
    let ufs = mufs mdl
    saveFrDrawing ipath (mnm ++ "_uf") ufs
    let rf = reso_m mdl
    saveFrDrawing ipath (mnm ++ "_rf") rf
    saveDrawingWithMdlFrs ipath mnm  mdl

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

saveGFGDrawing path nm gfg = do
   putStrLn "Writing GraphViz file" 
   let draw_src = wrGFGAsGraphviz nm gfg 
   writeFile (path ++ nm ++ ".gv") draw_src

saveDrawingWithMdlFrs path nm mdl = do
   let draw_src = wrMdlAsGraphviz nm mdl
   writeFile (path ++ nm ++ "_Mdl.gv") draw_src