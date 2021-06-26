-------------------------
-- Project: PCs/Fragmenta
-- Module: 'GFGrParsing'
-- Description: Module responsible for parsing Fragmenta's Global Fragment Graphs (GFGs)
-- Author: Nuno Amálio
--------------------------
module GFGrParsing(loadGFG) where

import GFGrs
import Sets
import CommonParsing
import Text.ParserCombinators.ReadP
import Control.Applicative hiding (many)
import The_Nil
import MyMaybe

-- A GFG node element has a name 
-- A GFG reference discriminates a source and a target node (Strings)
data GFGElem = GFGN String | GFGR String String
   deriving(Eq, Show)
data GFGDef = GFGDef String [GFGElem] 
   deriving(Eq, Show)

gfgd_name (GFGDef nm _) = nm

-- Constructs a GFG from a set of nodes and a relation between nodes
cons_gfg'::([String], [(String, String)])->GFGr String
cons_gfg' (ns, r_refs) =
    let e_nm ns nt =  "E" ++ (show ns) ++ "_" ++ (show nt) in
    let combine ns nt (es, s, t) = ((e_nm ns nt):es, (e_nm ns nt, ns):s, (e_nm ns nt, nt):t) in
    let (es', s', t') = foldr (\(n_s, n_t) ces ->if [n_s, n_t] `subseteq` ns then combine n_s n_t ces else ces) ([], [], []) r_refs in
    cons_gfg ns es' s' t'

extract::[GFGElem]->([String], [(String, String)])
extract es = foldr (\e ap-> combine e ap) ([], []) es
   where combine (GFGN n_nm) (ns, r)  =  (n_nm:ns, r)
         combine (GFGR n_s n_t) (ns, r)  =  (ns, (n_s, n_t):r)

cons_gfg_fr_d::GFGDef->GFGr String
cons_gfg_fr_d (GFGDef _ elems ) = cons_gfg' . extract $ elems

parse_gfg_node::ReadP GFGElem
parse_gfg_node = do
    string "fragment"
    skipSpaces
    nm<-parse_id
    skipSpaces
    return (GFGN nm)

parse_gfg_ref::ReadP GFGElem
parse_gfg_ref = do
    sn<-parse_id 
    skipSpaces
    string "references"
    skipSpaces
    tn<-parse_id
    skipSpaces
    return (GFGR sn tn)

parse_gfg_elem::ReadP GFGElem
parse_gfg_elem = do
   skipSpaces
   e<-parse_gfg_node <|> parse_gfg_ref
   return e

parse_gfg::ReadP GFGDef
parse_gfg = do
   skipSpaces
   string "GFG"
   skipSpaces
   g_nm<-parse_id
   skipSpaces
   elems<-between (char '{') (char '}') (many parse_gfg_elem)
   return (GFGDef g_nm elems)

loadGFGDefFrFile :: FilePath -> IO (Maybe GFGDef)
loadGFGDefFrFile fn = do   
    contents <- readFile fn
    let g = parseMaybe parse_gfg contents
    return g

test_gfg = "GFG A_B{\n"
   ++ "fragment FA\n"
   ++ "fragment FB\n"
   ++ "FA references FB\n"
   ++ "}"


loadGFG:: FilePath -> IO (Maybe (String, (GFGr String)))
loadGFG fn = do
    g_def<-loadGFGDefFrFile fn
    --return (toMaybeP (appl_f_M sgd_name sg_def) (appl_f_M cons_sg_fr_sgd sg_def))
    if isNil g_def 
        then do
            putStrLn "Global gragment graph definition on file  could not be parsed"
            return (Nothing)
        else do
            let gd = the g_def
            return(Just (gfgd_name gd, cons_gfg_fr_d gd))

test1 = readP_to_S parse_gfg test_gfg
test2 = loadGFGDefFrFile "Tests/GFGTests/gfg_felines.gfg"
test3 = loadGFGDefFrFile "PCs/MM/PCs_AMM.gfg"