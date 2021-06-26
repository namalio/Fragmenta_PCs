module FrParsing (loadFragment, loadSG) where

import Sets
import Relations
import Grs
import SGrs
import Frs
import Text.ParserCombinators.ReadP
import Control.Applicative hiding (many)
import The_Nil
import MyMaybe
import CommonParsing
import SGElemTys
import Mult

-- An edge definition has an optional name, a source and a target node (Strings), an edge type, and two optional multiplicities
data EdgeDef = EdgeDef String String String SGETy (Maybe Mult) (Maybe Mult)
   deriving(Eq, Show)
-- A Node has a name and a type
data NodeDef = NodeDef String SGNTy 
   deriving(Eq, Show)
-- Representative of an enumeration cluster: a enum name and its values
data ClEnum = ClEnum String [String]
   deriving(Eq, Show)
data SGElem = ElemN NodeDef | ElemE EdgeDef  | ElemClE ClEnum 
-- | ElemComment String
   deriving(Eq, Show)
data SGDef = SGDef String [SGElem] 
   deriving(Eq, Show)
-- A proxy reference links a proxy to some node
data ProxyRef = ProxyRef String String 
   deriving(Eq, Show)
-- A fragment definition has a name, a SG, and a list of proxy refenrences
data FrDef = FrDef String SGDef [ProxyRef] 
   deriving(Eq, Show)

sgd_name (SGDef nm _) = nm

frd_sg_def (FrDef _ sgd _) = sgd

frd_fname::FrDef->String
frd_fname (FrDef fnm _ _) = fnm

ext_mult_t::String->Maybe Mult->[(String, Mult)]
ext_mult_t e Nothing = [(e, Sm $ Val 1)]
ext_mult_t e (Just m) = [(e, m)]

ext_mult_s::String->Maybe Mult->[(String, Mult)]
ext_mult_s _ Nothing = []
ext_mult_s e (Just m) = [(e, m)]


extract_elem::SGElem->SGr String
extract_elem (ElemN (NodeDef n nty)) = cons_sg (cons_g [n] [] [] []) [(n, nty)] [] [] []
extract_elem (ElemE (EdgeDef e s t ety om1 om2)) = 
   let e' = nm_of_edge ety e s t in 
   let sm = ext_mult_s e' om1 in
   let tm = ext_mult_s e' om2 in
   cons_sg (cons_g [s, t] [e'] [(e', s)] [(e', t)]) [] [(e', ety)] sm tm
   where nm_of_edge Einh _ s t = "EI" ++ s ++ "_" ++ t
         nm_of_edge _ enm s t = "E"++ (if null enm then s ++ "_" ++ t else enm)
extract_elem (ElemClE (ClEnum ne vs)) = 
   let f_nty = (ne, Nenum):(map (\v->(v, Nval)) vs) in
   let f_ety = (map (\v->("EI"++v, Einh)) vs) in
   cons_sg (cons_g (ne:vs) (map (\v->"EI"++v) vs) (map (\v->("EI"++v, v)) vs) (map (\v->("EI"++v, ne)) vs)) f_nty f_ety [] []

extract_sg::[SGElem]->SGr String
extract_sg es = foldl (\sg e-> sg `union_sg` (extract_elem e)) empty_sg es

--extract_sg ((ElemN (NodeDef n nty)):es) = (cons_sg (cons_g [n] [] [] []) [(n, nty)] [] [] []) `union_sg` (extract_sg es)
--extract_sg ((ElemE (EdgeDef e s t ety om1 om2)):es) = 
--   let e' = nm_of_edge ety e s t in 
--   let sm = ext_mult_s e' om1 in
--   let tm = ext_mult_s e' om2 in
--   (cons_sg (cons_g [s, t] [e'] [(e', s)] [(e', t)]) [] [(e', ety)] sm tm)  `union_sg` (extract_sg es)
--   where nm_of_edge Einh _ s t = "EI" ++ s ++ "_" ++ t
--         nm_of_edge _ enm s t = "E"++ (if null enm then s ++ "_" ++ t else enm)
--extract_sg ((ElemClE (ClEnum s v)):es) = 

cons_sg_fr_sgd::SGDef->SGr String
cons_sg_fr_sgd (SGDef _ elems) = extract_sg elems

t_union::(Eq a, Eq b, Eq c)=>([a], [b], [c])->([a], [b], [c])->([a], [b], [c])
t_union (e1a, e2a, e3a) (e1b, e2b, e3b) = (e1a `union` e1b, e2a `union` e2b, e3a `union` e3b)

ext_proxy_refs::[ProxyRef]->([String], [(String, String)], [(String, String)])
ext_proxy_refs [] = ([], [], [])
ext_proxy_refs ((ProxyRef p r):prs) = (["E"++p], [("E"++p, p)], [("E"++p, r)]) `t_union` (ext_proxy_refs prs)

cons_fr_fr_frd::FrDef->Fr String
cons_fr_fr_frd (FrDef _ sgd prs ) = 
   let (esr, s, t) = ext_proxy_refs prs in
   cons_f (cons_sg_fr_sgd sgd) esr s t

parse_fin_node::SGNTy->ReadP NodeDef
parse_fin_node nty= do
   nm<-parse_id
   skipSpaces
   return (NodeDef nm nty)

parse_nodea::ReadP NodeDef
parse_nodea = do
   string "nodea"
   skipSpaces
   n<-parse_fin_node Nabst
   return n

parse_noden::ReadP NodeDef
parse_noden = do
   string "node"
   skipSpaces
   n<-parse_fin_node Nnrml
   return n

parse_proxy::ReadP NodeDef
parse_proxy = do
   string "proxy"
   skipSpaces
   n<-parse_fin_node Nprxy
   return n

parse_nvirt::ReadP NodeDef
parse_nvirt = do
   string "virtual"
   skipSpaces
   n<-parse_fin_node Nvirt
   return n

parse_nopt::ReadP NodeDef
parse_nopt = do
   string "opt"
   skipSpaces
   n<-parse_fin_node Nopt
   return n

parse_sg_node::ReadP NodeDef
parse_sg_node = do
   n<-parse_noden <|> parse_nodea <|> parse_proxy <|>  parse_nvirt <|> parse_nopt 
   return n

parse_edge_name::ReadP String
parse_edge_name = do
   nm<-(between (char '[') (char ']') parse_id) <++ (return "")
   return nm

parse_mult_many::ReadP MultVal
parse_mult_many = do
   char '*'
   return (Many)

parse_mult_val::ReadP MultVal
parse_mult_val = do
   n<-parse_number
   return (Val $ read n)

parse_smult::ReadP MultVal
parse_smult = do
   m<-parse_mult_many <|> parse_mult_val
   return m

parse_range_mult::ReadP Mult
parse_range_mult = do
   n<-parse_number
   skipSpaces
   string ".."
   skipSpaces
   m<-parse_smult
   skipSpaces
   return (Rm (read n) m)

parse_single_mult::ReadP Mult
parse_single_mult = do
   m<-parse_smult
   skipSpaces
   return (Sm m)

parse_mult::ReadP Mult
parse_mult = do
   m<-parse_range_mult <|> parse_single_mult
   return m

parse_edge_info::ReadP(String, String, String)
parse_edge_info = do
   sn<-parse_id 
   skipSpaces
   string "->"
   skipSpaces
   tn<-parse_id
   skipSpaces
   enm<-parse_edge_name
   skipSpaces
   return (sn, tn, enm)


parse_rel_::SGETy->ReadP EdgeDef
parse_rel_ ek = do
   (sn, tn, enm)<-parse_edge_info
   char ':'
   skipSpaces
   m1<-parse_mult
   skipSpaces
   char ','
   skipSpaces
   m2<-parse_mult
   skipSpaces
   return (EdgeDef enm sn tn ek (Just m1) (Just m2))

parse_rel::ReadP EdgeDef
parse_rel = do
   string "rel"
   skipSpaces
   ed<-parse_rel_ (Erel Dbi)
   return ed

parse_opt_mult::ReadP Mult
parse_opt_mult = do
   char ':'
   skipSpaces
   m<-parse_mult
   return m

parse_rel_uni::SGETy->ReadP EdgeDef
parse_rel_uni ety = do
   (sn, tn, enm)<-parse_edge_info
   m<-parse_opt_mult <++ return (Sm $ Val 1)
   skipSpaces
   return (EdgeDef enm sn tn ety Nothing (Just m))

parse_relu::ReadP EdgeDef
parse_relu = do
   string "relu"
   skipSpaces
   ed<-parse_rel_uni (Erel Duni)
   return ed

parse_wander::ReadP EdgeDef
parse_wander = do
   string "wander"
   skipSpaces
   (sn, tn, enm)<-parse_edge_info
   return (EdgeDef enm sn tn Ewander (Just msole_many) (Just msole_many))


parse_compu::ReadP EdgeDef
parse_compu = do
   string "compu"
   skipSpaces
   ed<-parse_rel_uni (Ecomp Duni)
   return ed

parse_comp::ReadP EdgeDef
parse_comp = do
   string "comp"
   skipSpaces
   ed<-parse_rel_ (Ecomp Dbi)
   return ed

parse_inh::ReadP EdgeDef
parse_inh = do
   string "inh"
   skipSpaces
   sn<-parse_id 
   skipSpaces
   string "->"
   skipSpaces
   tn<-parse_id
   skipSpaces
   return (EdgeDef "" sn tn Einh Nothing Nothing)

parse_sg_edge::ReadP EdgeDef
parse_sg_edge = do
   e <- parse_rel <|> parse_relu  <|> parse_wander  <|> parse_comp  <|> parse_compu  <|> parse_inh 
   return e


end_of_sep_term::ReadP ()
end_of_sep_term = do
   char ',' <|> char '\n'
   skipSpaces
   return ()

parse_enum::ReadP ClEnum
parse_enum = do
   string "enum"
   skipSpaces
   nm<-parse_id
   skipSpaces
   char ':'
   skipSpaces
   vals<-endBy (parse_id) (end_of_sep_term)
   skipSpaces
   return (ClEnum nm vals)

parse_sg_elemN::ReadP SGElem
parse_sg_elemN = do
   n<-parse_sg_node
   return (ElemN n)

parse_sg_elemE::ReadP SGElem
parse_sg_elemE = do
   e<-parse_sg_edge
   return (ElemE e)

parse_sg_enumE::ReadP SGElem
parse_sg_enumE = do
   e<-parse_enum
   return (ElemClE e)

--parse_sg_comment::ReadP SGElem
--parse_sg_comment = do
--   string "--"
--   s<-parse_until_cr
--   return (ElemComment s)

parse_sg_elem::ReadP SGElem
parse_sg_elem = do
   skipSpaces
   e<-parse_sg_elemN <|> parse_sg_elemE <|> parse_sg_enumE -- <|> parse_sg_comment
   return e

parse_sg::ReadP SGDef
parse_sg = do
   string "SG"
   skipSpaces
   sg_nm<-parse_id
   skipSpaces
   elems<-between (char '{') (char '}') (many parse_sg_elem) 
   return (SGDef sg_nm elems)

parseProxyRef::ReadP ProxyRef
parseProxyRef = do
   string "ref"
   skipSpaces
   pnm<-parse_id
   skipSpaces
   string "->"
   skipSpaces
   nnm<-parse_id
   skipSpaces
   return (ProxyRef pnm nnm)

parse_fr :: ReadP FrDef
parse_fr = do
   string "fragment"
   skipSpaces
   fnm<-parse_id
   skipSpaces
   char '{'
   skipSpaces
   sg<-parse_sg
   skipSpaces
   elems<-manyTill parseProxyRef (char '}')
   return (FrDef fnm sg elems)

--parseFr ls = 
--   let (pcnm, st) = splitAt'(\c->c=='@') $ snd $ splitAt' (\c->c==' ')(head ls) in 
--   let elems = parseTo parseElem (tail ls) in
--   PCDef pcnm st elems



loadFrDefFrFile :: FilePath -> IO (Maybe FrDef)
loadFrDefFrFile fn = do   
    contents <- readFile fn
    let fr = parseMaybe parse_fr contents
    return fr

loadSGDefFrFile :: FilePath -> IO (Maybe SGDef)
loadSGDefFrFile fn = do   
    contents <- readFile fn
    let sg = parseMaybe parse_sg contents
    return sg

test_sg = "SG SG_Person1 {\n"
   ++ "node Person\n"
   ++ "node Hotel\n"
   ++ "node City\n"
   ++ "node Vehicle\n"
   ++ "rel Hotel->Person[Hosts]: 1,*\n"
   ++ "relu Person->City[lives]: 1\n"
   ++ "rel Person->Vehicle[Owns]:1,*\n"
   ++ "}"


loadFragment :: FilePath -> IO (Maybe (String, (Fr String)))
loadFragment fn = do
   fr_def<-loadFrDefFrFile fn
   --return (toMaybeP (appl_f_M frd_fname fr_def) (appl_f_M cons_fr_fr_frd fr_def))
   ofr <- if isNil fr_def 
      then do
         putStrLn "Fragment definition could not be parsed"
         return (Nothing)
      else do
         let frd = the fr_def
         return(Just (frd_fname frd,cons_fr_fr_frd frd)) -- This as a function here.
   return ofr 

loadSG :: FilePath -> IO (Maybe (String, (SGr String)))
loadSG fn = do
   sg_def<-loadSGDefFrFile fn
   --return (toMaybeP (appl_f_M sgd_name sg_def) (appl_f_M cons_sg_fr_sgd sg_def))
   osg <- if isNil sg_def 
      then do
         putStrLn "SG definition could not be parsed"
         return (Nothing)
      else do
         let sgd = the sg_def
         return(Just (sgd_name sgd, cons_sg_fr_sgd sgd))
   return osg

test1 = do
   fr<-loadFragment "Tests/f_Person1.fr"
   putStrLn $ show fr

test2 = do
   sg<-loadSG "Tests/SG_Employee_Car.sg"
   putStrLn $ show sg

test3 = readP_to_S parse_rel "rel Pet->POther[AnyRel1]: *,*"
test4 = readP_to_S parse_sg test_sg

