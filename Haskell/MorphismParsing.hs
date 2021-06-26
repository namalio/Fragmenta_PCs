module MorphismParsing (loadMorphism) where

import Relations
import Grs
import Text.ParserCombinators.ReadP
import Control.Applicative hiding (many)
import The_Nil
import MyMaybe
import CommonParsing

-- A Node mapping maps a node onto another
data NodeMapping = NodeMapping String String
   deriving(Eq, Show)
-- A Edge mapping maps an edge onto another
data EdgeMapping = EdgeMapping String String
   deriving(Eq, Show)
-- A morphism definition has a name, and two collections of node and edge mappings, respectively
data MorphismDef = MorphismDef String [NodeMapping] [EdgeMapping]
   deriving(Eq, Show)

morphD_name::MorphismDef->String
morphD_name (MorphismDef nm _ _) = nm

cons_morph_md::MorphismDef->GrM String
cons_morph_md (MorphismDef _ nms ems) = cons_gm (extract_node_pairs nms) (extract_edge_pairs ems)

extract_pair_fr_nm::NodeMapping->(String, String)
extract_pair_fr_nm (NodeMapping n1 n2) = (n1, n2) 

extract_pair_fr_em::EdgeMapping->(String, String)
extract_pair_fr_em (EdgeMapping e1 e2) = (e1, e2) 

extract_node_pairs::[NodeMapping]->[(String, String)]
extract_node_pairs nms = foldr (\nm lps-> (extract_pair_fr_nm nm):lps) [] nms

extract_edge_pairs::[EdgeMapping]->[(String, String)]
extract_edge_pairs ems = foldr (\em lps-> (extract_pair_fr_em em):lps) [] ems


parse_map::ReadP (String, String)
parse_map = do
   nm1<-parse_id
   skipSpaces
   string "->"
   skipSpaces
   nm2<-parse_id
   skipSpaces
   return ((nm1, nm2))

parse_nodeM::ReadP NodeMapping
parse_nodeM = do
   skipSpaces
   (nm1, nm2)<-parse_map
   return (NodeMapping nm1 nm2)

parse_edgeM::ReadP EdgeMapping
parse_edgeM = do
   skipSpaces
   (nm1, nm2)<-parse_map
   return (EdgeMapping ("E"++nm1) ("E"++nm2))

--map_sep::ReadP ()
--map_sep = do
--   char '\n'
--   skipSpaces
--   return ()

parse_nodeMappings::ReadP [NodeMapping]
parse_nodeMappings = do
   string "nodes"
   skipSpaces
   nms<-between (char '{') (char '}') (many parse_nodeM) 
   return (nms)

parse_edgeMappings::ReadP [EdgeMapping]
parse_edgeMappings = do
   string "edges"
   skipSpaces
   ems<-between (char '{') (char '}') (many parse_edgeM) 
   return (ems)

parse_morphism::ReadP MorphismDef
parse_morphism = do
   string "Morphism"
   skipSpaces
   m_nm<-parse_id
   skipSpaces
   char '{'
   skipSpaces
   nms<-parse_nodeMappings
   skipSpaces 
   ems<-parse_edgeMappings
   skipSpaces 
   char '}'
   skipSpaces
   return (MorphismDef m_nm nms ems)

loadMorphDefFrFile :: FilePath -> IO (Maybe MorphismDef)
loadMorphDefFrFile fn = do   
    contents <- readFile fn
    let m = parseMaybe parse_morphism contents
    return m

loadMorphism :: FilePath -> IO (Maybe (String, (GrM String)))
loadMorphism fn = do
   m_def<-loadMorphDefFrFile fn
   --return (toMaybeP (appl_f_M sgd_name sg_def) (appl_f_M cons_sg_fr_sgd sg_def))
   om <- if isNil m_def 
      then do
         putStrLn $ "Morphism definition of file '" ++fn++ "' could not be parsed"
         return (Nothing)
      else do
         let md = the m_def
         return(Just (morphD_name md, cons_morph_md md))
   return om

test1 = do
   m<-loadMorphism "Tests/m_Employee_Car.gm"
   putStrLn $ show m

test2 = readP_to_S parse_edgeMappings "edges {A->B B->C}"
test3 = readP_to_S parse_morphism "Morphism A {\n nodes{A->B}\n edges {C->D\nD->E}}"
test4 = readP_to_S parse_morphism "Morphism M_Employee_Car {\n\tnodes {\n\t   Employee->Employee\n\t   Car->Car\n\t}\n\tedges {\n\t   Owns->Owns\n\t   ICar_Car->ICar_Car\n\t   IEmployee_Employee->IEmployee_Employee\n\t}\n}"
test5 = readP_to_S parse_morphism "Morphism F_MM_4 {\n\tnodes {\n\t\tOperatorVal->Attribute\n\t\tOpChoice->Attribute\n\t\tOpParallel->Attribute\n\t\tOpIf->Attribute\n\t\tOpInterleave->Attribute\n\t\tOpThrow->Attribute\n\t}\n\tedges {}\n}\n"

test6 = do
   contents <- readFile "PCs/F_MM_4.gm"
   putStrLn $ show contents
