
import Gr_Cls
import Mdls 
import LoadCheckDraw
import CheckUtils
import Utils
import Grs
import SGrs
import Frs
import ShowUtils
import Sets

def_path = "PCs/MM/"
img_path = "PCs/MM/img/"
wr_path = "./"

saveDrawings = do
   draw_mdl def_path img_path "PCs_AMM"
   draw_mdl def_path img_path "PCs_MM"

check_AMM = do
    mdl<-load_mdl_def def_path "PCs_AMM"
    check_report_wf "PCs_AMM" (Just Total) mdl True

code_preamble = "module PCs_MM_Names (PCs_AMM_Ns(..), PCs_AMM_Es(..), PCs_CMM_Ns(..), PCs_CMM_Es(..), show_amm_n, show_amm_e, show_cmm_n, show_cmm_e\n"
    ++ "    , read_cmm)\n"
    ++ "where\n\n"
--code_concl = "data PCS_MM_Ns = AMMN PCs_AMM_Ns | CMMN PCs_CMM_Ns\n"
--    ++ "data PCS_MM_Es = AMME PCs_AMM_Es | CMME PCs_CMM_Es\n"
code_concl = "show_amm_n nt = drop 4 (show nt)\n"
    ++ "show_amm_e et = drop 4 (show et)\n"
    ++ "show_cmm_n nt = drop 4 (show nt)\n"
    ++ "show_cmm_e et = drop 4 (show et)\n"
    ++ "read_cmm x = read (\"CMM_\" ++ x)\n"


cons_data_type nm elems = "data " ++ nm ++ " = " ++ (showStrs elems " | ") ++ "\n    deriving (Read, Show, Eq)"

cons_MM_datatypes = do
    mdla<-load_mdl_def def_path "PCs_AMM"
    mdlc<-load_mdl_def def_path "PCs_MM"
    let ausg = fsg . mufs $ mdla
    let data_amm_ns = cons_data_type "PCs_AMM_Ns" (map ("AMM_" ++ ) $ ns ausg)
    let data_amm_es = cons_data_type "PCs_AMM_Es" (map ("AMM_" ++ ) $ es ausg `diff` esI ausg)
    let cusg = fsg . mufs $ mdlc
    let data_cmm_ns = cons_data_type "PCs_CMM_Ns" (map ("CMM_" ++ ) $ ns cusg)
    let data_cmm_es = cons_data_type "PCs_CMM_Es" (map ("CMM_" ++ ) $ es cusg `diff` esI cusg)
    let code = code_preamble ++ data_amm_ns ++ "\n\n" ++ data_amm_es ++ "\n\n" ++ data_cmm_ns ++ "\n\n" ++ data_cmm_es ++ "\n\n" ++ code_concl ++ "\n"
    writeFile (wr_path ++ "PCs_MM_Names.hs") code

check_MMs = do
    amdl<-load_mdl_def def_path "PCs_AMM"
    check_report_wf "PCs_AMM" (Just Total) amdl True
    mdl<-load_mdl_def def_path "PCs_MM"
    check_report_wf "PCs_MM" (Just Total) mdl True

check_morphisms = do
    (nm_af, af)<-load_fr_def def_path "F_AMM.fr"
    (nm_f1, f1)<-load_fr_def def_path "F_MM_1.fr"
    (nm_f2, f2)<-load_fr_def def_path "F_MM_2.fr"
    (nm_f3, f3)<-load_fr_def def_path "F_MM_3.fr"
    (nm_f4, f4)<-load_fr_def def_path "F_MM_4.fr"
    (nm_f5, f5)<-load_fr_def def_path "F_MM_5.fr"
    (nm_f6, f6)<-load_fr_def def_path "F_MM_6.fr"
    (nm_f7, f7)<-load_fr_def def_path "F_MM_7.fr"
    (nm_f8, f8)<-load_fr_def def_path "F_MM_8.fr"
    (nm_f9, f9)<-load_fr_def def_path "F_MM_9.fr"
    (nm_f10, f10)<-load_fr_def def_path "F_MM_10.fr"
    (nm_f11, f11)<-load_fr_def def_path "F_MM_11.fr"
    (nm_m1, m1)<-load_morphism_def def_path "F_MM_1.gm"
    (nm_m2, m2)<-load_morphism_def def_path "F_MM_2.gm"
    (nm_m3, m3)<-load_morphism_def def_path "F_MM_3.gm"
    (nm_m4, m4)<-load_morphism_def def_path "F_MM_4.gm"
    (nm_m5, m5)<-load_morphism_def def_path "F_MM_5.gm"
    (nm_m6, m6)<-load_morphism_def def_path "F_MM_6.gm"
    (nm_m7, m7)<-load_morphism_def def_path "F_MM_7.gm"
    (nm_m8, m8)<-load_morphism_def def_path "F_MM_8.gm"
    (nm_m9, m9)<-load_morphism_def def_path "F_MM_9.gm"
    (nm_m10, m10)<-load_morphism_def def_path "F_MM_10.gm"
    (nm_m11, m11)<-load_morphism_def def_path "F_MM_11.gm"
    check_report_wf nm_af (Just Total) af True
    check_report_wf nm_f1 (Just Partial) f1 True
    check_report_wf nm_f2 (Just Partial) f2 True
    check_report_wf nm_f3 (Just Partial) f3 True
    check_report_wf nm_f4 (Just Partial) f4 True
    check_report_wf nm_f5 (Just Partial) f5 True
    check_report_wf nm_f6 (Just Partial) f6 True
    check_report_wf nm_f7 (Just Partial) f7 True
    check_report_wf nm_f8 (Just Partial) f8 True
    check_report_wf nm_f9 (Just Partial) f9 True
    check_report_wf nm_f10 (Just Partial) f10 True
    check_report_wf nm_f11 (Just Partial) f11 True
    check_morphism (nm_m1 ++ " (Partial)") (Just PartialM) f1 m1 af True
    check_morphism (nm_m2 ++ " (Partial)") (Just PartialM) f2 m2 af True
    check_morphism (nm_m3 ++ " (Partial)") (Just PartialM) f3 m3 af True
    check_morphism (nm_m4 ++ " (Partial)") (Just PartialM) f4 m4 af True
    check_morphism (nm_m5 ++ " (Partial)") (Just PartialM) f5 m5 af True
    check_morphism (nm_m6 ++ " (Partial)") (Just PartialM) f6 m6 af True
    check_morphism (nm_m7 ++ " (Partial)") (Just PartialM) f7 m7 af True
    check_morphism (nm_m8 ++ " (Partial)") (Just PartialM) f8 m8 af True
    check_morphism (nm_m9 ++ " (Partial)") (Just PartialM) f9 m9 af True
    check_morphism (nm_m10 ++ " (Partial)") (Just PartialM) f10 m10 af True
    check_morphism (nm_m11 ++ " (Partial)") (Just PartialM) f11 m11 af True

check_models_ref = do
    amdl<-load_mdl_def def_path "PCs_AMM"
    cmdl<-load_mdl_def def_path "PCs_MM"
    rms<-load_rm_cmdl_def def_path "PCs_MM"
    check_report_wf "PCs_AMM" (Just Total) amdl True
    check_report_wf "PCs_MM" (Just Total) cmdl True
    check_morphism "Refinement of PCs_MM by PCs_AMM " (Just TotalM) cmdl rms amdl True


do_main = do
    check_models_ref

main = do
    option_main_save do_main saveDrawings
    cons_MM_datatypes