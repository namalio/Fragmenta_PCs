module CheckUtils(check_report_wf, check_morphism, check_ty_morphism, show_typing_msg, show_wf_msg) where

import Gr_Cls
import Grs
import SGrs
import Utils
import Frs
import ShowUtils
import ErrorAnalysis

show_wf_msg g_id errs = do
   if is_nil errs 
      then putStrLn $ g_id ++ " is well formed" 
      else putStrLn $ g_id ++ " is mal-formed\n" ++  (show_err errs) 

report_errs id errs b = do
   if is_nil errs
      then putStrLn $ id ++ " is well formed (" ++ (evalExpectation b True) ++ ")"
      else putStrLn $ "(" ++ (evalExpectation b False) ++ ") " ++ id ++ " is mal-formed\n" ++ (show_err errs) 

check_report_wf id otk g b = do
   let errs = check_wf id otk g 
   report_errs id errs b

check_morphism::(Eq a, Show a, GM_CHK g g')=>String->Maybe MK->g a->GrM a->g' a->Bool->IO()
check_morphism id omk gs m gt b = do 
   let errs = check_wf_gm id omk (gs, m, gt) 
   report_errs id errs b

check_ty_morphism id omk gwt sg b = do 
   let errs = check_wf_gm' id omk (gwt, sg) 
   report_errs id errs b

show_typing_msg errs = 
   if is_nil errs
      then putStrLn "The PC is well-typed."
      else putStrLn $ "The PC is not well-typed:\n" ++ (show_err errs) 

--check_instance_morphism_strong id om gwt sg b = do
--   let errs = check_wf_gm' id (Just PartialM) (gwt, sg) 
--   report_errs id errs b

--check_report_f_wf id f m b = 
--   let errs = check_wf_fr f m id in
--   if null errs
--      then putStrLn $ "Fragment " ++ id ++ " is well formed (" ++ (evalExpectation b True) ++ ")"
--      else putStrLn $ "(" ++ (evalExpectation b False) ++ ") " ++ (transToStr errs ".")

--check_f_morphism id gm fs ft m b  = 
--   let errs = check_wf_gm_frs gm fs ft m id in
--   if null errs 
--      then putStrLn $ id ++ " is well formed (" ++ (evalExpectation b True) ++ ")"
--      else putStr $ "(" ++ (evalExpectation b False) ++ ")" ++ (transToStr errs ".")

--check_f_typing id gm fs ft m b = 
--   let errs = check_wf_ty_frs gm fs ft id m in
--   if null errs
--      then putStrLn $ id ++ " is well typed (" ++ (evalExpectation b True) ++ ")"
--      else putStr $ "(" ++ (evalExpectation b False) ++ ")" ++ (transToStr errs ".")

--check_f_typing_ref id gm fs ft b = 
--   let errs = check_wf_ty_frs_ref gm fs ft id in
--   if null errs
--      then putStrLn $ id ++ " is well typed (" ++ (evalExpectation b True) ++ ")"
--      else putStr $ "(" ++ (evalExpectation b False) ++ ")" ++ (transToStr errs ".")