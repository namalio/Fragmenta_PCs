module Utils(transToStr, check_wf_of, evalExpectation, print_g_wf_msg, option_main_save) where

import ErrorAnalysis
import System.Environment
import Control.Monad(when)

transToStr ss sep = foldl (\ss s->if null ss then (show s) else (show s)++sep++ss) "" ss


check_wf_of s nm wf_f errs_f = 
    if wf_f s then nile else cons_et (nm++" is malformed. ") (errs_f s)

evalExpectation e r = if e == r then "Ok" else "Fail"

print_g_wf_msg g_id errs = 
   if null errs 
      then putStrLn $ g_id ++ " is well formed" 
      else putStrLn $ show (unlines errs) 

option_main_save mainp sdsp = do
   args <- getArgs
   mainp
   when (not $ null args) $ do
      if args == ["-g"]
         then sdsp
         else putStrLn "Invalid option"