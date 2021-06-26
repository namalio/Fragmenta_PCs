module FrUtils(load_check_draw, load_check_fr) where

import Frs
import FrParsing
import Utils
import DrawUtils
import Grs
import Control.Monad(when)
import LsFuns
import SGsDraw

check_fr fnm k f= do
   let errs = check_wf fnm (Just Total) f 
   if null errs
      then do
         putStrLn "Fragment is well formed!"
      else
         putStrLn $ "Fragment is malformed:" ++ (transToStr errs "\n")

load_check_draw::FilePath->FilePath-> IO ()
load_check_draw fn img_path = do
   ofr<-loadFragment fn
   when (not . isNil $ ofr) $ do
      let (Just (fnm, f)) = ofr
      let errs = check_wf fnm (Just Partial) f 
      if null errs
         then do
            putStrLn "Fragment is well formed!"
            saveFrDrawing img_path fnm f 
         else
            putStrLn $ "Fragment is malformed:" ++ (transToStr errs "\n")


load_check_fr::FilePath->IO(Maybe (String, Fr String))
load_check_fr fn = do
   ofr <-loadFragment fn
   ofr'<- if (isNil $ ofr)
             then return Nothing
             else do
                let (fnm, f) = theM ofr   
                let errs = check_wf fnm (Just Partial) f 
                return (if null errs then ofr else Nothing)
   return ofr'