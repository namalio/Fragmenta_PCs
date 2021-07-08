
------------------
-- Project: PCs/Utils
-- Module: 'PCsUtils'
-- Description: Utilities module of PCs
-- Author: Nuno Amálio
-----------------
module PCsUtils(writeCSPToFile, checkWFAndGeneratePCTree, checkWF, optionsPCs, startPCOps, outputDrawing, outputCSP) where

import Gr_Cls
import PCs
import SGrs
import GrswT
import PCsCSP
import PCTrees
import CSPPrint
import System.IO
import Control.Monad(when, forM)
import PCsDraw
import PCsParsing
import Relations
import Sets
import SimpleFuns
import ErrorAnalysis
import CheckUtils
import The_Nil
import MyMaybe
import System.Environment

mm_path = "PCs/MM/"
pcs_path = "PCs/PCs/"
csp_path = "PCs/PCs/CSP/"
img_path = "PCs/PCs/img/"

getImportedAtoms::FilePath->SGr String->GrwT String->IO([String])
getImportedAtoms pcs_path sg_mm pc = do
   let is = importsOf sg_mm pc
   as <- forM is (\n-> do 
      pc'<-loadPC sg_mm (pcs_path ++ n ++".pc") 
      as <- getImportedAtoms pcs_path sg_mm pc'
      let as' = getAtoms sg_mm pc' 
      return (as `union` as'))
   return (gunion as)


getImports::FilePath->SGr String->GrwT String->IO([String])
getImports pcs_path sg_mm pc = do
   let is = importsOf sg_mm pc
   is <- forM is (\n-> do 
      pc'<-loadPC sg_mm (pcs_path ++ n ++".pc") 
      is' <- getImports pcs_path sg_mm pc'
      let is_ = importsOf sg_mm pc' 
      return (is `union` (is' `union` is_)))
   return (gunion is)

writeDrawingToFile img_path mmi pc = do
   let draw_src = wrPCAsGraphviz mmi pc  
   writeFile (img_path ++ (getPCDef pc) ++ ".gv") draw_src

--writePCDef pc m = 
--   let pc_txt = wrPC $ frPCtoPCNot pc m in
--   writeFile ("pcs/"++ (getPCDef m) ++ ".pc") pc_txt

checkWFAndGeneratePCTree mmi pc = do 
   b <- checkWF mmi pc 
   when b $ do 
     putStrLn "The PC treee is as follows:" 
     putStrLn $ show_pctd $ consPCTD mmi pc

check_MM mmi = do
    let errs1 = check_wf "PCs_AMM" (Just Total) (pc_amm mmi)
    when (not . is_nil $ errs1) $ do 
        show_wf_msg "PCs abstract metamodel" errs1
    let errs2 = check_wf "PCs_MM" (Just Total) (pc_cmm mmi)
    when (not . is_nil $ errs2) $ do 
        show_wf_msg "PCs concrete metamodel" errs2
    let errs3 = check_wf_gm "Refinement of PCs_MM by PCs_AMM " (Just TotalM) (pc_cmm mmi, pc_rm mmi, pc_amm mmi)
    when (not . is_nil $ errs3) $ do 
        show_wf_msg "PCs abstract metamodel" errs3
    return (all is_nil [errs1, errs2, errs3])

checkWF::MMInfo String->PC String->IO(Bool)
checkWF mmi pc = do
    let pc_nm = getPCDef pc
    let errs = check_wf_gm' pc_nm (Just TotalM) (pc, pc_cmm mmi) 
    when (not . is_nil $ errs) $ do
        show_wf_msg ("PC " ++ pc_nm) errs
    return (is_nil errs)


wrCSPToFile pcs_path csp_path mmi pc = do
   putStrLn "Writing the CSP file..." 
   ias <- getImportedAtoms pcs_path (pc_sg_cmm mmi) pc 
   is <-getImports pcs_path (pc_sg_cmm mmi) pc 
   let (cspb, cspp, cspm) = mapT wrCSP (toCSP mmi pc ias is)
   writeFile (csp_path ++ (getPCDef pc) ++ "_base.csp") cspb
   writeFile (csp_path ++ (getPCDef pc) ++ "P.csp") cspp
   writeFile (csp_path ++ (getPCDef pc) ++ ".csp") cspm


wrPCDrawingToFile img_path mmi pc = do
    putStrLn "Writing the GraphViz file..." 
    writeDrawingToFile img_path mmi pc

--checkWFAndHealth pc m = do
--  b <- checkWF pc m 
--  if (not b) then
--    return b
--    else do
--      b'<- checkHealth pc m
--      return b'

showPCAsGwT _ _ _ _ pc = do
   putStrLn $ show pc

showAfterERel _ _ _ mmi pc = do 
  putStrLn $ show $ afterCRel mmi pc

showPCTree _ _ _ mmi pc = do
   putStrLn $ show_pctd $ consPCTD mmi pc

showWithinRel _ _ _ mmi pc= do
   putStrLn $ show $ withinRel mmi pc

drawPCToFile _ img_path _ mmi pc = do
    wrPCDrawingToFile img_path mmi pc

writeCSPToFile pcs_path _ csp_path mmi pc = do
   wrCSPToFile pcs_path csp_path mmi pc


menuStr = "1 - show graph and morphism\n"
   ++ "2 - show after relation\n"
   ++ "3 - show PC Tree\n"
   ++ "4 - show PC's within relation\n"
   ++ "5 - draw PC's Graphviz code\n"
   ++ "6 - generate CSP\n"
   ++ "0 - quit\n"

dispatch =  [ (1, showPCAsGwT) 
            , (2, showAfterERel)  
            , (3, showPCTree)
            , (4, showWithinRel)
            , (5, drawPCToFile)  
            , (6, writeCSPToFile)  
            ]  

optionsPCs pcs_path img_path csp_path mmi pc = do
    putStrLn menuStr
    putStr "Which option? "  
    optStr <- getLine 
    let opt = (read optStr)
    when (opt > 0 && opt <= 6) $ do
       let (Just action) = lookup opt dispatch   
       action pcs_path img_path csp_path mmi pc
       optionsPCs pcs_path img_path csp_path mmi pc

loadAndCheck pcs_path fnm mmi = do
  pc <- loadPC (pc_sg_cmm mmi) (pcs_path ++ fnm)
  b <- checkWF mmi pc 
  let is = importsOf (pc_sg_cmm mmi)  pc
  chs <- forM is (\n-> do 
    opc <- loadAndCheck pcs_path (n++".pc") mmi
    return $ isSomething opc)
  return (boolMaybe b pc)

askLoadAndOpsPCs mmi = do
  putStrLn "Name of directory with PC definitions? [enter for current directory]"
  d <- getLine 
  putStrLn "Name of PC file?"
  fn <- getLine 
  opc <- loadAndCheck d fn mmi
  when (isSomething opc) $ do optionsPCs d (d++"img/") (d++"CSP/") mmi (the opc)

startPCOps = do
    mmi<-load_mm_info mm_path
    b <- check_MM mmi
    if b
        then askLoadAndOpsPCs mmi
        else putStrLn "Errors in the metamodel definition."

outputDrawing pcs_path img_path csp_path fn mmi = do
   opc <- loadAndCheck pcs_path fn mmi
   when (isSomething opc) $ do drawPCToFile pcs_path img_path csp_path mmi (the opc) 

outputCSP pcs_path img_path csp_path fn mmi = do
   opc <- loadAndCheck pcs_path fn mmi
   when (isSomething opc) $ do writeCSPToFile pcs_path img_path csp_path mmi (the opc) 

check pcs_path mmi fn = do
  loadAndCheck pcs_path fn mmi
  return ()

--main = startPCOps

check_generate pcs_path img_path csp_path mmi fn = do
   putStrLn $ "Processing '" ++ fn ++ "'" 
   opc <- loadAndCheck pcs_path fn mmi
   when (isSomething opc) $ do
      drawPCToFile pcs_path img_path csp_path mmi (the opc)
      wrCSPToFile pcs_path csp_path mmi (the opc)

generate_Clock mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Clock.pc"

generate_Clock_ref mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Clock_ref.pc"

generate_GreetChat mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_GreetChat.pc"

generate_VM mmi = do
  check_generate pcs_path img_path csp_path mmi "PC_VM.pc"

generate_VM2 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_VM2.pc"

generate_CCVM mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_CCVM.pc"

generate_BreakStealHouse1 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BreakStealHouse1.pc"

generate_BreakStealHouse2 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BreakStealHouse2.pc"

generate_BreakStealHouse3 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BreakStealHouse3.pc"

generate_BreakStealHouse4 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BreakStealHouse4.pc"

generate_StealHouseTreasure mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_StealHouseTreasure.pc"

generate_HouseAlarm mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_HouseAlarm.pc"
  
generate_HouseLiving mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_HouseLiving.pc"

generate_HouseUnderAttack mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_HouseUnderAttack_Snatch.pc"
   check_generate pcs_path img_path csp_path mmi "PC_HouseUnderAttack_Ransack.pc"
   check_generate pcs_path img_path csp_path mmi "PC_HouseUnderAttack.pc"

generate_SuccessfulHouseAttack mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_SuccessfulHouseAttack.pc"

generate_UnnoticedAttack mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_UnnoticedAttack.pc"

generate_ProtectedHouse mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_ProtectedHouse_HouseAlarm.pc"
    check_generate pcs_path img_path csp_path mmi "PC_ProtectedHouse.pc"

generate_SecureHouse mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_SecureHouse.pc"

generate_HouseAttacker mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_HouseAttacker.pc"

generate_SecuredHouse mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_SecuredHouse.pc"

-- generate_HouseMovement mmi = do
--   check_generate pcs_path img_path csp_path mmi "PC_HouseMovement.pc"

generate_Bool mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Bool.pc"

generate_Bool2 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Bool2.pc"

generate_BoolSetter mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BoolSetter.pc"

generate_Lasbscs mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Lasbscs.pc"

generate_Timer mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Timer.pc"

generate_SimpleLife mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_SimpleLife.pc"

generate_CardReader mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_CardReader.pc"

generate_Authentication mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Authentication.pc"

generate_CashMachine mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_CashMachine.pc"

generate_TravelBus mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_TravelBus.pc"

generate_ABusRide mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_ABusRide.pc"

generate_Withdraw mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_Withdraw.pc"

generate_ShowBalance mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_ShowBalance.pc"

generate_DoCancel mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_DoCancel.pc"

generate_CashMachineOps mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_CashMachineOps.pc"

generate_MadTicker mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_MadTicker.pc"

generate_TicketMachine mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_TicketMachine.pc"

generate_OrderGoods mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_OrderGoods.pc"

generate_POS mmi = do -- From Hoare's book, p.156
    check_generate pcs_path img_path csp_path mmi "PC_POS.pc"

generate_Buzzer mmi = do 
    check_generate pcs_path img_path csp_path mmi "PC_Buzzer.pc"

generateAll = do
    mmi<-load_mm_info mm_path
    b <- check_MM mmi
    when b $ do
        generate_Clock mmi
        generate_Clock_ref mmi
        generate_GreetChat mmi
        generate_VM mmi
        generate_VM2 mmi
        generate_CCVM mmi
        generate_BreakStealHouse1 mmi
        generate_BreakStealHouse2 mmi
        generate_BreakStealHouse3 mmi
        generate_BreakStealHouse4 mmi
        generate_StealHouseTreasure mmi
        generate_HouseUnderAttack mmi
        generate_HouseAttacker mmi
        generate_HouseAlarm mmi
        generate_ProtectedHouse mmi
        generate_SecuredHouse mmi
        generate_Bool mmi
        generate_Bool2 mmi
        generate_BoolSetter mmi
        generate_Lasbscs mmi 
        generate_Timer mmi
        generate_TravelBus mmi 
        generate_ABusRide mmi
        generate_SimpleLife mmi
        generate_CardReader mmi
        generate_Authentication mmi
        generate_ShowBalance mmi
        generate_Withdraw mmi
        generate_DoCancel mmi
        generate_CashMachine mmi
        generate_CashMachineOps mmi
        generate_MadTicker mmi 
        generate_POS mmi
        generate_TicketMachine mmi
        generate_OrderGoods mmi
        generate_Buzzer mmi

load_check_show_tree mmi fnm = do
    pc <- loadPC (pc_sg_cmm mmi) (pcs_path ++ fnm)
    b<-checkWF mmi pc 
    when b $ do
        let td = consPCTD mmi pc 
        putStrLn $ show_pctd td

generate fnm = do
  mmi<-load_mm_info mm_path
  check_generate pcs_path img_path csp_path mmi (fnm ++ ".pc")

main = do
  mmi<-load_mm_info mm_path
  args <- getArgs
  check_generate pcs_path img_path csp_path mmi ((head args) ++ ".pc")

test = do 
    mmi<-load_mm_info mm_path
    pc <- loadPC (pc_sg_cmm mmi) (pcs_path ++ "PC_CMBarred.pc")
    is<-getImports pcs_path (pc_sg_cmm mmi) pc
    putStrLn $ show is
    --generate_Timer mmi
    --generate_CashMachineOps mmi
    --generate_HouseUnderAttack mmi
    --generate_HouseAttacker mmi
    --generate_SecuredHouse mmi
    --generate_HouseAlarm mmi
    --generate_ProtectedHouse mmi
    --generate_SuccessfulHouseAttack mmi
    --generate_SecureHouse mmi
    --pc <- loadPC (pc_sg_cmm mmi) (pcs_path ++ "PC_Timer.pc")
    --putStrLn $ show $ compoundStart mmi pc "HouseAlarm"
    --putStrLn $ show $ inner_Ref pc "RefGive"
    --putStrLn $ show $ nmOfRefF mmi pc "RefGive"
    --putStrLn $ "Inner ks: " ++ (show $ innerKs mmi pc "SecuredHouse")
    --putStrLn $ "Common Inner ks: " ++ (show $ commonInnerKs mmi pc "GetandGive")
    --putStrLn $ "Inner ps: " ++ (show $ innerRefKs mmi pc "SecuredHouse")
    --pc <- loadPC (pc_sg_cmm mmi) (pcs_path ++ "PC_HouseAttacker.pc")
    --putStrLn $ show $ commonInnerKs mmi pc (startCompound mmi pc)
    --putStrLn $ show $ nextNodes mmi pc "OpChat"
    --load_check_show_tree mmi "PC_Buzzer.pc"
    --generate_PC_SimpleLife mmi
    --generate_PC_Bool mmi
    --pc <- loadPC (pc_sg_cmm mmi) (pcs_path ++ "PC_SimpleLife.pc")
    --putStrLn $ show $ nmOfRefF mmi pc "RefLive"
    --putStrLn $ show $ paramsOfRef mmi pc "RefLive"
    --putStrLn $ show $ (successorsOf mmi pc "RefTimer") `intersec` (pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_ReferenceC)
    --putStrLn $ show $ successorsOf mmi pc "CRefTimer"
    --putStrLn $ show $ nextNodeAfter mmi pc "RefTimer"
    --putStrLn $ show $ isNodeOfTy "Timer" CMM_Compound (pc_sg_cmm mmi) pc
    --generate_PC_Lasbscs mmi 
    --generate_PC_GreetChat mmi
    --generate_PC_CashMachine mmi
    --pc <- loadPC (pc_sg_cmm mmi) (pcs_path ++ "PC_Clock.pc")
    --b<-checkWF mmi pc 
    --when b $ do
    --    let n = startCompound mmi pc 
    --    putStrLn $ show $ nextNodeAfter mmi pc n
    --    let (t, _, _) = consPCTNode mmi pc n nil_guard []
    --    putStrLn $ show t
    --load_check_show_tree mmi "PC_Clock.pc"
    --load_check_show_tree mmi "PC_BreakStealHouse1.pc"
    --load_check_show_tree mmi "GreetChat.pc"
    --load_check_show_tree mmi "PC_BreakStealHouse2.pc"
    --load_check_show_tree mmi "PC_Bool.pc"
--  when b $ do
--    let t = consPCTree mmi pc 
--    putStrLn $ show t
  --let csp = genCSPDecl t
  --putStrLn $ show csp
  --putStrLn $ show $ generatePCTree pc tm 
  --putStrLn $ show $ generateForOperator pc tm "OpProcessAuthenticate" ["ATM", "ProcessAuthenticate"]
  --putStrLn $ show $ nextNodesInPC pc tm "ProcessAuthenticate"
  --putStrLn $ show $ withinRelWith' pc tm "ATM" []
  --putStrLn $ show $ withinRelOfPC pc tm
  --putStrLn $ show $ drawPC pc tm 
  --putStrLn $ show $ withinRelOfPC pc tm
  --putStrLn $ show $ withinRelWith' pc tm "Bool" []
  --putStrLn $ show $ nextNodesInPC pc tm "BoolT"
  --putStrLn $ show $ nextNodesInPC pc tm "OpBoolT"
  --putStrLn $ show $ withinRelWith' pc tm "BoolT" ["Bool"]
  --putStrLn $ show $ withinRelWithAux pc tm "BoolT" "getT" ["Bool"]
  --putStrLn $ show $ withinRelWithAux pc tm "BoolT" "RefBool" ["Bool"]
  --putStrLn $ show $ typeOfN "OpChooseGive" tm 
  --putStrLn $ show $ getOpVal pc tm "OpChoiceVal"
  --putStrLn $ show $ getOperatorOp pc tm "OpChooseGive"
  --putStrLn $ show $ getOperatorOp pc tm "OpChooseGive"
  --putStrLn $ show pc
  --b<-checkWF pc tm
  --putStrLn $ show $ successorsPC pc tm "Clock"
  --putStrLn $ show $ getCompoundStart pc tm "Clock"
  --putStrLn $ show $ nextNodeInPC pc tm "tick"
  --putStrLn $ show $ successorsPC pc tm "RefClock"
  --putStrLn $ show $ successorsPC pc tm "RefClockC"
  --putStrLn $ show $ getPCStartCompound pc tm 