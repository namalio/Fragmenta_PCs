
import Gr_Cls
import PCsParsing
import PCs
import CheckUtils
import PCs_MM_Names
import MyMaybe

pcs_path = "PCs/PCs/"
def_path = "PCs/MM/"

tst_1 = do
    mmi<-load_mm_info def_path
    pc<-loadPC (pc_sg_cmm mmi) (pcs_path ++ "PC_Clock.pc") 
    -- Checks whether the PC is well formed
    check_ty_morphism (getPCDef pc) (Just TotalM) pc (pc_cmm mmi) True
    --putStrLn $ show $ startCompound mmi pc 
    --putStrLn $ show $ getPCStart (pc_sg_cmm mmi) pc 
    --putStrLn $ show $ afterCRel mmi pc 
    --putStrLn $ show $ nmOfNamed pc $ startCompound mmi pc 
    --putStrLn $ show $ pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_AfterC
    --putStrLn $ show $ withinRel mmi pc