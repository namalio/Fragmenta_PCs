module PCs_MM_Names (PCs_AMM_Ns(..), PCs_AMM_Es(..), PCs_CMM_Ns(..), PCs_CMM_Es(..), show_amm_n, show_amm_e, show_cmm_n, show_cmm_e
    , read_cmm)
where

data PCs_AMM_Ns = AMM_Attribute | AMM_Element | AMM_PCDef | AMM_Connector | AMM_Node
    deriving (Read, Show, Eq)

data PCs_AMM_Es = AMM_EHas | AMM_EHas2 | AMM_EContains | AMM_EStarts | AMM_EConnector_src | AMM_EConnector_tgt
    deriving (Read, Show, Eq)

data PCs_CMM_Ns = CMM_NamedNode | CMM_Name | CMM_Node | CMM_Connector | CMM_PCDef | CMM_StartN | CMM_PNamedNode | CMM_Import | CMM_TargetOfRef | CMM_Atom | CMM_Compound | CMM_Action | CMM_Parameterised | CMM_Parameter | CMM_Guarded | CMM_Guard | CMM_YesNo | CMM_Yes | CMM_No | CMM_PAtom | CMM_AnyExp | CMM_PParameter | CMM_PNode | CMM_PParameterised | CMM_Stop | CMM_Skip | CMM_PAction | CMM_Operator | CMM_POperatorVal | CMM_OperatorVal | CMM_OpChoice | CMM_OpIntChoice | CMM_OpParallel | CMM_OpIf | CMM_OpInterleave | CMM_OpThrow | CMM_PNode2 | CMM_PParameterised2 | CMM_PAction2 | CMM_PGuarded | CMM_PName | CMM_PYesNo | CMM_Reference | CMM_Renaming | CMM_PConnector | CMM_PStartN | CMM_StartC | CMM_PCompound | CMM_PConnector2 | CMM_PAction3 | CMM_DefinesC | CMM_PCompound2 | CMM_AfterC | CMM_PYesNo2 | CMM_PConnector3 | CMM_PParameterised3 | CMM_PReference | CMM_PTargetOfRef | CMM_ReferenceC | CMM_PYesNo3 | CMM_BMainIfC | CMM_PGuarded2 | CMM_BElseC | CMM_BJumpC | CMM_PConnector4 | CMM_POperator2 | CMM_BranchC | CMM_PAction4
    deriving (Read, Show, Eq)

data PCs_CMM_Es = CMM_ENamedNode_name | CMM_EContainsNs | CMM_EContainsCs | CMM_EStarts | CMM_EHasParams | CMM_EHasGuard | CMM_EAtomExp | CMM_EAnyExp_atv | CMM_EAnyExp_atSet | CMM_EOperator_op | CMM_EReference_name | CMM_EReference_inner | CMM_ERenamings | CMM_EStartCSrc | CMM_EStartCTgt | CMM_EAfterCSrc | CMM_EAfterCTgt | CMM_EDefinesCTgt | CMM_EDefinesCSrc | CMM_EAfterC_copen | CMM_EReferenceCSrc | CMM_EReferenceCTgt | CMM_EReferenceC_hidden | CMM_EBranchCSrc | CMM_EBranchCTgt
    deriving (Read, Show, Eq)

show_amm_n nt = drop 4 (show nt)
show_amm_e et = drop 4 (show et)
show_cmm_n nt = drop 4 (show nt)
show_cmm_e et = drop 4 (show et)
read_cmm x = read ("CMM_" ++ x)

