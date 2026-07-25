import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectFormulaAlignment

/-! # Empty-variable source syntax of the original bounded endpoint formula -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalSyntax

open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula

def compactParserInitialFinalBoundedDirectEmptySourceExplicitTerms :
    Fin 36 -> ArithmeticSemiterm Empty 37 :=
  ![(#23 : ArithmeticSemiterm Empty 37), #24, #25, #26, #27, #28,
      #29, #30, #31, #32, #33, #34, #35,
      #22, #21, #20, #19, #18, #17, #16, #15, #14, #13, #12, #11,
      #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

def compactParserInitialFinalBoundedDirectEmptySourceRawTerminal :
    ArithmeticSemiformula Empty 37 :=
  compactUnifiedParserInitialFinalRowsDef.val ⇜
    compactParserInitialFinalBoundedDirectEmptySourceExplicitTerms

def compactParserInitialFinalBoundedDirectEmptySourceRawBody :
    ArithmeticSemiformula Empty 14 :=
  sourceBoundedWitnessFormula
    (#13 : ArithmeticSemiterm Empty 14) 23
    compactParserInitialFinalBoundedDirectEmptySourceRawTerminal

set_option maxRecDepth 8192 in
theorem compactParserInitialFinalBoundedDef_eq_directEmptySourceRawBody :
    compactParserInitialFinalBoundedDef.val =
      compactParserInitialFinalBoundedDirectEmptySourceRawBody := by
  unfold compactParserInitialFinalBoundedDef
    compactParserInitialFinalBoundedDirectEmptySourceRawBody
    sourceBoundedWitnessFormula sourceSubstitutionLift
    compactParserInitialFinalBoundedDirectEmptySourceRawTerminal
    compactParserInitialFinalBoundedDirectEmptySourceExplicitTerms
  rfl

#print axioms compactParserInitialFinalBoundedDef_eq_directEmptySourceRawBody

end FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalSyntax
