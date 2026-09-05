import integration.FoundationCompactNumericListedDirectNatListConsRowsHeadTerminalUniformBound
import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds

/-! # Exact bounded-witness certificate for the natural-list cons head -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 220000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsHeadCertificate

open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsHeadTerminalUniformBound

private abbrev consHeadZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

def compactAdditiveNatListConsHeadValues
    {tokenTable width tokenCount targetBoundary head : Nat}
    (data : CompactAdditiveNatListConsHeadData tokenTable width tokenCount
      targetBoundary head) : Fin 2 -> Nat :=
  ![data.targetRight, data.targetLeft]

theorem compactAdditiveNatListConsHeadValues_le
    {tokenTable width tokenCount targetBoundary head : Nat}
    (data : CompactAdditiveNatListConsHeadData tokenTable width tokenCount
      targetBoundary head) :
    forall coordinate, compactAdditiveNatListConsHeadValues data coordinate <=
      tokenCount := by
  intro coordinate
  fin_cases coordinate
  · exact data.targetRight_le
  · exact data.targetLeft_le

noncomputable def compactAdditiveNatListConsRowsHeadCertificate
    (tokenTable width tokenCount targetBoundary head : Nat)
    (data : CompactAdditiveNatListConsHeadData tokenTable width tokenCount
      targetBoundary head) :
    CheckedHybridValuationBoundedFormulaCertificate consHeadZeroValuation
      (compactAdditiveNatListConsRowsHeadBody tokenTable width tokenCount
        targetBoundary head) := by
  let values := compactAdditiveNatListConsHeadValues data
  let terminal :=
    compactAdditiveNatListConsRowsHeadTerminalCertificate tokenTable width
      tokenCount targetBoundary head data
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
    (compactAdditiveNatListConsRowsHeadTerminal tokenTable width tokenCount
      targetBoundary head) values
        (compactAdditiveNatListConsHeadValues_le data) terminal
  exact CheckedHybridValuationBoundedFormulaCertificate.cast (by rfl) installed

#print axioms compactAdditiveNatListConsRowsHeadCertificate

end FoundationCompactNumericListedDirectNatListConsRowsHeadCertificate
