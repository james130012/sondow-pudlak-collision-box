import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessPublicProof

/-! # Payload bound for the public open-index bounded-row proof -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler

open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData

theorem
    compactSequentFormulaStepRowBoundedAtValuationIndexProof_payloadLength_le
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    (compactSequentFormulaStepRowBoundedAtValuationIndexProofOfData tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      rowIndex valueBound data).payloadLength <=
      compactSequentFormulaStepRowBoundedAtValuationIndexWitnessPayloadEnvelope
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex valueBound data := by
  let sourceBound :=
    compactSequentFormulaStepRowBoundedAtValuationIndexExplicitWitnessBoundOfData
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound data
  let hformula :=
    compactSequentFormulaStepRowBoundedAtValuationIndexExplicitFormula_eq_public
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound
  change
    (castValuationContextProof hformula sourceBound.proof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  exact sourceBound.payloadLength_le

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexProof_payloadLength_le

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler
