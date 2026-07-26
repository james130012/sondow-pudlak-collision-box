import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectWitnessCompilation

/-! # Structural direct compiler for one bounded sequent-step row -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectStructuralCompiler

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectFreeVariables
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectTerminalBound
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectWitnessCompilation

structure CompactSequentFormulaStepRowBoundedClosedDirectBound
    (formula : ValuationFormula) (resource : Nat) where
  proof : CertifiedPAContextProof ∅ formula
  payloadLength_le : proof.payloadLength <= resource

noncomputable def
    compactSequentFormulaStepRowBoundedDirectStructuralPayloadEnvelopeOfBounded
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (hbounded : CompactSequentFormulaStepRowBounded tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex valueBound) :
    Nat :=
  let data :=
    compactSequentFormulaStepRowBoundedDirectDataOfBounded tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound hbounded
  compactSequentFormulaStepRowBoundedDirectWitnessPayloadEnvelope tokenTable
    width tokenCount suffixBoundary suffixCount valueBoundary valueCount
    rowIndex valueBound data

noncomputable def
    compactSequentFormulaStepRowBoundedClosedDirectBoundOfBounded
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (hbounded : CompactSequentFormulaStepRowBounded tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex valueBound) :
    CompactSequentFormulaStepRowBoundedClosedDirectBound
      (compactSequentFormulaStepRowBoundedDirectClosedFormula tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound)
      (compactSequentFormulaStepRowBoundedDirectStructuralPayloadEnvelopeOfBounded
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex valueBound hbounded) := by
  let data :=
    compactSequentFormulaStepRowBoundedDirectDataOfBounded tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound hbounded
  let sourceBound :=
    compactSequentFormulaStepRowBoundedExplicitWitnessDirectBoundOfData
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound data
  let sourceFormula :=
    explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 18
      (compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex)
  have hformula :
      sourceFormula =
        compactSequentFormulaStepRowBoundedDirectClosedFormula tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount
          rowIndex valueBound :=
    (compactSequentFormulaStepRowBoundedDirectClosedFormula_alignment
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound).symm
  let contextualProof :=
    castValuationContextProof hformula sourceBound.proof
  have hclosed :
      (compactSequentFormulaStepRowBoundedDirectClosedFormula tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound).freeVariables = ∅ :=
    compactSequentFormulaStepRowBoundedDirectClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound
  let proof : CertifiedPAContextProof ∅
      (compactSequentFormulaStepRowBoundedDirectClosedFormula tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound) :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed]
      simp [valuationContext])
      contextualProof
  refine ⟨proof, ?_⟩
  change (CertifiedPAContextProof.castContext _
    contextualProof).payloadLength <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  change (castValuationContextProof hformula
    sourceBound.proof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  simpa only [
    compactSequentFormulaStepRowBoundedDirectStructuralPayloadEnvelopeOfBounded,
    data, sourceBound] using sourceBound.payloadLength_le

#print axioms
  compactSequentFormulaStepRowBoundedClosedDirectBoundOfBounded

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectStructuralCompiler
