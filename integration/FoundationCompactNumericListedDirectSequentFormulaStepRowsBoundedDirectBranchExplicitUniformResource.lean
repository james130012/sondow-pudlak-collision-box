import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFull21UniformBound
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax

/-! # Explicit row-independent resource for one bounded sequent row -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchExplicitUniformResource

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactCertifiedContextProof
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepFull21UniformResources
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedOfTerminal
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFull21UniformBound

def compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound : Nat) : Nat :=
  Nat.size tokenTable + Nat.size width + Nat.size tokenCount +
    Nat.size suffixBoundary + Nat.size suffixCount + Nat.size valueBoundary +
    Nat.size valueCount + Nat.size valueBound + 1

def compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchResource
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound : Nat) : Nat :=
  let bitBound :=
    compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      valueBound
  compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedPayloadPolynomial
    rowCount valueBound bitBound
    (compactSequentFormulaStepTail01UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount rowCount bitBound valueBound)

noncomputable def compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchProof
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount rowIndex valueBound : Nat)
    (hrow : CompactSequentFormulaStepRowBounded tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex valueBound)
    (hrowIndex : rowIndex < rowCount) :
    CertifiedPAContextProof
      (valuationContext
        (Rewriting.free
          (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
            tokenCount suffixBoundary suffixCount valueBoundary valueCount
            valueBound)).freeVariables
        (extendValuation rowIndex zeroValuation))
      (Rewriting.free
        (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount
          valueBound)) := by
  let data :=
    compactSequentFormulaStepRowBoundedDirectDataOfBounded tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound hrow
  let bitBound :=
    compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      valueBound
  have htokenTable : Nat.size tokenTable <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  have hwidth : Nat.size width <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  have htokenCount : Nat.size tokenCount <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  have hsuffixBoundary : Nat.size suffixBoundary <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  have hsuffixCount : Nat.size suffixCount <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  have hvalueBoundary : Nat.size valueBoundary <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  have hvalueCount : Nat.size valueCount <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  have hvalueBound : Nat.size valueBound <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  let raw :=
    compactSequentFormulaStepRowBoundedAtValuationIndexFull21UniformBoundOfData
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound rowCount bitBound data
      (Nat.le_of_lt hrowIndex) htokenTable hwidth htokenCount hsuffixBoundary
      hsuffixCount hvalueBoundary hvalueCount hvalueBound
  exact castValuationContextProof
    (compactSequentFormulaStepRowsBoundedUniversalBody_free_alignment tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      valueBound).symm
    raw.proof

theorem
    compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchProof_payloadLength_le
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount rowIndex valueBound : Nat)
    (hrow : CompactSequentFormulaStepRowBounded tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex valueBound)
    (hrowIndex : rowIndex < rowCount) :
    (compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchProof
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount rowIndex valueBound hrow hrowIndex).payloadLength <=
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchResource
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound := by
  let data :=
    compactSequentFormulaStepRowBoundedDirectDataOfBounded tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound hrow
  let bitBound :=
    compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      valueBound
  have htokenTable : Nat.size tokenTable <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  have hwidth : Nat.size width <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  have htokenCount : Nat.size tokenCount <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  have hsuffixBoundary : Nat.size suffixBoundary <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  have hsuffixCount : Nat.size suffixCount <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  have hvalueBoundary : Nat.size valueBoundary <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  have hvalueCount : Nat.size valueCount <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  have hvalueBound : Nat.size valueBound <= bitBound := by
    unfold bitBound
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBitBound
    omega
  let raw :=
    compactSequentFormulaStepRowBoundedAtValuationIndexFull21UniformBoundOfData
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound rowCount bitBound data
      (Nat.le_of_lt hrowIndex) htokenTable hwidth htokenCount hsuffixBoundary
      hsuffixCount hvalueBoundary hvalueCount hvalueBound
  let hformula :=
    (compactSequentFormulaStepRowsBoundedUniversalBody_free_alignment tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      valueBound).symm
  change (castValuationContextProof hformula raw.proof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  simpa only [
    compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchResource,
    bitBound] using raw.payloadLength_le

#print axioms
  compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchProof_payloadLength_le

end FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchExplicitUniformResource
