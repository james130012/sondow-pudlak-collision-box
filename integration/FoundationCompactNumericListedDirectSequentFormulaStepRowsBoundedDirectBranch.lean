import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessPublicPayload
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

/-! # One direct finite-universal branch for bounded sequent rows -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranch

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactCertifiedContextProof
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler

noncomputable def compactSequentFormulaStepRowsBoundedDirectBranchData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (hrow : CompactSequentFormulaStepRowBounded tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex valueBound) :
    CompactSequentFormulaStepRowBoundedDirectData tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex valueBound :=
  compactSequentFormulaStepRowBoundedDirectDataOfBounded tokenTable width
    tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
    valueBound hrow

noncomputable def compactSequentFormulaStepRowsBoundedDirectBranchResource
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (hrow : CompactSequentFormulaStepRowBounded tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex valueBound) :
    Nat :=
  compactSequentFormulaStepRowBoundedAtValuationIndexWitnessPayloadEnvelope
    tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
    valueCount rowIndex valueBound
    (compactSequentFormulaStepRowsBoundedDirectBranchData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound hrow)

noncomputable def compactSequentFormulaStepRowsBoundedDirectBranchProof
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (hrow : CompactSequentFormulaStepRowBounded tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex valueBound) :
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
    compactSequentFormulaStepRowsBoundedDirectBranchData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound hrow
  let raw :=
    compactSequentFormulaStepRowBoundedAtValuationIndexProofOfData tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      rowIndex valueBound data
  exact castValuationContextProof
    (compactSequentFormulaStepRowsBoundedUniversalBody_free_alignment tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      valueBound).symm
    raw

theorem
    compactSequentFormulaStepRowsBoundedDirectBranchProof_payloadLength_le
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (hrow : CompactSequentFormulaStepRowBounded tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex valueBound) :
    (compactSequentFormulaStepRowsBoundedDirectBranchProof tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound hrow).payloadLength <=
      compactSequentFormulaStepRowsBoundedDirectBranchResource tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound hrow := by
  let data :=
    compactSequentFormulaStepRowsBoundedDirectBranchData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound hrow
  let raw :=
    compactSequentFormulaStepRowBoundedAtValuationIndexProofOfData tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      rowIndex valueBound data
  let hformula :=
    (compactSequentFormulaStepRowsBoundedUniversalBody_free_alignment tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      valueBound).symm
  change (castValuationContextProof hformula raw).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  exact
    compactSequentFormulaStepRowBoundedAtValuationIndexProof_payloadLength_le
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound data

#print axioms
  compactSequentFormulaStepRowsBoundedDirectBranchProof
#print axioms
  compactSequentFormulaStepRowsBoundedDirectBranchProof_payloadLength_le

end FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranch
