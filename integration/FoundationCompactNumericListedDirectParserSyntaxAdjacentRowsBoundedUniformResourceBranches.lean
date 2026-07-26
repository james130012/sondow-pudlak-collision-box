import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexUniformResourceBound
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranches

/-! # Uniform-resource branches for all adjacent parser rows -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedUniformResourceBranches

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranches
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranches
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexUniformResourceBound

private theorem uniformBranchIndex_code_length_le :
    (binaryTermCode (&0 : ValuationTerm)).length <=
      compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope := by
  unfold compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope
  omega

private theorem uniformBranchNextIndex_code_length_le :
    (binaryTermCode (‘&0 + 1’ : ValuationTerm)).length <=
      compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope := by
  unfold compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope
  omega

private theorem uniformBranchNextNextIndex_code_length_le :
    (binaryTermCode
      (‘!!(‘&0 + 1’ : ValuationTerm) + 1’ : ValuationTerm)).length <=
      compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope := by
  unfold compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope
  omega

def compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchResource
    (tokenCount uniformValueBound numericBound bitBound : Nat) : Nat :=
  compactParserSyntaxAdjacentRowBoundedAtValuationIndexUniformPayloadPolynomial
    uniformValueBound
    compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope tokenCount
    numericBound bitBound

noncomputable def
    compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchProof
    (tokenTable width tokenCount stateBoundary stateCount rowCount
      formulaValueBound uniformValueBound numericBound bitBound rowIndex : Nat)
    (hformulaValue : formulaValueBound <= uniformValueBound)
    (hrowIndex : rowIndex < rowCount)
    (hrowCount : rowCount <= numericBound)
    (hrow : CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
      stateBoundary stateCount rowIndex formulaValueBound)
    (hvalueBound : formulaValueBound <= numericBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (Rewriting.free
          (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
            tokenCount stateBoundary stateCount formulaValueBound)).freeVariables
        (extendValuation rowIndex zeroValuation))
      (Rewriting.free
        (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
          tokenCount stateBoundary stateCount formulaValueBound)) := by
  have hcurrent :
      CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
        stateBoundary stateCount
          (termValue (adjacentRowsBranchValuation rowIndex)
            (&0 : ValuationTerm)) formulaValueBound := by
    simpa [adjacentRowsBranchValuation, zeroValuation, extendValuation] using hrow
  have hzero : adjacentRowsBranchValuation rowIndex 0 <= numericBound := by
    change rowIndex <= numericBound
    omega
  let raw :=
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexUniformBound
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount formulaValueBound uniformValueBound
      (&0 : ValuationTerm)
      compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope
      numericBound bitBound hformulaValue (by simp)
      uniformBranchIndex_code_length_le uniformBranchNextIndex_code_length_le
      uniformBranchNextNextIndex_code_length_le hcurrent hvalueBound hwidth
      hwidthBit htokenCount hstateCount htokenTableSize hstateBoundarySize
      hareaNumeric hareaBit hzero hnumericSize hbitPositive
  exact castValuationContextProof
    (compactParserSyntaxAdjacentRowsBoundedUniversalBody_free_alignment
      tokenTable width tokenCount stateBoundary stateCount formulaValueBound).symm
    raw.proof

theorem
    compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchProof_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount
      formulaValueBound uniformValueBound numericBound bitBound rowIndex : Nat)
    (hformulaValue : formulaValueBound <= uniformValueBound)
    (hrowIndex : rowIndex < rowCount)
    (hrowCount : rowCount <= numericBound)
    (hrow : CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
      stateBoundary stateCount rowIndex formulaValueBound)
    (hvalueBound : formulaValueBound <= numericBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchProof tokenTable
      width tokenCount stateBoundary stateCount rowCount formulaValueBound
      uniformValueBound numericBound bitBound rowIndex hformulaValue hrowIndex
      hrowCount hrow hvalueBound hwidth hwidthBit htokenCount hstateCount
      htokenTableSize hstateBoundarySize hareaNumeric hareaBit hnumericSize
      hbitPositive).payloadLength <=
    compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchResource tokenCount
      uniformValueBound numericBound bitBound := by
  unfold compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchProof
    compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchResource
  rw [castValuationContextProof_payloadLength_eq]
  exact
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexUniformBound
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount formulaValueBound uniformValueBound
      (&0 : ValuationTerm)
      compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope
      numericBound bitBound hformulaValue (by simp)
      uniformBranchIndex_code_length_le uniformBranchNextIndex_code_length_le
      uniformBranchNextNextIndex_code_length_le (by
        simpa [adjacentRowsBranchValuation, zeroValuation, extendValuation] using
          hrow)
      hvalueBound hwidth hwidthBit htokenCount hstateCount htokenTableSize
      hstateBoundarySize hareaNumeric hareaBit (by
        change rowIndex <= numericBound
        omega)
      hnumericSize hbitPositive).payloadLength_le

#print axioms compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchProof
#print axioms
  compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchProof_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedUniformResourceBranches
