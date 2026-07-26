import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexTermCodeFixedBound
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranches

/-! # Uniform term-code fixed branches for all adjacent parser rows -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranches

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranches
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexTermCodeFixedBound

def compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope : Nat :=
  (binaryTermCode (&0 : ValuationTerm)).length +
    (binaryTermCode (‘&0 + 1’ : ValuationTerm)).length +
    (binaryTermCode
      (‘!!(‘&0 + 1’ : ValuationTerm) + 1’ :
        ValuationTerm)).length

private theorem branchIndex_code_length_le :
    (binaryTermCode (&0 : ValuationTerm)).length <=
      compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope := by
  unfold compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope
  omega

private theorem branchNextIndex_code_length_le :
    (binaryTermCode (‘&0 + 1’ : ValuationTerm)).length <=
      compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope := by
  unfold compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope
  omega

private theorem branchNextNextIndex_code_length_le :
    (binaryTermCode
      (‘!!(‘&0 + 1’ : ValuationTerm) + 1’ :
        ValuationTerm)).length <=
      compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope := by
  unfold compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope
  omega

def compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchResource
    (tokenCount valueBound numericBound bitBound : Nat) : Nat :=
  compactParserSyntaxAdjacentRowBoundedAtValuationIndexTermCodeFixedPayloadPolynomial
    valueBound
    compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope
    tokenCount numericBound bitBound

noncomputable def
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchProof
    (tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound rowIndex : Nat)
    (hrowIndex : rowIndex < rowCount)
    (hrowCount : rowCount <= numericBound)
    (hrow : CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
      stateBoundary stateCount rowIndex valueBound)
    (hvalueBound : valueBound <= numericBound)
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
            tokenCount stateBoundary stateCount valueBound)).freeVariables
        (extendValuation rowIndex zeroValuation))
      (Rewriting.free
        (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
          tokenCount stateBoundary stateCount valueBound)) := by
  have hcurrent :
      CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
        stateBoundary stateCount
          (termValue (adjacentRowsBranchValuation rowIndex)
            (&0 : ValuationTerm)) valueBound := by
    simpa [adjacentRowsBranchValuation, zeroValuation, extendValuation] using
      hrow
  have hindexVariables : (&0 : ValuationTerm).freeVariables ⊆ {0} := by
    simp
  have hzero : adjacentRowsBranchValuation rowIndex 0 <= numericBound := by
    change rowIndex <= numericBound
    omega
  let raw :=
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexTermCodeFixedBound
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount valueBound (&0 : ValuationTerm)
      compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope
      numericBound bitBound hindexVariables branchIndex_code_length_le
      branchNextIndex_code_length_le branchNextNextIndex_code_length_le
      hcurrent hvalueBound hwidth hwidthBit htokenCount hstateCount
      htokenTableSize hstateBoundarySize hareaNumeric hareaBit hzero
      hnumericSize hbitPositive
  exact castValuationContextProof
    (compactParserSyntaxAdjacentRowsBoundedUniversalBody_free_alignment
      tokenTable width tokenCount stateBoundary stateCount valueBound).symm
    raw.proof

theorem
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchProof_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound rowIndex : Nat)
    (hrowIndex : rowIndex < rowCount)
    (hrowCount : rowCount <= numericBound)
    (hrow : CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
      stateBoundary stateCount rowIndex valueBound)
    (hvalueBound : valueBound <= numericBound)
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
    (compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchProof
      tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound rowIndex hrowIndex hrowCount hrow hvalueBound
      hwidth hwidthBit htokenCount hstateCount htokenTableSize
      hstateBoundarySize hareaNumeric hareaBit hnumericSize
      hbitPositive).payloadLength <=
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchResource
      tokenCount valueBound numericBound bitBound := by
  unfold
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchProof
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchResource
  rw [castValuationContextProof_payloadLength_eq]
  exact
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexTermCodeFixedBound
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount valueBound (&0 : ValuationTerm)
      compactParserSyntaxAdjacentRowsBoundedBranchIndexTermCodeEnvelope
      numericBound bitBound (by simp) branchIndex_code_length_le
      branchNextIndex_code_length_le branchNextNextIndex_code_length_le (by
        simpa [adjacentRowsBranchValuation, zeroValuation, extendValuation]
          using hrow)
      hvalueBound hwidth hwidthBit htokenCount hstateCount htokenTableSize
      hstateBoundarySize hareaNumeric hareaBit (by
        change rowIndex <= numericBound
        omega)
      hnumericSize hbitPositive).payloadLength_le

#print axioms
  compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchProof
#print axioms
  compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchProof_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranches
