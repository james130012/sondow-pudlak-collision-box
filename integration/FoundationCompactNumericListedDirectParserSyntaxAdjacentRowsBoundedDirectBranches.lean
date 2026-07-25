import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
import integration.FoundationCompactPAExplicitDirectUniversalBranches

/-!
# Direct proof branches for all bounded adjacent parser rows

Every branch calls the completed open-index twenty-seven-witness compiler.
The public numeric and bit bounds are shared by all rows; the row index is
bounded solely from `rowIndex < rowCount <= numericBound`.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranches

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexResourceDefinitions
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFinal
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax

def zeroValuation : Nat -> Nat := fun _ => 0

def adjacentRowsBranchValuation (rowIndex : Nat) : Nat -> Nat :=
  extendValuation rowIndex zeroValuation

def compactParserSyntaxAdjacentRowsBoundedDirectBranchResource
    (tokenTable width tokenCount stateBoundary stateCount valueBound
      numericBound bitBound : Nat) : Nat :=
  compactParserSyntaxAdjacentRowBoundedAtValuationIndexFullyFixedPayloadPolynomial
    tokenTable width tokenCount stateBoundary stateCount valueBound
      (&0 : ValuationTerm) numericBound bitBound

noncomputable def compactParserSyntaxAdjacentRowsBoundedDirectBranchProof
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
  have hzero :
      adjacentRowsBranchValuation rowIndex 0 <= numericBound := by
    change rowIndex <= numericBound
    omega
  let raw :=
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexFullyFixedBound
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount valueBound (&0 : ValuationTerm) numericBound
      bitBound hindexVariables hcurrent hvalueBound hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hzero hnumericSize hbitPositive
  exact castValuationContextProof
    (compactParserSyntaxAdjacentRowsBoundedUniversalBody_free_alignment
      tokenTable width tokenCount stateBoundary stateCount valueBound).symm
    raw.proof

theorem
    compactParserSyntaxAdjacentRowsBoundedDirectBranchProof_payloadLength_le
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
    (compactParserSyntaxAdjacentRowsBoundedDirectBranchProof tokenTable width
      tokenCount stateBoundary stateCount rowCount valueBound numericBound
      bitBound rowIndex hrowIndex hrowCount hrow hvalueBound hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive).payloadLength <=
    compactParserSyntaxAdjacentRowsBoundedDirectBranchResource tokenTable width
      tokenCount stateBoundary stateCount valueBound numericBound bitBound := by
  unfold compactParserSyntaxAdjacentRowsBoundedDirectBranchProof
    compactParserSyntaxAdjacentRowsBoundedDirectBranchResource
  rw [castValuationContextProof_payloadLength_eq]
  exact
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexFullyFixedBound
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount valueBound (&0 : ValuationTerm) numericBound
      bitBound (by simp) (by
        simpa [adjacentRowsBranchValuation, zeroValuation, extendValuation]
          using hrow)
      hvalueBound hwidth hwidthBit htokenCount hstateCount htokenTableSize
      hstateBoundarySize hareaNumeric hareaBit (by
        change rowIndex <= numericBound
        omega)
      hnumericSize hbitPositive).payloadLength_le

#print axioms compactParserSyntaxAdjacentRowsBoundedDirectBranchProof
#print axioms
  compactParserSyntaxAdjacentRowsBoundedDirectBranchProof_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranches
