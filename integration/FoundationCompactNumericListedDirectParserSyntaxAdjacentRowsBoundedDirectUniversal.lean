import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranchTree
import integration.FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerBounds

/-!
# Direct bounded universal for all adjacent parser rows

The finite direct branch tree is transported from the canonical successor
bound to the closed binary numeral `rowCount`, discharged, and universally
introduced.  The exported resource uses the polynomial branch envelope.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectUniversal

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranches
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranchTree

private noncomputable def
    compactParserSyntaxAdjacentRowsBoundedDirectBoundEquality
    (rowCount : Nat) :
    CertifiedPAContextProof
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (“!!(iteratedSuccessorTerm 0 rowCount) =
        !!(Rew.free
          (Rew.bShift (shortBinaryNumeralTerm rowCount)))” :
        ValuationFormula) := by
  let raw := compileClosedShortBoundEquality rowCount
  have hformula :
      (“!!(iteratedSuccessorTerm 0 rowCount) =
        !!(shortBinaryNumeralTerm rowCount)” : ValuationFormula) =
      (“!!(iteratedSuccessorTerm 0 rowCount) =
        !!(Rew.free
          (Rew.bShift (shortBinaryNumeralTerm rowCount)))” :
        ValuationFormula) := by
    simp
  exact CertifiedPAContextProof.castContext (by simp)
    (CertifiedPAContextProof.cast hformula raw)

def compactParserSyntaxAdjacentRowsBoundedDirectUniversalPolynomialResource
    (tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound : Nat) : Nat :=
  let body :=
    compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
      tokenCount stateBoundary stateCount valueBound
  let branchPolynomial :=
    explicitDirectUniversalBranchesPayloadPolynomial rowCount body
      (compactParserSyntaxAdjacentRowsBoundedDirectBranchResource tokenTable
        width tokenCount stateBoundary stateCount valueBound numericBound
          bitBound)
  compileContextualTermBoundedUniversalPayloadEnvelope ∅ rowCount
    (Rew.bShift (shortBinaryNumeralTerm rowCount)) body
    (closedShortBoundEqualityPayloadPolynomial rowCount)
    (contextualBranchesUnderBoundPayloadEnvelope ∅ rowCount
      (Rewriting.free body) branchPolynomial)

noncomputable def
    compileCompactParserSyntaxAdjacentRowsBoundedDirectUniversalContext
    (tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
        stateBoundary stateCount rowIndex valueBound)
    (hrowCount : rowCount <= numericBound)
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
    CertifiedPAContextProof ∅
      ((compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
        tokenCount stateBoundary stateCount valueBound).ballLT
          (shortBinaryNumeralTerm rowCount)) := by
  let body := compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable
    width tokenCount stateBoundary stateCount valueBound
  let branches :=
    compactParserSyntaxAdjacentRowsBoundedFullyDirectBranches tokenTable width
      tokenCount stateBoundary stateCount rowCount valueBound numericBound
      bitBound hrows hrowCount hvalueBound hwidth hwidthBit htokenCount
      hstateCount htokenTableSize hstateBoundarySize hareaNumeric hareaBit
      hnumericSize hbitPositive
  let boundEquality :=
    compactParserSyntaxAdjacentRowsBoundedDirectBoundEquality rowCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) rowCount
    (Rew.bShift (shortBinaryNumeralTerm rowCount)) body boundEquality branches
  exact CertifiedPAContextProof.cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm rowCount)) body) =
        body.ballLT (shortBinaryNumeralTerm rowCount)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

theorem
    compileCompactParserSyntaxAdjacentRowsBoundedDirectUniversalContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
        stateBoundary stateCount rowIndex valueBound)
    (hrowCount : rowCount <= numericBound)
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
    (compileCompactParserSyntaxAdjacentRowsBoundedDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound hrows hrowCount hvalueBound hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive).payloadLength <=
    compactParserSyntaxAdjacentRowsBoundedDirectUniversalPolynomialResource
      tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
        numericBound bitBound := by
  let body := compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable
    width tokenCount stateBoundary stateCount valueBound
  let branches :=
    compactParserSyntaxAdjacentRowsBoundedFullyDirectBranches tokenTable width
      tokenCount stateBoundary stateCount rowCount valueBound numericBound
      bitBound hrows hrowCount hvalueBound hwidth hwidthBit htokenCount
      hstateCount htokenTableSize hstateBoundarySize hareaNumeric hareaBit
      hnumericSize hbitPositive
  let boundEquality :=
    compactParserSyntaxAdjacentRowsBoundedDirectBoundEquality rowCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) rowCount
    (Rew.bShift (shortBinaryNumeralTerm rowCount)) body boundEquality branches
  let branchPolynomial :=
    explicitDirectUniversalBranchesPayloadPolynomial rowCount body
      (compactParserSyntaxAdjacentRowsBoundedDirectBranchResource tokenTable
        width tokenCount stateBoundary stateCount valueBound numericBound
          bitBound)
  have hboundRaw :=
    compileClosedShortBoundEquality_payloadLength_le_publicPolynomial rowCount
  have hbound : boundEquality.payloadLength <=
      closedShortBoundEqualityPayloadPolynomial rowCount := by
    simpa only [boundEquality,
      compactParserSyntaxAdjacentRowsBoundedDirectBoundEquality,
      CertifiedPAContextProof.castContext_payloadLength,
      CertifiedPAContextProof.cast_payloadLength] using hboundRaw
  have hbranchesStructural :=
    compactParserSyntaxAdjacentRowsBoundedFullyDirectBranches_structuralPayloadBound_le
      tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound hrows hrowCount hvalueBound hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive
  have henvelopePolynomial :=
    compactParserSyntaxAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope_le_polynomial
      tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
        numericBound bitBound
  have hbranchesCore :
      branches.structuralPayloadBound rowCount <= branchPolynomial := by
    exact hbranchesStructural.trans henvelopePolynomial
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ rowCount
    (Rewriting.free body) branchPolynomial
  have hbranches :
      branches.compileUnderBoundAssumptionStructuralPayloadBound <=
        branchResource := by
    unfold branchResource contextualBranchesUnderBoundPayloadEnvelope
      CertifiedContextFiniteUniversalBranches.compileUnderBoundAssumptionStructuralPayloadBound
      CertifiedContextFiniteUniversalBranches.underExhaustionStructuralPayloadBound
    dsimp only [body, branchPolynomial] at hbranchesCore ⊢
    simp only [Finset.image_empty] at hbranchesCore ⊢
    omega
  have hstructural :=
    compileContextualTermBoundedUniversal_payloadLength_le_structural
      (Gamma := ∅) rowCount
      (Rew.bShift (shortBinaryNumeralTerm rowCount)) body boundEquality branches
  have htotal :=
    compileContextualTermBoundedUniversalStructuralPayloadBound_le_envelope
      (Gamma := ∅) rowCount
      (Rew.bShift (shortBinaryNumeralTerm rowCount)) body boundEquality branches
      (closedShortBoundEqualityPayloadPolynomial rowCount) branchResource
      hbound hbranches
  unfold
    compileCompactParserSyntaxAdjacentRowsBoundedDirectUniversalContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change direct.payloadLength <= _
  exact hstructural.trans (htotal.trans (by
    rfl))

#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedDirectUniversalContext
#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedDirectUniversalContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectUniversal
