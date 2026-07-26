import integration.FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectUniversal
import integration.FoundationCompactPACertifiedContextEquality
import integration.FoundationCompactPAValuationTermCompilerPublicBounds

/-!
# Direct bounded universal at the exact parser fuel term

The branch tree still ranges over the numeric parser fuel.  Its canonical
successor bound is first identified with the short binary numeral and then,
inside PA, with the original composite parser fuel term.  The bounded
universal therefore preserves the syntax used by the exact parser graph.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversal

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPACertifiedContextEquality
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranches
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranchTree
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality

private theorem compactParserSyntaxExactFuelTerm_shift_eq_self
    (inputCount : Nat) :
    Rew.shift (compactParserSyntaxExactFuelTerm inputCount) =
      compactParserSyntaxExactFuelTerm inputCount := by
  apply Semiterm.rew_eq_of_funEqOn Rew.shift Rew.id
  · intro index
    simp
  · intro index hindex
    have hfree :
        index ∈
          (compactParserSyntaxExactFuelTerm inputCount).freeVariables :=
      hindex
    rw [compactParserSyntaxExactFuelTerm_freeVariables_eq_empty] at hfree
    simp at hfree

private noncomputable def compactParserSyntaxExactFuelShortBoundEquality
    (inputCount : Nat) :
    CertifiedPAContextProof
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (“!!(iteratedSuccessorTerm 0
          (compactParserSyntaxExactFuel inputCount)) =
        !!(Rew.free
          (Rew.bShift
            (shortBinaryNumeralTerm
              (compactParserSyntaxExactFuel inputCount))))” :
        ValuationFormula) := by
  let fuel := compactParserSyntaxExactFuel inputCount
  let raw := compileClosedShortBoundEquality fuel
  have hformula :
      (“!!(iteratedSuccessorTerm 0 fuel) =
        !!(shortBinaryNumeralTerm fuel)” : ValuationFormula) =
      (“!!(iteratedSuccessorTerm 0 fuel) =
        !!(Rew.free
          (Rew.bShift (shortBinaryNumeralTerm fuel)))” :
        ValuationFormula) := by
    simp
  exact CertifiedPAContextProof.castContext (by simp)
    (CertifiedPAContextProof.cast hformula raw)

private noncomputable def compactParserSyntaxExactFuelTermEquality
    (inputCount : Nat) :
    CertifiedPAContextProof
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (“!!(Rew.free
          (Rew.bShift
            (shortBinaryNumeralTerm
              (compactParserSyntaxExactFuel inputCount)))) =
        !!(Rew.free
          (Rew.bShift
            (compactParserSyntaxExactFuelTerm inputCount)))” :
        ValuationFormula) := by
  let raw := (compactParserSyntaxExactFuelEqualityBound inputCount).proof
  have hformula :
      (“!!(shortBinaryNumeralTerm
          (compactParserSyntaxExactFuel inputCount)) =
        !!(compactParserSyntaxExactFuelTerm inputCount)” :
        ValuationFormula) =
      (“!!(Rew.free
          (Rew.bShift
            (shortBinaryNumeralTerm
              (compactParserSyntaxExactFuel inputCount)))) =
        !!(Rew.free
          (Rew.bShift
            (compactParserSyntaxExactFuelTerm inputCount)))” :
        ValuationFormula) := by
    simp only [free_bShift_term]
    rw [compactParserSyntaxExactFuelTerm_shift_eq_self]
    simp
  exact CertifiedPAContextProof.castContext (by simp)
    (CertifiedPAContextProof.cast hformula raw)

def compactParserSyntaxExactFuelDirectBoundEqualityResource
    (inputCount : Nat) : Nat :=
  let fuel := compactParserSyntaxExactFuel inputCount
  contextualEqualityTransitivityStructuralPayloadBound
    ((∅ : Finset ValuationFormula).image Rewriting.shift)
    (iteratedSuccessorTerm 0 fuel)
    (Rew.free (Rew.bShift (shortBinaryNumeralTerm fuel)))
    (Rew.free (Rew.bShift
      (compactParserSyntaxExactFuelTerm inputCount)))
    (closedShortBoundEqualityPayloadPolynomial fuel)
    (compactParserSyntaxExactFuelEqualityPayloadResource inputCount)

noncomputable def compactParserSyntaxExactFuelDirectBoundEquality
    (inputCount : Nat) :
    CertifiedPAContextProof
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (“!!(iteratedSuccessorTerm 0
          (compactParserSyntaxExactFuel inputCount)) =
        !!(Rew.free
          (Rew.bShift
            (compactParserSyntaxExactFuelTerm inputCount)))” :
        ValuationFormula) :=
  contextualEqualityTransitivity
    (iteratedSuccessorTerm 0
      (compactParserSyntaxExactFuel inputCount))
    (Rew.free (Rew.bShift
      (shortBinaryNumeralTerm
        (compactParserSyntaxExactFuel inputCount))))
    (Rew.free (Rew.bShift
      (compactParserSyntaxExactFuelTerm inputCount)))
    (compactParserSyntaxExactFuelShortBoundEquality inputCount)
    (compactParserSyntaxExactFuelTermEquality inputCount)

theorem compactParserSyntaxExactFuelDirectBoundEquality_payloadLength_le
    (inputCount : Nat) :
    (compactParserSyntaxExactFuelDirectBoundEquality inputCount).payloadLength <=
      compactParserSyntaxExactFuelDirectBoundEqualityResource inputCount := by
  let fuel := compactParserSyntaxExactFuel inputCount
  let leftProof :=
    compactParserSyntaxExactFuelShortBoundEquality inputCount
  let rightProof :=
    compactParserSyntaxExactFuelTermEquality inputCount
  have hleftRaw :=
    compileClosedShortBoundEquality_payloadLength_le_publicPolynomial fuel
  have hleft : leftProof.payloadLength <=
      closedShortBoundEqualityPayloadPolynomial fuel := by
    simpa only [leftProof,
      compactParserSyntaxExactFuelShortBoundEquality,
      CertifiedPAContextProof.castContext_payloadLength,
      CertifiedPAContextProof.cast_payloadLength] using hleftRaw
  have hrightRaw :=
    (compactParserSyntaxExactFuelEqualityBound inputCount).payloadLength_le
  have hright : rightProof.payloadLength <=
      compactParserSyntaxExactFuelEqualityPayloadResource inputCount := by
    simpa only [rightProof,
      compactParserSyntaxExactFuelTermEquality,
      CertifiedPAContextProof.castContext_payloadLength,
      CertifiedPAContextProof.cast_payloadLength] using hrightRaw
  have hstructural :=
    contextualEqualityTransitivity_payloadLength_le
      (iteratedSuccessorTerm 0 fuel)
      (Rew.free (Rew.bShift (shortBinaryNumeralTerm fuel)))
      (Rew.free (Rew.bShift
        (compactParserSyntaxExactFuelTerm inputCount)))
      leftProof rightProof
  have hmono :=
    contextualEqualityTransitivityStructuralPayloadBound_mono
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (iteratedSuccessorTerm 0 fuel)
      (Rew.free (Rew.bShift (shortBinaryNumeralTerm fuel)))
      (Rew.free (Rew.bShift
        (compactParserSyntaxExactFuelTerm inputCount)))
      leftProof.payloadLength rightProof.payloadLength
      (closedShortBoundEqualityPayloadPolynomial fuel)
      (compactParserSyntaxExactFuelEqualityPayloadResource inputCount)
      hleft hright
  change
    (contextualEqualityTransitivity
      (iteratedSuccessorTerm 0 fuel)
      (Rew.free (Rew.bShift (shortBinaryNumeralTerm fuel)))
      (Rew.free (Rew.bShift
        (compactParserSyntaxExactFuelTerm inputCount)))
      leftProof rightProof).payloadLength <= _
  exact hstructural.trans hmono

def compactParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversalResource
    (tokenTable width tokenCount stateBoundary stateCount inputCount
      valueBound numericBound bitBound : Nat) : Nat :=
  let fuel := compactParserSyntaxExactFuel inputCount
  let body :=
    compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
      tokenCount stateBoundary stateCount valueBound
  let branchPolynomial :=
    explicitDirectUniversalBranchesPayloadPolynomial fuel body
      (compactParserSyntaxAdjacentRowsBoundedDirectBranchResource tokenTable
        width tokenCount stateBoundary stateCount valueBound numericBound
          bitBound)
  compileContextualTermBoundedUniversalPayloadEnvelope ∅ fuel
    (Rew.bShift (compactParserSyntaxExactFuelTerm inputCount)) body
    (compactParserSyntaxExactFuelDirectBoundEqualityResource inputCount)
    (contextualBranchesUnderBoundPayloadEnvelope ∅ fuel
      (Rewriting.free body) branchPolynomial)

noncomputable def
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversalContext
    (tokenTable width tokenCount stateBoundary stateCount inputCount valueBound
      numericBound bitBound : Nat)
    (hrows : ∀ rowIndex < compactParserSyntaxExactFuel inputCount,
      CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
        stateBoundary stateCount rowIndex valueBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound)
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
          (compactParserSyntaxExactFuelTerm inputCount)) := by
  let fuel := compactParserSyntaxExactFuel inputCount
  let body := compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable
    width tokenCount stateBoundary stateCount valueBound
  let branches :=
    compactParserSyntaxAdjacentRowsBoundedFullyDirectBranches tokenTable width
      tokenCount stateBoundary stateCount fuel valueBound numericBound
      bitBound hrows hfuel hvalueBound hwidth hwidthBit htokenCount
      hstateCount htokenTableSize hstateBoundarySize hareaNumeric hareaBit
      hnumericSize hbitPositive
  let boundEquality :=
    compactParserSyntaxExactFuelDirectBoundEquality inputCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) fuel
    (Rew.bShift (compactParserSyntaxExactFuelTerm inputCount)) body
    boundEquality branches
  exact CertifiedPAContextProof.cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (compactParserSyntaxExactFuelTerm inputCount)) body) =
        body.ballLT (compactParserSyntaxExactFuelTerm inputCount)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

theorem
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversalContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount inputCount valueBound
      numericBound bitBound : Nat)
    (hrows : ∀ rowIndex < compactParserSyntaxExactFuel inputCount,
      CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
        stateBoundary stateCount rowIndex valueBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound)
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
    (compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount inputCount
      valueBound numericBound bitBound hrows hfuel hvalueBound hwidth
      hwidthBit htokenCount hstateCount htokenTableSize hstateBoundarySize
      hareaNumeric hareaBit hnumericSize hbitPositive).payloadLength <=
    compactParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversalResource
      tokenTable width tokenCount stateBoundary stateCount inputCount
        valueBound numericBound bitBound := by
  let fuel := compactParserSyntaxExactFuel inputCount
  let body := compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable
    width tokenCount stateBoundary stateCount valueBound
  let branches :=
    compactParserSyntaxAdjacentRowsBoundedFullyDirectBranches tokenTable width
      tokenCount stateBoundary stateCount fuel valueBound numericBound
      bitBound hrows hfuel hvalueBound hwidth hwidthBit htokenCount
      hstateCount htokenTableSize hstateBoundarySize hareaNumeric hareaBit
      hnumericSize hbitPositive
  let boundEquality :=
    compactParserSyntaxExactFuelDirectBoundEquality inputCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) fuel
    (Rew.bShift (compactParserSyntaxExactFuelTerm inputCount)) body
    boundEquality branches
  let branchPolynomial :=
    explicitDirectUniversalBranchesPayloadPolynomial fuel body
      (compactParserSyntaxAdjacentRowsBoundedDirectBranchResource tokenTable
        width tokenCount stateBoundary stateCount valueBound numericBound
          bitBound)
  have hbound :=
    compactParserSyntaxExactFuelDirectBoundEquality_payloadLength_le inputCount
  have hbranchesStructural :=
    compactParserSyntaxAdjacentRowsBoundedFullyDirectBranches_structuralPayloadBound_le
      tokenTable width tokenCount stateBoundary stateCount fuel valueBound
      numericBound bitBound hrows hfuel hvalueBound hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive
  have henvelopePolynomial :=
    compactParserSyntaxAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope_le_polynomial
      tokenTable width tokenCount stateBoundary stateCount fuel valueBound
        numericBound bitBound
  have hbranchesCore :
      branches.structuralPayloadBound fuel <= branchPolynomial := by
    exact hbranchesStructural.trans henvelopePolynomial
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ fuel
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
      (Gamma := ∅) fuel
      (Rew.bShift (compactParserSyntaxExactFuelTerm inputCount)) body
      boundEquality branches
  have htotal :=
    compileContextualTermBoundedUniversalStructuralPayloadBound_le_envelope
      (Gamma := ∅) fuel
      (Rew.bShift (compactParserSyntaxExactFuelTerm inputCount)) body
      boundEquality branches
      (compactParserSyntaxExactFuelDirectBoundEqualityResource inputCount)
      branchResource hbound hbranches
  unfold
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversalContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change direct.payloadLength <= _
  exact hstructural.trans (htotal.trans (by
    rfl))

#print axioms compactParserSyntaxExactFuelDirectBoundEquality
#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversalContext
#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversalContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversal
