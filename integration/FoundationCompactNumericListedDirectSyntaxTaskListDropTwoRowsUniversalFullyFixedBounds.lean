import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsContextualBranchesFullyFixedBounds
import integration.FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds

/-!
# Fully fixed universal resource for syntax-task drop two

The contextual target-row branches, normalized-bound equality, and closed
short bounded-universal shell use the same public numeric and bit bounds.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsUniversalFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsContextualBranchesFullyFixedBounds

private abbrev dropTwoRowsZeroValuationUniversal : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

def taskDropTwoShiftedBoundFixedScalePolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound + binaryNumeralTermCodeEnvelope bitBound

def taskDropTwoUniversalFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
    (taskDropTwoUniversalSyntaxFixedPolynomial numericBound bitBound)
    (taskDropTwoUniversalBodyFormulaCodePolynomial numericBound bitBound)
    (taskDropTwoContextualBranchesFullyFixedPayloadPolynomial numericBound
      bitBound)
    (compileShiftedBoundEqualityFixedPayloadPolynomial
      (taskDropTwoShiftedBoundFixedScalePolynomial numericBound bitBound))

private theorem taskDropTwoShiftedBoundResource_le_fullyFixed
    (targetCount numericBound bitBound : Nat)
    (htargetCount : targetCount <= numericBound)
    (htargetCountSize : Nat.size targetCount <= bitBound) :
    compileShiftedBoundEqualityPayloadResource
        dropTwoRowsZeroValuationUniversal ∅
        (shortBinaryNumeralTerm targetCount) <=
      compileShiftedBoundEqualityFixedPayloadPolynomial
        (taskDropTwoShiftedBoundFixedScalePolynomial numericBound
          bitBound) := by
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm targetCount
  let scale :=
    taskDropTwoShiftedBoundFixedScalePolynomial numericBound bitBound
  have hclosed : boundTerm.freeVariables = ∅ := by
    dsimp only [boundTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty targetCount
  have hpublic :=
    compileShiftedBoundEqualityPayloadResource_le_publicPolynomial
      dropTwoRowsZeroValuationUniversal ∅ boundTerm hclosed
  have hcode :
      (binaryTermCode boundTerm).length <= scale := by
    have hraw := binaryNumeralTerm_code_length_le_envelope targetCount
      bitBound htargetCountSize
    dsimp only [boundTerm, scale]
    unfold taskDropTwoShiftedBoundFixedScalePolynomial
    omega
  have hfixed :=
    compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq
      dropTwoRowsZeroValuationUniversal ∅ boundTerm
      (compileShiftedBoundEqualityPayloadPublicPolynomial
        dropTwoRowsZeroValuationUniversal ∅ boundTerm)
      (compileShiftedBoundEqualityFixedPayloadPolynomial scale)
      scale rfl rfl hclosed (by simp)
      (by
        dsimp only [dropTwoRowsZeroValuationUniversal]
        simp [
          FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation,
          scale, taskDropTwoShiftedBoundFixedScalePolynomial])
      (by
        dsimp only [boundTerm]
        rw [termValue_shortBinaryNumeralTerm]
        dsimp only [scale]
        unfold taskDropTwoShiftedBoundFixedScalePolynomial
        omega)
      hcode
  exact hpublic.trans hfixed

theorem
    compactAdditiveSyntaxTaskListDropTwoRowsUniversalPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 2)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveSyntaxTaskListDropRowData tokenTable width tokenCount
        sourceBoundary targetBoundary 2 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsUniversalPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        2 rows <=
      taskDropTwoUniversalFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let body :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 2
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm targetCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma :=
    valuationContext outerVariables dropTwoRowsZeroValuationUniversal
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅
    targetCount (Rewriting.free body)
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesTransparentEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      2 rows)
  let boundResource := compileShiftedBoundEqualityPayloadResource
    dropTwoRowsZeroValuationUniversal ∅ boundTerm
  have htargetCount : targetCount <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have houterVariables : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body, boundTerm]
    exact
      compactAdditiveSyntaxTaskListDropTwoRowsOuterFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount sourceBoundary targetCount targetBoundary
  have hGamma : Gamma = ∅ := by
    dsimp only [Gamma]
    rw [houterVariables]
    simp [valuationContext]
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody :
      (binaryFormulaCode body).length <=
        taskDropTwoUniversalBodyFormulaCodePolynomial numericBound bitBound := by
    dsimp only [body]
    exact compactAdditiveSyntaxTaskListDropTwoRowsBody_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound htokenCount htokenTableSize hwidthSize htokenCountSize
      hsourceBoundarySize htargetBoundarySize
  have htargetCountSize : Nat.size targetCount <= bitBound :=
    (Nat.size_le_size htargetCount).trans hnumericSize
  have hboundResource :
      boundResource <=
        compileShiftedBoundEqualityFixedPayloadPolynomial
          (taskDropTwoShiftedBoundFixedScalePolynomial numericBound
            bitBound) := by
    dsimp only [boundResource, boundTerm]
    exact taskDropTwoShiftedBoundResource_le_fullyFixed targetCount
      numericBound bitBound htargetCount htargetCountSize
  have hbranch :
      branchResource <=
        taskDropTwoContextualBranchesFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [branchResource, body]
    exact
      compactAdditiveSyntaxTaskListDropTwoRowsContextualBranchesResource_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount numericBound bitBound hgraph rows hwidth htokenCount
        hsourceCount htokenTableSize hsourceBoundarySize htargetBoundarySize
        hnumericSize
  have hshell :=
    compileContextualTermBoundedUniversalPayloadEnvelope_empty_short_le_fixed
      body targetCount numericBound bitBound
      (taskDropTwoUniversalSyntaxFixedPolynomial numericBound bitBound)
      (taskDropTwoUniversalBodyFormulaCodePolynomial numericBound bitBound)
      boundResource branchResource
      (compileShiftedBoundEqualityFixedPayloadPolynomial
        (taskDropTwoShiftedBoundFixedScalePolynomial numericBound bitBound))
      (taskDropTwoContextualBranchesFullyFixedPayloadPolynomial numericBound
        bitBound)
      htargetCount htargetCountSize
      (by
        unfold taskDropTwoUniversalSyntaxFixedPolynomial
        omega)
      hbody hboundResource hbranch
  unfold
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsUniversalPayloadEnvelope
  simp only [termValue_shortBinaryNumeralTerm]
  rw [show
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm targetCount))
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary 2)).freeVariables = ∅ by
      exact
        compactAdditiveSyntaxTaskListDropTwoRowsOuterFormula_freeVariables_eq_empty_fixed
          tokenTable width tokenCount sourceBoundary targetCount
          targetBoundary]
  simp only [valuationContext, Finset.image_empty]
  unfold taskDropTwoUniversalFullyFixedPayloadPolynomial
  simpa only [body, boundTerm, branchResource, boundResource] using hshell

#print axioms taskDropTwoShiftedBoundResource_le_fullyFixed
#print axioms
  compactAdditiveSyntaxTaskListDropTwoRowsUniversalPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsUniversalFullyFixedBounds
