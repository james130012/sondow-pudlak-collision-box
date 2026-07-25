import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsContextualBranchesFullyFixedBounds
import integration.FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds

/-!
# Fully fixed universal resource for syntax-task same rows

The contextual branches, normalized-bound equality, and the closed short
bounded-universal shell are charged to the same public numeric and bit-width
coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniversalFullyFixedBounds

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
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsContextualBranchesFullyFixedBounds

private abbrev taskSameRowsZeroValuationUniversal : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate.zeroValuation

def taskSameRowsShiftedBoundFixedScalePolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound + binaryNumeralTermCodeEnvelope bitBound

def taskSameRowsUniversalFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
    (taskSameRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
    (taskSameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
    (taskSameRowsContextualBranchesFullyFixedPayloadPolynomial numericBound
      bitBound)
    (compileShiftedBoundEqualityFixedPayloadPolynomial
      (taskSameRowsShiftedBoundFixedScalePolynomial numericBound bitBound))

private theorem taskSameRowsShiftedBoundResource_le_fullyFixed
    (sourceCount numericBound bitBound : Nat)
    (hsourceCount : sourceCount <= numericBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound) :
    compileShiftedBoundEqualityPayloadResource
        taskSameRowsZeroValuationUniversal ∅
        (shortBinaryNumeralTerm sourceCount) <=
      compileShiftedBoundEqualityFixedPayloadPolynomial
        (taskSameRowsShiftedBoundFixedScalePolynomial numericBound bitBound) := by
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let scale :=
    taskSameRowsShiftedBoundFixedScalePolynomial numericBound bitBound
  have hclosed : boundTerm.freeVariables = ∅ := by
    dsimp only [boundTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty sourceCount
  have hpublic :=
    compileShiftedBoundEqualityPayloadResource_le_publicPolynomial
      taskSameRowsZeroValuationUniversal ∅ boundTerm hclosed
  have hcode :
      (binaryTermCode boundTerm).length <= scale := by
    have hraw := binaryNumeralTerm_code_length_le_envelope sourceCount
      bitBound hsourceCountSize
    dsimp only [boundTerm, scale]
    unfold taskSameRowsShiftedBoundFixedScalePolynomial
    omega
  have hfixed :=
    compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq
      taskSameRowsZeroValuationUniversal ∅ boundTerm
      (compileShiftedBoundEqualityPayloadPublicPolynomial
        taskSameRowsZeroValuationUniversal ∅ boundTerm)
      (compileShiftedBoundEqualityFixedPayloadPolynomial scale)
      scale rfl rfl hclosed (by simp)
      (by
        dsimp only [taskSameRowsZeroValuationUniversal]
        simp [
          FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate.zeroValuation,
          scale, taskSameRowsShiftedBoundFixedScalePolynomial])
      (by
        dsimp only [boundTerm]
        rw [termValue_shortBinaryNumeralTerm]
        dsimp only [scale]
        unfold taskSameRowsShiftedBoundFixedScalePolynomial
        omega)
      hcode
  exact hpublic.trans hfixed

theorem
    compactAdditiveSyntaxTaskListSameRowsUniversalPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskListSameRowsUniversalPayloadEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows <=
      taskSameRowsUniversalFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let body := compactAdditiveSyntaxTaskListSameRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma :=
    valuationContext outerVariables taskSameRowsZeroValuationUniversal
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅
    sourceCount (Rewriting.free body)
    (compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows)
  let boundResource := compileShiftedBoundEqualityPayloadResource
    taskSameRowsZeroValuationUniversal ∅ boundTerm
  have houterVariables : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body, boundTerm]
    exact
      compactAdditiveSyntaxTaskListSameRowsOuterFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
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
        taskSameRowsUniversalBodyFormulaCodePolynomial numericBound
          bitBound := by
    dsimp only [body]
    exact compactAdditiveSyntaxTaskListSameRowsBody_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound htokenCount htokenTableSize hwidthSize htokenCountSize
      hsourceBoundarySize htargetBoundarySize
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCount).trans hnumericSize
  have hboundResource :
      boundResource <=
        compileShiftedBoundEqualityFixedPayloadPolynomial
          (taskSameRowsShiftedBoundFixedScalePolynomial numericBound
            bitBound) := by
    dsimp only [boundResource, boundTerm]
    exact taskSameRowsShiftedBoundResource_le_fullyFixed sourceCount
      numericBound bitBound hsourceCount hsourceCountSize
  have hbranch :
      branchResource <=
        taskSameRowsContextualBranchesFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [branchResource, body]
    exact
      compactAdditiveSyntaxTaskListSameRowsContextualBranchesResource_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        numericBound bitBound rows hwidth htokenCount hsourceCount
        htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hshell :=
    compileContextualTermBoundedUniversalPayloadEnvelope_empty_short_le_fixed
      body sourceCount numericBound bitBound
      (taskSameRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (taskSameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
      boundResource branchResource
      (compileShiftedBoundEqualityFixedPayloadPolynomial
        (taskSameRowsShiftedBoundFixedScalePolynomial numericBound bitBound))
      (taskSameRowsContextualBranchesFullyFixedPayloadPolynomial numericBound
        bitBound)
      hsourceCount hsourceCountSize
      (by
        unfold taskSameRowsUniversalSyntaxFixedPolynomial
        omega)
      hbody hboundResource hbranch
  unfold compactAdditiveSyntaxTaskListSameRowsUniversalPayloadEnvelope
  simp only [termValue_shortBinaryNumeralTerm]
  rw [show
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm sourceCount))
      (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary)).freeVariables = ∅ by
      exact
        compactAdditiveSyntaxTaskListSameRowsOuterFormula_freeVariables_eq_empty_fixed
          tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary]
  simp only [valuationContext, Finset.image_empty]
  unfold taskSameRowsUniversalFullyFixedPayloadPolynomial
  simpa only [body, boundTerm, branchResource, boundResource] using hshell

#print axioms taskSameRowsShiftedBoundResource_le_fullyFixed
#print axioms
  compactAdditiveSyntaxTaskListSameRowsUniversalPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniversalFullyFixedBounds
