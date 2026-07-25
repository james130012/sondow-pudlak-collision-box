import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailContextualBranchesFullyFixedBounds
import integration.FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds

/-!
# Fully fixed universal resource for syntax-task cons-rows tail

The contextual branches, normalized-bound equality, and the closed short
bounded-universal shell are charged to the same public numeric and bit-width
coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailUniversalFullyFixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailContextualBranchesFullyFixedBounds

private abbrev taskConsRowsTailZeroValuationUniversal : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation

def taskConsRowsTailShiftedBoundFixedScalePolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound + binaryNumeralTermCodeEnvelope bitBound

def taskConsRowsTailUniversalFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
    (taskConsRowsTailUniversalSyntaxFixedPolynomial numericBound bitBound)
    (taskConsRowsTailUniversalBodyFormulaCodePolynomial numericBound bitBound)
    (taskConsRowsTailContextualBranchesFullyFixedPayloadPolynomial numericBound
      bitBound)
    (compileShiftedBoundEqualityFixedPayloadPolynomial
      (taskConsRowsTailShiftedBoundFixedScalePolynomial numericBound bitBound))

private theorem taskConsRowsTailShiftedBoundResource_le_fullyFixed
    (sourceCount numericBound bitBound : Nat)
    (hsourceCount : sourceCount <= numericBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound) :
    compileShiftedBoundEqualityPayloadResource
        taskConsRowsTailZeroValuationUniversal ∅
        (shortBinaryNumeralTerm sourceCount) <=
      compileShiftedBoundEqualityFixedPayloadPolynomial
        (taskConsRowsTailShiftedBoundFixedScalePolynomial numericBound bitBound) := by
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let scale :=
    taskConsRowsTailShiftedBoundFixedScalePolynomial numericBound bitBound
  have hclosed : boundTerm.freeVariables = ∅ := by
    dsimp only [boundTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty sourceCount
  have hpublic :=
    compileShiftedBoundEqualityPayloadResource_le_publicPolynomial
      taskConsRowsTailZeroValuationUniversal ∅ boundTerm hclosed
  have hcode :
      (binaryTermCode boundTerm).length <= scale := by
    have hraw := binaryNumeralTerm_code_length_le_envelope sourceCount
      bitBound hsourceCountSize
    dsimp only [boundTerm, scale]
    unfold taskConsRowsTailShiftedBoundFixedScalePolynomial
    omega
  have hfixed :=
    compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq
      taskConsRowsTailZeroValuationUniversal ∅ boundTerm
      (compileShiftedBoundEqualityPayloadPublicPolynomial
        taskConsRowsTailZeroValuationUniversal ∅ boundTerm)
      (compileShiftedBoundEqualityFixedPayloadPolynomial scale)
      scale rfl rfl hclosed (by simp)
      (by
        dsimp only [taskConsRowsTailZeroValuationUniversal]
        simp [
          FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation,
          scale, taskConsRowsTailShiftedBoundFixedScalePolynomial])
      (by
        dsimp only [boundTerm]
        rw [termValue_shortBinaryNumeralTerm]
        dsimp only [scale]
        unfold taskConsRowsTailShiftedBoundFixedScalePolynomial
        omega)
      hcode
  exact hpublic.trans hfixed

theorem
    compactAdditiveSyntaxTaskListConsRowsTailUniversalPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCountSuccessor : sourceCount + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskListConsRowsTailUniversalPayloadEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows <=
      taskConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let body := compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width
    tokenCount sourceBoundary targetBoundary
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma :=
    valuationContext outerVariables taskConsRowsTailZeroValuationUniversal
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅
    sourceCount (Rewriting.free body)
    (compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows)
  let boundResource := compileShiftedBoundEqualityPayloadResource
    taskConsRowsTailZeroValuationUniversal ∅ boundTerm
  have hsourceCount : sourceCount <= numericBound := by omega
  have houterVariables : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body, boundTerm]
    exact
      compactAdditiveSyntaxTaskListConsRowsTailOuterFormula_freeVariables_eq_empty_fixed
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
        taskConsRowsTailUniversalBodyFormulaCodePolynomial numericBound
          bitBound := by
    dsimp only [body]
    exact compactAdditiveSyntaxTaskListConsRowsTailBody_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound htokenCount htokenTableSize hwidthSize htokenCountSize
      hsourceBoundarySize htargetBoundarySize
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCount).trans hnumericSize
  have hboundResource :
      boundResource <=
        compileShiftedBoundEqualityFixedPayloadPolynomial
          (taskConsRowsTailShiftedBoundFixedScalePolynomial numericBound
            bitBound) := by
    dsimp only [boundResource, boundTerm]
    exact taskConsRowsTailShiftedBoundResource_le_fullyFixed sourceCount
      numericBound bitBound hsourceCount hsourceCountSize
  have hbranch :
      branchResource <=
        taskConsRowsTailContextualBranchesFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [branchResource, body]
    exact
      compactAdditiveSyntaxTaskListConsRowsTailContextualBranchesResource_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        numericBound bitBound rows hwidth htokenCount hsourceCountSuccessor
        htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hshell :=
    compileContextualTermBoundedUniversalPayloadEnvelope_empty_short_le_fixed
      body sourceCount numericBound bitBound
      (taskConsRowsTailUniversalSyntaxFixedPolynomial numericBound bitBound)
      (taskConsRowsTailUniversalBodyFormulaCodePolynomial numericBound bitBound)
      boundResource branchResource
      (compileShiftedBoundEqualityFixedPayloadPolynomial
        (taskConsRowsTailShiftedBoundFixedScalePolynomial numericBound bitBound))
      (taskConsRowsTailContextualBranchesFullyFixedPayloadPolynomial numericBound
        bitBound)
      hsourceCount hsourceCountSize
      (by
        unfold taskConsRowsTailUniversalSyntaxFixedPolynomial
        omega)
      hbody hboundResource hbranch
  unfold compactAdditiveSyntaxTaskListConsRowsTailUniversalPayloadEnvelope
  simp only [termValue_shortBinaryNumeralTerm]
  rw [show
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm sourceCount))
      (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary)).freeVariables = ∅ by
      exact
        compactAdditiveSyntaxTaskListConsRowsTailOuterFormula_freeVariables_eq_empty_fixed
          tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary]
  simp only [valuationContext, Finset.image_empty]
  unfold taskConsRowsTailUniversalFullyFixedPayloadPolynomial
  simpa only [body, boundTerm, branchResource, boundResource] using hshell

#print axioms taskConsRowsTailShiftedBoundResource_le_fullyFixed
#print axioms
  compactAdditiveSyntaxTaskListConsRowsTailUniversalPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailUniversalFullyFixedBounds
