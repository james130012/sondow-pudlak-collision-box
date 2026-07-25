import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniversalBodyFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

/-!
# Fully fixed branch recursion for syntax-task same rows

The exact finite row recursion is bounded using the already fixed branch sum,
closed outer context, and fixed source-body syntax.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListSameRowsBranchesFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniformBranchFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniversalBodyFixedBounds

private abbrev taskSameRowsZeroValuationBranchesFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate.zeroValuation

def taskSameRowsUniversalSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound +
    taskSameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound

def taskSameRowsUniversalFormulaFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (taskSameRowsUniversalSyntaxFixedPolynomial numericBound bitBound) +
    2 * taskSameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound

def taskSameRowsUniversalLocalPayloadFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (taskSameRowsUniversalFormulaFixedPolynomial numericBound bitBound)

def taskSameRowsBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (taskSameRowsAllBranchesFullyFixedPayloadPolynomial numericBound bitBound +
      3 * taskSameRowsUniversalLocalPayloadFixedPolynomial numericBound
        bitBound)

private theorem
    hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf_taskFixed
    (totalBound : Nat) (outerVariables : Finset Nat)
    (valuation : Nat -> Nat)
    (body : ArithmeticSemiformula Nat 1)
    {small large : Nat} (hresource : small <= large) :
    forall bound,
      hybridBranchesUniformStructuralPayloadEnvelope totalBound outerVariables
          valuation body small bound <=
        hybridBranchesUniformStructuralPayloadEnvelope totalBound
          outerVariables valuation body large bound
  | 0 => by rfl
  | bound + 1 => by
      simp only [hybridBranchesUniformStructuralPayloadEnvelope]
      have hinduction :=
        hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf_taskFixed
          totalBound outerVariables valuation body hresource bound
      omega

theorem
    compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope_le_fullyFixed
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
    compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows <=
      taskSameRowsBranchesFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let body := compactAdditiveSyntaxTaskListSameRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
  let outerVariables := outerFormula.freeVariables
  let leafBound :=
    taskSameRowsAllBranchesFullyFixedPayloadPolynomial numericBound bitBound
  let exactCore :=
    hybridBranchesUniformStructuralPayloadEnvelope sourceCount outerVariables
      taskSameRowsZeroValuationBranchesFixed body
      (compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows)
      sourceCount
  let fixedLeafCore :=
    hybridBranchesUniformStructuralPayloadEnvelope sourceCount outerVariables
      taskSameRowsZeroValuationBranchesFixed body leafBound sourceCount
  let Gamma :=
    (valuationContext outerVariables
      taskSameRowsZeroValuationBranchesFixed).image Rewriting.shift
  let contextualCore :=
    contextualHybridUniversalBranchesPayloadPolynomial Gamma sourceCount
      sourceCount body leafBound
  have hleaf :=
    compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound rows hwidth htokenCount hsourceCount
      htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hcore : exactCore <= fixedLeafCore := by
    dsimp only [exactCore, fixedLeafCore]
    exact
      hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf_taskFixed
        sourceCount outerVariables taskSameRowsZeroValuationBranchesFixed body
        hleaf sourceCount
  have houterVariables : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      compactAdditiveSyntaxTaskListSameRowsOuterFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
  have hGammaCard : Gamma.card <= 1 := by
    dsimp only [Gamma]
    rw [houterVariables]
    simp [valuationContext]
  have hcontextual : fixedLeafCore <= contextualCore := by
    dsimp only [fixedLeafCore, contextualCore]
    exact
      hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
        sourceCount outerVariables taskSameRowsZeroValuationBranchesFixed body
        leafBound hGammaCard (caseCount := sourceCount) le_rfl
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
  have hsyntax :
      explicitHybridUniversalSyntaxResource sourceCount body <=
        taskSameRowsUniversalSyntaxFixedPolynomial numericBound
          bitBound := by
    unfold explicitHybridUniversalSyntaxResource
      taskSameRowsUniversalSyntaxFixedPolynomial
    omega
  have hclosed :=
    boundedUniversalClosedFormulaEnvelope_mono_completed hsyntax
  have hformula :
      explicitHybridUniversalFormulaEnvelope sourceCount body <=
        taskSameRowsUniversalFormulaFixedPolynomial numericBound
          bitBound := by
    unfold explicitHybridUniversalFormulaEnvelope
      taskSameRowsUniversalFormulaFixedPolynomial
    omega
  have hlocal :
      contextualHybridUniversalLocalPayloadEnvelope Gamma sourceCount body <=
        taskSameRowsUniversalLocalPayloadFixedPolynomial numericBound
          bitBound := by
    have hGammaEmpty : Gamma = ∅ := by
      dsimp only [Gamma]
      rw [houterVariables]
      simp [valuationContext]
    rw [hGammaEmpty]
    unfold contextualHybridUniversalLocalPayloadEnvelope
      contextualHybridUniversalFormulaEnvelope
      contextualHybridUniversalFormulaCodeSum
      taskSameRowsUniversalLocalPayloadFixedPolynomial
    simpa only [Finset.sum_empty, Nat.add_zero] using
      smallContextAssemblyEnvelope_mono_local hformula
  have hfixed :
      contextualCore <=
        taskSameRowsBranchesFullyFixedPayloadPolynomial numericBound
          bitBound := by
    unfold contextualCore contextualHybridUniversalBranchesPayloadPolynomial
      taskSameRowsBranchesFullyFixedPayloadPolynomial
    exact Nat.mul_le_mul (by omega) (Nat.add_le_add le_rfl
      (Nat.mul_le_mul_left 3 hlocal))
  have htransparent :
      compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope
          tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary rows = exactCore := by
    unfold compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope
    dsimp only [exactCore, body, outerFormula, outerVariables]
    simp only [termValue_shortBinaryNumeralTerm]
  rw [htransparent]
  exact hcore.trans (hcontextual.trans hfixed)

#print axioms
  compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListSameRowsBranchesFullyFixedBounds
