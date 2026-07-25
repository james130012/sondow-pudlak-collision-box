import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailUniversalBodyFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

/-!
# Fully fixed branch recursion for syntax-task cons-rows tail

The exact finite row recursion is bounded using the already fixed branch sum,
closed outer context, and fixed source-body syntax.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailBranchesFullyFixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailUniformBranchFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailUniversalBodyFixedBounds

private abbrev taskConsRowsTailZeroValuationBranchesFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation

def taskConsRowsTailUniversalSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound +
    taskConsRowsTailUniversalBodyFormulaCodePolynomial numericBound bitBound

def taskConsRowsTailUniversalFormulaFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (taskConsRowsTailUniversalSyntaxFixedPolynomial numericBound bitBound) +
    2 * taskConsRowsTailUniversalBodyFormulaCodePolynomial numericBound bitBound

def taskConsRowsTailUniversalLocalPayloadFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (taskConsRowsTailUniversalFormulaFixedPolynomial numericBound bitBound)

def taskConsRowsTailBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (taskConsRowsTailAllBranchesFullyFixedPayloadPolynomial numericBound bitBound +
      3 * taskConsRowsTailUniversalLocalPayloadFixedPolynomial numericBound
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
    compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope_le_fullyFixed
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
    compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows <=
      taskConsRowsTailBranchesFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let body := compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width
    tokenCount sourceBoundary targetBoundary
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
  let outerVariables := outerFormula.freeVariables
  let leafBound :=
    taskConsRowsTailAllBranchesFullyFixedPayloadPolynomial numericBound bitBound
  let exactCore :=
    hybridBranchesUniformStructuralPayloadEnvelope sourceCount outerVariables
      taskConsRowsTailZeroValuationBranchesFixed body
      (compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadResourceSum tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows)
      sourceCount
  let fixedLeafCore :=
    hybridBranchesUniformStructuralPayloadEnvelope sourceCount outerVariables
      taskConsRowsTailZeroValuationBranchesFixed body leafBound sourceCount
  let Gamma :=
    (valuationContext outerVariables
      taskConsRowsTailZeroValuationBranchesFixed).image Rewriting.shift
  let contextualCore :=
    contextualHybridUniversalBranchesPayloadPolynomial Gamma sourceCount
      sourceCount body leafBound
  have hleaf :=
    compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadResourceSum_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound rows hwidth htokenCount hsourceCountSuccessor
      htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hsourceCount : sourceCount <= numericBound := by omega
  have hcore : exactCore <= fixedLeafCore := by
    dsimp only [exactCore, fixedLeafCore]
    exact
      hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf_taskFixed
        sourceCount outerVariables taskConsRowsTailZeroValuationBranchesFixed body
        hleaf sourceCount
  have houterVariables : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      compactAdditiveSyntaxTaskListConsRowsTailOuterFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
  have hGammaCard : Gamma.card <= 1 := by
    dsimp only [Gamma]
    rw [houterVariables]
    simp [valuationContext]
  have hcontextual : fixedLeafCore <= contextualCore := by
    dsimp only [fixedLeafCore, contextualCore]
    exact
      hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
        sourceCount outerVariables taskConsRowsTailZeroValuationBranchesFixed body
        leafBound hGammaCard (caseCount := sourceCount) le_rfl
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
  have hsyntax :
      explicitHybridUniversalSyntaxResource sourceCount body <=
        taskConsRowsTailUniversalSyntaxFixedPolynomial numericBound
          bitBound := by
    unfold explicitHybridUniversalSyntaxResource
      taskConsRowsTailUniversalSyntaxFixedPolynomial
    omega
  have hclosed :=
    boundedUniversalClosedFormulaEnvelope_mono_completed hsyntax
  have hformula :
      explicitHybridUniversalFormulaEnvelope sourceCount body <=
        taskConsRowsTailUniversalFormulaFixedPolynomial numericBound
          bitBound := by
    unfold explicitHybridUniversalFormulaEnvelope
      taskConsRowsTailUniversalFormulaFixedPolynomial
    omega
  have hlocal :
      contextualHybridUniversalLocalPayloadEnvelope Gamma sourceCount body <=
        taskConsRowsTailUniversalLocalPayloadFixedPolynomial numericBound
          bitBound := by
    have hGammaEmpty : Gamma = ∅ := by
      dsimp only [Gamma]
      rw [houterVariables]
      simp [valuationContext]
    rw [hGammaEmpty]
    unfold contextualHybridUniversalLocalPayloadEnvelope
      contextualHybridUniversalFormulaEnvelope
      contextualHybridUniversalFormulaCodeSum
      taskConsRowsTailUniversalLocalPayloadFixedPolynomial
    simpa only [Finset.sum_empty, Nat.add_zero] using
      smallContextAssemblyEnvelope_mono_local hformula
  have hfixed :
      contextualCore <=
        taskConsRowsTailBranchesFullyFixedPayloadPolynomial numericBound
          bitBound := by
    unfold contextualCore contextualHybridUniversalBranchesPayloadPolynomial
      taskConsRowsTailBranchesFullyFixedPayloadPolynomial
    exact Nat.mul_le_mul (by omega) (Nat.add_le_add le_rfl
      (Nat.mul_le_mul_left 3 hlocal))
  have htransparent :
      compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope
          tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary rows = exactCore := by
    unfold compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope
    dsimp only [exactCore, body, outerFormula, outerVariables]
    simp only [termValue_shortBinaryNumeralTerm]
  rw [htransparent]
  exact hcore.trans (hcontextual.trans hfixed)

#print axioms
  compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailBranchesFullyFixedBounds
