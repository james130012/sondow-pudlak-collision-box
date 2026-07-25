import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsUniversalBodyFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

/-!
# Fully fixed branch recursion for syntax-task drop one

The checked drop-one graph supplies the exact shifted target count.  The
uniform four-witness branch sum is then combined with the closed universal
body and its empty outer context.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsBranchesFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
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
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsUniformBranchFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsUniversalBodyFixedBounds

private abbrev dropOneRowsZeroValuationBranchesFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

def taskDropOneUniversalSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound +
    taskDropOneUniversalBodyFormulaCodePolynomial numericBound bitBound

def taskDropOneUniversalFormulaFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (taskDropOneUniversalSyntaxFixedPolynomial numericBound bitBound) +
    2 * taskDropOneUniversalBodyFormulaCodePolynomial numericBound bitBound

def taskDropOneUniversalLocalPayloadFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (taskDropOneUniversalFormulaFixedPolynomial numericBound bitBound)

def taskDropOneBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (taskDropOneAllBranchesFullyFixedPayloadPolynomial numericBound bitBound +
      3 * taskDropOneUniversalLocalPayloadFixedPolynomial numericBound bitBound)

private theorem dropOneHybridBranchesEnvelope_mono_leaf
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
        dropOneHybridBranchesEnvelope_mono_leaf totalBound outerVariables
          valuation body hresource bound
      omega

theorem
    compactAdditiveSyntaxTaskListDropOneRowsBranchesTransparentEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 1)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveSyntaxTaskListDropRowData tokenTable width tokenCount
        sourceBoundary targetBoundary 1 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesTransparentEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        1 rows <=
      taskDropOneBranchesFullyFixedPayloadPolynomial numericBound bitBound := by
  let body :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 1
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm targetCount)) body
  let outerVariables := outerFormula.freeVariables
  let leafBound :=
    taskDropOneAllBranchesFullyFixedPayloadPolynomial numericBound bitBound
  let exactCore :=
    hybridBranchesUniformStructuralPayloadEnvelope targetCount outerVariables
      dropOneRowsZeroValuationBranchesFixed body
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchPayloadResourceSum
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        1 rows)
      targetCount
  let fixedLeafCore :=
    hybridBranchesUniformStructuralPayloadEnvelope targetCount outerVariables
      dropOneRowsZeroValuationBranchesFixed body leafBound targetCount
  let Gamma :=
    (valuationContext outerVariables
      dropOneRowsZeroValuationBranchesFixed).image Rewriting.shift
  let contextualCore :=
    contextualHybridUniversalBranchesPayloadPolynomial Gamma targetCount
      targetCount body leafBound
  have hshiftedCount : 1 + targetCount <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    exact hsourceCount
  have htargetCount : targetCount <= numericBound := by omega
  have hleaf :=
    compactAdditiveSyntaxTaskListDropOneRowsBranchPayloadResourceSum_le_fullyFixed
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      numericBound bitBound rows hwidth htokenCount hshiftedCount
      htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hcore : exactCore <= fixedLeafCore := by
    dsimp only [exactCore, fixedLeafCore]
    exact dropOneHybridBranchesEnvelope_mono_leaf targetCount outerVariables
      dropOneRowsZeroValuationBranchesFixed body hleaf targetCount
  have houterVariables : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      compactAdditiveSyntaxTaskListDropOneRowsOuterFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount sourceBoundary targetCount targetBoundary
  have hGammaCard : Gamma.card <= 1 := by
    dsimp only [Gamma]
    rw [houterVariables]
    simp [valuationContext]
  have hcontextual : fixedLeafCore <= contextualCore := by
    dsimp only [fixedLeafCore, contextualCore]
    exact
      hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
        targetCount outerVariables dropOneRowsZeroValuationBranchesFixed body
        leafBound hGammaCard (caseCount := targetCount) le_rfl
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody :
      (binaryFormulaCode body).length <=
        taskDropOneUniversalBodyFormulaCodePolynomial numericBound
          bitBound := by
    dsimp only [body]
    exact compactAdditiveSyntaxTaskListDropOneRowsBody_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound htokenCount htokenTableSize hwidthSize htokenCountSize
      hsourceBoundarySize htargetBoundarySize
  have hsyntax :
      explicitHybridUniversalSyntaxResource targetCount body <=
        taskDropOneUniversalSyntaxFixedPolynomial numericBound bitBound := by
    unfold explicitHybridUniversalSyntaxResource
      taskDropOneUniversalSyntaxFixedPolynomial
    omega
  have hclosed :=
    boundedUniversalClosedFormulaEnvelope_mono_completed hsyntax
  have hformula :
      explicitHybridUniversalFormulaEnvelope targetCount body <=
        taskDropOneUniversalFormulaFixedPolynomial numericBound bitBound := by
    unfold explicitHybridUniversalFormulaEnvelope
      taskDropOneUniversalFormulaFixedPolynomial
    omega
  have hlocal :
      contextualHybridUniversalLocalPayloadEnvelope Gamma targetCount body <=
        taskDropOneUniversalLocalPayloadFixedPolynomial numericBound
          bitBound := by
    have hGammaEmpty : Gamma = ∅ := by
      dsimp only [Gamma]
      rw [houterVariables]
      simp [valuationContext]
    rw [hGammaEmpty]
    unfold contextualHybridUniversalLocalPayloadEnvelope
      contextualHybridUniversalFormulaEnvelope
      contextualHybridUniversalFormulaCodeSum
      taskDropOneUniversalLocalPayloadFixedPolynomial
    simpa only [Finset.sum_empty, Nat.add_zero] using
      smallContextAssemblyEnvelope_mono_local hformula
  have hfixed :
      contextualCore <=
        taskDropOneBranchesFullyFixedPayloadPolynomial numericBound
          bitBound := by
    unfold contextualCore contextualHybridUniversalBranchesPayloadPolynomial
      taskDropOneBranchesFullyFixedPayloadPolynomial
    exact Nat.mul_le_mul (by omega) (Nat.add_le_add le_rfl
      (Nat.mul_le_mul_left 3 hlocal))
  have htransparent :
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesTransparentEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary targetCount
          1 rows =
        exactCore := by
    unfold
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesTransparentEnvelope
    dsimp only [exactCore, body, outerFormula, outerVariables]
    simp only [termValue_shortBinaryNumeralTerm]
  rw [htransparent]
  exact hcore.trans (hcontextual.trans hfixed)

#print axioms
  compactAdditiveSyntaxTaskListDropOneRowsBranchesTransparentEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsBranchesFullyFixedBounds
