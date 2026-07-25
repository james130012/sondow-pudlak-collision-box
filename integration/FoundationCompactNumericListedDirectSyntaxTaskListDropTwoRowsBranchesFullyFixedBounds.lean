import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsUniversalBodyFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

/-!
# Fully fixed branch recursion for syntax-task drop two

The checked drop-two graph supplies the exact shifted target count.  The
uniform four-witness branch sum is then combined with the closed universal
body and its empty outer context.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsBranchesFullyFixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsUniformBranchFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsUniversalBodyFixedBounds

private abbrev dropTwoRowsZeroValuationBranchesFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

def taskDropTwoUniversalSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound +
    taskDropTwoUniversalBodyFormulaCodePolynomial numericBound bitBound

def taskDropTwoUniversalFormulaFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (taskDropTwoUniversalSyntaxFixedPolynomial numericBound bitBound) +
    2 * taskDropTwoUniversalBodyFormulaCodePolynomial numericBound bitBound

def taskDropTwoUniversalLocalPayloadFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (taskDropTwoUniversalFormulaFixedPolynomial numericBound bitBound)

def taskDropTwoBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (taskDropTwoAllBranchesFullyFixedPayloadPolynomial numericBound bitBound +
      3 * taskDropTwoUniversalLocalPayloadFixedPolynomial numericBound bitBound)

private theorem dropTwoHybridBranchesEnvelope_mono_leaf
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
        dropTwoHybridBranchesEnvelope_mono_leaf totalBound outerVariables
          valuation body hresource bound
      omega

theorem
    compactAdditiveSyntaxTaskListDropTwoRowsBranchesTransparentEnvelope_le_fullyFixed
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
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesTransparentEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        2 rows <=
      taskDropTwoBranchesFullyFixedPayloadPolynomial numericBound bitBound := by
  let body :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 2
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm targetCount)) body
  let outerVariables := outerFormula.freeVariables
  let leafBound :=
    taskDropTwoAllBranchesFullyFixedPayloadPolynomial numericBound bitBound
  let exactCore :=
    hybridBranchesUniformStructuralPayloadEnvelope targetCount outerVariables
      dropTwoRowsZeroValuationBranchesFixed body
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchPayloadResourceSum
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        2 rows)
      targetCount
  let fixedLeafCore :=
    hybridBranchesUniformStructuralPayloadEnvelope targetCount outerVariables
      dropTwoRowsZeroValuationBranchesFixed body leafBound targetCount
  let Gamma :=
    (valuationContext outerVariables
      dropTwoRowsZeroValuationBranchesFixed).image Rewriting.shift
  let contextualCore :=
    contextualHybridUniversalBranchesPayloadPolynomial Gamma targetCount
      targetCount body leafBound
  have hshiftedCount : 2 + targetCount <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    exact hsourceCount
  have htargetCount : targetCount <= numericBound := by omega
  have hleaf :=
    compactAdditiveSyntaxTaskListDropTwoRowsBranchPayloadResourceSum_le_fullyFixed
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      numericBound bitBound rows hwidth htokenCount hshiftedCount
      htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hcore : exactCore <= fixedLeafCore := by
    dsimp only [exactCore, fixedLeafCore]
    exact dropTwoHybridBranchesEnvelope_mono_leaf targetCount outerVariables
      dropTwoRowsZeroValuationBranchesFixed body hleaf targetCount
  have houterVariables : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      compactAdditiveSyntaxTaskListDropTwoRowsOuterFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount sourceBoundary targetCount targetBoundary
  have hGammaCard : Gamma.card <= 1 := by
    dsimp only [Gamma]
    rw [houterVariables]
    simp [valuationContext]
  have hcontextual : fixedLeafCore <= contextualCore := by
    dsimp only [fixedLeafCore, contextualCore]
    exact
      hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
        targetCount outerVariables dropTwoRowsZeroValuationBranchesFixed body
        leafBound hGammaCard (caseCount := targetCount) le_rfl
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody :
      (binaryFormulaCode body).length <=
        taskDropTwoUniversalBodyFormulaCodePolynomial numericBound
          bitBound := by
    dsimp only [body]
    exact compactAdditiveSyntaxTaskListDropTwoRowsBody_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound htokenCount htokenTableSize hwidthSize htokenCountSize
      hsourceBoundarySize htargetBoundarySize
  have hsyntax :
      explicitHybridUniversalSyntaxResource targetCount body <=
        taskDropTwoUniversalSyntaxFixedPolynomial numericBound bitBound := by
    unfold explicitHybridUniversalSyntaxResource
      taskDropTwoUniversalSyntaxFixedPolynomial
    omega
  have hclosed :=
    boundedUniversalClosedFormulaEnvelope_mono_completed hsyntax
  have hformula :
      explicitHybridUniversalFormulaEnvelope targetCount body <=
        taskDropTwoUniversalFormulaFixedPolynomial numericBound bitBound := by
    unfold explicitHybridUniversalFormulaEnvelope
      taskDropTwoUniversalFormulaFixedPolynomial
    omega
  have hlocal :
      contextualHybridUniversalLocalPayloadEnvelope Gamma targetCount body <=
        taskDropTwoUniversalLocalPayloadFixedPolynomial numericBound
          bitBound := by
    have hGammaEmpty : Gamma = ∅ := by
      dsimp only [Gamma]
      rw [houterVariables]
      simp [valuationContext]
    rw [hGammaEmpty]
    unfold contextualHybridUniversalLocalPayloadEnvelope
      contextualHybridUniversalFormulaEnvelope
      contextualHybridUniversalFormulaCodeSum
      taskDropTwoUniversalLocalPayloadFixedPolynomial
    simpa only [Finset.sum_empty, Nat.add_zero] using
      smallContextAssemblyEnvelope_mono_local hformula
  have hfixed :
      contextualCore <=
        taskDropTwoBranchesFullyFixedPayloadPolynomial numericBound
          bitBound := by
    unfold contextualCore contextualHybridUniversalBranchesPayloadPolynomial
      taskDropTwoBranchesFullyFixedPayloadPolynomial
    exact Nat.mul_le_mul (by omega) (Nat.add_le_add le_rfl
      (Nat.mul_le_mul_left 3 hlocal))
  have htransparent :
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesTransparentEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary targetCount
          2 rows =
        exactCore := by
    unfold
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesTransparentEnvelope
    dsimp only [exactCore, body, outerFormula, outerVariables]
    simp only [termValue_shortBinaryNumeralTerm]
  rw [htransparent]
  exact hcore.trans (hcontextual.trans hfixed)

#print axioms
  compactAdditiveSyntaxTaskListDropTwoRowsBranchesTransparentEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsBranchesFullyFixedBounds
