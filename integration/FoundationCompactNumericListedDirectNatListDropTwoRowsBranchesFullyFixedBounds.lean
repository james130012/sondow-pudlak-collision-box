import integration.FoundationCompactNumericListedDirectNatListDropTwoRowsUniformBranchFullyFixedBounds
import integration.FoundationCompactNumericListedDirectNatListDropTwoRowsUniversalBodyFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

/-!
# Fully fixed outer branch recursion for drop-two natural-list rows

The checked drop-two graph controls the target-row count.  The uniform branch
sum, closed universal body, and empty outer context are combined before the
contextual branch shell.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListDropTwoRowsBranchesFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectNatListDropTwoRowsUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectNatListDropTwoRowsUniformBranchFullyFixedBounds

private abbrev dropTwoRowsZeroValuationBranchesFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

def dropTwoRowsUniversalSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound +
    dropTwoRowsUniversalBodyFormulaCodePolynomial numericBound bitBound

def dropTwoRowsUniversalFormulaFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (dropTwoRowsUniversalSyntaxFixedPolynomial numericBound bitBound) +
    2 * dropTwoRowsUniversalBodyFormulaCodePolynomial numericBound bitBound

def dropTwoRowsUniversalLocalPayloadFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (dropTwoRowsUniversalFormulaFixedPolynomial numericBound bitBound)

def dropTwoRowsBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (dropTwoRowsAllBranchesFullyFixedPayloadPolynomial numericBound bitBound +
      3 * dropTwoRowsUniversalLocalPayloadFixedPolynomial numericBound bitBound)

private theorem
    dropTwoHybridBranchesEnvelope_mono_leaf
    (totalBound : Nat) (outerVariables : Finset Nat)
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
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
    compactAdditiveNatListDropTwoRowsBranchesTransparentEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 2)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveNatListDropRowData tokenTable width tokenCount
        sourceBoundary targetBoundary 2 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        2 rows <=
      dropTwoRowsBranchesFullyFixedPayloadPolynomial numericBound bitBound := by
  let body := compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary 2
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm targetCount)) body
  let outerVariables := outerFormula.freeVariables
  let leafBound :=
    dropTwoRowsAllBranchesFullyFixedPayloadPolynomial numericBound bitBound
  let exactCore :=
    hybridBranchesUniformStructuralPayloadEnvelope targetCount outerVariables
      dropTwoRowsZeroValuationBranchesFixed body
      (compactAdditiveNatListDropFixedNumeralRowsBranchPayloadResourceSum
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
  have htargetCount : targetCount <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have hleaf :=
    compactAdditiveNatListDropTwoRowsBranchPayloadResourceSum_le_fullyUniform
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound hgraph rows hwidth htokenCount
      hsourceCount htokenTableSize hsourceBoundarySize htargetBoundarySize
      hnumericSize
  have hcore : exactCore <= fixedLeafCore := by
    dsimp only [exactCore, fixedLeafCore]
    exact dropTwoHybridBranchesEnvelope_mono_leaf targetCount outerVariables
      dropTwoRowsZeroValuationBranchesFixed body hleaf targetCount
  have houterVariables : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      compactAdditiveNatListDropTwoRowsOuterFormula_freeVariables_eq_empty
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
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
  have hbody :
      (binaryFormulaCode body).length <=
        dropTwoRowsUniversalBodyFormulaCodePolynomial numericBound bitBound := by
    dsimp only [body]
    exact compactAdditiveNatListDropTwoRowsBody_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound hwidth htokenCount htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize
  have hsyntax :
      explicitHybridUniversalSyntaxResource targetCount body <=
        dropTwoRowsUniversalSyntaxFixedPolynomial numericBound bitBound := by
    unfold explicitHybridUniversalSyntaxResource
      dropTwoRowsUniversalSyntaxFixedPolynomial
    omega
  have hclosed :=
    boundedUniversalClosedFormulaEnvelope_mono_completed hsyntax
  have hformula :
      explicitHybridUniversalFormulaEnvelope targetCount body <=
        dropTwoRowsUniversalFormulaFixedPolynomial numericBound bitBound := by
    unfold explicitHybridUniversalFormulaEnvelope
      dropTwoRowsUniversalFormulaFixedPolynomial
    omega
  have hlocal :
      contextualHybridUniversalLocalPayloadEnvelope Gamma targetCount body <=
        dropTwoRowsUniversalLocalPayloadFixedPolynomial numericBound
          bitBound := by
    have hGammaEmpty : Gamma = ∅ := by
      dsimp only [Gamma]
      rw [houterVariables]
      simp [valuationContext]
    rw [hGammaEmpty]
    unfold contextualHybridUniversalLocalPayloadEnvelope
      contextualHybridUniversalFormulaEnvelope
      contextualHybridUniversalFormulaCodeSum
      dropTwoRowsUniversalLocalPayloadFixedPolynomial
    simpa only [Finset.sum_empty, Nat.add_zero] using
      smallContextAssemblyEnvelope_mono_local hformula
  have hfixed :
      contextualCore <=
        dropTwoRowsBranchesFullyFixedPayloadPolynomial numericBound
          bitBound := by
    unfold contextualCore contextualHybridUniversalBranchesPayloadPolynomial
      dropTwoRowsBranchesFullyFixedPayloadPolynomial
    exact Nat.mul_le_mul (by omega) (Nat.add_le_add le_rfl
      (Nat.mul_le_mul_left 3 hlocal))
  have htransparent :
      compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary targetCount
          2 rows =
        exactCore := by
    unfold
      compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope
    dsimp only [exactCore, body, outerFormula, outerVariables]
    simp only [termValue_shortBinaryNumeralTerm]
  rw [htransparent]
  exact hcore.trans (hcontextual.trans hfixed)

#print axioms
  compactAdditiveNatListDropTwoRowsBranchesTransparentEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectNatListDropTwoRowsBranchesFullyFixedBounds
