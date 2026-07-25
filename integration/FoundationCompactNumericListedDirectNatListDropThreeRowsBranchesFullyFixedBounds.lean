import integration.FoundationCompactNumericListedDirectNatListDropThreeRowsUniformBranchFullyFixedBounds
import integration.FoundationCompactNumericListedDirectNatListDropThreeRowsUniversalBodyFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

/-!
# Fully fixed outer branch recursion for drop-one natural-list rows

The checked drop-one graph controls the target-row count.  The uniform branch
sum, closed universal body, and empty outer context are combined before the
contextual branch shell.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListDropThreeRowsBranchesFullyFixedBounds

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
open FoundationCompactNumericListedDirectNatListDropThreeRowsUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectNatListDropThreeRowsUniformBranchFullyFixedBounds

private abbrev dropThreeRowsZeroValuationBranchesFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

def dropThreeRowsUniversalSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound +
    dropThreeRowsUniversalBodyFormulaCodePolynomial numericBound bitBound

def dropThreeRowsUniversalFormulaFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (dropThreeRowsUniversalSyntaxFixedPolynomial numericBound bitBound) +
    2 * dropThreeRowsUniversalBodyFormulaCodePolynomial numericBound bitBound

def dropThreeRowsUniversalLocalPayloadFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (dropThreeRowsUniversalFormulaFixedPolynomial numericBound bitBound)

def dropThreeRowsBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (dropThreeRowsAllBranchesFullyFixedPayloadPolynomial numericBound bitBound +
      3 * dropThreeRowsUniversalLocalPayloadFixedPolynomial numericBound bitBound)

private theorem
    dropThreeHybridBranchesEnvelope_mono_leaf
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
        dropThreeHybridBranchesEnvelope_mono_leaf totalBound outerVariables
          valuation body hresource bound
      omega

theorem
    compactAdditiveNatListDropThreeRowsBranchesTransparentEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 3)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveNatListDropRowData tokenTable width tokenCount
        sourceBoundary targetBoundary 3 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        3 rows <=
      dropThreeRowsBranchesFullyFixedPayloadPolynomial numericBound bitBound := by
  let body := compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary 3
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm targetCount)) body
  let outerVariables := outerFormula.freeVariables
  let leafBound :=
    dropThreeRowsAllBranchesFullyFixedPayloadPolynomial numericBound bitBound
  let exactCore :=
    hybridBranchesUniformStructuralPayloadEnvelope targetCount outerVariables
      dropThreeRowsZeroValuationBranchesFixed body
      (compactAdditiveNatListDropFixedNumeralRowsBranchPayloadResourceSum
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        3 rows)
      targetCount
  let fixedLeafCore :=
    hybridBranchesUniformStructuralPayloadEnvelope targetCount outerVariables
      dropThreeRowsZeroValuationBranchesFixed body leafBound targetCount
  let Gamma :=
    (valuationContext outerVariables
      dropThreeRowsZeroValuationBranchesFixed).image Rewriting.shift
  let contextualCore :=
    contextualHybridUniversalBranchesPayloadPolynomial Gamma targetCount
      targetCount body leafBound
  have htargetCount : targetCount <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have hleaf :=
    compactAdditiveNatListDropThreeRowsBranchPayloadResourceSum_le_fullyUniform
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound hgraph rows hwidth htokenCount
      hsourceCount htokenTableSize hsourceBoundarySize htargetBoundarySize
      hnumericSize
  have hcore : exactCore <= fixedLeafCore := by
    dsimp only [exactCore, fixedLeafCore]
    exact dropThreeHybridBranchesEnvelope_mono_leaf targetCount outerVariables
      dropThreeRowsZeroValuationBranchesFixed body hleaf targetCount
  have houterVariables : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      compactAdditiveNatListDropThreeRowsOuterFormula_freeVariables_eq_empty
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
  have hGammaCard : Gamma.card <= 1 := by
    dsimp only [Gamma]
    rw [houterVariables]
    simp [valuationContext]
  have hcontextual : fixedLeafCore <= contextualCore := by
    dsimp only [fixedLeafCore, contextualCore]
    exact
      hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
        targetCount outerVariables dropThreeRowsZeroValuationBranchesFixed body
        leafBound hGammaCard (caseCount := targetCount) le_rfl
  have hbody :
      (binaryFormulaCode body).length <=
        dropThreeRowsUniversalBodyFormulaCodePolynomial numericBound bitBound := by
    dsimp only [body]
    exact compactAdditiveNatListDropThreeRowsBody_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound hwidth htokenCount htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize
  have hsyntax :
      explicitHybridUniversalSyntaxResource targetCount body <=
        dropThreeRowsUniversalSyntaxFixedPolynomial numericBound bitBound := by
    unfold explicitHybridUniversalSyntaxResource
      dropThreeRowsUniversalSyntaxFixedPolynomial
    omega
  have hclosed :=
    boundedUniversalClosedFormulaEnvelope_mono_completed hsyntax
  have hformula :
      explicitHybridUniversalFormulaEnvelope targetCount body <=
        dropThreeRowsUniversalFormulaFixedPolynomial numericBound bitBound := by
    unfold explicitHybridUniversalFormulaEnvelope
      dropThreeRowsUniversalFormulaFixedPolynomial
    omega
  have hlocal :
      contextualHybridUniversalLocalPayloadEnvelope Gamma targetCount body <=
        dropThreeRowsUniversalLocalPayloadFixedPolynomial numericBound
          bitBound := by
    have hGammaEmpty : Gamma = ∅ := by
      dsimp only [Gamma]
      rw [houterVariables]
      simp [valuationContext]
    rw [hGammaEmpty]
    unfold contextualHybridUniversalLocalPayloadEnvelope
      contextualHybridUniversalFormulaEnvelope
      contextualHybridUniversalFormulaCodeSum
      dropThreeRowsUniversalLocalPayloadFixedPolynomial
    simpa only [Finset.sum_empty, Nat.add_zero] using
      smallContextAssemblyEnvelope_mono_local hformula
  have hfixed :
      contextualCore <=
        dropThreeRowsBranchesFullyFixedPayloadPolynomial numericBound
          bitBound := by
    unfold contextualCore contextualHybridUniversalBranchesPayloadPolynomial
      dropThreeRowsBranchesFullyFixedPayloadPolynomial
    exact Nat.mul_le_mul (by omega) (Nat.add_le_add le_rfl
      (Nat.mul_le_mul_left 3 hlocal))
  have htransparent :
      compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary targetCount
          3 rows =
        exactCore := by
    unfold
      compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope
    dsimp only [exactCore, body, outerFormula, outerVariables]
    simp only [termValue_shortBinaryNumeralTerm]
  rw [htransparent]
  exact hcore.trans (hcontextual.trans hfixed)

#print axioms
  compactAdditiveNatListDropThreeRowsBranchesTransparentEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectNatListDropThreeRowsBranchesFullyFixedBounds
