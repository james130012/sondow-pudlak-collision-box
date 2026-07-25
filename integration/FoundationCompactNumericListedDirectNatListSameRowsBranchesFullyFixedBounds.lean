import integration.FoundationCompactNumericListedDirectNatListSameRowsUniformBranchFullyFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

/-!
# Fully fixed outer branch recursion for equal natural-list rows

The concrete row count, body code, and row-resource sum are replaced by the
shared numeric/bit coordinates before entering the contextual branch shell.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListSameRowsBranchesFullyFixedBounds

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
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectNatListSameRowsUniformBranchFullyFixedBounds

private abbrev sameRowsZeroValuationBranchesFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate.zeroValuation

def sameRowsUniversalSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound +
    sameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound

def sameRowsUniversalFormulaFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (sameRowsUniversalSyntaxFixedPolynomial numericBound bitBound) +
    2 * sameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound

def sameRowsUniversalLocalPayloadFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (sameRowsUniversalFormulaFixedPolynomial numericBound bitBound)

def sameRowsBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (sameRowsAllBranchesFullyFixedPayloadPolynomial numericBound bitBound +
      3 * sameRowsUniversalLocalPayloadFixedPolynomial numericBound bitBound)

private theorem
    hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf_branchesFixed
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
        hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf_branchesFixed
          totalBound outerVariables valuation body hresource bound
      omega

theorem
    compactAdditiveNatListSameRowsBranchesTransparentEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListSameRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListSameRowsBranchesTransparentEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows <=
      sameRowsBranchesFullyFixedPayloadPolynomial numericBound bitBound := by
  let body := compactAdditiveNatListSameRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
  let outerVariables := outerFormula.freeVariables
  let leafBound :=
    sameRowsAllBranchesFullyFixedPayloadPolynomial numericBound bitBound
  let exactCore :=
    hybridBranchesUniformStructuralPayloadEnvelope sourceCount outerVariables
      sameRowsZeroValuationBranchesFixed body
      (compactAdditiveNatListSameRowsBranchPayloadResourceSum tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows)
      sourceCount
  let fixedLeafCore :=
    hybridBranchesUniformStructuralPayloadEnvelope sourceCount outerVariables
      sameRowsZeroValuationBranchesFixed body leafBound sourceCount
  let Gamma :=
    (valuationContext outerVariables sameRowsZeroValuationBranchesFixed).image
      Rewriting.shift
  let contextualCore :=
    contextualHybridUniversalBranchesPayloadPolynomial Gamma sourceCount
      sourceCount body leafBound
  have hleaf :=
    compactAdditiveNatListSameRowsBranchPayloadResourceSum_le_fullyUniform
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound rows hwidth htokenCount hsourceCount
      htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hcore : exactCore <= fixedLeafCore := by
    dsimp only [exactCore, fixedLeafCore]
    exact
      hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf_branchesFixed
        sourceCount outerVariables sameRowsZeroValuationBranchesFixed body
        hleaf sourceCount
  have houterVariables : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      compactAdditiveNatListSameRowsOuterFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
  have hGammaCard : Gamma.card <= 1 := by
    dsimp only [Gamma]
    rw [houterVariables]
    simp [valuationContext]
  have hcontextual : fixedLeafCore <= contextualCore := by
    dsimp only [fixedLeafCore, contextualCore]
    exact
      hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
        sourceCount outerVariables sameRowsZeroValuationBranchesFixed body
        leafBound hGammaCard (caseCount := sourceCount) le_rfl
  have hbody :
      (binaryFormulaCode body).length <=
        sameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound := by
    dsimp only [body]
    exact compactAdditiveNatListSameRowsBody_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound hwidth htokenCount htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize
  have hsyntax :
      explicitHybridUniversalSyntaxResource sourceCount body <=
        sameRowsUniversalSyntaxFixedPolynomial numericBound bitBound := by
    unfold explicitHybridUniversalSyntaxResource
      sameRowsUniversalSyntaxFixedPolynomial
    omega
  have hclosed :=
    boundedUniversalClosedFormulaEnvelope_mono_completed hsyntax
  have hformula :
      explicitHybridUniversalFormulaEnvelope sourceCount body <=
        sameRowsUniversalFormulaFixedPolynomial numericBound bitBound := by
    unfold explicitHybridUniversalFormulaEnvelope
      sameRowsUniversalFormulaFixedPolynomial
    omega
  have hlocal :
      contextualHybridUniversalLocalPayloadEnvelope Gamma sourceCount body <=
        sameRowsUniversalLocalPayloadFixedPolynomial numericBound bitBound := by
    have hGammaEmpty : Gamma = ∅ := by
      dsimp only [Gamma]
      rw [houterVariables]
      simp [valuationContext]
    rw [hGammaEmpty]
    unfold contextualHybridUniversalLocalPayloadEnvelope
      contextualHybridUniversalFormulaEnvelope
      contextualHybridUniversalFormulaCodeSum
      sameRowsUniversalLocalPayloadFixedPolynomial
    simpa only [Finset.sum_empty, Nat.add_zero] using
      smallContextAssemblyEnvelope_mono_local hformula
  have hfixed :
      contextualCore <=
        sameRowsBranchesFullyFixedPayloadPolynomial numericBound bitBound := by
    unfold contextualCore contextualHybridUniversalBranchesPayloadPolynomial
      sameRowsBranchesFullyFixedPayloadPolynomial
    exact Nat.mul_le_mul (by omega) (Nat.add_le_add le_rfl
      (Nat.mul_le_mul_left 3 hlocal))
  have htransparent : 
      compactAdditiveNatListSameRowsBranchesTransparentEnvelope tokenTable
          width tokenCount sourceBoundary sourceCount targetBoundary rows =
        exactCore := by
    unfold compactAdditiveNatListSameRowsBranchesTransparentEnvelope
    dsimp only [exactCore, body, outerFormula, outerVariables]
    simp only [termValue_shortBinaryNumeralTerm]
  rw [htransparent]
  exact hcore.trans (hcontextual.trans hfixed)

#print axioms
  compactAdditiveNatListSameRowsBranchesTransparentEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectNatListSameRowsBranchesFullyFixedBounds
