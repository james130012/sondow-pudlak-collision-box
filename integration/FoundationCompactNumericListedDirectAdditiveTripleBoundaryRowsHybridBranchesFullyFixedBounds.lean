import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformHybridBranchFullyFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

/-!
# Fully fixed hybrid branch tree for additive triple-boundary rows

The actual checked row-resource sum is installed into the original hybrid
finite-universal branch tree and bounded by one public polynomial.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridBranchesFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsDirectCompiler
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectFixedPolynomialBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformHybridBranchFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

private abbrev tripleZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.zeroValuation

def tripleBoundaryRowsHybridUniversalSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound +
    tripleBoundaryRowUniversalBodyFormulaCodePolynomial numericBound bitBound

def tripleBoundaryRowsHybridUniversalFormulaFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (tripleBoundaryRowsHybridUniversalSyntaxFixedPolynomial
        numericBound bitBound) +
    2 * tripleBoundaryRowUniversalBodyFormulaCodePolynomial
      numericBound bitBound

def tripleBoundaryRowsHybridUniversalLocalFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (tripleBoundaryRowsHybridUniversalFormulaFixedPolynomial
      numericBound bitBound)

def tripleBoundaryRowsHybridBranchesFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (tripleBoundaryRowsAllHybridBranchesFixedPayloadPolynomial
        numericBound bitBound +
      3 * tripleBoundaryRowsHybridUniversalLocalFixedPolynomial
        numericBound bitBound)

private theorem tripleHybridBranchesEnvelope_mono_leaf
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
        tripleHybridBranchesEnvelope_mono_leaf totalBound outerVariables
          valuation body hresource bound
      omega

theorem
    compactAdditiveTripleBoundaryRowsBranchesTransparentStructuralEnvelope_le_fullyFixed
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveTripleBoundaryRowsBranchesTransparentStructuralEnvelope
        tokenCount count boundaryTable rows <=
      tripleBoundaryRowsHybridBranchesFixedPayloadPolynomial
        numericBound bitBound := by
  let body := compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm count)) body
  let outerVariables := outerFormula.freeVariables
  let leafBound :=
    tripleBoundaryRowsAllHybridBranchesFixedPayloadPolynomial
      numericBound bitBound
  let exactCore :=
    hybridBranchesUniformStructuralPayloadEnvelope count outerVariables
      tripleZeroValuation body
      (compactAdditiveTripleBoundaryRowsBranchStructuralPayloadResourceSum
        tokenCount count boundaryTable rows)
      count
  let fixedLeafCore :=
    hybridBranchesUniformStructuralPayloadEnvelope count outerVariables
      tripleZeroValuation body leafBound count
  let Gamma :=
    (valuationContext outerVariables tripleZeroValuation).image Rewriting.shift
  let contextualCore :=
    contextualHybridUniversalBranchesPayloadPolynomial Gamma count count body
      leafBound
  have hleaf :=
    compactAdditiveTripleBoundaryRowsBranchStructuralPayloadResourceSum_le_fullyFixed
      tokenCount count boundaryTable numericBound bitBound rows htokenCount
      hcount htableSize hnumericSize
  have hcore : exactCore <= fixedLeafCore := by
    dsimp only [exactCore, fixedLeafCore]
    exact tripleHybridBranchesEnvelope_mono_leaf count outerVariables
      tripleZeroValuation body hleaf count
  have houterVariables : outerVariables = ∅ := by
    have hclosed :=
      compactAdditiveTripleBoundaryRowsClosedFormula_freeVariables_eq_empty
        tokenCount count boundaryTable
    rw [compactAdditiveTripleBoundaryRowsClosedFormula_alignment] at hclosed
    have halign :
        outerFormula =
          compactAdditiveTripleBoundaryRowsExplicitFormula
            tokenCount count boundaryTable := by
      dsimp only [outerFormula, body,
        compactAdditiveTripleBoundaryRowsExplicitFormula]
      rw [termBoundedUniversal_eq_ball]
      rfl
    dsimp only [outerVariables]
    rw [halign]
    exact hclosed
  have hGammaCard : Gamma.card <= 1 := by
    dsimp only [Gamma]
    rw [houterVariables]
    simp [valuationContext]
  have hcontextual : fixedLeafCore <= contextualCore := by
    dsimp only [fixedLeafCore, contextualCore]
    exact
      hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
        count outerVariables tripleZeroValuation body leafBound hGammaCard
        (caseCount := count) le_rfl
  have hbody :
      (binaryFormulaCode body).length <=
        tripleBoundaryRowUniversalBodyFormulaCodePolynomial
          numericBound bitBound := by
    dsimp only [body]
    exact compactAdditiveTripleBoundaryRowsBody_code_length_le_fixed
      tokenCount boundaryTable numericBound bitBound htokenCount htableSize
      hnumericSize
  have hsyntax :
      explicitHybridUniversalSyntaxResource count body <=
        tripleBoundaryRowsHybridUniversalSyntaxFixedPolynomial
          numericBound bitBound := by
    unfold explicitHybridUniversalSyntaxResource
      tripleBoundaryRowsHybridUniversalSyntaxFixedPolynomial
    omega
  have hclosed :=
    boundedUniversalClosedFormulaEnvelope_mono_completed hsyntax
  have hformula :
      explicitHybridUniversalFormulaEnvelope count body <=
        tripleBoundaryRowsHybridUniversalFormulaFixedPolynomial
          numericBound bitBound := by
    unfold explicitHybridUniversalFormulaEnvelope
      tripleBoundaryRowsHybridUniversalFormulaFixedPolynomial
    omega
  have hlocal :
      contextualHybridUniversalLocalPayloadEnvelope Gamma count body <=
        tripleBoundaryRowsHybridUniversalLocalFixedPolynomial
          numericBound bitBound := by
    have hGammaEmpty : Gamma = ∅ := by
      dsimp only [Gamma]
      rw [houterVariables]
      simp [valuationContext]
    rw [hGammaEmpty]
    unfold contextualHybridUniversalLocalPayloadEnvelope
      contextualHybridUniversalFormulaEnvelope
      contextualHybridUniversalFormulaCodeSum
      tripleBoundaryRowsHybridUniversalLocalFixedPolynomial
    simpa only [Finset.sum_empty, Nat.add_zero] using
      smallContextAssemblyEnvelope_mono_local hformula
  have hfixed :
      contextualCore <=
        tripleBoundaryRowsHybridBranchesFixedPayloadPolynomial
          numericBound bitBound := by
    unfold contextualCore contextualHybridUniversalBranchesPayloadPolynomial
      tripleBoundaryRowsHybridBranchesFixedPayloadPolynomial
    exact Nat.mul_le_mul (by omega) (Nat.add_le_add le_rfl
      (Nat.mul_le_mul_left 3 hlocal))
  have htransparent :
      compactAdditiveTripleBoundaryRowsBranchesTransparentStructuralEnvelope
          tokenCount count boundaryTable rows =
        exactCore := by
    unfold
      compactAdditiveTripleBoundaryRowsBranchesTransparentStructuralEnvelope
    dsimp only [exactCore, body, outerFormula, outerVariables]
    simp only [termValue_shortBinaryNumeralTerm]
  rw [htransparent]
  exact hcore.trans (hcontextual.trans hfixed)

#print axioms
  compactAdditiveTripleBoundaryRowsBranchesTransparentStructuralEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridBranchesFullyFixedBounds
