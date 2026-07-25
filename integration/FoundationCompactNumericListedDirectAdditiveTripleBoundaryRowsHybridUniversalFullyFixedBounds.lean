import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridContextualBranchesFullyFixedBounds
import integration.FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds

/-!
# Fully fixed original hybrid universal for triple-boundary rows

The fixed actual-row branch tree, shifted short bound, and closed universal
shell are combined without replacing the original hybrid certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridUniversalFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectFixedPolynomialBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridContextualBranchesFullyFixedBounds

private abbrev tripleZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.zeroValuation

def tripleBoundaryRowsHybridShiftedBoundFixedScalePolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound + binaryNumeralTermCodeEnvelope bitBound

def tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
    (tripleBoundaryRowDirectUniversalSyntaxFixedPolynomial
      numericBound bitBound)
    (tripleBoundaryRowUniversalBodyFormulaCodePolynomial
      numericBound bitBound)
    (tripleBoundaryRowsHybridContextualBranchesFixedPayloadPolynomial
      numericBound bitBound)
    (compileShiftedBoundEqualityFixedPayloadPolynomial
      (tripleBoundaryRowsHybridShiftedBoundFixedScalePolynomial
        numericBound bitBound))

private theorem tripleBoundaryRowsHybridShiftedBoundResource_le_fullyFixed
    (count numericBound bitBound : Nat)
    (hcount : count <= numericBound)
    (hcountSize : Nat.size count <= bitBound) :
    compileShiftedBoundEqualityPayloadResource tripleZeroValuation ∅
        (shortBinaryNumeralTerm count) <=
      compileShiftedBoundEqualityFixedPayloadPolynomial
        (tripleBoundaryRowsHybridShiftedBoundFixedScalePolynomial
          numericBound bitBound) := by
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm count
  let scale :=
    tripleBoundaryRowsHybridShiftedBoundFixedScalePolynomial
      numericBound bitBound
  have hclosed : boundTerm.freeVariables = ∅ := by
    dsimp only [boundTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty count
  have hpublic :=
    compileShiftedBoundEqualityPayloadResource_le_publicPolynomial
      tripleZeroValuation ∅ boundTerm hclosed
  have hcode : (binaryTermCode boundTerm).length <= scale := by
    have hraw := binaryNumeralTerm_code_length_le_envelope count bitBound
      hcountSize
    dsimp only [boundTerm, scale]
    unfold tripleBoundaryRowsHybridShiftedBoundFixedScalePolynomial
    omega
  have hfixed :=
    compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq
      tripleZeroValuation ∅ boundTerm
      (compileShiftedBoundEqualityPayloadPublicPolynomial
        tripleZeroValuation ∅ boundTerm)
      (compileShiftedBoundEqualityFixedPayloadPolynomial scale)
      scale rfl rfl hclosed (by simp)
      (by
        dsimp only [tripleZeroValuation]
        simp [
          FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.zeroValuation,
          scale, tripleBoundaryRowsHybridShiftedBoundFixedScalePolynomial])
      (by
        dsimp only [boundTerm]
        rw [termValue_shortBinaryNumeralTerm]
        dsimp only [scale]
        unfold tripleBoundaryRowsHybridShiftedBoundFixedScalePolynomial
        omega)
      hcode
  exact hpublic.trans hfixed

theorem
    compactAdditiveTripleBoundaryRowsUniversalStructuralPayloadEnvelope_le_fullyFixed
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveTripleBoundaryRowsUniversalStructuralPayloadEnvelope
        tokenCount count boundaryTable rows <=
      tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial
        numericBound bitBound := by
  let body := compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables tripleZeroValuation
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ count
    (Rewriting.free body)
    (compactAdditiveTripleBoundaryRowsBranchesTransparentStructuralEnvelope
      tokenCount count boundaryTable rows)
  let boundResource := compileShiftedBoundEqualityPayloadResource
    tripleZeroValuation ∅ boundTerm
  have houterVariables : outerVariables = ∅ := by
    have hclosed :=
      compactAdditiveTripleBoundaryRowsClosedFormula_freeVariables_eq_empty
        tokenCount count boundaryTable
    rw [compactAdditiveTripleBoundaryRowsClosedFormula_alignment] at hclosed
    have halign :
        outerFormula =
          compactAdditiveTripleBoundaryRowsExplicitFormula
            tokenCount count boundaryTable := by
      dsimp only [outerFormula, body, boundTerm,
        compactAdditiveTripleBoundaryRowsExplicitFormula]
      rw [termBoundedUniversal_eq_ball]
      rfl
    dsimp only [outerVariables]
    rw [halign]
    exact hclosed
  have hGamma : Gamma = ∅ := by
    dsimp only [Gamma]
    rw [houterVariables]
    simp [valuationContext]
  have hbody :
      (binaryFormulaCode body).length <=
        tripleBoundaryRowUniversalBodyFormulaCodePolynomial
          numericBound bitBound := by
    dsimp only [body]
    exact compactAdditiveTripleBoundaryRowsBody_code_length_le_fixed
      tokenCount boundaryTable numericBound bitBound htokenCount htableSize
      hnumericSize
  have hcountSize : Nat.size count <= bitBound :=
    (Nat.size_le_size hcount).trans hnumericSize
  have hboundResource :
      boundResource <=
        compileShiftedBoundEqualityFixedPayloadPolynomial
          (tripleBoundaryRowsHybridShiftedBoundFixedScalePolynomial
            numericBound bitBound) := by
    dsimp only [boundResource, boundTerm]
    exact tripleBoundaryRowsHybridShiftedBoundResource_le_fullyFixed count
      numericBound bitBound hcount hcountSize
  have hbranch :
      branchResource <=
        tripleBoundaryRowsHybridContextualBranchesFixedPayloadPolynomial
          numericBound bitBound := by
    dsimp only [branchResource, body]
    exact
      compactAdditiveTripleBoundaryRowsHybridContextualBranchesResource_le_fullyFixed
        tokenCount count boundaryTable numericBound bitBound rows htokenCount
        hcount htableSize hnumericSize
  have hshell :=
    compileContextualTermBoundedUniversalPayloadEnvelope_empty_short_le_fixed
      body count numericBound bitBound
      (tripleBoundaryRowDirectUniversalSyntaxFixedPolynomial
        numericBound bitBound)
      (tripleBoundaryRowUniversalBodyFormulaCodePolynomial
        numericBound bitBound)
      boundResource branchResource
      (compileShiftedBoundEqualityFixedPayloadPolynomial
        (tripleBoundaryRowsHybridShiftedBoundFixedScalePolynomial
          numericBound bitBound))
      (tripleBoundaryRowsHybridContextualBranchesFixedPayloadPolynomial
        numericBound bitBound)
      hcount hcountSize
      (by
        unfold tripleBoundaryRowDirectUniversalSyntaxFixedPolynomial
        omega)
      hbody hboundResource hbranch
  unfold compactAdditiveTripleBoundaryRowsUniversalStructuralPayloadEnvelope
  simp only [termValue_shortBinaryNumeralTerm]
  rw [show
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm count))
      (compactAdditiveTripleBoundaryRowsBody
        tokenCount boundaryTable)).freeVariables = ∅ by
      simpa only [outerFormula, body, boundTerm, outerVariables] using
        houterVariables]
  simp only [valuationContext, Finset.image_empty]
  unfold tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial
  simpa only [body, boundTerm, branchResource, boundResource] using hshell

theorem
    compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope_le_fullyFixed
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (hrows : CompactAdditiveTripleBoundaryRows
      tokenCount count boundaryTable)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope
        tokenCount count boundaryTable hrows <=
      tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial
        numericBound bitBound := by
  unfold compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope
  exact
    compactAdditiveTripleBoundaryRowsUniversalStructuralPayloadEnvelope_le_fullyFixed
      tokenCount count boundaryTable numericBound bitBound
      (compactAdditiveTripleBoundaryRowDataOfGraph
        tokenCount count boundaryTable hrows)
      htokenCount hcount htableSize hnumericSize

#print axioms tripleBoundaryRowsHybridShiftedBoundResource_le_fullyFixed
#print axioms
  compactAdditiveTripleBoundaryRowsUniversalStructuralPayloadEnvelope_le_fullyFixed
#print axioms
  compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridUniversalFullyFixedBounds
