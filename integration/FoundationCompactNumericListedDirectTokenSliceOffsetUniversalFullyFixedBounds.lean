import integration.FoundationCompactNumericListedDirectTokenSliceOffsetBranchesFullyFixedBounds
import integration.FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds

/-!
# Fully fixed offset-universal certificate for token slices

This closes the finite offset branches, short-count equality, empty outer
context, and contextual bounded-universal shell in one public polynomial.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceOffsetUniversalFullyFixedBounds

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
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetBodyFixedBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetUniversalFixedBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetBranchesFullyFixedBounds

def tokenSliceOffsetShiftedBoundFixedScalePolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound + binaryNumeralTermCodeEnvelope bitBound

def tokenSliceOffsetUniversalFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
    (tokenSliceOffsetUniversalSyntaxFixedPolynomial numericBound bitBound)
    (tokenSliceOffsetUniversalBodyCodePolynomial numericBound bitBound)
    (tokenSliceOffsetContextualBranchesFullyFixedPayloadPolynomial
      numericBound bitBound)
    (compileShiftedBoundEqualityFixedPayloadPolynomial
      (tokenSliceOffsetShiftedBoundFixedScalePolynomial numericBound
        bitBound))

private theorem tokenSliceOffsetShiftedBoundResource_le_fullyFixed
    (valuation : Nat -> Nat)
    (count numericBound bitBound : Nat)
    (hcount : count <= numericBound)
    (hcountSize : Nat.size count <= bitBound) :
    compileShiftedBoundEqualityPayloadResource valuation ∅
        (shortBinaryNumeralTerm count) <=
      compileShiftedBoundEqualityFixedPayloadPolynomial
        (tokenSliceOffsetShiftedBoundFixedScalePolynomial numericBound
          bitBound) := by
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm count
  let scale :=
    tokenSliceOffsetShiftedBoundFixedScalePolynomial numericBound bitBound
  have hclosed : boundTerm.freeVariables = ∅ := by
    dsimp only [boundTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty count
  have hpublic :=
    compileShiftedBoundEqualityPayloadResource_le_publicPolynomial valuation
      ∅ boundTerm hclosed
  have hcode : (binaryTermCode boundTerm).length <= scale := by
    have hraw := binaryNumeralTerm_code_length_le_envelope count bitBound
      hcountSize
    dsimp only [boundTerm, scale]
    unfold tokenSliceOffsetShiftedBoundFixedScalePolynomial
    omega
  have hfixed :=
    compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq_of_values
      valuation ∅ boundTerm
      (compileShiftedBoundEqualityPayloadPublicPolynomial valuation ∅
        boundTerm)
      (compileShiftedBoundEqualityFixedPayloadPolynomial scale)
      scale rfl rfl hclosed (by simp)
      (by
        intro index hindex
        simp at hindex)
      (by
        dsimp only [boundTerm, scale]
        rw [termValue_shortBinaryNumeralTerm]
        unfold tokenSliceOffsetShiftedBoundFixedScalePolynomial
        omega)
      hcode
  exact hpublic.trans hfixed

theorem tokenSliceAtValuationOffsetUniversalPayloadEnvelope_le_fullyFixed
    (valuation : Nat -> Nat)
    (tokenTable width sourceStart targetStart count numericBound bitBound :
      Nat)
    (hwidth : width <= numericBound)
    (hsourceStart : sourceStart <= numericBound)
    (htargetStart : targetStart <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    tokenSliceAtValuationOffsetUniversalPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm targetStart) count <=
      tokenSliceOffsetUniversalFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let sourceTerm := shortBinaryNumeralTerm sourceStart
  let targetTerm := shortBinaryNumeralTerm targetStart
  let body := tokenSliceAtValuationOffsetBody tableTerm widthTerm sourceTerm
    targetTerm
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ count
    (Rewriting.free body)
    (tokenSliceAtValuationOffsetBranchesTransparentEnvelope valuation
      tableTerm widthTerm sourceTerm targetTerm count)
  let boundResource := compileShiftedBoundEqualityPayloadResource valuation ∅
    boundTerm
  have houter : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body, boundTerm, tableTerm,
      widthTerm, sourceTerm, targetTerm]
    exact tokenSliceAtValuationOffsetUniversal_freeVariables_eq_empty
      tokenTable width sourceStart targetStart count
  have hGamma : Gamma = ∅ := by
    dsimp only [Gamma]
    rw [houter]
    simp [valuationContext]
  have hcountSize : Nat.size count <= bitBound :=
    (Nat.size_le_size hcount).trans hnumericSize
  have hbody :
      (binaryFormulaCode body).length <=
        tokenSliceOffsetUniversalBodyCodePolynomial numericBound bitBound := by
    dsimp only [body, tableTerm, widthTerm, sourceTerm, targetTerm]
    exact tokenSliceAtValuationOffsetBody_code_length_le_fixed tokenTable width
      sourceStart targetStart bitBound htableSize hwidthSize hsourceStartSize
      htargetStartSize
  have hboundResource :
      boundResource <=
        compileShiftedBoundEqualityFixedPayloadPolynomial
          (tokenSliceOffsetShiftedBoundFixedScalePolynomial numericBound
            bitBound) := by
    dsimp only [boundResource, boundTerm]
    exact tokenSliceOffsetShiftedBoundResource_le_fullyFixed valuation count
      numericBound bitBound hcount hcountSize
  have hbranch :
      branchResource <=
        tokenSliceOffsetContextualBranchesFullyFixedPayloadPolynomial
          numericBound bitBound := by
    dsimp only [branchResource, body, tableTerm, widthTerm, sourceTerm,
      targetTerm]
    exact tokenSliceAtValuationOffsetContextualBranchesResource_le_fullyFixed
      valuation tokenTable width sourceStart targetStart count numericBound
      bitBound hwidth hsourceStart htargetStart hcount htableSize hwidthSize
      hsourceStartSize htargetStartSize
  have hshell :=
    compileContextualTermBoundedUniversalPayloadEnvelope_empty_short_le_fixed
      body count numericBound bitBound
      (tokenSliceOffsetUniversalSyntaxFixedPolynomial numericBound bitBound)
      (tokenSliceOffsetUniversalBodyCodePolynomial numericBound bitBound)
      boundResource branchResource
      (compileShiftedBoundEqualityFixedPayloadPolynomial
        (tokenSliceOffsetShiftedBoundFixedScalePolynomial numericBound
          bitBound))
      (tokenSliceOffsetContextualBranchesFullyFixedPayloadPolynomial
        numericBound bitBound)
      hcount hcountSize
      (by
        unfold tokenSliceOffsetUniversalSyntaxFixedPolynomial
        omega)
      hbody hboundResource hbranch
  unfold tokenSliceAtValuationOffsetUniversalPayloadEnvelope
  simp only [termValue_shortBinaryNumeralTerm]
  rw [show
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm count))
      (tokenSliceAtValuationOffsetBody tableTerm widthTerm sourceTerm
        targetTerm)).freeVariables = ∅ by
      simpa only [tableTerm, widthTerm, sourceTerm, targetTerm] using
        tokenSliceAtValuationOffsetUniversal_freeVariables_eq_empty
          tokenTable width sourceStart targetStart count]
  simp only [valuationContext, Finset.image_empty]
  unfold tokenSliceOffsetUniversalFullyFixedPayloadPolynomial
  simpa only [body, boundTerm, branchResource, boundResource, tableTerm,
    widthTerm, sourceTerm, targetTerm] using hshell

theorem tokenSliceAtValuationOffsetUniversalCertificate_le_fullyFixed
    (valuation : Nat -> Nat)
    (tokenTable width sourceStart targetStart count numericBound bitBound :
      Nat)
    (hbits : ∀ offset < count, ∀ bitIndex < width,
      tokenTable.testBit ((sourceStart + offset) * width + bitIndex) =
        tokenTable.testBit ((targetStart + offset) * width + bitIndex))
    (hwidth : width <= numericBound)
    (hsourceStart : sourceStart <= numericBound)
    (htargetStart : targetStart <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (tokenSliceAtValuationOffsetUniversalCertificate valuation
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm sourceStart)
          (shortBinaryNumeralTerm targetStart) count (by
            simpa only [termValue_shortBinaryNumeralTerm] using hbits)) <=
      tokenSliceOffsetUniversalFullyFixedPayloadPolynomial numericBound
        bitBound := by
  have htransparent :=
    tokenSliceAtValuationOffsetUniversalCertificate_structuralPayloadBound_le_transparent
      valuation
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm sourceStart)
      (shortBinaryNumeralTerm targetStart) count (by
        simpa only [termValue_shortBinaryNumeralTerm] using hbits)
  exact htransparent.trans
    (tokenSliceAtValuationOffsetUniversalPayloadEnvelope_le_fullyFixed
      valuation tokenTable width sourceStart targetStart count numericBound
      bitBound hwidth hsourceStart htargetStart hcount htableSize hwidthSize
      hsourceStartSize htargetStartSize hnumericSize)

#print axioms tokenSliceOffsetShiftedBoundResource_le_fullyFixed
#print axioms
  tokenSliceAtValuationOffsetUniversalPayloadEnvelope_le_fullyFixed
#print axioms
  tokenSliceAtValuationOffsetUniversalCertificate_le_fullyFixed

end FoundationCompactNumericListedDirectTokenSliceOffsetUniversalFullyFixedBounds
