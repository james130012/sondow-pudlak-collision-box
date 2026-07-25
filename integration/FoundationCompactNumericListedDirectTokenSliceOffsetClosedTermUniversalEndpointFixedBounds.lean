import integration.FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermBranchesFixedBounds
import integration.FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds

/-!
# Short-count offset-universal endpoint over arbitrary closed starts

This closes the finite offset branches, short count equality, empty outer
context, and final bounded-universal shell.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermUniversalEndpointFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermBodyFixedBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermUniversalFixedBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermBranchesFixedBounds

def tokenSliceClosedTermOffsetShiftedBoundFixedScalePolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound + binaryNumeralTermCodeEnvelope bitBound

def tokenSliceClosedTermOffsetUniversalFullyFixedPayloadPolynomial
    (numericBound termCode bitBound : Nat) : Nat :=
  closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
    (tokenSliceClosedTermOffsetUniversalSyntaxFixedPolynomial numericBound
      termCode)
    (tokenSliceClosedTermOffsetUniversalBodyCodePolynomial termCode)
    (tokenSliceClosedTermOffsetContextualBranchesFixedPayloadPolynomial
      numericBound termCode bitBound)
    (compileShiftedBoundEqualityFixedPayloadPolynomial
      (tokenSliceClosedTermOffsetShiftedBoundFixedScalePolynomial numericBound
        bitBound))

private theorem tokenSliceClosedTermOffsetShiftedBoundResource_le_fixed
    (valuation : Nat -> Nat) (count numericBound bitBound : Nat)
    (hcount : count <= numericBound)
    (hcountSize : Nat.size count <= bitBound) :
    compileShiftedBoundEqualityPayloadResource valuation ∅
        (shortBinaryNumeralTerm count) <=
      compileShiftedBoundEqualityFixedPayloadPolynomial
        (tokenSliceClosedTermOffsetShiftedBoundFixedScalePolynomial
          numericBound bitBound) := by
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm count
  let scale :=
    tokenSliceClosedTermOffsetShiftedBoundFixedScalePolynomial numericBound
      bitBound
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
    unfold tokenSliceClosedTermOffsetShiftedBoundFixedScalePolynomial
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
        unfold tokenSliceClosedTermOffsetShiftedBoundFixedScalePolynomial
        omega)
      hcode
  exact hpublic.trans hfixed

theorem
    tokenSliceAtValuationOffsetUniversalPayloadEnvelope_le_closedFixed
    (valuation : Nat -> Nat)
    (tokenTable width count numericBound termCode bitBound : Nat)
    (sourceStartTerm targetStartTerm : ValuationTerm)
    (hsourceClosed : sourceStartTerm.freeVariables = ∅)
    (htargetClosed : targetStartTerm.freeVariables = ∅)
    (htableCode :
      (binaryTermCode (shortBinaryNumeralTerm tokenTable)).length <= termCode)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode)
    (hwidth : width <= numericBound)
    (hsource : termValue valuation sourceStartTerm <= numericBound)
    (htarget : termValue valuation targetStartTerm <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    tokenSliceAtValuationOffsetUniversalPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        sourceStartTerm targetStartTerm count <=
      tokenSliceClosedTermOffsetUniversalFullyFixedPayloadPolynomial
        numericBound termCode bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let body := tokenSliceAtValuationOffsetBody tableTerm widthTerm
    sourceStartTerm targetStartTerm
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ count
    (Rewriting.free body)
    (tokenSliceAtValuationOffsetBranchesTransparentEnvelope valuation
      tableTerm widthTerm sourceStartTerm targetStartTerm count)
  let boundResource := compileShiftedBoundEqualityPayloadResource valuation ∅
    boundTerm
  have houter : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body, boundTerm, tableTerm,
      widthTerm]
    exact
      tokenSliceAtValuationOffsetUniversal_freeVariables_eq_empty_closed
        tokenTable width count sourceStartTerm targetStartTerm hsourceClosed
        htargetClosed
  have hGamma : Gamma = ∅ := by
    dsimp only [Gamma]
    rw [houter]
    simp [valuationContext]
  have hcountSize : Nat.size count <= bitBound :=
    (Nat.size_le_size hcount).trans hnumericSize
  have hbody :
      (binaryFormulaCode body).length <=
        tokenSliceClosedTermOffsetUniversalBodyCodePolynomial termCode := by
    dsimp only [body, tableTerm, widthTerm]
    exact tokenSliceAtValuationOffsetBody_code_length_le_closedFixed
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      sourceStartTerm targetStartTerm termCode htableCode hwidthCode
      hsourceCode htargetCode
  have hboundResource :
      boundResource <=
        compileShiftedBoundEqualityFixedPayloadPolynomial
          (tokenSliceClosedTermOffsetShiftedBoundFixedScalePolynomial
            numericBound bitBound) := by
    dsimp only [boundResource, boundTerm]
    exact tokenSliceClosedTermOffsetShiftedBoundResource_le_fixed valuation
      count numericBound bitBound hcount hcountSize
  have hbranch :
      branchResource <=
        tokenSliceClosedTermOffsetContextualBranchesFixedPayloadPolynomial
          numericBound termCode bitBound := by
    dsimp only [branchResource, body, tableTerm, widthTerm]
    exact
      tokenSliceAtValuationOffsetContextualBranchesResource_le_closedFixed
        valuation tokenTable width count numericBound termCode bitBound
        sourceStartTerm targetStartTerm hsourceClosed htargetClosed htableCode
        hwidthCode hsourceCode htargetCode hwidth hsource htarget hcount
        htableSize hwidthSize
  have hshell :=
    compileContextualTermBoundedUniversalPayloadEnvelope_empty_short_le_fixed
      body count numericBound bitBound
      (tokenSliceClosedTermOffsetUniversalSyntaxFixedPolynomial numericBound
        termCode)
      (tokenSliceClosedTermOffsetUniversalBodyCodePolynomial termCode)
      boundResource branchResource
      (compileShiftedBoundEqualityFixedPayloadPolynomial
        (tokenSliceClosedTermOffsetShiftedBoundFixedScalePolynomial
          numericBound bitBound))
      (tokenSliceClosedTermOffsetContextualBranchesFixedPayloadPolynomial
        numericBound termCode bitBound)
      hcount hcountSize
      (by
        unfold tokenSliceClosedTermOffsetUniversalSyntaxFixedPolynomial
        omega)
      hbody hboundResource hbranch
  unfold tokenSliceAtValuationOffsetUniversalPayloadEnvelope
  simp only [termValue_shortBinaryNumeralTerm]
  rw [show
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm count))
      (tokenSliceAtValuationOffsetBody tableTerm widthTerm sourceStartTerm
        targetStartTerm)).freeVariables = ∅ by
      simpa only [tableTerm, widthTerm] using
        tokenSliceAtValuationOffsetUniversal_freeVariables_eq_empty_closed
          tokenTable width count sourceStartTerm targetStartTerm
          hsourceClosed htargetClosed]
  simp only [valuationContext, Finset.image_empty]
  unfold tokenSliceClosedTermOffsetUniversalFullyFixedPayloadPolynomial
  simpa only [body, boundTerm, branchResource, boundResource, tableTerm,
    widthTerm] using hshell

#print axioms
  tokenSliceAtValuationOffsetUniversalPayloadEnvelope_le_closedFixed

end FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermUniversalEndpointFixedBounds
