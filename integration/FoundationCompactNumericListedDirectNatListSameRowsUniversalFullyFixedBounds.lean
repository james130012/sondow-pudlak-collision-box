import integration.FoundationCompactNumericListedDirectNatListSameRowsContextualBranchesFullyFixedBounds
import integration.FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds

/-!
# Fully fixed universal resource for equal natural-list rows

The contextual branches, normalized-bound equality, and the closed short
bounded-universal shell are all charged to the same public numeric and
bit-width coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListSameRowsUniversalFullyFixedBounds

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
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectNatListSameRowsBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectNatListSameRowsContextualBranchesFullyFixedBounds

private abbrev sameRowsZeroValuationUniversal : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate.zeroValuation

def sameRowsShiftedBoundFixedScalePolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound + binaryNumeralTermCodeEnvelope bitBound

def sameRowsUniversalFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
    (sameRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
    (sameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
    (sameRowsContextualBranchesFullyFixedPayloadPolynomial numericBound
      bitBound)
    (compileShiftedBoundEqualityFixedPayloadPolynomial
      (sameRowsShiftedBoundFixedScalePolynomial numericBound bitBound))

private theorem sameRowsShiftedBoundResource_le_fullyFixed
    (sourceCount numericBound bitBound : Nat)
    (hsourceCount : sourceCount <= numericBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound) :
    compileShiftedBoundEqualityPayloadResource sameRowsZeroValuationUniversal
        ∅ (shortBinaryNumeralTerm sourceCount) <=
      compileShiftedBoundEqualityFixedPayloadPolynomial
        (sameRowsShiftedBoundFixedScalePolynomial numericBound bitBound) := by
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let scale := sameRowsShiftedBoundFixedScalePolynomial numericBound bitBound
  have hclosed : boundTerm.freeVariables = ∅ := by
    dsimp only [boundTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty sourceCount
  have hpublic :=
    compileShiftedBoundEqualityPayloadResource_le_publicPolynomial
      sameRowsZeroValuationUniversal ∅ boundTerm hclosed
  have hcode :
      (binaryTermCode boundTerm).length <= scale := by
    have hraw := binaryNumeralTerm_code_length_le_envelope sourceCount
      bitBound hsourceCountSize
    dsimp only [boundTerm, scale]
    unfold sameRowsShiftedBoundFixedScalePolynomial
    omega
  have hfixed :=
    compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq
      sameRowsZeroValuationUniversal ∅ boundTerm
      (compileShiftedBoundEqualityPayloadPublicPolynomial
        sameRowsZeroValuationUniversal ∅ boundTerm)
      (compileShiftedBoundEqualityFixedPayloadPolynomial scale)
      scale rfl rfl hclosed (by simp)
      (by
        dsimp only [sameRowsZeroValuationUniversal]
        simp [
          FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate.zeroValuation,
          scale, sameRowsShiftedBoundFixedScalePolynomial])
      (by
        dsimp only [boundTerm]
        rw [termValue_shortBinaryNumeralTerm]
        dsimp only [scale]
        unfold sameRowsShiftedBoundFixedScalePolynomial
        omega)
      hcode
  exact hpublic.trans hfixed

theorem compactAdditiveNatListSameRowsUniversalPayloadEnvelope_le_fullyFixed
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
    compactAdditiveNatListSameRowsUniversalPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows <=
      sameRowsUniversalFullyFixedPayloadPolynomial numericBound bitBound := by
  let body := compactAdditiveNatListSameRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables sameRowsZeroValuationUniversal
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅
    sourceCount (Rewriting.free body)
    (compactAdditiveNatListSameRowsBranchesTransparentEnvelope tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary rows)
  let boundResource := compileShiftedBoundEqualityPayloadResource
    sameRowsZeroValuationUniversal ∅ boundTerm
  have houterVariables : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body, boundTerm]
    exact
      compactAdditiveNatListSameRowsOuterFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
  have hGamma : Gamma = ∅ := by
    dsimp only [Gamma]
    rw [houterVariables]
    simp [valuationContext]
  have hbody :
      (binaryFormulaCode body).length <=
        sameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound := by
    dsimp only [body]
    exact compactAdditiveNatListSameRowsBody_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound hwidth htokenCount htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCount).trans hnumericSize
  have hboundResource :
      boundResource <=
        compileShiftedBoundEqualityFixedPayloadPolynomial
          (sameRowsShiftedBoundFixedScalePolynomial numericBound bitBound) := by
    dsimp only [boundResource, boundTerm]
    exact sameRowsShiftedBoundResource_le_fullyFixed sourceCount numericBound
      bitBound hsourceCount hsourceCountSize
  have hbranch :
      branchResource <=
        sameRowsContextualBranchesFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [branchResource, body]
    exact
      compactAdditiveNatListSameRowsContextualBranchesResource_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        numericBound bitBound rows hwidth htokenCount hsourceCount
        htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hshell :=
    compileContextualTermBoundedUniversalPayloadEnvelope_empty_short_le_fixed
      body sourceCount numericBound bitBound
      (sameRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (sameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
      boundResource branchResource
      (compileShiftedBoundEqualityFixedPayloadPolynomial
        (sameRowsShiftedBoundFixedScalePolynomial numericBound bitBound))
      (sameRowsContextualBranchesFullyFixedPayloadPolynomial numericBound
        bitBound)
      hsourceCount hsourceCountSize
      (by
        unfold sameRowsUniversalSyntaxFixedPolynomial
        omega)
      hbody hboundResource hbranch
  unfold compactAdditiveNatListSameRowsUniversalPayloadEnvelope
  simp only [termValue_shortBinaryNumeralTerm]
  rw [show
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm sourceCount))
      (compactAdditiveNatListSameRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary)).freeVariables = ∅ by
      exact
        compactAdditiveNatListSameRowsOuterFormula_freeVariables_eq_empty_fixed
          tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary]
  simp only [valuationContext, Finset.image_empty]
  unfold sameRowsUniversalFullyFixedPayloadPolynomial
  simpa only [body, boundTerm, branchResource, boundResource] using hshell

#print axioms sameRowsShiftedBoundResource_le_fullyFixed
#print axioms
  compactAdditiveNatListSameRowsUniversalPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectNatListSameRowsUniversalFullyFixedBounds
