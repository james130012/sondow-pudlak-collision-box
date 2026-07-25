import integration.FoundationCompactNumericListedDirectNatListDropOneRowsContextualBranchesFullyFixedBounds
import integration.FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds

/-!
# Fully fixed universal resource for drop-one natural-list rows

The contextual target-row branches, normalized-bound equality, and closed
short bounded-universal shell use the same public numeric and bit bounds.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListDropOneRowsUniversalFullyFixedBounds

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
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectNatListDropOneRowsUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectNatListDropOneRowsBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectNatListDropOneRowsContextualBranchesFullyFixedBounds

private abbrev dropOneRowsZeroValuationUniversal : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

def dropOneRowsShiftedBoundFixedScalePolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound + binaryNumeralTermCodeEnvelope bitBound

def dropOneRowsUniversalFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
    (dropOneRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
    (dropOneRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
    (dropOneRowsContextualBranchesFullyFixedPayloadPolynomial numericBound
      bitBound)
    (compileShiftedBoundEqualityFixedPayloadPolynomial
      (dropOneRowsShiftedBoundFixedScalePolynomial numericBound bitBound))

private theorem dropOneRowsShiftedBoundResource_le_fullyFixed
    (targetCount numericBound bitBound : Nat)
    (htargetCount : targetCount <= numericBound)
    (htargetCountSize : Nat.size targetCount <= bitBound) :
    compileShiftedBoundEqualityPayloadResource
        dropOneRowsZeroValuationUniversal ∅
        (shortBinaryNumeralTerm targetCount) <=
      compileShiftedBoundEqualityFixedPayloadPolynomial
        (dropOneRowsShiftedBoundFixedScalePolynomial numericBound
          bitBound) := by
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm targetCount
  let scale :=
    dropOneRowsShiftedBoundFixedScalePolynomial numericBound bitBound
  have hclosed : boundTerm.freeVariables = ∅ := by
    dsimp only [boundTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty targetCount
  have hpublic :=
    compileShiftedBoundEqualityPayloadResource_le_publicPolynomial
      dropOneRowsZeroValuationUniversal ∅ boundTerm hclosed
  have hcode :
      (binaryTermCode boundTerm).length <= scale := by
    have hraw := binaryNumeralTerm_code_length_le_envelope targetCount
      bitBound htargetCountSize
    dsimp only [boundTerm, scale]
    unfold dropOneRowsShiftedBoundFixedScalePolynomial
    omega
  have hfixed :=
    compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq
      dropOneRowsZeroValuationUniversal ∅ boundTerm
      (compileShiftedBoundEqualityPayloadPublicPolynomial
        dropOneRowsZeroValuationUniversal ∅ boundTerm)
      (compileShiftedBoundEqualityFixedPayloadPolynomial scale)
      scale rfl rfl hclosed (by simp)
      (by
        dsimp only [dropOneRowsZeroValuationUniversal]
        simp [
          FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation,
          scale, dropOneRowsShiftedBoundFixedScalePolynomial])
      (by
        dsimp only [boundTerm]
        rw [termValue_shortBinaryNumeralTerm]
        dsimp only [scale]
        unfold dropOneRowsShiftedBoundFixedScalePolynomial
        omega)
      hcode
  exact hpublic.trans hfixed

theorem
    compactAdditiveNatListDropOneRowsUniversalPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 1)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveNatListDropRowData tokenTable width tokenCount
        sourceBoundary targetBoundary 1 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListDropFixedNumeralRowsUniversalPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        1 rows <=
      dropOneRowsUniversalFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let body := compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary 1
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm targetCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma :=
    valuationContext outerVariables dropOneRowsZeroValuationUniversal
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅
    targetCount (Rewriting.free body)
    (compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      1 rows)
  let boundResource := compileShiftedBoundEqualityPayloadResource
    dropOneRowsZeroValuationUniversal ∅ boundTerm
  have htargetCount : targetCount <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have houterVariables : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body, boundTerm]
    exact
      compactAdditiveNatListDropOneRowsOuterFormula_freeVariables_eq_empty
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
  have hGamma : Gamma = ∅ := by
    dsimp only [Gamma]
    rw [houterVariables]
    simp [valuationContext]
  have hbody :
      (binaryFormulaCode body).length <=
        dropOneRowsUniversalBodyFormulaCodePolynomial numericBound bitBound := by
    dsimp only [body]
    exact compactAdditiveNatListDropOneRowsBody_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound hwidth htokenCount htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize
  have htargetCountSize : Nat.size targetCount <= bitBound :=
    (Nat.size_le_size htargetCount).trans hnumericSize
  have hboundResource :
      boundResource <=
        compileShiftedBoundEqualityFixedPayloadPolynomial
          (dropOneRowsShiftedBoundFixedScalePolynomial numericBound
            bitBound) := by
    dsimp only [boundResource, boundTerm]
    exact dropOneRowsShiftedBoundResource_le_fullyFixed targetCount
      numericBound bitBound htargetCount htargetCountSize
  have hbranch :
      branchResource <=
        dropOneRowsContextualBranchesFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [branchResource, body]
    exact
      compactAdditiveNatListDropOneRowsContextualBranchesResource_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount numericBound bitBound hgraph rows hwidth htokenCount
        hsourceCount htokenTableSize hsourceBoundarySize htargetBoundarySize
        hnumericSize
  have hshell :=
    compileContextualTermBoundedUniversalPayloadEnvelope_empty_short_le_fixed
      body targetCount numericBound bitBound
      (dropOneRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (dropOneRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
      boundResource branchResource
      (compileShiftedBoundEqualityFixedPayloadPolynomial
        (dropOneRowsShiftedBoundFixedScalePolynomial numericBound bitBound))
      (dropOneRowsContextualBranchesFullyFixedPayloadPolynomial numericBound
        bitBound)
      htargetCount htargetCountSize
      (by
        unfold dropOneRowsUniversalSyntaxFixedPolynomial
        omega)
      hbody hboundResource hbranch
  unfold compactAdditiveNatListDropFixedNumeralRowsUniversalPayloadEnvelope
  simp only [termValue_shortBinaryNumeralTerm]
  rw [show
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm targetCount))
      (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary 1)).freeVariables = ∅ by
      exact
        compactAdditiveNatListDropOneRowsOuterFormula_freeVariables_eq_empty
          tokenTable width tokenCount sourceBoundary targetBoundary
          targetCount]
  simp only [valuationContext, Finset.image_empty]
  unfold dropOneRowsUniversalFullyFixedPayloadPolynomial
  simpa only [body, boundTerm, branchResource, boundResource] using hshell

#print axioms dropOneRowsShiftedBoundResource_le_fullyFixed
#print axioms
  compactAdditiveNatListDropOneRowsUniversalPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectNatListDropOneRowsUniversalFullyFixedBounds
