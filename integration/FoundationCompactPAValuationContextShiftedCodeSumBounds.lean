import integration.FoundationCompactPAValuationTermCompilerPublicBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds

/-!
# Code sum of a shifted valuation context

The image under formula shift has no larger cardinality, and each shifted
formula has at most twice the binary code length of its source.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactPAValuationContextShiftedCodeSumBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactSyntaxTransformationCodeBounds

theorem shiftedValuationContext_formulaCodeSum_le_uniform
    (vars : Finset Nat) (valuation : Nat -> Nat)
    (cardBound numericBound variableTermCodeBound : Nat)
    (hcard : vars.card <= cardBound)
    (hvalues : forall index, index ∈ vars ->
      valuation index <= numericBound)
    (hvariables : forall index, index ∈ vars ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        variableTermCodeBound) :
    contextualHybridUniversalFormulaCodeSum
        ((valuationContext vars valuation).image Rewriting.shift) <=
      2 * valuationContextFormulaCodeSumEnvelope cardBound numericBound
        variableTermCodeBound := by
  let sourceContext := valuationContext vars valuation
  let shiftedContext := sourceContext.image Rewriting.shift
  let formulaBound :=
    valuationEqualityAssumptionFormulaCodeEnvelope numericBound
      variableTermCodeBound
  have hsourceCard : sourceContext.card <= cardBound := by
    dsimp only [sourceContext]
    exact (Finset.card_image_le.trans hcard)
  have hshiftedCard : shiftedContext.card <= cardBound := by
    exact Finset.card_image_le.trans hsourceCard
  have hformula : forall formula, formula ∈ shiftedContext ->
      (binaryFormulaCode formula).length <= 2 * formulaBound := by
    intro formula hformula
    rcases Finset.mem_image.mp hformula with
      ⟨source, hsource, rfl⟩
    have hsourceCode : (binaryFormulaCode source).length <= formulaBound := by
      dsimp only [sourceContext] at hsource
      rcases Finset.mem_image.mp hsource with ⟨index, hindex, rfl⟩
      exact valuationEqualityAssumption_code_le_uniform valuation index
        numericBound variableTermCodeBound (hvalues index hindex)
        (hvariables index hindex)
    exact (binaryFormulaCode_shift_length_le source).trans
      (Nat.mul_le_mul_left 2 hsourceCode)
  have hsum :
      shiftedContext.sum
          (fun formula => (binaryFormulaCode formula).length) <=
        shiftedContext.card * (2 * formulaBound) := by
    simpa [nsmul_eq_mul] using
      shiftedContext.sum_le_card_nsmul
        (fun formula => (binaryFormulaCode formula).length)
        (2 * formulaBound) hformula
  unfold contextualHybridUniversalFormulaCodeSum
    valuationContextFormulaCodeSumEnvelope
  dsimp only [shiftedContext, sourceContext, formulaBound] at hsum ⊢
  calc
    _ <= ((valuationContext vars valuation).image
        Rewriting.shift).card * (2 *
          valuationEqualityAssumptionFormulaCodeEnvelope numericBound
            variableTermCodeBound) := hsum
    _ <= cardBound * (2 *
          valuationEqualityAssumptionFormulaCodeEnvelope numericBound
            variableTermCodeBound) :=
      Nat.mul_le_mul_right _ hshiftedCard
    _ = 2 * (cardBound *
          valuationEqualityAssumptionFormulaCodeEnvelope numericBound
            variableTermCodeBound) := by ring

#print axioms shiftedValuationContext_formulaCodeSum_le_uniform

end FoundationCompactPAValuationContextShiftedCodeSumBounds
