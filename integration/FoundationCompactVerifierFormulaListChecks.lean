import integration.FoundationCompactVerifierBitCostPrimitives

/-!
# Costed formula-list checks for compact sequents

Formula codes are generated canonically and their complete emitted weight is
charged before the bit-string comparison cost.  Lists are compared
extensionally, matching the `Finset` sequents of the Foundation calculus.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactVerifierFormulaListChecks

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactVerifierBitCostPrimitives

abbrev ArithmeticProposition := LO.FirstOrder.ArithmeticProposition

def formulaBitStrings (formulas : List ArithmeticProposition) :
    List (List Bool) :=
  formulas.map binaryFormulaCode

def formulaListCodeWeight (formulas : List ArithmeticProposition) : Nat :=
  bitStringFamilyWeight (formulaBitStrings formulas)

@[simp] theorem formulaBitStrings_nil : formulaBitStrings [] = [] := rfl

@[simp] theorem formulaBitStrings_cons
    (formula : ArithmeticProposition)
    (formulas : List ArithmeticProposition) :
    formulaBitStrings (formula :: formulas) =
      binaryFormulaCode formula :: formulaBitStrings formulas := rfl

@[simp] theorem formulaListCodeWeight_nil :
    formulaListCodeWeight [] = 0 := rfl

@[simp] theorem formulaListCodeWeight_cons
    (formula : ArithmeticProposition)
    (formulas : List ArithmeticProposition) :
    formulaListCodeWeight (formula :: formulas) =
      (binaryFormulaCode formula).length + 3 +
        formulaListCodeWeight formulas := by
  simp [formulaListCodeWeight]

theorem mem_formulaBitStrings_iff
    (formula : ArithmeticProposition)
    (formulas : List ArithmeticProposition) :
    binaryFormulaCode formula ∈ formulaBitStrings formulas ↔
      formula ∈ formulas := by
  constructor
  · rw [formulaBitStrings, List.mem_map]
    rintro ⟨candidate, hcandidate, hcode⟩
    have : candidate = formula :=
      binaryFormulaCode_injective hcode
    simpa [this] using hcandidate
  · intro hformula
    exact List.mem_map.mpr ⟨formula, hformula, rfl⟩

theorem formulaBitStrings_subset_iff
    (left right : List ArithmeticProposition) :
    (forall code, code ∈ formulaBitStrings left ->
        code ∈ formulaBitStrings right) ↔
      forall formula, formula ∈ left -> formula ∈ right := by
  constructor
  · intro hsubset formula hformula
    have hcode : binaryFormulaCode formula ∈ formulaBitStrings left :=
      (mem_formulaBitStrings_iff formula left).2 hformula
    exact (mem_formulaBitStrings_iff formula right).1
      (hsubset (binaryFormulaCode formula) hcode)
  · intro hsubset code hcode
    rw [formulaBitStrings, List.mem_map] at hcode ⊢
    rcases hcode with ⟨formula, hformula, rfl⟩
    exact ⟨formula, hsubset formula hformula, rfl⟩

theorem formulaBitStrings_toFinset_eq_iff
    (left right : List ArithmeticProposition) :
    (formulaBitStrings left).toFinset =
        (formulaBitStrings right).toFinset ↔
      left.toFinset = right.toFinset := by
  constructor
  · intro hcodes
    ext formula
    simp only [List.mem_toFinset]
    rw [← mem_formulaBitStrings_iff formula left,
      ← mem_formulaBitStrings_iff formula right]
    simpa using Finset.ext_iff.mp hcodes (binaryFormulaCode formula)
  · intro hformulas
    apply Finset.ext
    intro code
    simp only [List.mem_toFinset]
    constructor
    · intro hcode
      rw [formulaBitStrings, List.mem_map] at hcode
      rcases hcode with ⟨formula, hformula, rfl⟩
      apply (mem_formulaBitStrings_iff formula right).2
      have : formula ∈ left.toFinset := by simpa
      rw [hformulas] at this
      simpa using this
    · intro hcode
      rw [formulaBitStrings, List.mem_map] at hcode
      rcases hcode with ⟨formula, hformula, rfl⟩
      apply (mem_formulaBitStrings_iff formula left).2
      have : formula ∈ right.toFinset := by simpa
      rw [← hformulas] at this
      simpa using this

/-- Formula equality by canonical bit codes, charging both emitted codes. -/
def formulaEqTrace
    (left right : ArithmeticProposition) : Bool × Nat :=
  let comparison :=
    bitStringEqTrace (binaryFormulaCode left) (binaryFormulaCode right)
  (comparison.1,
    comparison.2 + (binaryFormulaCode left).length +
      (binaryFormulaCode right).length + 1)

theorem formulaEqTrace_result_eq_true_iff
    (left right : ArithmeticProposition) :
    (formulaEqTrace left right).1 = true ↔ left = right := by
  rw [formulaEqTrace, bitStringEqTrace_result_eq_true_iff]
  exact binaryFormulaCode_injective.eq_iff

theorem formulaEqTrace_cost_le
    (left right : ArithmeticProposition) :
    (formulaEqTrace left right).2 <=
      2 * (binaryFormulaCode left).length +
        (binaryFormulaCode right).length + 2 := by
  have hcomparison := bitStringEqTrace_cost_le
    (binaryFormulaCode left) (binaryFormulaCode right)
  simp only [formulaEqTrace]
  omega

/-- Formula membership with all canonical-code emission charged. -/
def formulaMemTrace
    (formula : ArithmeticProposition)
    (formulas : List ArithmeticProposition) : Bool × Nat :=
  let comparison := bitStringMemTrace
    (binaryFormulaCode formula) (formulaBitStrings formulas)
  (comparison.1,
    comparison.2 + (binaryFormulaCode formula).length +
      formulaListCodeWeight formulas + 1)

theorem formulaMemTrace_result_eq_true_iff
    (formula : ArithmeticProposition)
    (formulas : List ArithmeticProposition) :
    (formulaMemTrace formula formulas).1 = true ↔ formula ∈ formulas := by
  simp only [formulaMemTrace]
  exact (bitStringMemTrace_result_eq_true_iff
    (binaryFormulaCode formula) (formulaBitStrings formulas)).trans
      (mem_formulaBitStrings_iff formula formulas)

theorem formulaMemTrace_cost_le
    (formula : ArithmeticProposition)
    (formulas : List ArithmeticProposition) :
    (formulaMemTrace formula formulas).2 <=
      ((binaryFormulaCode formula).length + 2) *
          (formulas.length + 1) +
        (binaryFormulaCode formula).length +
        formulaListCodeWeight formulas + 1 := by
  have hcomparison := bitStringMemTrace_cost_le
    (binaryFormulaCode formula) (formulaBitStrings formulas)
  simpa [formulaMemTrace, formulaBitStrings] using
    Nat.add_le_add_right
      (Nat.add_le_add_right
        (Nat.add_le_add_right hcomparison
          (binaryFormulaCode formula).length)
        (formulaListCodeWeight formulas)) 1

/-- Formula-list inclusion with canonical-code emission charged. -/
def formulaSubsetTrace
    (left right : List ArithmeticProposition) : Bool × Nat :=
  let comparison := bitStringSubsetTrace
    (formulaBitStrings left) (formulaBitStrings right)
  (comparison.1,
    comparison.2 + formulaListCodeWeight left +
      formulaListCodeWeight right + 1)

theorem formulaSubsetTrace_result_eq_true_iff
    (left right : List ArithmeticProposition) :
    (formulaSubsetTrace left right).1 = true ↔
      left.toFinset ⊆ right.toFinset := by
  rw [formulaSubsetTrace,
    bitStringSubsetTrace_result_eq_true_iff,
    formulaBitStrings_subset_iff]
  simp only [Finset.subset_iff, List.mem_toFinset]

theorem formulaSubsetTrace_cost_le
    (left right : List ArithmeticProposition) :
    (formulaSubsetTrace left right).2 <=
      2 + (right.length + 1) * formulaListCodeWeight left +
        formulaListCodeWeight left + formulaListCodeWeight right := by
  have hcomparison := bitStringSubsetTrace_cost_le
    (formulaBitStrings left) (formulaBitStrings right)
  have hcomparison' : (bitStringSubsetTrace
        (formulaBitStrings left) (formulaBitStrings right)).2 <=
      1 + (right.length + 1) * formulaListCodeWeight left := by
    simpa only [formulaBitStrings, List.length_map,
      formulaListCodeWeight] using hcomparison
  simp only [formulaSubsetTrace]
  omega

/-- Extensional formula-list equality with canonical-code emission charged. -/
def formulaSetEqTrace
    (left right : List ArithmeticProposition) : Bool × Nat :=
  let comparison := bitStringSetEqTrace
    (formulaBitStrings left) (formulaBitStrings right)
  (comparison.1,
    comparison.2 + formulaListCodeWeight left +
      formulaListCodeWeight right + 1)

theorem formulaSetEqTrace_result_eq_true_iff
    (left right : List ArithmeticProposition) :
    (formulaSetEqTrace left right).1 = true ↔
      left.toFinset = right.toFinset := by
  rw [formulaSetEqTrace,
    bitStringSetEqTrace_result_eq_true_iff,
    formulaBitStrings_toFinset_eq_iff]

theorem formulaSetEqTrace_cost_le
    (left right : List ArithmeticProposition) :
    (formulaSetEqTrace left right).2 <=
      4 + (right.length + 1) * formulaListCodeWeight left +
        (left.length + 1) * formulaListCodeWeight right +
        formulaListCodeWeight left + formulaListCodeWeight right := by
  have hcomparison := bitStringSetEqTrace_cost_le
    (formulaBitStrings left) (formulaBitStrings right)
  have hcomparison' : (bitStringSetEqTrace
        (formulaBitStrings left) (formulaBitStrings right)).2 <=
      3 + (right.length + 1) * formulaListCodeWeight left +
        (left.length + 1) * formulaListCodeWeight right := by
    simpa only [formulaBitStrings, List.length_map,
      formulaListCodeWeight] using hcomparison
  simp only [formulaSetEqTrace]
  omega

#print axioms formulaMemTrace_result_eq_true_iff
#print axioms formulaEqTrace_result_eq_true_iff
#print axioms formulaSubsetTrace_cost_le
#print axioms formulaSetEqTrace_result_eq_true_iff

end FoundationCompactVerifierFormulaListChecks
