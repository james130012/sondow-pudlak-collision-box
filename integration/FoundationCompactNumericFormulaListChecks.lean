import integration.FoundationCompactNumericSyntaxValueParser
import integration.FoundationCompactVerifierFormulaListChecks

/-!
# Pure numeric formula-list checks

The public arithmetic graph cannot retain typed formulas as hidden inputs.
This file compares the canonical natural-token values produced by the numeric
syntax parsers.  Equality, membership, inclusion, and extensional equality are
all primitive recursive and are proved pointwise equal to the corresponding
typed formula checks on every canonical input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericFormulaListChecks

open FoundationCompactSyntaxTokenMachine
open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactVerifierFormulaListChecks

abbrev ArithmeticProposition := LO.FirstOrder.ArithmeticProposition

def arithmeticPropositionTokenValue
    (formula : ArithmeticProposition) : List Nat :=
  compactArithmeticFormulaTokens formula

def arithmeticPropositionTokenValues
    (formulas : List ArithmeticProposition) : List (List Nat) :=
  formulas.map arithmeticPropositionTokenValue

theorem arithmeticPropositionTokenValue_injective :
    Function.Injective arithmeticPropositionTokenValue := by
  intro left right htokens
  apply binaryFormulaCode_injective
  rw [binaryFormulaCode_eq_tokenStream,
    binaryFormulaCode_eq_tokenStream]
  apply congrArg (List.flatMap binaryNatCode)
  exact htokens

theorem mem_arithmeticPropositionTokenValues_iff
    (formula : ArithmeticProposition)
    (formulas : List ArithmeticProposition) :
    arithmeticPropositionTokenValue formula ∈
        arithmeticPropositionTokenValues formulas ↔
      formula ∈ formulas := by
  constructor
  · rw [arithmeticPropositionTokenValues, List.mem_map]
    rintro ⟨candidate, hcandidate, hcode⟩
    have : candidate = formula :=
      arithmeticPropositionTokenValue_injective hcode
    simpa [this] using hcandidate
  · intro hformula
    exact List.mem_map.mpr ⟨formula, hformula, rfl⟩

theorem arithmeticPropositionTokenValues_subset_iff
    (left right : List ArithmeticProposition) :
    (forall value, value ∈ arithmeticPropositionTokenValues left ->
        value ∈ arithmeticPropositionTokenValues right) ↔
      forall formula, formula ∈ left -> formula ∈ right := by
  constructor
  · intro hsubset formula hformula
    have hvalue : arithmeticPropositionTokenValue formula ∈
        arithmeticPropositionTokenValues left :=
      (mem_arithmeticPropositionTokenValues_iff formula left).2 hformula
    exact (mem_arithmeticPropositionTokenValues_iff formula right).1
      (hsubset (arithmeticPropositionTokenValue formula) hvalue)
  · intro hsubset value hvalue
    rw [arithmeticPropositionTokenValues, List.mem_map] at hvalue ⊢
    rcases hvalue with ⟨formula, hformula, rfl⟩
    exact ⟨formula, hsubset formula hformula, rfl⟩

theorem arithmeticPropositionTokenValues_toFinset_eq_iff
    (left right : List ArithmeticProposition) :
    (arithmeticPropositionTokenValues left).toFinset =
        (arithmeticPropositionTokenValues right).toFinset ↔
      left.toFinset = right.toFinset := by
  constructor
  · intro hvalues
    ext formula
    simp only [List.mem_toFinset]
    rw [← mem_arithmeticPropositionTokenValues_iff formula left,
      ← mem_arithmeticPropositionTokenValues_iff formula right]
    simpa using Finset.ext_iff.mp hvalues
      (arithmeticPropositionTokenValue formula)
  · intro hformulas
    apply Finset.ext
    intro value
    simp only [List.mem_toFinset]
    constructor
    · intro hvalue
      rw [arithmeticPropositionTokenValues, List.mem_map] at hvalue
      rcases hvalue with ⟨formula, hformula, rfl⟩
      apply (mem_arithmeticPropositionTokenValues_iff formula right).2
      have : formula ∈ left.toFinset := by simpa
      rw [hformulas] at this
      simpa using this
    · intro hvalue
      rw [arithmeticPropositionTokenValues, List.mem_map] at hvalue
      rcases hvalue with ⟨formula, hformula, rfl⟩
      apply (mem_arithmeticPropositionTokenValues_iff formula left).2
      have : formula ∈ right.toFinset := by simpa
      rw [← hformulas] at this
      simpa using this

def tokenFormulaEq (left right : List Nat) : Bool :=
  decide (left = right)

theorem tokenFormulaEq_primrec : Primrec₂ tokenFormulaEq := by
  exact Primrec.eq.decide

@[simp] theorem tokenFormulaEq_eq_true_iff
    (left right : List Nat) :
    tokenFormulaEq left right = true ↔ left = right := by
  simp [tokenFormulaEq]

def tokenFormulaMem : List Nat -> List (List Nat) -> Bool
  | _, [] => false
  | formula, candidate :: formulas =>
      tokenFormulaEq formula candidate ||
        tokenFormulaMem formula formulas

theorem tokenFormulaMem_primrec : Primrec₂ tokenFormulaMem := by
  apply Primrec₂.mk
  let Input := List Nat × List (List Nat)
  have hformulas : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have heq : Primrec₂
      (fun (input : Input) (candidateResult : List Nat × Bool) =>
        tokenFormulaEq input.1 candidateResult.1) :=
    tokenFormulaEq_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left)
      (Primrec.fst.comp₂ Primrec₂.right)
  have hstep : Primrec₂
      (fun (input : Input) (candidateResult : List Nat × Bool) =>
        tokenFormulaEq input.1 candidateResult.1 || candidateResult.2) :=
    Primrec.or.comp₂ heq
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr hformulas (Primrec.const false) hstep).of_eq
      fun input => by
        induction input.2 with
        | nil => rfl
        | cons candidate formulas ih =>
            simp [tokenFormulaMem, ih]

@[simp] theorem tokenFormulaMem_eq_true_iff
    (formula : List Nat) (formulas : List (List Nat)) :
    tokenFormulaMem formula formulas = true ↔ formula ∈ formulas := by
  induction formulas with
  | nil => simp [tokenFormulaMem]
  | cons candidate formulas ih =>
      simp [tokenFormulaMem, ih]

def tokenFormulaSubset : List (List Nat) -> List (List Nat) -> Bool
  | [], _ => true
  | formula :: formulas, right =>
      tokenFormulaMem formula right &&
        tokenFormulaSubset formulas right

theorem tokenFormulaSubset_primrec : Primrec₂ tokenFormulaSubset := by
  apply Primrec₂.mk
  let Input := List (List Nat) × List (List Nat)
  have hleft : Primrec (fun input : Input => input.1) :=
    Primrec.fst
  have hmem : Primrec₂
      (fun (input : Input) (formulaResult : List Nat × Bool) =>
        tokenFormulaMem formulaResult.1 input.2) :=
    tokenFormulaMem_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.left)
  have hstep : Primrec₂
      (fun (input : Input) (formulaResult : List Nat × Bool) =>
        tokenFormulaMem formulaResult.1 input.2 && formulaResult.2) :=
    Primrec.and.comp₂ hmem
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr hleft (Primrec.const true) hstep).of_eq
      fun input => by
        induction input.1 with
        | nil => rfl
        | cons formula formulas ih =>
            simp [tokenFormulaSubset, ih]

@[simp] theorem tokenFormulaSubset_eq_true_iff
    (left right : List (List Nat)) :
    tokenFormulaSubset left right = true ↔
      forall formula, formula ∈ left -> formula ∈ right := by
  induction left with
  | nil => simp [tokenFormulaSubset]
  | cons formula formulas ih =>
      simp [tokenFormulaSubset, ih]

def tokenFormulaSetEq
    (left right : List (List Nat)) : Bool :=
  tokenFormulaSubset left right && tokenFormulaSubset right left

theorem tokenFormulaSetEq_primrec : Primrec₂ tokenFormulaSetEq := by
  exact Primrec.and.comp₂ tokenFormulaSubset_primrec
    tokenFormulaSubset_primrec.swap

@[simp] theorem tokenFormulaSetEq_eq_true_iff
    (left right : List (List Nat)) :
    tokenFormulaSetEq left right = true ↔
      left.toFinset = right.toFinset := by
  rw [tokenFormulaSetEq, Bool.and_eq_true,
    tokenFormulaSubset_eq_true_iff,
    tokenFormulaSubset_eq_true_iff, Finset.ext_iff]
  simp only [List.mem_toFinset]
  constructor
  · rintro ⟨hleft, hright⟩ formula
    exact ⟨hleft formula, hright formula⟩
  · intro hiff
    exact ⟨fun formula hformula => (hiff formula).1 hformula,
      fun formula hformula => (hiff formula).2 hformula⟩

theorem tokenFormulaEq_canonical_eq_formulaEqTrace_result
    (left right : ArithmeticProposition) :
    tokenFormulaEq (arithmeticPropositionTokenValue left)
        (arithmeticPropositionTokenValue right) =
      (formulaEqTrace left right).1 := by
  apply Bool.eq_iff_iff.mpr
  rw [tokenFormulaEq_eq_true_iff,
    formulaEqTrace_result_eq_true_iff]
  exact arithmeticPropositionTokenValue_injective.eq_iff

theorem tokenFormulaMem_canonical_eq_formulaMemTrace_result
    (formula : ArithmeticProposition)
    (formulas : List ArithmeticProposition) :
    tokenFormulaMem (arithmeticPropositionTokenValue formula)
        (arithmeticPropositionTokenValues formulas) =
      (formulaMemTrace formula formulas).1 := by
  apply Bool.eq_iff_iff.mpr
  rw [tokenFormulaMem_eq_true_iff,
    mem_arithmeticPropositionTokenValues_iff,
    formulaMemTrace_result_eq_true_iff]

theorem tokenFormulaSubset_canonical_eq_formulaSubsetTrace_result
    (left right : List ArithmeticProposition) :
    tokenFormulaSubset (arithmeticPropositionTokenValues left)
        (arithmeticPropositionTokenValues right) =
      (formulaSubsetTrace left right).1 := by
  apply Bool.eq_iff_iff.mpr
  rw [tokenFormulaSubset_eq_true_iff,
    arithmeticPropositionTokenValues_subset_iff,
    formulaSubsetTrace_result_eq_true_iff]
  simp only [Finset.subset_iff, List.mem_toFinset]

theorem tokenFormulaSetEq_canonical_eq_formulaSetEqTrace_result
    (left right : List ArithmeticProposition) :
    tokenFormulaSetEq (arithmeticPropositionTokenValues left)
        (arithmeticPropositionTokenValues right) =
      (formulaSetEqTrace left right).1 := by
  apply Bool.eq_iff_iff.mpr
  rw [tokenFormulaSetEq_eq_true_iff,
    arithmeticPropositionTokenValues_toFinset_eq_iff,
    formulaSetEqTrace_result_eq_true_iff]

#print axioms arithmeticPropositionTokenValue_injective
#print axioms tokenFormulaEq_primrec
#print axioms tokenFormulaMem_primrec
#print axioms tokenFormulaSubset_primrec
#print axioms tokenFormulaSetEq_primrec
#print axioms tokenFormulaEq_canonical_eq_formulaEqTrace_result
#print axioms tokenFormulaMem_canonical_eq_formulaMemTrace_result
#print axioms tokenFormulaSubset_canonical_eq_formulaSubsetTrace_result
#print axioms tokenFormulaSetEq_canonical_eq_formulaSetEqTrace_result

end FoundationCompactNumericFormulaListChecks
