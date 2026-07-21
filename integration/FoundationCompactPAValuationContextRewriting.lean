import integration.FoundationCompactPAValuationTermCompiler

/-!
# Valuation contexts across binder freeing and free-variable shifting

Nested bounded quantifiers free the current bound variable as `&0` and shift
every outer free variable by one.  The lemmas below prove that the concrete
valuation-equality context follows exactly the same transformation.  They are
pure syntax facts and introduce no proof-existence assumptions.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAValuationContextRewriting

open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAValuationTermCompiler

def extendValuation
    (head : Nat) (tail : Nat -> Nat) : Nat -> Nat
  | 0 => head
  | index + 1 => tail index

@[simp] theorem extendValuation_zero
    (head : Nat) (tail : Nat -> Nat) :
    extendValuation head tail 0 = head := rfl

@[simp] theorem extendValuation_succ
    (head : Nat) (tail : Nat -> Nat) (index : Nat) :
    extendValuation head tail (index + 1) = tail index := rfl

theorem termValue_shift
    (head : Nat) (tail : Nat -> Nat)
    (term : ValuationTerm) :
    termValue (extendValuation head tail) (Rew.shift term) =
      termValue tail term := by
  induction term with
  | bvar index => exact Fin.elim0 index
  | fvar index => rfl
  | @func arity functionSymbol args inductionHypothesis =>
      cases functionSymbol with
      | zero =>
          simpa [Rew.shift_func] using
            (termValue_zero (extendValuation head tail)
              (fun index => Rew.shift (args index)))
      | one =>
          simpa [Rew.shift_func] using
            (termValue_one (extendValuation head tail)
              (fun index => Rew.shift (args index)))
      | add =>
          simpa [Rew.shift_func, inductionHypothesis] using
            (termValue_add (extendValuation head tail)
              (fun index => Rew.shift (args index)))
      | mul =>
          simpa [Rew.shift_func, inductionHypothesis] using
            (termValue_mul (extendValuation head tail)
              (fun index => Rew.shift (args index)))

theorem iteratedSuccessorTerm_shift
    (value : Nat) :
    Rew.shift (iteratedSuccessorTerm 0 value) =
      iteratedSuccessorTerm 0 value := by
  induction value with
  | zero =>
      simp [iteratedSuccessorTerm, finiteCaseZeroTerm, Rew.func]
  | succ value inductionHypothesis =>
      simp [iteratedSuccessorTerm_succ, finiteCaseAddTerm,
        finiteCaseOneTerm, Rew.func, inductionHypothesis]

theorem valuationEqualityAssumption_shift
    (head : Nat) (tail : Nat -> Nat) (index : Nat) :
    Rewriting.shift (valuationEqualityAssumption tail index) =
      valuationEqualityAssumption
        (extendValuation head tail) (index + 1) := by
  unfold valuationEqualityAssumption finiteCaseEqualityFormula
  simp only [LogicalConnective.HomClass.map_neg, Semiformula.rew_rel]
  rw [Matrix.fun_eq_vec_two (fun coordinate =>
    Rew.shift
      (![iteratedSuccessorTerm 0 (tail index),
        (&index : ValuationTerm)] coordinate))]
  simp [iteratedSuccessorTerm_shift]

theorem valuationEqualityAssumption_extended_zero
    (head : Nat) (tail : Nat -> Nat) :
    valuationEqualityAssumption (extendValuation head tail) 0 =
      ∼finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 head) (&0) := by
  rfl

theorem mem_freeVariables_shiftTerm
    (term : ValuationTerm) {index : Nat}
    (hindex : index ∈ (Rew.shift term).freeVariables) :
    ∃ sourceIndex,
      sourceIndex ∈ term.freeVariables ∧ index = sourceIndex + 1 := by
  have hrewritten : (Rew.shift term).FVar? index := hindex
  rcases LO.FirstOrder.Semiterm.fvar?_rew hrewritten with
      hbound | hfree
  · rcases hbound with ⟨boundIndex, _⟩
    exact Fin.elim0 boundIndex
  · rcases hfree with ⟨sourceIndex, hsource, himage⟩
    refine ⟨sourceIndex, hsource, ?_⟩
    simpa [LO.FirstOrder.Semiterm.FVar?] using himage

theorem freeFormula_freeVariables_subset
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (Rewriting.free formula).freeVariables ⊆
      insert 0 (formula.freeVariables.image Nat.succ) := by
  intro index hindex
  have hrewritten : (Rewriting.free formula).FVar? index := hindex
  rcases LO.FirstOrder.Semiformula.fvar?_rew hrewritten with
      hbound | hfree
  · rcases hbound with ⟨boundIndex, hboundIndex⟩
    have hboundIndexZero : boundIndex = (0 : Fin 1) :=
      Fin.eq_zero boundIndex
    subst boundIndex
    have hindexZero : index = 0 := by
      simpa [LO.FirstOrder.Semiterm.FVar?] using hboundIndex
    subst index
    exact Finset.mem_insert_self _ _
  · rcases hfree with ⟨sourceIndex, hsource, himage⟩
    have hindexSucc : index = sourceIndex + 1 := by
      simpa [LO.FirstOrder.Semiterm.FVar?] using himage
    subst index
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨sourceIndex, hsource, rfl⟩)

theorem shiftedTermValuationContext_subset
    (head : Nat) (tail : Nat -> Nat)
    (term : ValuationTerm) (outerVariables : Finset Nat)
    (hvariables : term.freeVariables ⊆ outerVariables) :
    valuationContext (Rew.shift term).freeVariables
        (extendValuation head tail) ⊆
      (valuationContext outerVariables tail).image Rewriting.shift := by
  intro formula hformula
  rcases Finset.mem_image.mp hformula with
    ⟨index, hindex, rfl⟩
  rcases mem_freeVariables_shiftTerm term hindex with
    ⟨sourceIndex, hsource, rfl⟩
  have hsourceAssumption :
      valuationEqualityAssumption tail sourceIndex ∈
        valuationContext outerVariables tail :=
    Finset.mem_image.mpr
      ⟨sourceIndex, hvariables hsource, rfl⟩
  have hshifted :
      Rewriting.shift (valuationEqualityAssumption tail sourceIndex) ∈
        (valuationContext outerVariables tail).image Rewriting.shift :=
    Finset.mem_image.mpr
      ⟨valuationEqualityAssumption tail sourceIndex,
        hsourceAssumption, rfl⟩
  rw [valuationEqualityAssumption_shift head tail sourceIndex] at hshifted
  exact hshifted

theorem freedFormulaValuationContext_subset_branch
    (head : Nat) (tail : Nat -> Nat)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (outerVariables : Finset Nat)
    (hvariables : formula.freeVariables ⊆ outerVariables) :
    valuationContext (Rewriting.free formula).freeVariables
        (extendValuation head tail) ⊆
      insert
        (∼finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 head) (&0))
        ((valuationContext outerVariables tail).image Rewriting.shift) := by
  intro assumption hassumption
  rcases Finset.mem_image.mp hassumption with
    ⟨index, hindex, rfl⟩
  have hshape := freeFormula_freeVariables_subset formula hindex
  rcases Finset.mem_insert.mp hshape with hzero | hshifted
  · subst index
    rw [valuationEqualityAssumption_extended_zero]
    exact Finset.mem_insert_self _ _
  · rcases Finset.mem_image.mp hshifted with
      ⟨sourceIndex, hsource, hindexSucc⟩
    subst index
    have hsourceAssumption :
        valuationEqualityAssumption tail sourceIndex ∈
          valuationContext outerVariables tail :=
      Finset.mem_image.mpr
        ⟨sourceIndex, hvariables hsource, rfl⟩
    have hshiftedAssumption :
        Rewriting.shift (valuationEqualityAssumption tail sourceIndex) ∈
          (valuationContext outerVariables tail).image Rewriting.shift :=
      Finset.mem_image.mpr
        ⟨valuationEqualityAssumption tail sourceIndex,
          hsourceAssumption, rfl⟩
    rw [valuationEqualityAssumption_shift head tail sourceIndex]
      at hshiftedAssumption
    exact Finset.mem_insert_of_mem hshiftedAssumption

#print axioms shiftedTermValuationContext_subset
#print axioms freedFormulaValuationContext_subset_branch

end FoundationCompactPAValuationContextRewriting
