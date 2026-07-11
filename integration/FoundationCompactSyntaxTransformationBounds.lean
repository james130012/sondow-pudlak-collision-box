import integration.FoundationCompactCertificateDecoderStructuralBound

/-!
# Polynomial size bounds for syntax transformations used by the checker
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactSyntaxTransformationBounds

open FoundationSuccinctFiniteConsistencyTarget

theorem one_le_termSymbolCount
    {L : Language} {xi : Type*} {arity : Nat}
    (term : Semiterm L xi arity) :
    1 <= termSymbolCount term := by
  cases term <;> simp [termSymbolCount]

theorem one_le_formulaSymbolCount
    {L : Language} {xi : Type*} {arity : Nat}
    (formula : Semiformula L xi arity) :
    1 <= formulaSymbolCount formula := by
  cases formula <;> simp [formulaSymbolCount] <;> omega

theorem termSymbolCount_bShift
    {L : Language} {xi : Type*} {arity : Nat}
    (term : Semiterm L xi arity) :
    termSymbolCount (Rew.bShift term) = termSymbolCount term := by
  induction term with
  | bvar index => simp [termSymbolCount]
  | fvar index => simp [termSymbolCount]
  | func functionSymbol arguments ih =>
      simp only [Rew.func, termSymbolCount]
      apply congrArg (fun value => 1 + value)
      exact Finset.sum_congr rfl (fun index _ => ih index)

/-- Every variable image under a rewriting has at most `bound` symbols. -/
def RewritingTermImageBound
    {L : Language} {xi1 xi2 : Type*} {arity1 arity2 : Nat}
    (rewriting : Rew L xi1 arity1 xi2 arity2)
    (bound : Nat) : Prop :=
  (forall index,
      termSymbolCount (rewriting (#index : Semiterm L xi1 arity1)) <=
        bound) ∧
    (forall index,
      termSymbolCount (rewriting (&index : Semiterm L xi1 arity1)) <=
        bound)

theorem RewritingTermImageBound.q
    {L : Language} {xi1 xi2 : Type*} {arity1 arity2 bound : Nat}
    {rewriting : Rew L xi1 arity1 xi2 arity2}
    (hbound : 1 <= bound)
    (himages : RewritingTermImageBound rewriting bound) :
    RewritingTermImageBound rewriting.q bound := by
  constructor
  · intro index
    cases index using Fin.cases with
    | zero => simpa [termSymbolCount] using hbound
    | succ index =>
        simpa [termSymbolCount_bShift] using himages.1 index
  · intro index
    simpa [termSymbolCount_bShift] using himages.2 index

theorem termSymbolCount_rewriting_le_mul
    {L : Language} {xi1 xi2 : Type*} {arity1 arity2 bound : Nat}
    (rewriting : Rew L xi1 arity1 xi2 arity2)
    (hbound : 1 <= bound)
    (himages : RewritingTermImageBound rewriting bound)
    (term : Semiterm L xi1 arity1) :
    termSymbolCount (rewriting term) <= termSymbolCount term * bound := by
  induction term with
  | bvar index =>
      simpa [termSymbolCount] using himages.1 index
  | fvar index =>
      simpa [termSymbolCount] using himages.2 index
  | func functionSymbol arguments ih =>
      have hchildren :
          Finset.univ.sum
              (fun index => termSymbolCount (rewriting (arguments index))) <=
            Finset.univ.sum
              (fun index => termSymbolCount (arguments index) * bound) :=
        Finset.sum_le_sum (fun index _ => ih index)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                termSymbolCount ((rewriting ∘ arguments) index)) <=
            Finset.univ.sum
              (fun index => termSymbolCount (arguments index) * bound) := by
        simpa [Function.comp_def] using hchildren
      simp only [Rew.func, termSymbolCount]
      rw [Nat.add_mul, one_mul, Finset.sum_mul]
      omega

theorem formulaSymbolCount_rewriting_le_mul
    {L : Language} {xi1 xi2 : Type*} {arity1 arity2 bound : Nat}
    (rewriting : Rew L xi1 arity1 xi2 arity2)
    (hbound : 1 <= bound)
    (himages : RewritingTermImageBound rewriting bound)
    (formula : Semiformula L xi1 arity1) :
    formulaSymbolCount (rewriting ▹ formula) <=
      formulaSymbolCount formula * bound := by
  induction formula using Semiformula.rec' generalizing arity2 with
  | hverum => simp [formulaSymbolCount, hbound]
  | hfalsum => simp [formulaSymbolCount, hbound]
  | hrel relationSymbol arguments =>
      have hchildren :
          Finset.univ.sum
              (fun index =>
                termSymbolCount (rewriting (arguments index))) <=
            Finset.univ.sum
              (fun index => termSymbolCount (arguments index) * bound) :=
        Finset.sum_le_sum (fun index _ =>
          termSymbolCount_rewriting_le_mul rewriting hbound himages
            (arguments index))
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                termSymbolCount ((rewriting ∘ arguments) index)) <=
            Finset.univ.sum
              (fun index => termSymbolCount (arguments index) * bound) := by
        simpa [Function.comp_def] using hchildren
      simp only [Semiformula.rew_rel, formulaSymbolCount]
      rw [Nat.add_mul, one_mul, Finset.sum_mul]
      omega
  | hnrel relationSymbol arguments =>
      have hchildren :
          Finset.univ.sum
              (fun index =>
                termSymbolCount (rewriting (arguments index))) <=
            Finset.univ.sum
              (fun index => termSymbolCount (arguments index) * bound) :=
        Finset.sum_le_sum (fun index _ =>
          termSymbolCount_rewriting_le_mul rewriting hbound himages
            (arguments index))
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                termSymbolCount ((rewriting ∘ arguments) index)) <=
            Finset.univ.sum
              (fun index => termSymbolCount (arguments index) * bound) := by
        simpa [Function.comp_def] using hchildren
      simp only [Semiformula.rew_nrel, formulaSymbolCount]
      rw [Nat.add_mul, one_mul, Finset.sum_mul]
      omega
  | hand left right ihLeft ihRight =>
      simp only [LogicalConnective.HomClass.map_and, formulaSymbolCount]
      rw [Nat.add_mul, Nat.add_mul, one_mul]
      have hleft := ihLeft rewriting himages
      have hright := ihRight rewriting himages
      omega
  | hor left right ihLeft ihRight =>
      simp only [LogicalConnective.HomClass.map_or, formulaSymbolCount]
      rw [Nat.add_mul, Nat.add_mul, one_mul]
      have hleft := ihLeft rewriting himages
      have hright := ihRight rewriting himages
      omega
  | hall body ih =>
      simp only [Rewriting.app_all, formulaSymbolCount]
      rw [Nat.add_mul, one_mul]
      have hbody := ih rewriting.q (himages.q hbound)
      omega
  | hexs body ih =>
      simp only [Rewriting.app_exs, formulaSymbolCount]
      rw [Nat.add_mul, one_mul]
      have hbody := ih rewriting.q (himages.q hbound)
      omega

theorem formulaSymbolCount_neg
    {L : Language} {xi : Type*} {arity : Nat}
    (formula : Semiformula L xi arity) :
    formulaSymbolCount (∼formula) = formulaSymbolCount formula := by
  induction formula using Semiformula.rec' <;>
    simp [formulaSymbolCount, *]

theorem rewritingMap_termImageBound_one
    {L : Language} {xi1 xi2 : Type*} {arity1 arity2 : Nat}
    (boundMap : Fin arity1 -> Fin arity2)
    (freeMap : xi1 -> xi2) :
    RewritingTermImageBound (Rew.map (L := L) boundMap freeMap) 1 := by
  constructor <;> intro index <;> simp [termSymbolCount]

theorem formulaSymbolCount_rewritingMap_le
    {L : Language} {xi1 xi2 : Type*} {arity1 arity2 : Nat}
    (boundMap : Fin arity1 -> Fin arity2)
    (freeMap : xi1 -> xi2)
    (formula : Semiformula L xi1 arity1) :
    formulaSymbolCount (Rew.map (L := L) boundMap freeMap ▹ formula) <=
      formulaSymbolCount formula := by
  simpa using
    formulaSymbolCount_rewriting_le_mul
      (Rew.map (L := L) boundMap freeMap) (by simp)
      (rewritingMap_termImageBound_one boundMap freeMap) formula

theorem formulaSymbolCount_shift_le
    {L : Language} {arity : Nat}
    (formula : Semiformula L Nat arity) :
    formulaSymbolCount (Rewriting.shift formula) <=
      formulaSymbolCount formula := by
  exact formulaSymbolCount_rewritingMap_le id Nat.succ formula

theorem rewritingFree_termImageBound_one
    {L : Language} {arity : Nat} :
    RewritingTermImageBound (Rew.free (L := L) (n := arity)) 1 := by
  constructor
  · intro index
    cases index using Fin.lastCases <;> simp [termSymbolCount]
  · intro index
    simp [termSymbolCount]

theorem formulaSymbolCount_free_le
    {L : Language} {arity : Nat}
    (formula : Semiformula L Nat (arity + 1)) :
    formulaSymbolCount (Rewriting.free formula) <=
      formulaSymbolCount formula := by
  simpa using
    formulaSymbolCount_rewriting_le_mul
      (Rew.free (L := L) (n := arity)) (by simp)
      (rewritingFree_termImageBound_one (L := L) (arity := arity)) formula

theorem formulaSymbolCount_emb_le
    {L : Language} {emptyType xi : Type*} [IsEmpty emptyType]
    {arity : Nat} (formula : Semiformula L emptyType arity) :
    formulaSymbolCount
        (Rewriting.emb formula : Semiformula L xi arity) <=
      formulaSymbolCount formula := by
  exact formulaSymbolCount_rewritingMap_le id isEmptyElim formula

theorem substitutionOne_termImageBound
    {L : Language} {xi : Type*} {arity : Nat}
    (witness : Semiterm L xi arity) :
    RewritingTermImageBound (Rew.subst ![witness])
      (termSymbolCount witness) := by
  constructor
  · intro index
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    simp
  · intro index
    simpa [termSymbolCount] using one_le_termSymbolCount witness

theorem formulaSymbolCount_substitution_one_le_mul
    {L : Language} {xi : Type*} {arity : Nat}
    (formula : Semiformula L xi 1)
    (witness : Semiterm L xi arity) :
    formulaSymbolCount (formula/[witness]) <=
      formulaSymbolCount formula * termSymbolCount witness := by
  exact formulaSymbolCount_rewriting_le_mul
    (Rew.subst ![witness]) (one_le_termSymbolCount witness)
    (substitutionOne_termImageBound witness) formula

#print axioms formulaSymbolCount_rewriting_le_mul
#print axioms formulaSymbolCount_neg
#print axioms formulaSymbolCount_substitution_one_le_mul

end FoundationCompactSyntaxTransformationBounds
