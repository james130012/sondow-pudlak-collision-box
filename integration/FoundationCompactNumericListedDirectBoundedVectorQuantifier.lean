import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBoundedVectorQuantifier

/-- Views a term in the global variables after a prefix of local variables. -/
def liftPast (k : Nat) (t : ArithmeticSemiterm ξ n) :
    ArithmeticSemiterm ξ (n + k) :=
  Rew.subst (fun i => #(Fin.cast (Nat.add_comm k n) (Fin.natAdd k i))) t

@[simp] theorem liftPast_val
    (witnesses : Fin k -> Nat) (global : Fin n -> Nat)
    (t : ArithmeticSemiterm ξ n) (ε : ξ -> Nat) :
    (liftPast k t).val (Matrix.appendr witnesses global) ε = t.val global ε := by
  let embedding : Rew ℒₒᵣ ξ n ξ (n + k) :=
    Rew.subst (fun i => #(Fin.cast (Nat.add_comm k n) (Fin.natAdd k i)))
  unfold liftPast
  change (embedding t).val (Matrix.appendr witnesses global) ε = t.val global ε
  rw [Semiterm.val_rew]
  have hb :
      Semiterm.val (Matrix.appendr witnesses global) ε ∘
          ⇑embedding ∘
            Semiterm.bvar = global := by
    funext i
    change Matrix.appendr witnesses global
      (Fin.cast (Nat.add_comm k n) (Fin.natAdd k i)) = global i
    simp [Matrix.appendr, Matrix.vecAppend_eq_ite]
  have hf :
      Semiterm.val (Matrix.appendr witnesses global) ε ∘
          ⇑embedding ∘
            Semiterm.fvar = ε := by
    funext x
    change Semiterm.val (Matrix.appendr witnesses global) ε (&x) = ε x
    simp
  rw [hb, hf]

/-- Binds the first `k` variables, each by the same global-variable bound. -/
def boundedVectorBExs (valueBound : ArithmeticSemiterm ξ n) :
    (k : Nat) -> ArithmeticSemiformula ξ (n + k) -> ArithmeticSemiformula ξ n
  | 0, phi => phi
  | k + 1, phi =>
      boundedVectorBExs valueBound k (phi.bexsLTSucc (liftPast k valueBound))

theorem eval_boundedVectorBExs
    (valueBound : ArithmeticSemiterm ξ n)
    (phi : ArithmeticSemiformula ξ (n + k))
    (global : Fin n -> Nat) (ε : ξ -> Nat) :
    (boundedVectorBExs valueBound k phi).Eval global ε ↔
      ∃ witnesses : Fin k -> Nat,
        (∀ i, witnesses i ≤ valueBound.val global ε) /\
          phi.Eval (Matrix.appendr witnesses global) ε := by
  induction k with
  | zero =>
      constructor
      · intro hphi
        refine ⟨![], fun i => i.elim0, ?_⟩
        simpa [boundedVectorBExs] using hphi
      · rintro ⟨witnesses, _, hphi⟩
        have hwitnesses : witnesses = ![] := Subsingleton.elim _ _
        simpa [boundedVectorBExs, hwitnesses] using hphi
  | succ k ih =>
      rw [boundedVectorBExs, ih]
      constructor
      · rintro ⟨witnesses, hwitnesses, hphi⟩
        rw [eval_bexsLTSucc', liftPast_val] at hphi
        rcases hphi with ⟨x, hx, hphi⟩
        refine ⟨x :> witnesses, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact le_iff_eq_or_lt.mpr hx
          · exact hwitnesses j
        · simpa only [Matrix.appendr_cons] using hphi
      · rintro ⟨witnesses, hwitnesses, hphi⟩
        let x : Nat := witnesses 0
        let tail : Fin k -> Nat := witnesses ∘ Fin.succ
        have hwitnesses_eq : witnesses = x :> tail := by
          simp [x, tail, Matrix.eq_vecCons]
        apply Exists.intro tail
        refine ⟨?_, ?_⟩
        · intro i
          exact hwitnesses i.succ
        · rw [eval_bexsLTSucc', liftPast_val]
          refine ⟨x, le_iff_eq_or_lt.mp (hwitnesses 0), ?_⟩
          rw [hwitnesses_eq] at hphi
          simpa only [Matrix.appendr_cons] using hphi

theorem evalb_boundedVectorBExs
    (valueBound : ArithmeticSemiterm Empty n)
    (phi : ArithmeticSemiformula Empty (n + k))
    (global : Fin n -> Nat) :
    (boundedVectorBExs valueBound k phi).Evalb global ↔
      ∃ witnesses : Fin k -> Nat,
        (∀ i, witnesses i ≤ valueBound.val global Empty.elim) /\
          phi.Evalb (Matrix.appendr witnesses global) := by
  simpa using eval_boundedVectorBExs valueBound phi global Empty.elim

theorem boundedVectorBExs_sigmaZero
    (valueBound : ArithmeticSemiterm ξ n)
    (phi : ArithmeticSemiformula ξ (n + k))
    (hphi : Hierarchy Polarity.sigma 0 phi) :
    Hierarchy Polarity.sigma 0 (boundedVectorBExs valueBound k phi) := by
  induction k with
  | zero => simpa [boundedVectorBExs] using hphi
  | succ k ih =>
      simp only [boundedVectorBExs]
      apply ih
      simpa using hphi

#print axioms liftPast_val
#print axioms eval_boundedVectorBExs
#print axioms evalb_boundedVectorBExs
#print axioms boundedVectorBExs_sigmaZero

end FoundationCompactNumericListedDirectBoundedVectorQuantifier
