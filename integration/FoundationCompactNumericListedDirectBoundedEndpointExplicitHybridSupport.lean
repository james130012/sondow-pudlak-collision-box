import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

/-!
# Shared rewriting support for explicit bounded endpoints

This module records how one public substitution moves through a stack of
bounded existential quantifiers.  It is purely syntactic and is shared by the
certificate-node endpoint compilers.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport

open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

/-- Lift one public substitution through `depth` binders. -/
def sourceSubstitutionQpow
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity) :
    (depth : Nat) ->
      Rew ℒₒᵣ Nat (sourceArity + depth) Nat (targetArity + depth)
  | 0 => Rew.subst terms
  | depth + 1 => (sourceSubstitutionQpow terms depth).q

/-- Lift one target term through `depth` binders. -/
def sourceSubstitutionLift
    {Variable : Type*} {targetArity : Nat} :
    (depth : Nat) -> ArithmeticSemiterm Variable targetArity ->
      ArithmeticSemiterm Variable (targetArity + depth)
  | 0, term => term
  | depth + 1, term =>
      Rew.bShift (sourceSubstitutionLift depth term)

theorem sourceSubstitutionLift_freeVariables_eq
    {targetArity : Nat} :
    forall (depth : Nat)
      (term : ArithmeticSemiterm Nat targetArity),
      (sourceSubstitutionLift depth term).freeVariables =
        term.freeVariables
  | 0, _ => rfl
  | depth + 1, term => by
      change
        (Rew.bShift
          (sourceSubstitutionLift depth term)).freeVariables =
            term.freeVariables
      calc
        (Rew.bShift
            (sourceSubstitutionLift depth term)).freeVariables =
            (sourceSubstitutionLift depth term).freeVariables := by
          ext candidate
          exact LO.FirstOrder.Semiterm.fvar?_bShift
        _ = term.freeVariables :=
          sourceSubstitutionLift_freeVariables_eq depth term

/-- Close `depth` bounded existential witnesses while retaining a public
source arity.  At binder depth `k`, the public bound is shifted through exactly
`k` local binders. -/
def sourceBoundedWitnessFormula
    {Variable : Type*} {sourceArity : Nat}
    (bound : ArithmeticSemiterm Variable sourceArity) :
    (depth : Nat) ->
      ArithmeticSemiformula Variable (sourceArity + depth) ->
      ArithmeticSemiformula Variable sourceArity
  | 0, body => body
  | depth + 1, body =>
      sourceBoundedWitnessFormula bound depth
        (body.bexsLTSucc (sourceSubstitutionLift depth bound))

/-- Lift an arbitrary rewriting through `depth` new binders. -/
def rewritingQpow
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity) :
    (depth : Nat) ->
      Rew ℒₒᵣ sourceVariables (sourceArity + depth)
        targetVariables (targetArity + depth)
  | 0 => rewriting
  | depth + 1 => (rewritingQpow rewriting depth).q

@[simp] theorem rewritingQpow_emb_eq_emb
    (sourceArity depth : Nat) :
    rewritingQpow
        (Rew.emb : Rew ℒₒᵣ Empty sourceArity Nat sourceArity) depth =
      (Rew.emb : Rew ℒₒᵣ Empty (sourceArity + depth)
        Nat (sourceArity + depth)) := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [rewritingQpow]
      rw [inductionHypothesis]
      apply Rew.ext
      · intro coordinate
        cases coordinate using Fin.cases with
        | zero => simp
        | succ coordinate => simp
      · intro coordinate
        exact Empty.elim coordinate

@[simp] theorem rewritingQpow_sourceSubstitutionLift
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity) :
    forall (depth : Nat)
      (term : ArithmeticSemiterm sourceVariables sourceArity),
      rewritingQpow rewriting depth
          (sourceSubstitutionLift depth term) =
        sourceSubstitutionLift depth (rewriting term) := by
  intro depth
  induction depth with
  | zero =>
      intro term
      rfl
  | succ depth inductionHypothesis =>
      intro term
      simp [rewritingQpow, sourceSubstitutionLift,
        inductionHypothesis, Rew.q_comp_bShift_app]

@[simp] theorem sourceSubstitutionQpow_sourceSubstitutionLift
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity) :
    forall (depth : Nat)
      (term : ArithmeticSemiterm Nat sourceArity),
      sourceSubstitutionQpow terms depth
          (sourceSubstitutionLift depth term) =
        sourceSubstitutionLift depth (Rew.subst terms term) := by
  intro depth
  induction depth with
  | zero =>
      intro term
      rfl
  | succ depth inductionHypothesis =>
      intro term
      simp [sourceSubstitutionQpow, sourceSubstitutionLift,
        inductionHypothesis, Rew.q_comp_bShift_app]

def sourceSubstitutionNormalizedBVarResult
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity)
    (depth : Nat) (index : Fin (sourceArity + depth)) :
    ArithmeticSemiterm Nat (targetArity + depth) :=
  if hlocal : index.val < depth then
    (#(⟨index.val, by omega⟩ : Fin (targetArity + depth)) :
      ArithmeticSemiterm Nat (targetArity + depth))
  else
    sourceSubstitutionLift depth
      (terms ⟨index.val - depth, by omega⟩)

theorem sourceSubstitutionNormalizedBVarResult_eq
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity) :
    ∀ (depth : Nat) (index : Fin (sourceArity + depth)),
      sourceSubstitutionNormalizedBVarResult terms depth index =
        sourceSubstitutionQpow terms depth
          (#index : ArithmeticSemiterm Nat (sourceArity + depth)) := by
  intro depth
  induction depth with
  | zero =>
      intro index
      simp [sourceSubstitutionNormalizedBVarResult,
        sourceSubstitutionQpow, sourceSubstitutionLift,
        Rew.subst_bvar]
  | succ depth inductionHypothesis =>
      intro index
      cases index using Fin.cases with
      | zero =>
          simp [sourceSubstitutionNormalizedBVarResult,
            sourceSubstitutionQpow]
      | succ index =>
          rw [show
            sourceSubstitutionQpow terms (depth + 1)
                (#index.succ : ArithmeticSemiterm Nat
                  (sourceArity + (depth + 1))) =
              Rew.bShift
                (sourceSubstitutionQpow terms depth
                  (#index : ArithmeticSemiterm Nat
                    (sourceArity + depth))) by
            change (sourceSubstitutionQpow terms depth).q
                (#index.succ) = _
            rw [Rew.q_bvar_succ]]
          rw [← inductionHypothesis index]
          by_cases hlocal : index.val < depth
          · have hlocalSucc : index.val + 1 < depth + 1 := by omega
            simp [sourceSubstitutionNormalizedBVarResult,
              hlocal, hlocalSucc]
          · have hlocalSucc : ¬index.val + 1 < depth + 1 := by omega
            simp [sourceSubstitutionNormalizedBVarResult,
              hlocal, hlocalSucc, sourceSubstitutionLift]

@[simp] theorem sourceSubstitutionQpow_bvar
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity)
    (depth : Nat) (index : Fin (sourceArity + depth)) :
    sourceSubstitutionQpow terms depth
        (#index : ArithmeticSemiterm Nat (sourceArity + depth)) =
      sourceSubstitutionNormalizedBVarResult terms depth index :=
  (sourceSubstitutionNormalizedBVarResult_eq terms depth index).symm

private theorem rewriting_bexsLTSucc
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (bound : ArithmeticSemiterm sourceVariables sourceArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1)) :
    rewriting ▹ body.bexsLTSucc bound =
      (rewriting.q ▹ body).bexsLTSucc (rewriting bound) := by
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT]

@[simp] theorem rewritingQpow_bexsLTSucc
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity depth : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (bound : ArithmeticSemiterm sourceVariables (sourceArity + depth))
    (body : ArithmeticSemiformula sourceVariables
      (sourceArity + (depth + 1))) :
    rewritingQpow rewriting depth ▹ body.bexsLTSucc bound =
      (rewritingQpow rewriting (depth + 1) ▹ body).bexsLTSucc
        (rewritingQpow rewriting depth bound) := by
  simpa [rewritingQpow] using
    (rewriting_bexsLTSucc
      (rewritingQpow rewriting depth) bound body)

/-- Any rewriting crosses an arbitrary stack of shared-bound existential
binders by lifting both the rewriting and the bound at each level. -/
theorem rewriting_sourceBoundedWitnessFormula
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (bound : ArithmeticSemiterm sourceVariables sourceArity) :
    forall (depth : Nat)
      (body : ArithmeticSemiformula sourceVariables
        (sourceArity + depth)),
      rewriting ▹ sourceBoundedWitnessFormula bound depth body =
        sourceBoundedWitnessFormula (rewriting bound) depth
          (rewritingQpow rewriting depth ▹ body) := by
  intro depth
  induction depth with
  | zero =>
      intro body
      rfl
  | succ depth inductionHypothesis =>
      intro body
      simp only [sourceBoundedWitnessFormula]
      rw [inductionHypothesis]
      rw [rewritingQpow_bexsLTSucc]
      rw [rewritingQpow_sourceSubstitutionLift]

@[simp] theorem sourceSubstitutionQpow_bexsLTSucc
    {sourceArity targetArity depth : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity)
    (bound : ArithmeticSemiterm Nat (sourceArity + depth))
    (body : ArithmeticSemiformula Nat (sourceArity + (depth + 1))) :
    sourceSubstitutionQpow terms depth ▹ body.bexsLTSucc bound =
      (sourceSubstitutionQpow terms (depth + 1) ▹ body).bexsLTSucc
        (sourceSubstitutionQpow terms depth bound) := by
  simpa [sourceSubstitutionQpow] using
    (rewriting_bexsLTSucc
      (sourceSubstitutionQpow terms depth) bound body)

/-- A public substitution crosses an arbitrary stack of bounded existential
binders without changing either their order or their shared bound. -/
theorem sourceSubstitution_sourceBoundedWitnessFormula
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity)
    (bound : ArithmeticSemiterm Nat sourceArity) :
    forall (depth : Nat)
      (body : ArithmeticSemiformula Nat (sourceArity + depth)),
      Rew.subst terms ▹ sourceBoundedWitnessFormula bound depth body =
        sourceBoundedWitnessFormula (Rew.subst terms bound) depth
          (sourceSubstitutionQpow terms depth ▹ body) := by
  intro depth
  induction depth with
  | zero =>
      intro body
      rfl
  | succ depth inductionHypothesis =>
      intro body
      simp only [sourceBoundedWitnessFormula]
      rw [inductionHypothesis]
      rw [sourceSubstitutionQpow_bexsLTSucc]
      rw [sourceSubstitutionQpow_sourceSubstitutionLift]

/-- A public source coordinate becomes the same term shifted past every new
binder. -/
theorem sourceSubstitutionQpow_shiftedBVar
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity)
    (depth : Nat) (coordinate : Fin sourceArity) :
    sourceSubstitutionQpow terms depth
        (#(⟨depth + coordinate.val, by omega⟩ :
          Fin (sourceArity + depth)) :
          ArithmeticSemiterm Nat (sourceArity + depth)) =
      sourceSubstitutionLift depth (terms coordinate) := by
  rw [sourceSubstitutionQpow_bvar]
  simp [sourceSubstitutionNormalizedBVarResult]

#print axioms sourceSubstitutionNormalizedBVarResult_eq
#print axioms sourceSubstitutionQpow_bexsLTSucc
#print axioms sourceSubstitutionQpow_shiftedBVar
#print axioms sourceSubstitutionQpow_sourceSubstitutionLift
#print axioms sourceSubstitution_sourceBoundedWitnessFormula
#print axioms rewritingQpow_sourceSubstitutionLift
#print axioms rewriting_sourceBoundedWitnessFormula
#print axioms rewritingQpow_emb_eq_emb
#print axioms sourceSubstitutionLift_freeVariables_eq

end FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
