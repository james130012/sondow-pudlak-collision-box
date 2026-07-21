import integration.FoundationCompactPACertifiedInduction

/-!
# Syntax for finite PA case exhaustion

`finiteEqualityCases x B` is the explicit disjunction
`0 = x ∨ ... ∨ (B-1) = x`.  The companion induction body is
`finiteEqualityCases x B ∨ B ≤ x`.  Iterated successor numerals are used so
that the successor step is syntactically transparent; a later certified
normalization connects them to the project's short binary numerals.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAFiniteCaseSyntax

def finiteCaseZeroTerm (arity : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Nat arity :=
  LO.FirstOrder.Semiterm.func Language.Zero.zero ![]

def finiteCaseOneTerm (arity : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Nat arity :=
  LO.FirstOrder.Semiterm.func Language.One.one ![]

def finiteCaseAddTerm
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    LO.FirstOrder.ArithmeticSemiterm Nat arity :=
  LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]

def finiteCaseEqualityFormula
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    LO.FirstOrder.ArithmeticSemiformula Nat arity :=
  LO.FirstOrder.Semiformula.rel Language.Eq.eq ![left, right]

def finiteCaseLessThanFormula
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    LO.FirstOrder.ArithmeticSemiformula Nat arity :=
  LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt ![left, right]

theorem finiteCaseEqualityFormula_eq_operator
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    finiteCaseEqualityFormula left right =
      (“!!left = !!right” :
        LO.FirstOrder.ArithmeticSemiformula Nat arity) := by
  simp [finiteCaseEqualityFormula, Semiformula.Operator.eq_def,
    Matrix.fun_eq_vec_two]

theorem finiteCaseLessThanFormula_eq_operator
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    finiteCaseLessThanFormula left right =
      (“!!left < !!right” :
        LO.FirstOrder.ArithmeticSemiformula Nat arity) := by
  simp [finiteCaseLessThanFormula, Semiformula.Operator.lt_def,
    Matrix.fun_eq_vec_two]
  rfl

def iteratedSuccessorTerm (arity : Nat) :
    Nat → LO.FirstOrder.ArithmeticSemiterm Nat arity
  | 0 => finiteCaseZeroTerm arity
  | value + 1 => finiteCaseAddTerm
      (iteratedSuccessorTerm arity value) (finiteCaseOneTerm arity)

@[simp] theorem iteratedSuccessorTerm_zero (arity : Nat) :
    iteratedSuccessorTerm arity 0 = finiteCaseZeroTerm arity := rfl

@[simp] theorem iteratedSuccessorTerm_succ (arity value : Nat) :
    iteratedSuccessorTerm arity (value + 1) =
      finiteCaseAddTerm (iteratedSuccessorTerm arity value)
        (finiteCaseOneTerm arity) := rfl

theorem iteratedSuccessorTerm_freeVariables_eq_empty
    (arity value : Nat) :
    (iteratedSuccessorTerm arity value).freeVariables = ∅ := by
  induction value with
  | zero => rfl
  | succ value ih =>
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro index hindex
      simp [iteratedSuccessorTerm_succ, Semiterm.freeVariables_func,
        finiteCaseOneTerm, finiteCaseAddTerm,
        ih] at hindex

theorem iteratedSuccessorTerm_substitution
    (value : Nat)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (Rew.subst ![witness]) (iteratedSuccessorTerm 1 value) =
      iteratedSuccessorTerm 0 value := by
  induction value with
  | zero =>
      simp [iteratedSuccessorTerm, finiteCaseZeroTerm, Rew.func]
  | succ value ih =>
      simp only [iteratedSuccessorTerm_succ]
      simp [finiteCaseAddTerm, finiteCaseOneTerm, Rew.func, ih]

def finiteEqualityCases
    {arity : Nat}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    Nat → LO.FirstOrder.ArithmeticSemiformula Nat arity
  | 0 => ⊥
  | bound + 1 =>
      finiteEqualityCases subject bound ⋎
        finiteCaseEqualityFormula
          (iteratedSuccessorTerm arity bound) subject

@[simp] theorem finiteEqualityCases_zero
    {arity : Nat}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    finiteEqualityCases subject 0 =
      (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat arity) := rfl

@[simp] theorem finiteEqualityCases_succ
    {arity : Nat}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (bound : Nat) :
    finiteEqualityCases subject (bound + 1) =
      finiteEqualityCases subject bound ⋎
        finiteCaseEqualityFormula
          (iteratedSuccessorTerm arity bound) subject := rfl

theorem finiteCaseEqualityFormula_freeVariables_eq_empty
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (finiteCaseEqualityFormula left right).freeVariables = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro index hindex
  simp [finiteCaseEqualityFormula, Semiformula.freeVariables_rel,
    hleft, hright] at hindex

theorem finiteCaseLessThanFormula_freeVariables_eq_empty
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (finiteCaseLessThanFormula left right).freeVariables = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro index hindex
  simp [finiteCaseLessThanFormula, Semiformula.freeVariables_rel,
    hleft, hright] at hindex

theorem finiteCaseEqualityFormula_substitution
    (value : Nat)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (finiteCaseEqualityFormula
      (iteratedSuccessorTerm 1 value) (#0))/[witness] =
      finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 value) witness := by
  unfold finiteCaseEqualityFormula
  simp only [Semiformula.rew_rel]
  rw [Matrix.fun_eq_vec_two
    (fun index => (Rew.subst ![witness])
      (![iteratedSuccessorTerm 1 value,
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)] index))]
  simp [iteratedSuccessorTerm_substitution]

theorem finiteCaseLessThanFormula_substitution
    (bound : Nat)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (finiteCaseLessThanFormula (#0)
      (iteratedSuccessorTerm 1 bound))/[witness] =
      finiteCaseLessThanFormula witness
        (iteratedSuccessorTerm 0 bound) := by
  unfold finiteCaseLessThanFormula
  simp only [Semiformula.rew_rel]
  rw [Matrix.fun_eq_vec_two
    (fun index => (Rew.subst ![witness])
      (![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
        iteratedSuccessorTerm 1 bound] index))]
  simp [iteratedSuccessorTerm_substitution]

theorem finiteEqualityCases_freeVariables_eq_empty
    {arity bound : Nat}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (hsubject : subject.freeVariables = ∅) :
    (finiteEqualityCases subject bound).freeVariables = ∅ := by
  induction bound with
  | zero => rfl
  | succ bound ih =>
      have hnumeral := iteratedSuccessorTerm_freeVariables_eq_empty
        arity bound
      have hequality := finiteCaseEqualityFormula_freeVariables_eq_empty
        (iteratedSuccessorTerm arity bound) subject hnumeral hsubject
      simp only [finiteEqualityCases_succ,
        Semiformula.freeVariables_or]
      rw [ih, hequality]
      simp

theorem finiteEqualityCases_substitution
    (bound : Nat)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (finiteEqualityCases (#0 :
      LO.FirstOrder.ArithmeticSemiterm Nat 1) bound)/[witness] =
      finiteEqualityCases witness bound := by
  induction bound with
  | zero =>
      simp [finiteEqualityCases]
  | succ bound ih =>
      calc
        (finiteEqualityCases (#0 :
            LO.FirstOrder.ArithmeticSemiterm Nat 1) (bound + 1))/[witness] =
            (finiteEqualityCases (#0 :
              LO.FirstOrder.ArithmeticSemiterm Nat 1) bound)/[witness] ⋎
              (finiteCaseEqualityFormula
                (iteratedSuccessorTerm 1 bound) (#0))/[witness] := by
          simp only [finiteEqualityCases_succ,
            LogicalConnective.HomClass.map_or]
        _ = finiteEqualityCases witness bound ⋎
              finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 bound) witness := by
          rw [ih, finiteCaseEqualityFormula_substitution]
        _ = finiteEqualityCases witness (bound + 1) := by
          rfl

def finiteExhaustionBody (bound : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  let subject := (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)
  let boundTerm := iteratedSuccessorTerm 1 bound
  finiteEqualityCases subject bound ⋎
    ∼finiteCaseLessThanFormula subject boundTerm

def finiteExhaustionFormula
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  finiteEqualityCases subject bound ⋎
    ∼finiteCaseLessThanFormula subject (iteratedSuccessorTerm 0 bound)

theorem finiteExhaustionBody_substitution
    (bound : Nat)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (finiteExhaustionBody bound)/[witness] =
      finiteExhaustionFormula bound witness := by
  calc
    (finiteExhaustionBody bound)/[witness] =
        (finiteEqualityCases (#0 :
          LO.FirstOrder.ArithmeticSemiterm Nat 1) bound)/[witness] ⋎
        ∼((finiteCaseLessThanFormula (#0)
          (iteratedSuccessorTerm 1 bound))/[witness]) := by
      unfold finiteExhaustionBody
      simp only [LogicalConnective.HomClass.map_or,
        LogicalConnective.HomClass.map_neg]
    _ = finiteEqualityCases witness bound ⋎
        ∼finiteCaseLessThanFormula witness
          (iteratedSuccessorTerm 0 bound) := by
      rw [finiteEqualityCases_substitution,
        finiteCaseLessThanFormula_substitution]
    _ = finiteExhaustionFormula bound witness := by
      rfl

theorem finiteExhaustionBody_freeVariables_eq_empty
    (bound : Nat) :
    (finiteExhaustionBody bound).freeVariables = ∅ := by
  let subject := (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)
  have hsubject : subject.freeVariables = ∅ := by rfl
  have hcases := finiteEqualityCases_freeVariables_eq_empty
    (bound := bound) subject hsubject
  have hbound := iteratedSuccessorTerm_freeVariables_eq_empty 1 bound
  have hless := finiteCaseLessThanFormula_freeVariables_eq_empty
    subject (iteratedSuccessorTerm 1 bound) hsubject hbound
  unfold finiteExhaustionBody
  simp only [Semiformula.freeVariables_or,
    Semiformula.freeVariables_not]
  rw [hcases, hless]
  simp

#print axioms finiteExhaustionBody_substitution
#print axioms finiteExhaustionBody_freeVariables_eq_empty

end FoundationCompactPAFiniteCaseSyntax
