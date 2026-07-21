import integration.FoundationCompactPAValuationTermCompiler

/-!
# Free variables of embedded predicate instances

Substituting arithmetic terms into an embedded sentence cannot introduce any
free variable other than one already present in a substituted term.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactPAEmbeddedPredicateFreeVariables

def substitutionTermFreeVariables
    {arity : Nat}
    (terms : Fin arity ->
      LO.FirstOrder.ArithmeticSemiterm Nat 0) : Finset Nat :=
  Finset.univ.biUnion fun coordinate =>
    (terms coordinate).freeVariables

theorem embeddedSubstitution_freeVariables_subset
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty arity)
    (terms : Fin arity ->
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    ((Rewriting.emb (ξ := Nat) formula) ⇜ terms).freeVariables ⊆
      substitutionTermFreeVariables terms := by
  intro index hindex
  rcases LO.FirstOrder.Semiformula.fvar?_rew hindex with
      hbound | hfree
  · rcases hbound with ⟨coordinate, hcoordinate⟩
    have hcoordinate' :
        index ∈ (terms coordinate).freeVariables := by
      simpa using hcoordinate
    exact Finset.mem_biUnion.mpr
      ⟨coordinate, Finset.mem_univ coordinate, hcoordinate'⟩
  · rcases hfree with ⟨sourceIndex, hsource, _⟩
    have hemb : (Rewriting.emb (ξ := Nat) formula :
        LO.FirstOrder.ArithmeticSemiformula Nat arity).freeVariables = ∅ := by
      simp
    have hsource' : sourceIndex ∈
        (Rewriting.emb (ξ := Nat) formula :
          LO.FirstOrder.ArithmeticSemiformula Nat arity).freeVariables :=
      hsource
    rw [hemb] at hsource'
    simp at hsource'

theorem substitutionTermFreeVariables_vecTwo
    (first second : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    substitutionTermFreeVariables ![first, second] =
      first.freeVariables ∪ second.freeVariables := by
  ext index
  simp [substitutionTermFreeVariables]

theorem embeddedBinarySubstitution_freeVariables_subset
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty 2)
    (first second : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    ((Rewriting.emb (ξ := Nat) formula) ⇜ ![first, second]).freeVariables ⊆
      first.freeVariables ∪ second.freeVariables := by
  rw [← substitutionTermFreeVariables_vecTwo first second]
  exact embeddedSubstitution_freeVariables_subset formula ![first, second]

/-- Substituting only closed terms into an embedded bounded-arity formula
produces a closed proposition. -/
theorem embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty arity)
    (terms : Fin arity ->
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (hclosed : ∀ coordinate,
      (terms coordinate).freeVariables = ∅) :
    ((Rewriting.emb (ξ := Nat) formula) ⇜ terms).freeVariables = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro index hindex
  have hsource := embeddedSubstitution_freeVariables_subset
    formula terms hindex
  rcases Finset.mem_biUnion.mp hsource with
    ⟨coordinate, _, hcoordinate⟩
  rw [hclosed coordinate] at hcoordinate
  simpa using hcoordinate

/-! The same free-variable calculation at an arbitrary bound-variable
arity.  Bound variables are not members of `freeVariables`; only the `Nat`
coordinates of the substituted terms matter. -/

def substitutionTermFreeVariablesAtArity
    {arity boundArity : Nat}
    (terms : Fin arity ->
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity) : Finset Nat :=
  Finset.univ.biUnion fun coordinate =>
    (terms coordinate).freeVariables

theorem embeddedSubstitution_freeVariables_subset_atArity
    {arity boundArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty arity)
    (terms : Fin arity ->
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    ((Rewriting.emb (ξ := Nat) formula) ⇜ terms).freeVariables ⊆
      substitutionTermFreeVariablesAtArity terms := by
  intro index hindex
  rcases LO.FirstOrder.Semiformula.fvar?_rew hindex with
      hbound | hfree
  · rcases hbound with ⟨coordinate, hcoordinate⟩
    have hcoordinate' :
        index ∈ (terms coordinate).freeVariables := by
      simpa using hcoordinate
    exact Finset.mem_biUnion.mpr
      ⟨coordinate, Finset.mem_univ coordinate, hcoordinate'⟩
  · rcases hfree with ⟨sourceIndex, hsource, _⟩
    have hemb : (Rewriting.emb (ξ := Nat) formula :
        LO.FirstOrder.ArithmeticSemiformula Nat arity).freeVariables = ∅ := by
      simp
    have hsource' : sourceIndex ∈
        (Rewriting.emb (ξ := Nat) formula :
          LO.FirstOrder.ArithmeticSemiformula Nat arity).freeVariables :=
      hsource
    rw [hemb] at hsource'
    simp at hsource'

theorem embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    {arity boundArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty arity)
    (terms : Fin arity ->
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity)
    (vars : Finset Nat)
    (hterms : forall coordinate,
      (terms coordinate).freeVariables ⊆ vars) :
    ((Rewriting.emb (ξ := Nat) formula) ⇜ terms).freeVariables ⊆ vars := by
  intro candidate hcandidate
  have hsource := embeddedSubstitution_freeVariables_subset_atArity
    formula terms hcandidate
  rcases Finset.mem_biUnion.mp hsource with
    ⟨coordinate, _, hcoordinate⟩
  exact hterms coordinate hcoordinate

theorem
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    {arity boundArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty arity)
    (terms : Fin arity ->
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity)
    (hclosed : ∀ coordinate,
      (terms coordinate).freeVariables = ∅) :
    ((Rewriting.emb (ξ := Nat) formula) ⇜ terms).freeVariables = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro index hindex
  have hsource := embeddedSubstitution_freeVariables_subset_atArity
    formula terms hindex
  rcases Finset.mem_biUnion.mp hsource with
    ⟨coordinate, _, hcoordinate⟩
  rw [hclosed coordinate] at hcoordinate
  simpa using hcoordinate

theorem bShift_freeVariables_eq_empty_of_empty
    {boundArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat boundArity)
    (hclosed : term.freeVariables = ∅) :
    (Rew.bShift term).freeVariables = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro index hindex
  rcases LO.FirstOrder.Semiterm.fvar?_rew hindex with
      hbound | hfree
  · rcases hbound with ⟨coordinate, hcoordinate⟩
    simp at hcoordinate
  · rcases hfree with ⟨sourceIndex, hsource, _⟩
    have hsource' : sourceIndex ∈ term.freeVariables := hsource
    rw [hclosed] at hsource'
    simpa using hsource'

theorem equalityLeft_freeVariables_subset
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    left.freeVariables ⊆
      (“!!left = !!right” :
        LO.FirstOrder.ArithmeticProposition).freeVariables := by
  intro index hindex
  change index ∈
    (LO.FirstOrder.Semiformula.rel Language.Eq.eq
      ![left, right]).freeVariables
  exact Finset.mem_biUnion.mpr
    ⟨0, Finset.mem_univ 0, hindex⟩

theorem equalityRight_freeVariables_subset
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    right.freeVariables ⊆
      (“!!left = !!right” :
        LO.FirstOrder.ArithmeticProposition).freeVariables := by
  intro index hindex
  change index ∈
    (LO.FirstOrder.Semiformula.rel Language.Eq.eq
      ![left, right]).freeVariables
  exact Finset.mem_biUnion.mpr
    ⟨1, Finset.mem_univ 1, hindex⟩

@[simp] theorem equalityFormula_freeVariables
    {boundArity : Nat}
    (left right :
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    (“!!left = !!right” :
      LO.FirstOrder.ArithmeticSemiformula Nat boundArity).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiformula.rel Language.Eq.eq
      ![left, right]).freeVariables = _
  ext index
  simp [LO.FirstOrder.Semiformula.freeVariables_rel]

@[simp] theorem lessThanFormula_freeVariables
    {boundArity : Nat}
    (left right :
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    (“!!left < !!right” :
      LO.FirstOrder.ArithmeticSemiformula Nat boundArity).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
      ![left, right]).freeVariables = _
  ext index
  simp [LO.FirstOrder.Semiformula.freeVariables_rel]

#print axioms embeddedSubstitution_freeVariables_subset
#print axioms
  embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
#print axioms embeddedBinarySubstitution_freeVariables_subset
#print axioms embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
#print axioms
  embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
#print axioms bShift_freeVariables_eq_empty_of_empty
#print axioms equalityLeft_freeVariables_subset
#print axioms equalityRight_freeVariables_subset
#print axioms equalityFormula_freeVariables
#print axioms lessThanFormula_freeVariables

end FoundationCompactPAEmbeddedPredicateFreeVariables
