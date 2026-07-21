import Foundation.FirstOrder.Arithmetic.Exponential.Bit

/-!
# Computable recognition of arithmetic leaf formulas

This module recognizes whole proposition-level instances of `expDef`,
`lengthDef`, `bitDef`, and the negation of `bitDef`.  It deliberately builds
the four targets by substitution into Foundation's named predicates rather
than duplicating their syntax trees.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactPAFastArithmeticLeafRecognizer

abbrev ArithmeticTerm :=
  LO.FirstOrder.ArithmeticSemiterm Nat 0

abbrev ArithmeticFormula :=
  LO.FirstOrder.ArithmeticProposition

/-- Traverse a finite vector of optional results without using choice. -/
private def traverseFinOption {alpha : Type*} :
    (arity : Nat) -> (Fin arity -> Option alpha) ->
      Option (Fin arity -> alpha)
  | 0, _ => some Fin.elim0
  | arity + 1, values => do
      let head <- values 0
      let tail <- traverseFinOption arity (fun i => values i.succ)
      pure (Fin.cases head tail)

/--
Turn a term at arbitrary binder depth into a proposition-level term exactly
when it contains no bound variables.  Free variables and function symbols are
preserved, so both closed terms and valuation terms survive this projection.
-/
def eraseBoundVariables?
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) :
    Option ArithmeticTerm :=
  match term with
  | .bvar _ => none
  | .fvar index => some (.fvar index)
  | @Semiterm.func _ _ _ arity function arguments => do
      let arguments <- traverseFinOption arity
        (fun i => eraseBoundVariables? (arguments i))
      pure (.func function arguments)

private theorem traverseFinOption_component
    {alpha : Type*}
    {arity : Nat}
    {values : Fin arity -> Option alpha}
    {result : Fin arity -> alpha}
    (hresult : traverseFinOption arity values = some result)
    (i : Fin arity) :
    values i = some (result i) := by
  induction arity with
  | zero => exact Fin.elim0 i
  | succ arity ih =>
      simp only [traverseFinOption] at hresult
      rcases Option.bind_eq_some_iff.mp hresult with
        ⟨head, hhead, hresult⟩
      rcases Option.bind_eq_some_iff.mp hresult with
        ⟨tail, htail, hresult⟩
      have hresult' : (fun i => Fin.cases head tail i) = result :=
        Option.some.inj hresult
      subst result
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hhead
      · simpa using ih htail j

/-- Erasing bound variables preserves the complete free-variable set. -/
theorem eraseBoundVariables?_freeVariables_eq
    {binderArity : Nat}
    {source : LO.FirstOrder.ArithmeticSemiterm Nat binderArity}
    {target : ArithmeticTerm}
    (herase : eraseBoundVariables? source = some target) :
    target.freeVariables = source.freeVariables := by
  induction source generalizing target with
  | bvar index =>
      simp [eraseBoundVariables?] at herase
  | fvar index =>
      simp only [eraseBoundVariables?, Option.some.injEq] at herase
      subst target
      rfl
  | func function arguments ih =>
      simp only [eraseBoundVariables?] at herase
      rcases Option.bind_eq_some_iff.mp herase with
        ⟨targetArguments, harguments, htarget⟩
      have htarget' :
          (.func function targetArguments : ArithmeticTerm) = target :=
        Option.some.inj htarget
      subst target
      simp only [Semiterm.freeVariables_func]
      apply Finset.biUnion_congr rfl
      intro i _
      exact ih i (traverseFinOption_component harguments i)

/--
All bound-variable-free subterms of a term.  The root is listed before the
recursive argument subterms.
-/
def termSubterms
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) :
    List ArithmeticTerm :=
  (eraseBoundVariables? term).toList ++
    match term with
    | .bvar _ => []
    | .fvar _ => []
    | .func _ arguments =>
        List.flatten <| Matrix.toList fun i => termSubterms (arguments i)

/-- Every collected term has only free variables present in its source. -/
theorem termSubterms_freeVariables_subset
    {binderArity : Nat}
    {source : LO.FirstOrder.ArithmeticSemiterm Nat binderArity}
    {target : ArithmeticTerm}
    (hmem : target ∈ termSubterms source) :
    target.freeVariables ⊆ source.freeVariables := by
  induction source generalizing target with
  | bvar index =>
      simp [termSubterms, eraseBoundVariables?] at hmem
  | fvar index =>
      have htarget : target = (.fvar index : ArithmeticTerm) := by
        simpa [termSubterms, eraseBoundVariables?] using hmem
      subst target
      exact fun _ h => h
  | func function arguments ih =>
      simp only [termSubterms, List.mem_append] at hmem
      rcases hmem with hroot | hchild
      · have herase : eraseBoundVariables?
            (.func function arguments) = some target :=
          Option.mem_toList.mp hroot
        intro index hindex
        exact eraseBoundVariables?_freeVariables_eq herase ▸ hindex
      · rcases List.mem_flatten.mp hchild with
          ⟨terms, hterms, htarget⟩
        rcases Matrix.mem_toList_iff.mp hterms with ⟨i, rfl⟩
        intro index hindex
        rw [Semiterm.freeVariables_func]
        exact Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_univ i, ih i htarget hindex⟩

/--
Collect proposition-level arithmetic terms from every atomic formula,
including atoms below quantifiers, and recursively include their subterms.
-/
def formulaTermSubterms
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) :
    List ArithmeticTerm :=
  match formula with
  | .verum => []
  | .falsum => []
  | .rel _ arguments =>
      List.flatten <| Matrix.toList fun i => termSubterms (arguments i)
  | .nrel _ arguments =>
      List.flatten <| Matrix.toList fun i => termSubterms (arguments i)
  | .and left right =>
      formulaTermSubterms left ++ formulaTermSubterms right
  | .or left right =>
      formulaTermSubterms left ++ formulaTermSubterms right
  | .all body => formulaTermSubterms body
  | .exs body => formulaTermSubterms body

/-- Every collected term has only free variables present in its formula. -/
theorem formulaTermSubterms_freeVariables_subset
    {binderArity : Nat}
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity}
    {target : ArithmeticTerm}
    (hmem : target ∈ formulaTermSubterms formula) :
    target.freeVariables ⊆ formula.freeVariables := by
  induction formula using Semiformula.rec' generalizing target with
  | hverum =>
      simp [formulaTermSubterms] at hmem
  | hfalsum =>
      simp [formulaTermSubterms] at hmem
  | hrel relation arguments =>
      simp only [formulaTermSubterms] at hmem
      rcases List.mem_flatten.mp hmem with
        ⟨terms, hterms, htarget⟩
      rcases Matrix.mem_toList_iff.mp hterms with ⟨i, rfl⟩
      intro index hindex
      rw [Semiformula.freeVariables_rel]
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i,
          termSubterms_freeVariables_subset htarget hindex⟩
  | hnrel relation arguments =>
      simp only [formulaTermSubterms] at hmem
      rcases List.mem_flatten.mp hmem with
        ⟨terms, hterms, htarget⟩
      rcases Matrix.mem_toList_iff.mp hterms with ⟨i, rfl⟩
      intro index hindex
      rw [Semiformula.freeVariables_nrel]
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i,
          termSubterms_freeVariables_subset htarget hindex⟩
  | hand left right leftIH rightIH =>
      simp only [formulaTermSubterms, List.mem_append] at hmem
      rcases hmem with hleft | hright
      · intro index hindex
        rw [Semiformula.freeVariables_and]
        exact Finset.mem_union_left _ (leftIH hleft hindex)
      · intro index hindex
        rw [Semiformula.freeVariables_and]
        exact Finset.mem_union_right _ (rightIH hright hindex)
  | hor left right leftIH rightIH =>
      simp only [formulaTermSubterms, List.mem_append] at hmem
      rcases hmem with hleft | hright
      · intro index hindex
        rw [Semiformula.freeVariables_or]
        exact Finset.mem_union_left _ (leftIH hleft hindex)
      · intro index hindex
        rw [Semiformula.freeVariables_or]
        exact Finset.mem_union_right _ (rightIH hright hindex)
  | hall body ih =>
      simpa only [Semiformula.freeVariables_all] using ih hmem
  | hexs body ih =>
      simpa only [Semiformula.freeVariables_exs] using ih hmem

/-- The duplicate-free candidate list used by the recognizer. -/
def candidateTerms (formula : ArithmeticFormula) : List ArithmeticTerm :=
  (formulaTermSubterms formula).eraseDups

/-- A computational syntax-occurrence predicate suitable for later bounds. -/
def TermOccursIn
    (term : ArithmeticTerm) (formula : ArithmeticFormula) : Prop :=
  term ∈ formulaTermSubterms formula

theorem TermOccursIn_freeVariables_subset
    {term : ArithmeticTerm}
    {formula : ArithmeticFormula}
    (hoccurs : TermOccursIn term formula) :
    term.freeVariables ⊆ formula.freeVariables :=
  formulaTermSubterms_freeVariables_subset hoccurs

def expInstance (value exponent : ArithmeticTerm) : ArithmeticFormula :=
  (Rewriting.emb expDef.val :
      LO.FirstOrder.ArithmeticSemiformula Nat 2)/[value, exponent]

def lengthInstance (size value : ArithmeticTerm) : ArithmeticFormula :=
  (Rewriting.emb lengthDef.val :
      LO.FirstOrder.ArithmeticSemiformula Nat 2)/[size, value]

def bitInstance (index value : ArithmeticTerm) : ArithmeticFormula :=
  (Rewriting.emb bitDef.val :
      LO.FirstOrder.ArithmeticSemiformula Nat 2)/[index, value]

inductive ArithmeticLeafKind where
  | exp
  | length
  | bit
  | notBit
  deriving DecidableEq, Repr

/-- Interpret the two fields according to the selected named predicate. -/
def ArithmeticLeafKind.instantiate
    (kind : ArithmeticLeafKind)
    (first second : ArithmeticTerm) : ArithmeticFormula :=
  match kind with
  | .exp => expInstance first second
  | .length => lengthInstance first second
  | .bit => bitInstance first second
  | .notBit => ∼bitInstance first second

/--
A successful recognition.  `first`/`second` mean value/exponent for `exp`,
size/value for `length`, and index/value for either bit case.
-/
structure ArithmeticLeafRecognition (formula : ArithmeticFormula) where
  kind : ArithmeticLeafKind
  first : ArithmeticTerm
  second : ArithmeticTerm
  first_occurs : TermOccursIn first formula
  second_occurs : TermOccursIn second formula
  sound : formula = kind.instantiate first second

theorem ArithmeticLeafRecognition.first_freeVariables_subset
    {formula : ArithmeticFormula}
    (recognition : ArithmeticLeafRecognition formula) :
    recognition.first.freeVariables ⊆ formula.freeVariables :=
  TermOccursIn_freeVariables_subset recognition.first_occurs

theorem ArithmeticLeafRecognition.second_freeVariables_subset
    {formula : ArithmeticFormula}
    (recognition : ArithmeticLeafRecognition formula) :
    recognition.second.freeVariables ⊆ formula.freeVariables :=
  TermOccursIn_freeVariables_subset recognition.second_occurs

theorem ArithmeticLeafRecognition.freeVariables_union_subset
    {formula : ArithmeticFormula}
    (recognition : ArithmeticLeafRecognition formula) :
    recognition.first.freeVariables ∪ recognition.second.freeVariables ⊆
      formula.freeVariables := by
  intro index hindex
  rcases Finset.mem_union.mp hindex with hfirst | hsecond
  · exact recognition.first_freeVariables_subset hfirst
  · exact recognition.second_freeVariables_subset hsecond

private def recognizePair
    (formula : ArithmeticFormula)
    (first second : {term // term ∈ candidateTerms formula}) :
    Option (ArithmeticLeafRecognition formula) :=
  have firstOccurs : TermOccursIn first.1 formula := by
    simpa [candidateTerms, TermOccursIn] using first.2
  have secondOccurs : TermOccursIn second.1 formula := by
    simpa [candidateTerms, TermOccursIn] using second.2
  if sound : formula = expInstance first.1 second.1 then
    some {
      kind := .exp
      first := first.1
      second := second.1
      first_occurs := firstOccurs
      second_occurs := secondOccurs
      sound := sound
    }
  else if sound : formula = lengthInstance first.1 second.1 then
    some {
      kind := .length
      first := first.1
      second := second.1
      first_occurs := firstOccurs
      second_occurs := secondOccurs
      sound := sound
    }
  else if sound : formula = bitInstance first.1 second.1 then
    some {
      kind := .bit
      first := first.1
      second := second.1
      first_occurs := firstOccurs
      second_occurs := secondOccurs
      sound := sound
    }
  else if sound : formula = ∼bitInstance first.1 second.1 then
    some {
      kind := .notBit
      first := first.1
      second := second.1
      first_occurs := firstOccurs
      second_occurs := secondOccurs
      sound := sound
    }
  else
    none

/--
Fully computational recognition by equality checking all pairs of syntax
candidates.  No proof object or proof-length parameter is an input.
-/
def recognizeArithmeticLeaf
    (formula : ArithmeticFormula) :
    Option (ArithmeticLeafRecognition formula) :=
  let candidates := candidateTerms formula
  candidates.attach.findSome? fun first =>
    candidates.attach.findSome? fun second =>
      recognizePair formula first second

private theorem traverseFinOption_some
    {alpha : Type*}
    {arity : Nat}
    (values : Fin arity -> alpha) :
    traverseFinOption arity (fun i => some (values i)) = some values := by
  induction arity with
  | zero =>
      simp only [traverseFinOption, Option.some.injEq]
      funext i
      exact Fin.elim0 i
  | succ arity ih =>
      simp only [traverseFinOption]
      rw [ih]
      apply congrArg some
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

private theorem eraseBoundVariables?_self
    (term : ArithmeticTerm) :
    eraseBoundVariables? term = some term := by
  induction term with
  | bvar index => exact Fin.elim0 index
  | fvar index => rfl
  | func function arguments ih =>
      simp only [eraseBoundVariables?]
      have harguments :
          traverseFinOption _
              (fun i => eraseBoundVariables? (arguments i)) =
            some arguments := by
        simpa only [ih] using traverseFinOption_some arguments
      rw [harguments]
      rfl

private theorem eraseBoundVariables?_bShift
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) :
    eraseBoundVariables? (Rew.bShift term) =
      eraseBoundVariables? term := by
  induction term with
  | bvar index => rfl
  | fvar index => rfl
  | func function arguments ih =>
      simp only [Rew.func, eraseBoundVariables?, Function.comp_apply, ih]

/-- A bound variable occurs in one of the atomic terms of a formula. -/
private def boundVariableOccurs
    {freeVariables : Type*}
    {binderArity : Nat}
    (index : Fin binderArity)
    (formula :
      LO.FirstOrder.ArithmeticSemiformula freeVariables binderArity) : Prop :=
  match formula with
  | .verum => False
  | .falsum => False
  | .rel _ arguments => ∃ i, index ∈ (arguments i).bv
  | .nrel _ arguments => ∃ i, index ∈ (arguments i).bv
  | .and left right =>
      boundVariableOccurs index left ∨ boundVariableOccurs index right
  | .or left right =>
      boundVariableOccurs index left ∨ boundVariableOccurs index right
  | .all body => boundVariableOccurs index.succ body
  | .exs body => boundVariableOccurs index.succ body

private def boundVariableOccursDecidable
    {freeVariables : Type*}
    {binderArity : Nat}
    (index : Fin binderArity) :
    (formula :
      LO.FirstOrder.ArithmeticSemiformula freeVariables binderArity) ->
      Decidable (boundVariableOccurs index formula)
  | .verum => isFalse id
  | .falsum => isFalse id
  | .rel _ arguments => by
      change Decidable (∃ i, index ∈ (arguments i).bv)
      exact inferInstance
  | .nrel _ arguments => by
      change Decidable (∃ i, index ∈ (arguments i).bv)
      exact inferInstance
  | .and left right => by
      letI : Decidable (boundVariableOccurs index left) :=
        boundVariableOccursDecidable index left
      letI : Decidable (boundVariableOccurs index right) :=
        boundVariableOccursDecidable index right
      change Decidable
        (boundVariableOccurs index left ∨ boundVariableOccurs index right)
      exact inferInstance
  | .or left right => by
      letI : Decidable (boundVariableOccurs index left) :=
        boundVariableOccursDecidable index left
      letI : Decidable (boundVariableOccurs index right) :=
        boundVariableOccursDecidable index right
      change Decidable
        (boundVariableOccurs index left ∨ boundVariableOccurs index right)
      exact inferInstance
  | .all body => boundVariableOccursDecidable index.succ body
  | .exs body => boundVariableOccursDecidable index.succ body

private instance boundVariableOccurs_decidable
    {freeVariables : Type*}
    {binderArity : Nat}
    (index : Fin binderArity)
    (formula :
      LO.FirstOrder.ArithmeticSemiformula freeVariables binderArity) :
    Decidable (boundVariableOccurs index formula) :=
  boundVariableOccursDecidable index formula

private theorem termSubterms_rew_of_boundVariable
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity)
    {source :
      LO.FirstOrder.ArithmeticSemiterm Nat sourceArity}
    {index : Fin sourceArity}
    {target : ArithmeticTerm}
    (hindex : index ∈ source.bv)
    (herase : eraseBoundVariables? (rewriting (.bvar index)) = some target) :
    target ∈ termSubterms (rewriting source) := by
  induction source with
  | bvar found =>
      have hfound : index = found := by simpa using hindex
      subst index
      unfold termSubterms
      exact List.mem_append_left _ (Option.mem_toList.mpr herase)
  | fvar found =>
      simp at hindex
  | func function arguments ih =>
      rw [Semiterm.bv_func] at hindex
      rcases Finset.mem_biUnion.mp hindex with
        ⟨i, _hi, hindex⟩
      simp only [Rew.func, termSubterms, List.mem_append]
      apply Or.inr
      refine List.mem_flatten.mpr
        ⟨termSubterms (rewriting (arguments i)), ?_, ?_⟩
      · exact Matrix.mem_toList_iff.mpr ⟨i, rfl⟩
      · exact ih i hindex

private theorem formulaTermSubterms_rew_of_boundVariable
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity)
    {formula :
      LO.FirstOrder.ArithmeticSemiformula Nat sourceArity}
    {index : Fin sourceArity}
    {target : ArithmeticTerm}
    (hoccurs : boundVariableOccurs index formula)
    (herase : eraseBoundVariables? (rewriting (.bvar index)) = some target) :
    target ∈ formulaTermSubterms (rewriting ▹ formula) := by
  induction formula using Semiformula.rec' generalizing targetArity with
  | hverum =>
      exact False.elim hoccurs
  | hfalsum =>
      exact False.elim hoccurs
  | hrel relation arguments =>
      simp only [boundVariableOccurs] at hoccurs
      rcases hoccurs with ⟨i, hindex⟩
      rw [Semiformula.rew_rel]
      simp only [formulaTermSubterms]
      refine List.mem_flatten.mpr
        ⟨termSubterms (rewriting (arguments i)), ?_, ?_⟩
      · exact Matrix.mem_toList_iff.mpr ⟨i, rfl⟩
      · exact termSubterms_rew_of_boundVariable
          rewriting hindex herase
  | hnrel relation arguments =>
      simp only [boundVariableOccurs] at hoccurs
      rcases hoccurs with ⟨i, hindex⟩
      rw [Semiformula.rew_nrel]
      simp only [formulaTermSubterms]
      refine List.mem_flatten.mpr
        ⟨termSubterms (rewriting (arguments i)), ?_, ?_⟩
      · exact Matrix.mem_toList_iff.mpr ⟨i, rfl⟩
      · exact termSubterms_rew_of_boundVariable
          rewriting hindex herase
  | hand left right leftIH rightIH =>
      simp only [boundVariableOccurs] at hoccurs
      change target ∈
        formulaTermSubterms (rewriting ▹ left) ++
          formulaTermSubterms (rewriting ▹ right)
      rw [List.mem_append]
      rcases hoccurs with hleft | hright
      · exact Or.inl (leftIH rewriting hleft herase)
      · exact Or.inr (rightIH rewriting hright herase)
  | hor left right leftIH rightIH =>
      simp only [boundVariableOccurs] at hoccurs
      change target ∈
        formulaTermSubterms (rewriting ▹ left) ++
          formulaTermSubterms (rewriting ▹ right)
      rw [List.mem_append]
      rcases hoccurs with hleft | hright
      · exact Or.inl (leftIH rewriting hleft herase)
      · exact Or.inr (rightIH rewriting hright herase)
  | hall body ih =>
      simp only [boundVariableOccurs] at hoccurs
      change target ∈ formulaTermSubterms (rewriting.q ▹ body)
      have herase' :
          eraseBoundVariables?
              (rewriting.q (.bvar index.succ)) = some target := by
        rw [Rew.q_bvar_succ, eraseBoundVariables?_bShift]
        exact herase
      exact ih rewriting.q hoccurs herase'
  | hexs body ih =>
      simp only [boundVariableOccurs] at hoccurs
      change target ∈ formulaTermSubterms (rewriting.q ▹ body)
      have herase' :
          eraseBoundVariables?
              (rewriting.q (.bvar index.succ)) = some target := by
        rw [Rew.q_bvar_succ, eraseBoundVariables?_bShift]
        exact herase
      exact ih rewriting.q hoccurs herase'

private theorem candidateTerms_mem_of_boundVariableOccurs
    {binderArity : Nat}
    (formula :
      LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (terms : Fin binderArity -> ArithmeticTerm)
    (index : Fin binderArity)
    (hoccurs : boundVariableOccurs index formula) :
    terms index ∈ candidateTerms (formula ⇜ terms) := by
  rw [candidateTerms, List.mem_eraseDups]
  apply formulaTermSubterms_rew_of_boundVariable
    (rewriting := Rew.subst terms) hoccurs
  simpa using eraseBoundVariables?_self (terms index)

private theorem expDef_arguments_occur :
    boundVariableOccurs (0 : Fin 2)
        (Rewriting.emb expDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2) ∧
      boundVariableOccurs (1 : Fin 2)
        (Rewriting.emb expDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2) := by
  decide

private theorem lengthDef_arguments_occur :
    boundVariableOccurs (0 : Fin 2)
        (Rewriting.emb lengthDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2) ∧
      boundVariableOccurs (1 : Fin 2)
        (Rewriting.emb lengthDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2) := by
  decide

private theorem bitDef_arguments_occur :
    boundVariableOccurs (0 : Fin 2)
        (Rewriting.emb bitDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2) ∧
      boundVariableOccurs (1 : Fin 2)
        (Rewriting.emb bitDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2) := by
  decide

private theorem expInstance_first_mem_candidateTerms
    (value exponent : ArithmeticTerm) :
    value ∈ candidateTerms (expInstance value exponent) := by
  simpa [expInstance] using
    candidateTerms_mem_of_boundVariableOccurs
      (formula :=
        (Rewriting.emb expDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2))
      (terms := ![value, exponent])
      (index := (0 : Fin 2)) expDef_arguments_occur.1

private theorem expInstance_second_mem_candidateTerms
    (value exponent : ArithmeticTerm) :
    exponent ∈ candidateTerms (expInstance value exponent) := by
  simpa [expInstance] using
    candidateTerms_mem_of_boundVariableOccurs
      (formula :=
        (Rewriting.emb expDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2))
      (terms := ![value, exponent])
      (index := (1 : Fin 2)) expDef_arguments_occur.2

private theorem lengthInstance_first_mem_candidateTerms
    (size value : ArithmeticTerm) :
    size ∈ candidateTerms (lengthInstance size value) := by
  simpa [lengthInstance] using
    candidateTerms_mem_of_boundVariableOccurs
      (formula :=
        (Rewriting.emb lengthDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2))
      (terms := ![size, value])
      (index := (0 : Fin 2)) lengthDef_arguments_occur.1

private theorem lengthInstance_second_mem_candidateTerms
    (size value : ArithmeticTerm) :
    value ∈ candidateTerms (lengthInstance size value) := by
  simpa [lengthInstance] using
    candidateTerms_mem_of_boundVariableOccurs
      (formula :=
        (Rewriting.emb lengthDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2))
      (terms := ![size, value])
      (index := (1 : Fin 2)) lengthDef_arguments_occur.2

private theorem bitInstance_first_mem_candidateTerms
    (index value : ArithmeticTerm) :
    index ∈ candidateTerms (bitInstance index value) := by
  simpa [bitInstance] using
    candidateTerms_mem_of_boundVariableOccurs
      (formula :=
        (Rewriting.emb bitDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2))
      (terms := ![index, value])
      (index := (0 : Fin 2)) bitDef_arguments_occur.1

private theorem bitInstance_second_mem_candidateTerms
    (index value : ArithmeticTerm) :
    value ∈ candidateTerms (bitInstance index value) := by
  simpa [bitInstance] using
    candidateTerms_mem_of_boundVariableOccurs
      (formula :=
        (Rewriting.emb bitDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2))
      (terms := ![index, value])
      (index := (1 : Fin 2)) bitDef_arguments_occur.2

/-- The index term really occurs in a positive bit-predicate instance. -/
theorem bitInstance_first_freeVariables_subset
    (index value : ArithmeticTerm) :
    index.freeVariables ⊆
      (bitInstance index value).freeVariables := by
  apply TermOccursIn_freeVariables_subset
  simpa [TermOccursIn, candidateTerms] using
    bitInstance_first_mem_candidateTerms index value

/-- The value term really occurs in a positive bit-predicate instance. -/
theorem bitInstance_second_freeVariables_subset
    (index value : ArithmeticTerm) :
    value.freeVariables ⊆
      (bitInstance index value).freeVariables := by
  apply TermOccursIn_freeVariables_subset
  simpa [TermOccursIn, candidateTerms] using
    bitInstance_second_mem_candidateTerms index value

theorem bitInstance_argument_freeVariables_union_subset
    (index value : ArithmeticTerm) :
    index.freeVariables ∪ value.freeVariables ⊆
      (bitInstance index value).freeVariables :=
  Finset.union_subset
    (bitInstance_first_freeVariables_subset index value)
    (bitInstance_second_freeVariables_subset index value)

private theorem formulaTermSubterms_neg
    {binderArity : Nat}
    (formula :
      LO.FirstOrder.ArithmeticSemiformula Nat binderArity) :
    formulaTermSubterms (∼formula) = formulaTermSubterms formula := by
  induction formula using Semiformula.rec' <;>
    simp [formulaTermSubterms, *]

private theorem candidateTerms_neg (formula : ArithmeticFormula) :
    candidateTerms (∼formula) = candidateTerms formula := by
  simp [candidateTerms, formulaTermSubterms_neg]

private theorem notBitInstance_first_mem_candidateTerms
    (index value : ArithmeticTerm) :
    index ∈ candidateTerms (∼bitInstance index value) := by
  rw [candidateTerms_neg]
  exact bitInstance_first_mem_candidateTerms index value

private theorem notBitInstance_second_mem_candidateTerms
    (index value : ArithmeticTerm) :
    value ∈ candidateTerms (∼bitInstance index value) := by
  rw [candidateTerms_neg]
  exact bitInstance_second_mem_candidateTerms index value

private theorem recognizeArithmeticLeaf_isSome_of_pair
    {formula : ArithmeticFormula}
    {first second : ArithmeticTerm}
    (hfirst : first ∈ candidateTerms formula)
    (hsecond : second ∈ candidateTerms formula)
    (hpair :
      (recognizePair formula ⟨first, hfirst⟩
        ⟨second, hsecond⟩).isSome = true) :
    (recognizeArithmeticLeaf formula).isSome = true := by
  unfold recognizeArithmeticLeaf
  rw [List.findSome?_isSome_iff]
  refine ⟨⟨first, hfirst⟩, List.mem_attach _ _, ?_⟩
  rw [List.findSome?_isSome_iff]
  exact ⟨⟨second, hsecond⟩, List.mem_attach _ _, hpair⟩

/-- Every exponential leaf instance is recognized without any premise. -/
theorem recognizeArithmeticLeaf_expInstance_complete
    (value exponent : ArithmeticTerm) :
    exists recognition :
        ArithmeticLeafRecognition (expInstance value exponent),
      recognizeArithmeticLeaf (expInstance value exponent) =
        some recognition := by
  apply Option.isSome_iff_exists.mp
  apply recognizeArithmeticLeaf_isSome_of_pair
    (expInstance_first_mem_candidateTerms value exponent)
    (expInstance_second_mem_candidateTerms value exponent)
  simp [recognizePair]

/-- Every binary-length leaf instance is recognized without any premise. -/
theorem recognizeArithmeticLeaf_lengthInstance_complete
    (size value : ArithmeticTerm) :
    exists recognition :
        ArithmeticLeafRecognition (lengthInstance size value),
      recognizeArithmeticLeaf (lengthInstance size value) =
        some recognition := by
  apply Option.isSome_iff_exists.mp
  apply recognizeArithmeticLeaf_isSome_of_pair
    (lengthInstance_first_mem_candidateTerms size value)
    (lengthInstance_second_mem_candidateTerms size value)
  by_cases hexp :
      lengthInstance size value = expInstance size value
  · simp [recognizePair, hexp]
  · simp [recognizePair, hexp]

/-- Every positive bit leaf instance is recognized without any premise. -/
theorem recognizeArithmeticLeaf_bitInstance_complete
    (index value : ArithmeticTerm) :
    exists recognition :
        ArithmeticLeafRecognition (bitInstance index value),
      recognizeArithmeticLeaf (bitInstance index value) =
        some recognition := by
  apply Option.isSome_iff_exists.mp
  apply recognizeArithmeticLeaf_isSome_of_pair
    (bitInstance_first_mem_candidateTerms index value)
    (bitInstance_second_mem_candidateTerms index value)
  unfold recognizePair
  split
  · rfl
  split
  · rfl
  · simp

/-- Every negated bit leaf instance is recognized without any premise. -/
theorem recognizeArithmeticLeaf_notBitInstance_complete
    (index value : ArithmeticTerm) :
    exists recognition :
        ArithmeticLeafRecognition (∼bitInstance index value),
      recognizeArithmeticLeaf (∼bitInstance index value) =
        some recognition := by
  apply Option.isSome_iff_exists.mp
  apply recognizeArithmeticLeaf_isSome_of_pair
    (notBitInstance_first_mem_candidateTerms index value)
    (notBitInstance_second_mem_candidateTerms index value)
  unfold recognizePair
  split
  · rfl
  split
  · rfl
  split
  · rfl
  · simp

theorem recognizeArithmeticLeaf_sound
    {formula : ArithmeticFormula}
    {recognition : ArithmeticLeafRecognition formula}
    (_hit : recognizeArithmeticLeaf formula = some recognition) :
    formula = recognition.kind.instantiate
      recognition.first recognition.second :=
  recognition.sound

theorem recognizeArithmeticLeaf_first_occurs
    {formula : ArithmeticFormula}
    {recognition : ArithmeticLeafRecognition formula}
    (_hit : recognizeArithmeticLeaf formula = some recognition) :
    TermOccursIn recognition.first formula :=
  recognition.first_occurs

theorem recognizeArithmeticLeaf_second_occurs
    {formula : ArithmeticFormula}
    {recognition : ArithmeticLeafRecognition formula}
    (_hit : recognizeArithmeticLeaf formula = some recognition) :
    TermOccursIn recognition.second formula :=
  recognition.second_occurs

theorem recognizeArithmeticLeaf_first_freeVariables_subset
    {formula : ArithmeticFormula}
    {recognition : ArithmeticLeafRecognition formula}
    (_hit : recognizeArithmeticLeaf formula = some recognition) :
    recognition.first.freeVariables ⊆ formula.freeVariables :=
  recognition.first_freeVariables_subset

theorem recognizeArithmeticLeaf_second_freeVariables_subset
    {formula : ArithmeticFormula}
    {recognition : ArithmeticLeafRecognition formula}
    (_hit : recognizeArithmeticLeaf formula = some recognition) :
    recognition.second.freeVariables ⊆ formula.freeVariables :=
  recognition.second_freeVariables_subset

theorem recognizeArithmeticLeaf_freeVariables_union_subset
    {formula : ArithmeticFormula}
    {recognition : ArithmeticLeafRecognition formula}
    (_hit : recognizeArithmeticLeaf formula = some recognition) :
    recognition.first.freeVariables ∪ recognition.second.freeVariables ⊆
      formula.freeVariables :=
  recognition.freeVariables_union_subset

#print axioms recognizeArithmeticLeaf_expInstance_complete
#print axioms recognizeArithmeticLeaf_lengthInstance_complete
#print axioms recognizeArithmeticLeaf_bitInstance_complete
#print axioms recognizeArithmeticLeaf_notBitInstance_complete

end FoundationCompactPAFastArithmeticLeafRecognizer
