import integration.FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
import integration.FoundationCompactPAExplicitHybridUniversalBranches

/-!
# Explicit hybrid certificate for additive natural-list-list rows

The closed predicate is decomposed into its original bounded universal.  Every
live branch installs the three row witnesses explicitly and terminates with
the two fixed-width entries and the additive natural-list slice.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAExplicitWitnessExsClosureBuilder
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

abbrev HybridCertificate :=
  CheckedHybridValuationBoundedFormulaCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      (Rewriting.app right :
        ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
          ArithmeticSemiformula targetVariables targetArity) := by
  cases h
  rfl

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem rewriting_formulaOperator
    {sourceVariables targetVariables : Type*}
    {operatorArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (operator : Semiformula.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ operator.operator terms =
      operator.operator (rewriting ∘ terms) := by
  unfold Semiformula.Operator.operator
  exact rewriting_embeddedFormulaSubstitution
    rewriting operator.sentence terms

private theorem rewriting_termOperator
    {sourceVariables targetVariables : Type*}
    {operatorArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (operator : Semiterm.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting (operator.operator terms) =
      operator.operator (rewriting ∘ terms) := by
  unfold Semiterm.Operator.operator
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            sourceVariables operatorArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            targetVariables operatorArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting (Rew.subst terms (Rew.emb operator.term)) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            sourceVariables operatorArity)) operator.term := by
      rw [Rew.comp_app, Rew.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            targetVariables operatorArity)) operator.term := by
      rw [hcomposition]
    _ = Rew.subst (rewriting ∘ terms) (Rew.emb operator.term) := by
      rw [Rew.comp_app]

private theorem rewriting_ballLT
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1))
    (bound : ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ body.ballLT bound =
      (rewriting.q ▹ body).ballLT (rewriting bound) := by
  have hguardTerms :
      rewriting.q ∘
          ![(#0 : ArithmeticSemiterm sourceVariables (sourceArity + 1)),
            Rew.bShift bound] =
        ![(#0 : ArithmeticSemiterm targetVariables (targetArity + 1)),
          Rew.bShift (rewriting bound)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => exact Rew.q_bvar_zero rewriting
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Rew.q_comp_bShift_app rewriting bound
        | succ coordinate => exact Fin.elim0 coordinate
  unfold Semiformula.ballLT
  rw [Rewriting.smul_ball, rewriting_formulaOperator, hguardTerms]

def closedShift :
    (k : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat k
  | 0, term => term
  | k + 1, term => Rew.bShift (closedShift k term)

/-- The five inputs of the row predicate replaced by short binary numerals. -/
def compactAdditiveNatListListRowsClosedFormula
    (tokenTable width tokenCount boundaryTable count : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactAdditiveNatListListRowsWellFormedDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm boundaryTable,
      shortBinaryNumeralTerm count]

/-- The row conjunction before the three bounded existential binders close. -/
def compactAdditiveNatListListRowsTerminal
    (tokenTable width tokenCount boundaryTable : Nat) :
    ArithmeticSemiformula Nat 4 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 4 (shortBinaryNumeralTerm boundaryTable),
        closedShift 4 (shortBinaryNumeralTerm tokenCount),
        (#3 : ArithmeticSemiterm Nat 4),
        (#2 : ArithmeticSemiterm Nat 4)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 4 (shortBinaryNumeralTerm boundaryTable),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          ‘#3 + 1’,
          (#1 : ArithmeticSemiterm Nat 4)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactAdditiveNatListSliceDef.val) ⇜
        ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
          closedShift 4 (shortBinaryNumeralTerm width),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          (#2 : ArithmeticSemiterm Nat 4),
          (#0 : ArithmeticSemiterm Nat 4),
          (#1 : ArithmeticSemiterm Nat 4)]))

/-- One universal branch with `left`, `right`, and `innerCount` bounded. -/
def compactAdditiveNatListListRowsBody
    (tokenTable width tokenCount boundaryTable : Nat) :
    ArithmeticSemiformula Nat 1 :=
  ((((compactAdditiveNatListListRowsTerminal
      tokenTable width tokenCount boundaryTable).bexsLTSucc
        (closedShift 3 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (closedShift 2 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
    (closedShift 1 (shortBinaryNumeralTerm tokenCount)))

/-- The fully explicit bounded-universal presentation of the closed formula. -/
def compactAdditiveNatListListRowsExplicitFormula
    (tokenTable width tokenCount boundaryTable count : Nat) :
    ValuationFormula :=
  (compactAdditiveNatListListRowsBody
    tokenTable width tokenCount boundaryTable).ballLT
      (shortBinaryNumeralTerm count)

/-- Exact syntactic alignment with the original listed-direct row predicate. -/
theorem compactAdditiveNatListListRowsClosedFormula_alignment
    (tokenTable width tokenCount boundaryTable count : Nat) :
    compactAdditiveNatListListRowsClosedFormula
        tokenTable width tokenCount boundaryTable count =
      compactAdditiveNatListListRowsExplicitFormula
        tokenTable width tokenCount boundaryTable count := by
  unfold compactAdditiveNatListListRowsClosedFormula
  unfold compactAdditiveNatListListRowsExplicitFormula
  unfold compactAdditiveNatListListRowsBody
  unfold compactAdditiveNatListListRowsTerminal
  unfold compactAdditiveNatListListRowsWellFormedDef
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT,
    rewriting_ballLT,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  · apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    · congr 1
      congr 1
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      congr 1
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate

/-- Concrete data installed in one row branch. -/
structure CompactAdditiveNatListListRowData
    (tokenTable width tokenCount boundaryTable index : Nat) where
  left : Nat
  right : Nat
  innerCount : Nat
  left_le : left ≤ tokenCount
  right_le : right ≤ tokenCount
  innerCount_le : innerCount ≤ tokenCount
  left_entry : CompactFixedWidthEntry
    boundaryTable tokenCount index left
  right_entry : CompactFixedWidthEntry
    boundaryTable tokenCount (index + 1) right
  slice : CompactAdditiveNatListSlice
    tokenTable width tokenCount left innerCount right

/-- The header cursor in an additive natural-list slice is deterministic. -/
theorem compactAdditiveNatListSlice_explicitData
    {tokenTable width tokenCount start count finish : Nat}
    (hslice : CompactAdditiveNatListSlice
      tokenTable width tokenCount start count finish) :
    start + 1 ≤ tokenCount ∧
      CompactAdditiveListHeader
        tokenTable width tokenCount start count (start + 1) ∧
      finish = (start + 1) + count := by
  rcases hslice with ⟨bodyStart, hbodyStart, hheader, hfinish⟩
  have hbodyStartEq : bodyStart = start + 1 := hheader.1.2.1
  subst bodyStart
  exact ⟨hbodyStart, hheader, hfinish⟩

/-- The terminal after the universal index is exposed as free variable zero. -/
def compactAdditiveNatListListRowsBranchTerminal
    (tokenTable width tokenCount boundaryTable : Nat) :
    ArithmeticSemiformula Nat 3 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 3 (shortBinaryNumeralTerm boundaryTable),
        closedShift 3 (shortBinaryNumeralTerm tokenCount),
        closedShift 3 (&0 : ValuationTerm),
        (#2 : ArithmeticSemiterm Nat 3)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 3 (shortBinaryNumeralTerm boundaryTable),
          closedShift 3 (shortBinaryNumeralTerm tokenCount),
          closedShift 3 (‘&0 + 1’ : ValuationTerm),
          (#1 : ArithmeticSemiterm Nat 3)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactAdditiveNatListSliceDef.val) ⇜
        ![closedShift 3 (shortBinaryNumeralTerm tokenTable),
          closedShift 3 (shortBinaryNumeralTerm width),
          closedShift 3 (shortBinaryNumeralTerm tokenCount),
          (#2 : ArithmeticSemiterm Nat 3),
          (#0 : ArithmeticSemiterm Nat 3),
          (#1 : ArithmeticSemiterm Nat 3)]))

/-- Close an arbitrary terminal by a vector of bounded existential witnesses. -/
def explicitBoundedWitnessFormula (bound : ValuationTerm) :
    (k : Nat) -> ArithmeticSemiformula Nat k -> ValuationFormula
  | 0, body => body
  | k + 1, body =>
      explicitBoundedWitnessFormula bound k
        (body.bexsLTSucc (closedShift k bound))

@[simp] private theorem rewriting_bexsLTSucc
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (bound : ArithmeticSemiterm sourceVariables sourceArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1)) :
    rewriting ▹ body.bexsLTSucc bound =
      (rewriting.q ▹ body).bexsLTSucc (rewriting bound) := by
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT]

theorem substitute_closedShift
    {k : Nat} (values : Fin k -> ValuationTerm)
    (term : ValuationTerm) :
    Rew.subst values (closedShift k term) = term := by
  induction k with
  | zero =>
      have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) =
          Rew.id := by
        apply Rew.ext
        · intro index
          exact Fin.elim0 index
        · intro freeIndex
          rfl
      rw [hrew]
      exact Rew.id_app term
  | succ k inductionHypothesis =>
      have hrew :
          (Rew.subst values).comp Rew.bShift =
            Rew.subst (fun index : Fin k => values index.succ) := by
        apply Rew.ext
        · intro index
          simp [Rew.comp_app]
        · intro freeIndex
          simp [Rew.comp_app]
      calc
        Rew.subst values (closedShift (k + 1) term) =
            ((Rew.subst values).comp Rew.bShift)
              (closedShift k term) := by
                simp [closedShift, Rew.comp_app]
        _ = Rew.subst (fun index : Fin k => values index.succ)
              (closedShift k term) := by rw [hrew]
        _ = term := inductionHypothesis _

theorem shortBinarySubstitution_bexsLTSucc_tail
    {k : Nat}
    (bound : ValuationTerm)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat) :
    (body.bexsLTSucc (closedShift k bound)) ⇜
        (fun index : Fin k =>
          shortBinaryNumeralTerm (values index.succ)) =
      (explicitWitnessBodyAfterTail body values).bexsLTSucc bound := by
  unfold Semiformula.bexsLTSucc
  unfold Semiformula.bexsLT
  have hbound :
      Rew.subst (fun index : Fin k =>
          shortBinaryNumeralTerm (values index.succ))
          (closedShift k bound) = bound := by
    exact substitute_closedShift _ bound
  simp [explicitWitnessBodyAfterTail, hbound]

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

noncomputable def boundedWitnessGuardCertificate
    (valuation : Nat -> Nat) (value bound : Nat) (hvalue : value ≤ bound) :
    HybridCertificate valuation
      “!!(shortBinaryNumeralTerm value) <
        !!(shortBinaryNumeralTerm bound) + 1” := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bound) + 1’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    valuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm value, rightTerm] (by
      change termValue valuation (shortBinaryNumeralTerm value) <
        termValue valuation rightTerm
      simp only [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticOne]
      omega)
  exact .cast (Semiformula.Operator.lt_def _ _).symm direct

/-- Install the lowest bounded witness and expose the tail formula used by the
remaining witness coordinates. -/
noncomputable def advanceExplicitBoundedWitnessHybridTerminal
    {valuation : Nat -> Nat} {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat)
    (hbound : values 0 <= bound)
    (terminal : HybridCertificate valuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))) :
    HybridCertificate valuation
      ((body.bexsLTSucc
          (closedShift k (shortBinaryNumeralTerm bound))) ⇜
        (fun index : Fin k =>
          shortBinaryNumeralTerm (values index.succ))) := by
  let witnessBody := explicitWitnessBodyAfterTail body values
  let guard : ValuationFormula :=
    “!!(shortBinaryNumeralTerm (values 0)) <
      !!(shortBinaryNumeralTerm bound) + 1”
  let guardCertificate :=
    boundedWitnessGuardCertificate valuation (values 0) bound hbound
  have hbodySubstitution :
      witnessBody/[shortBinaryNumeralTerm (values 0)] =
        body ⇜ fun index => shortBinaryNumeralTerm (values index) :=
    explicitWitnessBodyAfterTail_subst_head body values
  let installed : HybridCertificate valuation
      (witnessBody/[shortBinaryNumeralTerm (values 0)]) :=
    .cast hbodySubstitution.symm terminal
  let guarded :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      guardCertificate installed
  let inner : HybridCertificate valuation
      (witnessBody.bexsLTSucc (shortBinaryNumeralTerm bound)) := by
    let boundedMatrix : ArithmeticSemiformula Nat 1 :=
      Semiformula.Operator.LT.lt.operator
          ![(#0 : ArithmeticSemiterm Nat 1),
            Rew.bShift
              ‘!!(shortBinaryNumeralTerm bound) + 1’] ⋏
        witnessBody
    let direct : HybridCertificate valuation (∃⁰ boundedMatrix) :=
      .existsWitness boundedMatrix (values 0) (.cast (by
        simp [boundedMatrix]) guarded)
    exact .cast (by rfl) direct
  exact .cast
    (shortBinarySubstitution_bexsLTSucc_tail
      (shortBinaryNumeralTerm bound) body values).symm inner

/-- Install every coordinate of a bounded witness vector explicitly. -/
noncomputable def buildExplicitBoundedWitnessHybridCertificate :
    {valuation : Nat -> Nat} -> {k : Nat} ->
    (bound : Nat) ->
    (body : ArithmeticSemiformula Nat k) ->
    (values : Fin k -> Nat) ->
    (∀ index, values index ≤ bound) ->
    HybridCertificate valuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)) ->
    HybridCertificate valuation
      (explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm bound) k body)
  | valuation, 0, bound, body, values, hbounds, terminal => by
      exact
        @CheckedHybridValuationBoundedFormulaCertificate.cast valuation
          (body ⇜ fun index => shortBinaryNumeralTerm (values index)) body
          (by simp) terminal
  | valuation, k + 1, bound, body, values, hbounds, terminal => by
      let tailValues : Fin k -> Nat := fun index => values index.succ
      let recursiveTerminal : HybridCertificate valuation
          ((body.bexsLTSucc
              (closedShift k (shortBinaryNumeralTerm bound))) ⇜
            (fun index : Fin k =>
              shortBinaryNumeralTerm (tailValues index))) :=
        advanceExplicitBoundedWitnessHybridTerminal
          bound body values (hbounds 0) terminal
      exact buildExplicitBoundedWitnessHybridCertificate bound
          (body.bexsLTSucc
            (closedShift k (shortBinaryNumeralTerm bound)))
          tailValues (fun index => hbounds index.succ) recursiveTerminal

private def closedShiftRewriting :
    (k : Nat) -> Rew ℒₒᵣ Nat 0 Nat k
  | 0 => Rew.id
  | k + 1 => Rew.bShift.comp (closedShiftRewriting k)

@[simp] private theorem closedShiftRewriting_apply
    (k : Nat) (term : ValuationTerm) :
    closedShiftRewriting k term = closedShift k term := by
  induction k with
  | zero => exact Rew.id_app term
  | succ k inductionHypothesis =>
      simp [closedShiftRewriting, closedShift, Rew.comp_app,
        inductionHypothesis]

@[simp] private theorem free_closedShift_shortBinaryNumeralTerm
    (k value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := k))
        (closedShift (k + 1) (shortBinaryNumeralTerm value)) =
      closedShift k (shortBinaryNumeralTerm value) := by
  let leftRewriting : Rew ℒₒᵣ Nat 0 Nat k :=
    (Rew.free (L := ℒₒᵣ) (n := k)).comp
      (closedShiftRewriting (k + 1))
  let rightRewriting : Rew ℒₒᵣ Nat 0 Nat k :=
    closedShiftRewriting k
  have h := Semiterm.rew_eq_of_funEqOn
    leftRewriting rightRewriting (shortBinaryNumeralTerm value)
    (fun coordinate => Fin.elim0 coordinate)
    (fun coordinate hcoordinate => by
      have : coordinate ∈
          (shortBinaryNumeralTerm value).freeVariables := hcoordinate
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at this
      simp at this)
  simpa [leftRewriting, rightRewriting, Rew.comp_app] using h

@[simp] private theorem shift_shortBinaryNumeralTerm (value : Nat) :
    Rew.shift (shortBinaryNumeralTerm value) =
      shortBinaryNumeralTerm value := by
  simpa [closedShift, free_bShift_term] using
    (free_closedShift_shortBinaryNumeralTerm 0 value)

@[simp] private theorem free_bShift2_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 1))
        (Rew.bShift (Rew.bShift (shortBinaryNumeralTerm value))) =
      Rew.bShift (shortBinaryNumeralTerm value) := by
  simpa [closedShift] using
    (free_closedShift_shortBinaryNumeralTerm 1 value)

@[simp] private theorem free_bShift3_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 2))
        (Rew.bShift (Rew.bShift
          (Rew.bShift (shortBinaryNumeralTerm value)))) =
      Rew.bShift (Rew.bShift (shortBinaryNumeralTerm value)) := by
  simpa [closedShift] using
    (free_closedShift_shortBinaryNumeralTerm 2 value)

@[simp] private theorem free_bShift4_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 3))
        (Rew.bShift (Rew.bShift (Rew.bShift
          (Rew.bShift (shortBinaryNumeralTerm value))))) =
      Rew.bShift (Rew.bShift
        (Rew.bShift (shortBinaryNumeralTerm value))) := by
  simpa [closedShift] using
    (free_closedShift_shortBinaryNumeralTerm 3 value)

@[simp] private theorem free_bvar_three_fin4 :
    (Rew.free (L := ℒₒᵣ) (n := 3))
        (#3 : ArithmeticSemiterm Nat 4) = &0 := by
  change (Rew.free (L := ℒₒᵣ) (n := 3))
      (#(Fin.last 3)) = &0
  exact Rew.free_bvar_last

@[simp] private theorem free_bvar_two_fin4 :
    (Rew.free (L := ℒₒᵣ) (n := 3))
        (#2 : ArithmeticSemiterm Nat 4) = #2 := by
  exact Rew.free_bvar_castSucc (2 : Fin 3)

@[simp] private theorem free_bvar_one_fin4 :
    (Rew.free (L := ℒₒᵣ) (n := 3))
        (#1 : ArithmeticSemiterm Nat 4) = #1 := by
  exact Rew.free_bvar_castSucc (1 : Fin 3)

private theorem compactAdditiveNatListListRowsTerminal_free_alignment
    (tokenTable width tokenCount boundaryTable : Nat) :
    Rewriting.free
        (compactAdditiveNatListListRowsTerminal
          tokenTable width tokenCount boundaryTable) =
      compactAdditiveNatListListRowsBranchTerminal
        tokenTable width tokenCount boundaryTable := by
  unfold compactAdditiveNatListListRowsTerminal
  unfold compactAdditiveNatListListRowsBranchTerminal
  simp [closedShift, ← TransitiveRewriting.comp_app]
  constructor
  · congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · constructor
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate

/-- Releasing the universal index exposes exactly three bounded witnesses. -/
theorem compactAdditiveNatListListRowsBody_free_alignment
    (tokenTable width tokenCount boundaryTable : Nat) :
    Rewriting.free
        (compactAdditiveNatListListRowsBody
          tokenTable width tokenCount boundaryTable) =
      explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm tokenCount) 3
        (compactAdditiveNatListListRowsBranchTerminal
          tokenTable width tokenCount boundaryTable) := by
  unfold compactAdditiveNatListListRowsBody
  simp [explicitBoundedWitnessFormula,
    Rew.q_free, closedShift, shift_shortBinaryNumeralTerm,
    free_bShift2_shortBinaryNumeralTerm,
    free_bShift3_shortBinaryNumeralTerm,
    compactAdditiveNatListListRowsTerminal_free_alignment]

/-- Substituting one row vector yields precisely the three row conjuncts. -/
theorem compactAdditiveNatListListRowsBranchTerminal_substitution_alignment
    (tokenTable width tokenCount boundaryTable left right innerCount : Nat) :
    (compactAdditiveNatListListRowsBranchTerminal
        tokenTable width tokenCount boundaryTable) ⇜
        ![shortBinaryNumeralTerm innerCount,
          shortBinaryNumeralTerm right,
          shortBinaryNumeralTerm left] =
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (&0 : ValuationTerm)
          (shortBinaryNumeralTerm left) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (‘&0 + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm right) ⋏
          compactAdditiveNatListSliceClosedFormula
            tokenTable width tokenCount left innerCount right)) := by
  unfold compactAdditiveNatListListRowsBranchTerminal
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactAdditiveNatListSliceClosedFormula
  simp [← TransitiveRewriting.comp_app]
  constructor
  · congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
    · intro coordinate
      exact Empty.elim coordinate
  · constructor
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
      · intro coordinate
        exact Empty.elim coordinate

private theorem termValue_eq_of_agreeOn_freeVariables
    (source target : Nat -> Nat) (term : ValuationTerm)
    (hagrees : ∀ index, index ∈ term.freeVariables ->
      source index = target index) :
    termValue source term = termValue target term := by
  unfold termValue
  exact LO.FirstOrder.Semiterm.val_eq_of_funEqOn term hagrees

private theorem formulaValue_iff_of_agreeOn_freeVariables
    (source target : Nat -> Nat) (formula : ValuationFormula)
    (hagrees : ∀ index, index ∈ formula.freeVariables ->
      source index = target index) :
    formulaValue source formula ↔ formulaValue target formula := by
  unfold formulaValue
  exact LO.FirstOrder.Semiformula.eval_iff_of_funEqOn formula hagrees

mutual

  /-- Rebuild a certificate under a valuation agreeing on its free variables. -/
  private noncomputable def revalueHybridCertificate :
      {source : Nat -> Nat} -> {formula : ValuationFormula} ->
      HybridCertificate source formula ->
      (target : Nat -> Nat) ->
      (∀ index, index ∈ formula.freeVariables ->
        source index = target index) ->
      HybridCertificate target formula
    | _, _, .verum _, target, _ => .verum target
    | _, _, .positiveAtomic source relationSymbol args htruth,
        target, hagrees =>
      .positiveAtomic target relationSymbol args
        ((formulaValue_iff_of_agreeOn_freeVariables source target
          (.rel relationSymbol args) hagrees).mp htruth)
    | _, _, .negativeAtomic source relationSymbol args htruth,
        target, hagrees =>
      .negativeAtomic target relationSymbol args
        ((formulaValue_iff_of_agreeOn_freeVariables source target
          (.nrel relationSymbol args) hagrees).mp htruth)
    | _, _, .exponential source valueTerm exponentTerm hvalue,
        target, hagrees => by
      have hvalueTerm : termValue source valueTerm =
          termValue target valueTerm :=
        termValue_eq_of_agreeOn_freeVariables source target valueTerm
          (fun index hindex => hagrees index (by
            rw [exponentialAtValuationFormula_freeVariables]
            exact Finset.mem_union_left _ hindex))
      have hexponentTerm : termValue source exponentTerm =
          termValue target exponentTerm :=
        termValue_eq_of_agreeOn_freeVariables source target exponentTerm
          (fun index hindex => hagrees index (by
            rw [exponentialAtValuationFormula_freeVariables]
            exact Finset.mem_union_right _ hindex))
      exact .exponential target valueTerm exponentTerm (by
        rw [← hvalueTerm, ← hexponentTerm]
        exact hvalue)
    | _, _, .binaryLength source sizeTerm valueTerm hsize,
        target, hagrees => by
      have hsizeTerm : termValue source sizeTerm =
          termValue target sizeTerm :=
        termValue_eq_of_agreeOn_freeVariables source target sizeTerm
          (fun index hindex => hagrees index (by
            rw [binaryLengthAtValuationFormula_freeVariables]
            exact Finset.mem_union_left _ hindex))
      have hvalueTerm : termValue source valueTerm =
          termValue target valueTerm :=
        termValue_eq_of_agreeOn_freeVariables source target valueTerm
          (fun index hindex => hagrees index (by
            rw [binaryLengthAtValuationFormula_freeVariables]
            exact Finset.mem_union_right _ hindex))
      exact .binaryLength target sizeTerm valueTerm (by
        rw [← hsizeTerm, ← hvalueTerm]
        exact hsize)
    | _, _, .binaryBit expected source indexTerm valueTerm hbit hvariables,
        target, hagrees => by
      have hindexTerm : termValue source indexTerm =
          termValue target indexTerm :=
        termValue_eq_of_agreeOn_freeVariables source target indexTerm
          (fun index hindex => hagrees index
            (hvariables (Finset.mem_union_left _ hindex)))
      have hvalueTerm : termValue source valueTerm =
          termValue target valueTerm :=
        termValue_eq_of_agreeOn_freeVariables source target valueTerm
          (fun index hindex => hagrees index
            (hvariables (Finset.mem_union_right _ hindex)))
      exact .binaryBit expected target indexTerm valueTerm (by
        rw [← hindexTerm, ← hvalueTerm]
        exact hbit) hvariables
    | _, _, .conjunction leftCertificate rightCertificate,
        target, hagrees =>
      .conjunction
        (revalueHybridCertificate leftCertificate target
          (fun index hindex => hagrees index (by simp [hindex])))
        (revalueHybridCertificate rightCertificate target
          (fun index hindex => hagrees index (by simp [hindex])))
    | _, _, .disjunctionLeft leftCertificate, target, hagrees =>
      .disjunctionLeft
        (revalueHybridCertificate leftCertificate target
          (fun index hindex => hagrees index (by simp [hindex])))
    | _, _, .disjunctionRight rightCertificate, target, hagrees =>
      .disjunctionRight
        (revalueHybridCertificate rightCertificate target
          (fun index hindex => hagrees index (by simp [hindex])))
    | _, _, .existsWitness body witness bodyCertificate,
        target, hagrees =>
      .existsWitness body witness
        (revalueHybridCertificate bodyCertificate target
          (fun index hindex => hagrees index (by
            simpa using
              shortBinarySubstitution_freeVariables_subset
                body witness hindex)))
    | source, _, .boundedUniversal boundSource body branches,
        target, hagrees => by
      have hbody : ∀ index, index ∈ body.freeVariables ->
          source index = target index := fun index hindex =>
        hagrees index
          (body_freeVariables_subset_universal boundSource body hindex)
      have hboundValue : termValue source boundSource =
          termValue target boundSource :=
        termValue_eq_of_agreeOn_freeVariables source target boundSource
          (fun index hindex => hagrees index
            (boundSource_freeVariables_subset_universal
              boundSource body hindex))
      exact .boundedUniversal boundSource body
        (hboundValue ▸ revalueHybridBranches branches target hbody)
    | _, _, .cast rfl sourceCertificate, target, hagrees =>
      revalueHybridCertificate sourceCertificate target hagrees

  /-- Transport all explicit branches while retaining each branch head. -/
  private noncomputable def revalueHybridBranches :
      {source : Nat -> Nat} ->
      {body : ArithmeticSemiformula Nat 1} ->
      {bound : Nat} ->
      CheckedHybridValuationUniversalBranches source body bound ->
      (target : Nat -> Nat) ->
      (∀ index, index ∈ body.freeVariables ->
        source index = target index) ->
      CheckedHybridValuationUniversalBranches target body bound
    | _, _, _, .nil _ _, target, _ => .nil target _
    | _, _, _, .snoc initial last, target, hagrees => by
      let initial' := revalueHybridBranches initial target hagrees
      let last' := revalueHybridCertificate last
        (extendValuation _ target) (fun index hindex => by
          have hsubset := freeFormula_freeVariables_subset _ hindex
          rcases Finset.mem_insert.mp hsubset with hzero | hshifted
          · subst index
            rfl
          · rcases Finset.mem_image.mp hshifted with
              ⟨sourceIndex, hsourceIndex, rfl⟩
            simp [hagrees sourceIndex hsourceIndex])
      exact .snoc initial' last'

end

/-- Rebuild a closed hybrid certificate under any target valuation. -/
noncomputable def revalueClosedHybridCertificate
    {source : Nat -> Nat} {formula : ValuationFormula}
    (certificate : HybridCertificate source formula)
    (hclosed : formula.freeVariables = ∅)
    (target : Nat -> Nat) :
    HybridCertificate target formula :=
  revalueHybridCertificate certificate target (fun index hindex => by
    rw [hclosed] at hindex
    simp at hindex)

private noncomputable def
    compactAdditiveNatListSliceAtValuationExplicitHybridCertificate
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount start count finish : Nat)
    (hslice : CompactAdditiveNatListSlice
      tokenTable width tokenCount start count finish) :
    HybridCertificate valuation
      (compactAdditiveNatListSliceClosedFormula
        tokenTable width tokenCount start count finish) := by
  have hdata := compactAdditiveNatListSlice_explicitData hslice
  let atZero :=
    FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.compactAdditiveNatListSliceExplicitHybridCertificate
      tokenTable width tokenCount start count finish (start + 1)
      hdata.1 hdata.2.1 hdata.2.2
  exact revalueClosedHybridCertificate atZero (by
    unfold compactAdditiveNatListSliceClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      exact shortBinaryNumeralTerm_freeVariables_eq_empty _) valuation

private noncomputable def compactAdditiveNatListListRowBranchCertificate
    (tokenTable width tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveNatListListRowData
      tokenTable width tokenCount boundaryTable index) :
    HybridCertificate (extendValuation index zeroValuation)
      (Rewriting.free
        (compactAdditiveNatListListRowsBody
          tokenTable width tokenCount boundaryTable)) := by
  let valuation := extendValuation index zeroValuation
  let values : Fin 3 -> Nat :=
    ![data.innerCount, data.right, data.left]
  have hvalueTerms :
      (fun coordinate : Fin 3 =>
        shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.innerCount,
          shortBinaryNumeralTerm data.right,
          shortBinaryNumeralTerm data.left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        valuation
        (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount)
        (&0 : ValuationTerm)
        (shortBinaryNumeralTerm data.left) (by
          simpa [valuation, zeroValuation,
            termValue_shortBinaryNumeralTerm,
            FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
            using data.left_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          valuation
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (‘&0 + 1’ : ValuationTerm)
          (shortBinaryNumeralTerm data.right) (by
            simpa [valuation, zeroValuation,
              termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne,
              FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
              using data.right_entry))
        (compactAdditiveNatListSliceAtValuationExplicitHybridCertificate
          valuation tokenTable width tokenCount data.left data.innerCount
            data.right data.slice))
  let terminal : HybridCertificate valuation
      ((compactAdditiveNatListListRowsBranchTerminal
          tokenTable width tokenCount boundaryTable) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListListRowsBranchTerminal_substitution_alignment
          tokenTable width tokenCount boundaryTable data.left data.right
            data.innerCount).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate
    tokenCount
    (compactAdditiveNatListListRowsBranchTerminal
      tokenTable width tokenCount boundaryTable)
    values (by
      intro coordinate
      fin_cases coordinate
      · exact data.innerCount_le
      · exact data.right_le
      · exact data.left_le) terminal
  exact .cast
    (compactAdditiveNatListListRowsBody_free_alignment
      tokenTable width tokenCount boundaryTable).symm installed

private noncomputable def compactAdditiveNatListListRowsUniversalCertificate
    (tokenTable width tokenCount boundaryTable count : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveNatListListRowData
        tokenTable width tokenCount boundaryTable index) :
    HybridCertificate zeroValuation
      (compactAdditiveNatListListRowsExplicitFormula
        tokenTable width tokenCount boundaryTable count) := by
  let body := compactAdditiveNatListListRowsBody
    tokenTable width tokenCount boundaryTable
  let branches := buildExplicitHybridUniversalBranches count
    (fun index hindex =>
      compactAdditiveNatListListRowBranchCertificate
        tokenTable width tokenCount boundaryTable index
          (rows ⟨index, hindex⟩))
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      (shortBinaryNumeralTerm count) body (by
        simpa [termValue_shortBinaryNumeralTerm] using branches)
  exact .cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm count)) body) =
        body.ballLT (shortBinaryNumeralTerm count)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

/-- Explicit-row-data constructor for an arbitrary row count. -/
noncomputable def
    compactAdditiveNatListListRowsFromRowDataExplicitHybridCertificate
    (tokenTable width tokenCount boundaryTable count : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveNatListListRowData
        tokenTable width tokenCount boundaryTable index) :
    HybridCertificate zeroValuation
      (compactAdditiveNatListListRowsClosedFormula
        tokenTable width tokenCount boundaryTable count) := by
  exact .cast
    (compactAdditiveNatListListRowsClosedFormula_alignment
      tokenTable width tokenCount boundaryTable count).symm
    (compactAdditiveNatListListRowsUniversalCertificate
      tokenTable width tokenCount boundaryTable count rows)

/-- Select exactly the three concrete witnesses supplied by one `hrows` row. -/
noncomputable def compactAdditiveNatListListRowDataOfWellFormed
    (tokenTable width tokenCount boundaryTable count : Nat)
    (hrows : CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount boundaryTable count)
    (index : Fin count) :
    CompactAdditiveNatListListRowData
      tokenTable width tokenCount boundaryTable index := by
  let leftExists := hrows index index.isLt
  let left := Classical.choose leftExists
  have hleft := Classical.choose_spec leftExists
  let rightExists := hleft.2
  let right := Classical.choose rightExists
  have hright := Classical.choose_spec rightExists
  let innerCountExists := hright.2
  let innerCount := Classical.choose innerCountExists
  have hinnerCount := Classical.choose_spec innerCountExists
  exact
    { left := left
      right := right
      innerCount := innerCount
      left_le := hleft.1
      right_le := hright.1
      innerCount_le := hinnerCount.1
      left_entry := hinnerCount.2.1
      right_entry := hinnerCount.2.2.1
      slice := hinnerCount.2.2.2 }

/-- Public arbitrary-count constructor from the semantic row specification. -/
noncomputable def compactAdditiveNatListListRowsExplicitHybridCertificate
    (tokenTable width tokenCount boundaryTable count : Nat)
    (hrows : CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount boundaryTable count) :
    HybridCertificate zeroValuation
      (compactAdditiveNatListListRowsClosedFormula
        tokenTable width tokenCount boundaryTable count) :=
  compactAdditiveNatListListRowsFromRowDataExplicitHybridCertificate
    tokenTable width tokenCount boundaryTable count
      (compactAdditiveNatListListRowDataOfWellFormed
        tokenTable width tokenCount boundaryTable count hrows)

#print axioms compactAdditiveNatListListRowsClosedFormula_alignment
#print axioms buildExplicitBoundedWitnessHybridCertificate
#print axioms compactAdditiveNatListListRowsBody_free_alignment
#print axioms
  compactAdditiveNatListListRowsBranchTerminal_substitution_alignment
#print axioms revalueClosedHybridCertificate
#print axioms
  compactAdditiveNatListListRowsFromRowDataExplicitHybridCertificate
#print axioms compactAdditiveNatListListRowsExplicitHybridCertificate

end FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
