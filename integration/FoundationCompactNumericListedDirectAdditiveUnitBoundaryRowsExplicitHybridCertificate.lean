import integration.FoundationCompactNumericListedDirectAtomicListRowRealization
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactPAExplicitHybridUniversalBranches

/-!
# Explicit hybrid certificate for additive unit boundary rows

Each universal row branch installs its two bounded cursors, their fixed-width
boundary-table entries, and the successor equation directly from the semantic
row graph.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAExplicitHybridUniversalBranches

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

/-- Lift a closed valuation term below `k` bound variables. -/
def closedShift :
    (k : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat k
  | 0, term => term
  | k + 1, term => Rew.bShift (closedShift k term)

/-- The original three-coordinate predicate closed by short binary numerals. -/
def compactAdditiveUnitBoundaryRowsClosedFormula
    (tokenCount count boundaryTable : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveUnitBoundaryRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm count,
      shortBinaryNumeralTerm boundaryTable]

/-- The row conjunction before the two bounded cursor witnesses close. -/
def compactAdditiveUnitBoundaryRowsTerminal
    (tokenCount boundaryTable : Nat) : ArithmeticSemiformula Nat 3 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 3 (shortBinaryNumeralTerm boundaryTable),
        closedShift 3 (shortBinaryNumeralTerm tokenCount),
        (#2 : ArithmeticSemiterm Nat 3),
        (#1 : ArithmeticSemiterm Nat 3)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 3 (shortBinaryNumeralTerm boundaryTable),
          closedShift 3 (shortBinaryNumeralTerm tokenCount),
          ‘#2 + 1’,
          (#0 : ArithmeticSemiterm Nat 3)]) ⋏
      “#0 = #1 + 1”)

/-- One universal branch with `left` and `right` bounded by `tokenCount`. -/
def compactAdditiveUnitBoundaryRowsBody
    (tokenCount boundaryTable : Nat) : ArithmeticSemiformula Nat 1 :=
  ((compactAdditiveUnitBoundaryRowsTerminal tokenCount boundaryTable).bexsLTSucc
      (closedShift 2 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
    (closedShift 1 (shortBinaryNumeralTerm tokenCount))

/-- The explicit bounded-universal presentation of the unit-boundary rows. -/
def compactAdditiveUnitBoundaryRowsExplicitFormula
    (tokenCount count boundaryTable : Nat) : ValuationFormula :=
  (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable).ballLT
    (shortBinaryNumeralTerm count)

/-- Exact syntax alignment with `compactAdditiveUnitBoundaryRowsDef`. -/
theorem compactAdditiveUnitBoundaryRowsClosedFormula_alignment
    (tokenCount count boundaryTable : Nat) :
    compactAdditiveUnitBoundaryRowsClosedFormula
        tokenCount count boundaryTable =
      compactAdditiveUnitBoundaryRowsExplicitFormula
        tokenCount count boundaryTable := by
  unfold compactAdditiveUnitBoundaryRowsClosedFormula
  unfold compactAdditiveUnitBoundaryRowsExplicitFormula
  unfold compactAdditiveUnitBoundaryRowsBody
  unfold compactAdditiveUnitBoundaryRowsTerminal
  unfold compactAdditiveUnitBoundaryRowsDef
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT,
    rewriting_ballLT, ← TransitiveRewriting.comp_app]
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

/-- Concrete witnesses installed by one unit-boundary row branch. -/
structure CompactAdditiveUnitBoundaryRowData
    (tokenCount boundaryTable index : Nat) where
  left : Nat
  right : Nat
  left_le : left ≤ tokenCount
  right_le : right ≤ tokenCount
  left_entry : CompactFixedWidthEntry boundaryTable tokenCount index left
  right_entry : CompactFixedWidthEntry
    boundaryTable tokenCount (index + 1) right
  successor : right = left + 1

/-- The terminal after releasing the universal index. -/
def compactAdditiveUnitBoundaryRowsBranchTerminal
    (tokenCount boundaryTable : Nat) : ArithmeticSemiformula Nat 2 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm boundaryTable),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 (&0 : ValuationTerm),
        (#1 : ArithmeticSemiterm Nat 2)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm boundaryTable),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          closedShift 2 (‘&0 + 1’ : ValuationTerm),
          (#0 : ArithmeticSemiterm Nat 2)]) ⋏
      “#0 = #1 + 1”)

private theorem substitute_closedShift
    {k : Nat} (values : Fin k -> ValuationTerm)
    (term : ValuationTerm) :
    Rew.subst values (closedShift k term) = term := by
  induction k with
  | zero =>
      have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) = Rew.id := by
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
  simp

@[simp] private theorem free_bShift2_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 1))
        (Rew.bShift (Rew.bShift (shortBinaryNumeralTerm value))) =
      Rew.bShift (shortBinaryNumeralTerm value) := by
  change (Rew.free (L := ℒₒᵣ) (n := 1))
      (closedShift 2 (shortBinaryNumeralTerm value)) =
    closedShift 1 (shortBinaryNumeralTerm value)
  exact free_closedShift_shortBinaryNumeralTerm 1 value

@[simp] private theorem free_bShift3_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 2))
        (Rew.bShift (Rew.bShift
          (Rew.bShift (shortBinaryNumeralTerm value)))) =
      Rew.bShift (Rew.bShift (shortBinaryNumeralTerm value)) := by
  change (Rew.free (L := ℒₒᵣ) (n := 2))
      (closedShift 3 (shortBinaryNumeralTerm value)) =
    closedShift 2 (shortBinaryNumeralTerm value)
  exact free_closedShift_shortBinaryNumeralTerm 2 value

@[simp] private theorem free_bvar_two_fin3 :
    (Rew.free (L := ℒₒᵣ) (n := 2))
        (#2 : ArithmeticSemiterm Nat 3) = &0 := by
  change (Rew.free (L := ℒₒᵣ) (n := 2))
      (#(Fin.last 2)) = &0
  exact Rew.free_bvar_last

@[simp] private theorem free_bvar_one_fin3 :
    (Rew.free (L := ℒₒᵣ) (n := 2))
        (#1 : ArithmeticSemiterm Nat 3) = #1 := by
  exact Rew.free_bvar_castSucc (1 : Fin 2)

private theorem compactAdditiveUnitBoundaryRowsTerminal_free_alignment
    (tokenCount boundaryTable : Nat) :
    Rewriting.free
        (compactAdditiveUnitBoundaryRowsTerminal tokenCount boundaryTable) =
      compactAdditiveUnitBoundaryRowsBranchTerminal
        tokenCount boundaryTable := by
  unfold compactAdditiveUnitBoundaryRowsTerminal
  unfold compactAdditiveUnitBoundaryRowsBranchTerminal
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
  · congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

/-- Releasing the index exposes precisely the two bounded cursor witnesses. -/
theorem compactAdditiveUnitBoundaryRowsBody_free_alignment
    (tokenCount boundaryTable : Nat) :
    Rewriting.free
        (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable) =
      FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm tokenCount) 2
        (compactAdditiveUnitBoundaryRowsBranchTerminal
          tokenCount boundaryTable) := by
  have hexplicit
      (bound : ValuationTerm) (body : ArithmeticSemiformula Nat 2) :
      FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.explicitBoundedWitnessFormula
          bound 2 body =
        (body.bexsLTSucc (Rew.bShift bound)).bexsLTSucc bound := by
    rfl
  rw [hexplicit]
  unfold compactAdditiveUnitBoundaryRowsBody
  simp [Rew.q_free, closedShift,
    compactAdditiveUnitBoundaryRowsTerminal_free_alignment]

/-- Substituting the two cursor witnesses exposes all three terminal facts. -/
theorem compactAdditiveUnitBoundaryRowsBranchTerminal_substitution_alignment
    (tokenCount boundaryTable left right : Nat) :
    (compactAdditiveUnitBoundaryRowsBranchTerminal tokenCount boundaryTable) ⇜
        ![shortBinaryNumeralTerm right, shortBinaryNumeralTerm left] =
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
          “!!(shortBinaryNumeralTerm right) =
            !!(shortBinaryNumeralTerm left) + 1”)) := by
  unfold compactAdditiveUnitBoundaryRowsBranchTerminal
  unfold compactFixedWidthEntryAtValuationFormula
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
  · congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
    · intro coordinate
      exact Empty.elim coordinate

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

noncomputable def successorEqualityCertificate
    (valuation : Nat -> Nat) (left right : Nat)
    (hsuccessor : right = left + 1) :
    HybridCertificate valuation
      “!!(shortBinaryNumeralTerm right) =
        !!(shortBinaryNumeralTerm left) + 1” := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm left) + 1’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    valuation Language.Eq.eq ![shortBinaryNumeralTerm right, rightTerm] (by
      change termValue valuation (shortBinaryNumeralTerm right) =
        termValue valuation rightTerm
      simp only [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticOne]
      exact hsuccessor)
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

noncomputable def compactAdditiveUnitBoundaryRowsBranchCertificate
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index) :
    HybridCertificate (extendValuation index zeroValuation)
      (Rewriting.free
        (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable)) := by
  let valuation := extendValuation index zeroValuation
  let values : Fin 2 -> Nat := ![data.right, data.left]
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.right,
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
        (successorEqualityCertificate valuation data.left data.right
          data.successor))
  let terminal : HybridCertificate valuation
      ((compactAdditiveUnitBoundaryRowsBranchTerminal
          tokenCount boundaryTable) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveUnitBoundaryRowsBranchTerminal_substitution_alignment
          tokenCount boundaryTable data.left data.right).symm) terminalParts
  let installed :=
    FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.buildExplicitBoundedWitnessHybridCertificate
      tokenCount
      (compactAdditiveUnitBoundaryRowsBranchTerminal
        tokenCount boundaryTable)
      values (by
        intro coordinate
        fin_cases coordinate
        · exact data.right_le
        · exact data.left_le) terminal
  exact .cast
    (compactAdditiveUnitBoundaryRowsBody_free_alignment
      tokenCount boundaryTable).symm installed

/-- The concrete `count` row branches before transporting the short-numeral
bound to its evaluated value. -/
noncomputable def compactAdditiveUnitBoundaryRowsDirectHybridBranchesAtCount
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData tokenCount boundaryTable index) :
    CheckedHybridValuationUniversalBranches zeroValuation
      (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable) count :=
  buildExplicitHybridUniversalBranches count
    (fun index hindex =>
      compactAdditiveUnitBoundaryRowsBranchCertificate
        tokenCount boundaryTable index (rows ⟨index, hindex⟩))

/-- The same branches at the evaluated short-numeral bound expected by the
bounded-universal constructor. -/
theorem compactAdditiveUnitBoundaryRowsShortNumeralBound_eq_count
    (count : Nat) :
    termValue zeroValuation (shortBinaryNumeralTerm count) = count := by
  exact termValue_shortBinaryNumeralTerm zeroValuation count

noncomputable def compactAdditiveUnitBoundaryRowsDirectHybridBranches
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData tokenCount boundaryTable index) :
    CheckedHybridValuationUniversalBranches zeroValuation
      (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable)
      (termValue zeroValuation (shortBinaryNumeralTerm count)) :=
  (compactAdditiveUnitBoundaryRowsShortNumeralBound_eq_count count).symm ▸
    compactAdditiveUnitBoundaryRowsDirectHybridBranchesAtCount
      tokenCount count boundaryTable rows

noncomputable def compactAdditiveUnitBoundaryRowsUniversalCertificate
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData tokenCount boundaryTable index) :
    HybridCertificate zeroValuation
      (compactAdditiveUnitBoundaryRowsExplicitFormula
        tokenCount count boundaryTable) := by
  let body := compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable
  let branches := compactAdditiveUnitBoundaryRowsDirectHybridBranches
    tokenCount count boundaryTable rows
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      (shortBinaryNumeralTerm count) body branches
  exact .cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm count)) body) =
        body.ballLT (shortBinaryNumeralTerm count)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

/-- Build the closed certificate from explicitly supplied row data. -/
noncomputable def
    compactAdditiveUnitBoundaryRowsFromRowDataExplicitHybridCertificate
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData tokenCount boundaryTable index) :
    HybridCertificate zeroValuation
      (compactAdditiveUnitBoundaryRowsClosedFormula
        tokenCount count boundaryTable) := by
  exact .cast
    (compactAdditiveUnitBoundaryRowsClosedFormula_alignment
      tokenCount count boundaryTable).symm
    (compactAdditiveUnitBoundaryRowsUniversalCertificate
      tokenCount count boundaryTable rows)

/-- Canonical row data extracted from the semantic unit-boundary graph. -/
noncomputable def compactAdditiveUnitBoundaryRowDataOfGraph
    (tokenCount count boundaryTable : Nat)
    (hrows : CompactAdditiveUnitBoundaryRows
      tokenCount count boundaryTable)
    (index : Fin count) :
    CompactAdditiveUnitBoundaryRowData tokenCount boundaryTable index := by
  let leftExists := hrows index index.isLt
  let left := Classical.choose leftExists
  have hleft := Classical.choose_spec leftExists
  let rightExists := hleft.2
  let right := Classical.choose rightExists
  have hright := Classical.choose_spec rightExists
  exact
    { left := left
      right := right
      left_le := hleft.1
      right_le := hright.1
      left_entry := hright.2.1
      right_entry := hright.2.2.1
      successor := hright.2.2.2 }

/-- Build every row witness directly from the semantic unit-boundary graph. -/
noncomputable def compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph
    (tokenCount count boundaryTable : Nat)
    (hrows : CompactAdditiveUnitBoundaryRows
      tokenCount count boundaryTable) :
    HybridCertificate zeroValuation
      (compactAdditiveUnitBoundaryRowsClosedFormula
        tokenCount count boundaryTable) :=
  compactAdditiveUnitBoundaryRowsFromRowDataExplicitHybridCertificate
    tokenCount count boundaryTable
    (compactAdditiveUnitBoundaryRowDataOfGraph
      tokenCount count boundaryTable hrows)

#print axioms compactAdditiveUnitBoundaryRowsClosedFormula
#print axioms compactAdditiveUnitBoundaryRowsClosedFormula_alignment
#print axioms compactAdditiveUnitBoundaryRowsFromRowDataExplicitHybridCertificate
#print axioms compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
