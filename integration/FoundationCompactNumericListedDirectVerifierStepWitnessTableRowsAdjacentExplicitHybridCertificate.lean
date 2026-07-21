import integration.FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge
import integration.FoundationCompactNumericListedDirectCrossTableSliceExplicitHybridCertificate
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
import integration.FoundationCompactPAExplicitHybridUniversalBranches
import integration.FoundationCompactPAExplicitWitnessExsClosureBuilder
import integration.FoundationCompactNumericListedDirectVerifierBoundedTraceSelection

/-!
# Explicit hybrid certificate for adjacent verifier witness-table rows

Each row branch keeps the original arithmetic entry-index terms.  Its ten
decoded column values are installed as explicit existential witnesses, and the
terminal matrix is assembled from ten fixed-width-entry certificates and one
cross-table slice certificate.  The outer row bound is closed by an explicit
finite branch vector.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierStepWitnessTableRowsAdjacentExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectCrossTableSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierStepWitnessTableAdjacencyFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge
open FoundationCompactNumericListedDirectVerifierBoundedTraceSelection
open FoundationCompactNumericListedDirectBoundedVectorQuantifier
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAExplicitWitnessExsClosureBuilder
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

/-- The valuation below the row-count universal. -/
def zeroValuation : Nat -> Nat := fun _ => 0

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ :
        LO.FirstOrder.ArithmeticSemiterm Variable boundArity) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Variable boundArity) :
    (‘!!left * !!right’ :
        LO.FirstOrder.ArithmeticSemiterm Variable boundArity) =
      LO.FirstOrder.Semiterm.func Language.Mul.mul ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Mul.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left + !!right’) =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left * !!right’) =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

/-- One adjacent-row instance at four original valuation terms. -/
def compactNumericVerifierStepWitnessTableAdjacentRowAtValuationFormula
    (tableWidthTerm tableTerm valueBoundTerm rowIndexTerm : ValuationTerm) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStepWitnessTableAdjacentRowDef.val) ⇜
    ![tableWidthTerm, tableTerm, valueBoundTerm, rowIndexTerm]

/-- The original four-coordinate rows-adjacent predicate, retaining the
caller's row-count term. -/
def compactNumericVerifierStepWitnessTableRowsAdjacentAtValuationFormula
    (tableWidth table valueBound : Nat) (rowCountTerm : ValuationTerm) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStepWitnessTableRowsAdjacentDef.val) ⇜
    ![shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm table,
      rowCountTerm,
      shortBinaryNumeralTerm valueBound]

/- The ten definitions below intentionally retain the source formula's
arithmetic syntax instead of replacing indices by computed numerals. -/

def adjacentSourceTableIndexTerm (rowIndexTerm : ValuationTerm) :
    ValuationTerm :=
  ‘!!rowIndexTerm * 429 + 0’

def adjacentSourceWidthIndexTerm (rowIndexTerm : ValuationTerm) :
    ValuationTerm :=
  ‘!!rowIndexTerm * 429 + 1’

def adjacentSourceTokenCountIndexTerm (rowIndexTerm : ValuationTerm) :
    ValuationTerm :=
  ‘!!rowIndexTerm * 429 + 2’

def adjacentSourceStartIndexTerm (rowIndexTerm : ValuationTerm) :
    ValuationTerm :=
  ‘!!rowIndexTerm * 429 + 24’

def adjacentSourceFinishIndexTerm (rowIndexTerm : ValuationTerm) :
    ValuationTerm :=
  ‘!!rowIndexTerm * 429 + 25’

def adjacentTargetTableIndexTerm (rowIndexTerm : ValuationTerm) :
    ValuationTerm :=
  ‘(!!rowIndexTerm + 1) * 429 + 0’

def adjacentTargetWidthIndexTerm (rowIndexTerm : ValuationTerm) :
    ValuationTerm :=
  ‘(!!rowIndexTerm + 1) * 429 + 1’

def adjacentTargetTokenCountIndexTerm (rowIndexTerm : ValuationTerm) :
    ValuationTerm :=
  ‘(!!rowIndexTerm + 1) * 429 + 2’

def adjacentTargetStartIndexTerm (rowIndexTerm : ValuationTerm) :
    ValuationTerm :=
  ‘(!!rowIndexTerm + 1) * 429 + 3’

def adjacentTargetFinishIndexTerm (rowIndexTerm : ValuationTerm) :
    ValuationTerm :=
  ‘(!!rowIndexTerm + 1) * 429 + 4’

/-! ## Strict source-formula normalization -/

private def adjacentBoundedVectorCore :
    {arity : Nat} -> (k : Nat) ->
      LO.FirstOrder.ArithmeticSemiformula Empty arity ->
      LO.FirstOrder.ArithmeticSemiformula Empty (arity + k)
  | _, 0, formula => formula
  | arity, k + 1, .exs (.and _ tail) =>
      cast (congrArg (LO.FirstOrder.ArithmeticSemiformula Empty) (by omega))
        (adjacentBoundedVectorCore k tail)
  | _, _ + 1, _ => ⊤

private def adjacentRowRawCore :
    LO.FirstOrder.ArithmeticSemiformula Empty (4 + 10) :=
  adjacentBoundedVectorCore 10
    compactNumericVerifierStepWitnessTableAdjacentRowDef.val

private def adjacentRowDirectRawCore :
    LO.FirstOrder.ArithmeticSemiformula Empty 14 :=
  “targetFinish targetStart targetTokenCount targetWidth targetTable
      sourceFinish sourceStart sourceTokenCount sourceWidth sourceTable
      tableWidth table valueBound rowIndex.
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 429 + 0) sourceTable ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 429 + 1) sourceWidth ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 429 + 2) sourceTokenCount ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 429 + 24) sourceStart ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 429 + 25) sourceFinish ∧
    !(compactFixedWidthEntryDef)
      table tableWidth ((rowIndex + 1) * 429 + 0) targetTable ∧
    !(compactFixedWidthEntryDef)
      table tableWidth ((rowIndex + 1) * 429 + 1) targetWidth ∧
    !(compactFixedWidthEntryDef)
      table tableWidth ((rowIndex + 1) * 429 + 2) targetTokenCount ∧
    !(compactFixedWidthEntryDef)
      table tableWidth ((rowIndex + 1) * 429 + 3) targetStart ∧
    !(compactFixedWidthEntryDef)
      table tableWidth ((rowIndex + 1) * 429 + 4) targetFinish ∧
    !(compactFixedWidthCrossTableSlicesEqDef)
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish”

private theorem adjacentRowRawCore_eq_directRawCore :
    adjacentRowRawCore = adjacentRowDirectRawCore := by
  unfold adjacentRowRawCore adjacentBoundedVectorCore adjacentRowDirectRawCore
  unfold compactNumericVerifierStepWitnessTableAdjacentRowDef
  rfl

private theorem adjacentRowDef_val_eq_boundedVector :
    compactNumericVerifierStepWitnessTableAdjacentRowDef.val =
      boundedVectorBExs (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 4) 10
        adjacentRowRawCore := by
  unfold adjacentRowRawCore adjacentBoundedVectorCore
  unfold compactNumericVerifierStepWitnessTableAdjacentRowDef
  rfl

private def adjacentClosedShift :
    (depth : Nat) -> ValuationTerm ->
      LO.FirstOrder.ArithmeticSemiterm Nat depth
  | 0, term => term
  | depth + 1, term => Rew.bShift (adjacentClosedShift depth term)

private def adjacentExplicitClosedBoundedVectorFormula
    (bound : ValuationTerm) :
    (k : Nat) -> LO.FirstOrder.ArithmeticSemiformula Nat k ->
      ValuationFormula
  | 0, body => body
  | k + 1, body =>
      adjacentExplicitClosedBoundedVectorFormula bound k
        (body.bexsLTSucc (adjacentClosedShift k bound))

private def adjacentNormalizedGlobalSubstitutionQpow
    (terms : Fin 4 -> ValuationTerm) :
    (k : Nat) -> Rew ℒₒᵣ Empty (4 + k) Nat k
  | 0 => (Rew.subst terms).comp
      (Rew.emb : Rew ℒₒᵣ Empty 4 Nat 4)
  | k + 1 => (adjacentNormalizedGlobalSubstitutionQpow terms k).q

private def adjacentRowOpenWitnessMatrix
    (tableWidthTerm tableTerm valueBoundTerm rowIndexTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 10 :=
  adjacentNormalizedGlobalSubstitutionQpow
      ![tableWidthTerm, tableTerm, valueBoundTerm, rowIndexTerm] 10 ▹
    adjacentRowRawCore

@[simp] private theorem adjacentRewriting_bexsLTSucc
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (bound : LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity)
    (body : LO.FirstOrder.ArithmeticSemiformula sourceVariables
      (sourceArity + 1)) :
    rewriting ▹ body.bexsLTSucc bound =
      (rewriting.q ▹ body).bexsLTSucc (rewriting bound) := by
  simp [LO.FirstOrder.Semiformula.bexsLTSucc,
    LO.FirstOrder.Semiformula.bexsLT]

private def adjacentShiftedValueBoundVariable :
    (depth : Nat) -> Fin (4 + depth)
  | 0 => 2
  | depth + 1 => (adjacentShiftedValueBoundVariable depth).succ

@[simp] private theorem adjacentShiftedValueBoundVariable_val (depth : Nat) :
    (adjacentShiftedValueBoundVariable depth).val = 2 + depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp [adjacentShiftedValueBoundVariable, ih]
      omega

private theorem adjacentLiftPast_valueBound (depth : Nat) :
    liftPast depth (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 4) =
      (#(adjacentShiftedValueBoundVariable depth) :
        LO.FirstOrder.ArithmeticSemiterm Empty (4 + depth)) := by
  unfold liftPast
  rw [Rew.subst_bvar]
  congr 1
  apply Fin.ext
  simp

@[simp] private theorem adjacentNormalizedGlobalSubstitution_valueBound
    (terms : Fin 4 -> ValuationTerm) (depth : Nat) :
    adjacentNormalizedGlobalSubstitutionQpow terms depth
        (#(adjacentShiftedValueBoundVariable depth) :
          LO.FirstOrder.ArithmeticSemiterm Empty (4 + depth)) =
      adjacentClosedShift depth (terms 2) := by
  induction depth with
  | zero =>
      simp [adjacentNormalizedGlobalSubstitutionQpow,
        adjacentShiftedValueBoundVariable, adjacentClosedShift,
        Rew.comp_app, Rew.subst_bvar]
  | succ depth ih =>
      change (adjacentNormalizedGlobalSubstitutionQpow terms depth).q
          (#(adjacentShiftedValueBoundVariable depth).succ) = _
      rw [Rew.q_bvar_succ, ih]
      rfl

private theorem adjacentClosedMatrixRewriting_eq_openWitnessMatrix
    (tableWidthTerm tableTerm valueBoundTerm rowIndexTerm : ValuationTerm) :
    adjacentNormalizedGlobalSubstitutionQpow
        ![tableWidthTerm, tableTerm, valueBoundTerm, rowIndexTerm] 10 ▹
      adjacentRowRawCore =
        adjacentRowOpenWitnessMatrix tableWidthTerm tableTerm
          valueBoundTerm rowIndexTerm := by
  rfl

private theorem adjacentBoundedVectorRewriting_alignment
    (terms : Fin 4 -> ValuationTerm) :
    (k : Nat) ->
    (body : LO.FirstOrder.ArithmeticSemiformula Empty (4 + k)) ->
    (Rewriting.emb (ξ := Nat)
        (boundedVectorBExs
          (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 4) k body)) ⇜
    terms =
    adjacentExplicitClosedBoundedVectorFormula (terms 2) k
      (adjacentNormalizedGlobalSubstitutionQpow terms k ▹ body)
  | 0, body => by
      simp only [boundedVectorBExs,
        adjacentExplicitClosedBoundedVectorFormula,
        adjacentNormalizedGlobalSubstitutionQpow]
      rw [TransitiveRewriting.comp_app]
  | k + 1, body => by
      simp only [boundedVectorBExs,
        adjacentExplicitClosedBoundedVectorFormula]
      rw [adjacentBoundedVectorRewriting_alignment terms k]
      congr 1
      rw [adjacentRewriting_bexsLTSucc]
      congr 1
      rw [adjacentLiftPast_valueBound,
        adjacentNormalizedGlobalSubstitution_valueBound]

private theorem adjacentRowAtValuationFormula_alignment
    (tableWidthTerm tableTerm valueBoundTerm rowIndexTerm : ValuationTerm) :
    compactNumericVerifierStepWitnessTableAdjacentRowAtValuationFormula
        tableWidthTerm tableTerm valueBoundTerm rowIndexTerm =
      adjacentExplicitClosedBoundedVectorFormula valueBoundTerm 10
        (adjacentRowOpenWitnessMatrix tableWidthTerm tableTerm
          valueBoundTerm rowIndexTerm) := by
  unfold compactNumericVerifierStepWitnessTableAdjacentRowAtValuationFormula
  rw [adjacentRowDef_val_eq_boundedVector]
  rw [adjacentBoundedVectorRewriting_alignment
    ![tableWidthTerm, tableTerm, valueBoundTerm, rowIndexTerm] 10]
  exact congrArg
    (adjacentExplicitClosedBoundedVectorFormula valueBoundTerm 10)
    (adjacentClosedMatrixRewriting_eq_openWitnessMatrix
      tableWidthTerm tableTerm valueBoundTerm rowIndexTerm)

private def adjacentExistsBody {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    LO.FirstOrder.ArithmeticSemiformula Nat (arity + 1) :=
  match formula with
  | .exs body => body
  | _ => ⊤

private def adjacentAndLeft {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    LO.FirstOrder.ArithmeticSemiformula Nat arity :=
  match formula with
  | .and left _ => left
  | _ => ⊤

private def adjacentAndRight {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    LO.FirstOrder.ArithmeticSemiformula Nat arity :=
  match formula with
  | .and _ right => right
  | _ => ⊤

private theorem adjacentRowAtValuationFormula_exists_shape
    (tableWidthTerm tableTerm valueBoundTerm rowIndexTerm : ValuationTerm) :
    compactNumericVerifierStepWitnessTableAdjacentRowAtValuationFormula
        tableWidthTerm tableTerm valueBoundTerm rowIndexTerm =
      ∃⁰ adjacentExistsBody
        (compactNumericVerifierStepWitnessTableAdjacentRowAtValuationFormula
          tableWidthTerm tableTerm valueBoundTerm rowIndexTerm) := by
  unfold compactNumericVerifierStepWitnessTableAdjacentRowAtValuationFormula
  unfold compactNumericVerifierStepWitnessTableAdjacentRowDef
  unfold adjacentExistsBody
  rfl

private def adjacentRowBranchValuation (rowIndex : Nat) : Nat -> Nat :=
  extendValuation rowIndex zeroValuation

@[simp] theorem termValue_adjacentSourceTableIndexTerm (rowIndex : Nat) :
    termValue (adjacentRowBranchValuation rowIndex)
        (adjacentSourceTableIndexTerm (&0 : ValuationTerm)) =
      rowIndex * 429 + 0 := by
  simp [adjacentRowBranchValuation, adjacentSourceTableIndexTerm,
    termValue_arithmeticAdd, termValue_arithmeticMul,
    termValue, LO.FirstOrder.Semiterm.val_operator]

@[simp] theorem termValue_adjacentSourceWidthIndexTerm (rowIndex : Nat) :
    termValue (adjacentRowBranchValuation rowIndex)
        (adjacentSourceWidthIndexTerm (&0 : ValuationTerm)) =
      rowIndex * 429 + 1 := by
  simp [adjacentRowBranchValuation, adjacentSourceWidthIndexTerm,
    termValue_arithmeticAdd, termValue_arithmeticMul,
    termValue, LO.FirstOrder.Semiterm.val_operator]

@[simp] theorem termValue_adjacentSourceTokenCountIndexTerm (rowIndex : Nat) :
    termValue (adjacentRowBranchValuation rowIndex)
        (adjacentSourceTokenCountIndexTerm (&0 : ValuationTerm)) =
      rowIndex * 429 + 2 := by
  simp [adjacentRowBranchValuation, adjacentSourceTokenCountIndexTerm,
    termValue_arithmeticAdd, termValue_arithmeticMul,
    termValue, LO.FirstOrder.Semiterm.val_operator]

@[simp] theorem termValue_adjacentSourceStartIndexTerm (rowIndex : Nat) :
    termValue (adjacentRowBranchValuation rowIndex)
        (adjacentSourceStartIndexTerm (&0 : ValuationTerm)) =
      rowIndex * 429 + 24 := by
  simp [adjacentRowBranchValuation, adjacentSourceStartIndexTerm,
    termValue_arithmeticAdd, termValue_arithmeticMul,
    termValue, LO.FirstOrder.Semiterm.val_operator]

@[simp] theorem termValue_adjacentSourceFinishIndexTerm (rowIndex : Nat) :
    termValue (adjacentRowBranchValuation rowIndex)
        (adjacentSourceFinishIndexTerm (&0 : ValuationTerm)) =
      rowIndex * 429 + 25 := by
  simp [adjacentRowBranchValuation, adjacentSourceFinishIndexTerm,
    termValue_arithmeticAdd, termValue_arithmeticMul,
    termValue, LO.FirstOrder.Semiterm.val_operator]

@[simp] theorem termValue_adjacentTargetTableIndexTerm (rowIndex : Nat) :
    termValue (adjacentRowBranchValuation rowIndex)
        (adjacentTargetTableIndexTerm (&0 : ValuationTerm)) =
      (rowIndex + 1) * 429 + 0 := by
  simp [adjacentRowBranchValuation, adjacentTargetTableIndexTerm,
    termValue_arithmeticAdd, termValue_arithmeticMul,
    termValue_arithmeticOne, termValue,
    LO.FirstOrder.Semiterm.val_operator]

@[simp] theorem termValue_adjacentTargetWidthIndexTerm (rowIndex : Nat) :
    termValue (adjacentRowBranchValuation rowIndex)
        (adjacentTargetWidthIndexTerm (&0 : ValuationTerm)) =
      (rowIndex + 1) * 429 + 1 := by
  simp [adjacentRowBranchValuation, adjacentTargetWidthIndexTerm,
    termValue_arithmeticAdd, termValue_arithmeticMul,
    termValue_arithmeticOne, termValue,
    LO.FirstOrder.Semiterm.val_operator]

@[simp] theorem termValue_adjacentTargetTokenCountIndexTerm (rowIndex : Nat) :
    termValue (adjacentRowBranchValuation rowIndex)
        (adjacentTargetTokenCountIndexTerm (&0 : ValuationTerm)) =
      (rowIndex + 1) * 429 + 2 := by
  simp [adjacentRowBranchValuation, adjacentTargetTokenCountIndexTerm,
    termValue_arithmeticAdd, termValue_arithmeticMul,
    termValue_arithmeticOne, termValue,
    LO.FirstOrder.Semiterm.val_operator]

@[simp] theorem termValue_adjacentTargetStartIndexTerm (rowIndex : Nat) :
    termValue (adjacentRowBranchValuation rowIndex)
        (adjacentTargetStartIndexTerm (&0 : ValuationTerm)) =
      (rowIndex + 1) * 429 + 3 := by
  simp [adjacentRowBranchValuation, adjacentTargetStartIndexTerm,
    termValue_arithmeticAdd, termValue_arithmeticMul,
    termValue_arithmeticOne, termValue,
    LO.FirstOrder.Semiterm.val_operator]

@[simp] theorem termValue_adjacentTargetFinishIndexTerm (rowIndex : Nat) :
    termValue (adjacentRowBranchValuation rowIndex)
        (adjacentTargetFinishIndexTerm (&0 : ValuationTerm)) =
      (rowIndex + 1) * 429 + 4 := by
  simp [adjacentRowBranchValuation, adjacentTargetFinishIndexTerm,
    termValue_arithmeticAdd, termValue_arithmeticMul,
    termValue_arithmeticOne, termValue,
    LO.FirstOrder.Semiterm.val_operator]

@[simp] private theorem adjacentQ_bvarThree
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 4 targetVariables targetArity) :
    rewriting.q
        (#3 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 5) =
      Rew.bShift (rewriting #2) := by
  change rewriting.q (#((2 : Fin 4).succ)) = Rew.bShift (rewriting #2)
  exact Rew.q_bvar_succ rewriting 2

@[simp] private theorem adjacentQ_bvarFour
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 5 targetVariables targetArity) :
    rewriting.q
        (#4 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 6) =
      Rew.bShift (rewriting #3) := by
  change rewriting.q (#((3 : Fin 5).succ)) = Rew.bShift (rewriting #3)
  exact Rew.q_bvar_succ rewriting 3

@[simp] private theorem adjacentQ_bvarFive
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 6 targetVariables targetArity) :
    rewriting.q
        (#5 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 7) =
      Rew.bShift (rewriting #4) := by
  change rewriting.q (#((4 : Fin 6).succ)) = Rew.bShift (rewriting #4)
  exact Rew.q_bvar_succ rewriting 4

@[simp] private theorem adjacentQ_bvarSix
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 7 targetVariables targetArity) :
    rewriting.q
        (#6 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 8) =
      Rew.bShift (rewriting #5) := by
  change rewriting.q (#((5 : Fin 7).succ)) = Rew.bShift (rewriting #5)
  exact Rew.q_bvar_succ rewriting 5

@[simp] private theorem adjacentQ_bvarSeven
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 8 targetVariables targetArity) :
    rewriting.q
        (#7 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 9) =
      Rew.bShift (rewriting #6) := by
  change rewriting.q (#((6 : Fin 8).succ)) = Rew.bShift (rewriting #6)
  exact Rew.q_bvar_succ rewriting 6

@[simp] private theorem adjacentQ_bvarEight
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 9 targetVariables targetArity) :
    rewriting.q
        (#8 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 10) =
      Rew.bShift (rewriting #7) := by
  change rewriting.q (#((7 : Fin 9).succ)) = Rew.bShift (rewriting #7)
  exact Rew.q_bvar_succ rewriting 7

@[simp] private theorem adjacentQ_bvarNine
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 10 targetVariables targetArity) :
    rewriting.q
        (#9 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 11) =
      Rew.bShift (rewriting #8) := by
  change rewriting.q (#((8 : Fin 10).succ)) = Rew.bShift (rewriting #8)
  exact Rew.q_bvar_succ rewriting 8

@[simp] private theorem adjacentQ_bvarTen
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 11 targetVariables targetArity) :
    rewriting.q
        (#10 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 12) =
      Rew.bShift (rewriting #9) := by
  change rewriting.q (#((9 : Fin 11).succ)) = Rew.bShift (rewriting #9)
  exact Rew.q_bvar_succ rewriting 9

@[simp] private theorem adjacentQ_bvarEleven
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 12 targetVariables targetArity) :
    rewriting.q
        (#11 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 13) =
      Rew.bShift (rewriting #10) := by
  change rewriting.q (#((10 : Fin 12).succ)) = Rew.bShift (rewriting #10)
  exact Rew.q_bvar_succ rewriting 10

@[simp] private theorem adjacentQ_bvarTwelve
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 13 targetVariables targetArity) :
    rewriting.q
        (#12 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 14) =
      Rew.bShift (rewriting #11) := by
  change rewriting.q (#((11 : Fin 13).succ)) = Rew.bShift (rewriting #11)
  exact Rew.q_bvar_succ rewriting 11

private def adjacentWitnessGuardFormula
    (valueBound value : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) <
    !!(shortBinaryNumeralTerm valueBound) + 1”

private noncomputable def adjacentWitnessGuardCertificate
    (valuation : Nat -> Nat) (valueBound value : Nat)
    (hvalue : value <= valueBound) :
    CheckedHybridValuationBoundedFormulaCertificate
      valuation (adjacentWitnessGuardFormula valueBound value) := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm valueBound) + 1’
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      valuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm value, rightTerm] (by
        change termValue valuation (shortBinaryNumeralTerm value) <
          termValue valuation rightTerm
        simp only [rightTerm, termValue_arithmeticAdd,
          termValue_shortBinaryNumeralTerm, termValue_arithmeticOne]
        omega)
  exact .cast (by
    unfold adjacentWitnessGuardFormula
    exact (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm) direct

private theorem adjacentSubstituteClosedShift
    {k : Nat} (values : Fin k -> ValuationTerm) (term : ValuationTerm) :
    Rew.subst values (adjacentClosedShift k term) = term := by
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
  | succ k ih =>
      have hrew :
          (Rew.subst values).comp Rew.bShift =
            Rew.subst (fun index : Fin k => values index.succ) := by
        apply Rew.ext
        · intro index
          simp [Rew.comp_app]
        · intro freeIndex
          simp [Rew.comp_app]
      calc
        Rew.subst values (adjacentClosedShift (k + 1) term) =
            ((Rew.subst values).comp Rew.bShift)
              (adjacentClosedShift k term) := by
                simp [adjacentClosedShift, Rew.comp_app]
        _ = Rew.subst (fun index : Fin k => values index.succ)
              (adjacentClosedShift k term) := by rw [hrew]
        _ = term := ih _

private theorem adjacentShortBinarySubstitution_bexsLTSucc_tail
    {k : Nat}
    (bound : ValuationTerm)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat) :
    (body.bexsLTSucc (adjacentClosedShift k bound)) ⇜
        (fun index : Fin k =>
          shortBinaryNumeralTerm (values index.succ)) =
      (explicitWitnessBodyAfterTail body values).bexsLTSucc bound := by
  unfold LO.FirstOrder.Semiformula.bexsLTSucc
  unfold LO.FirstOrder.Semiformula.bexsLT
  have hbound :
      Rew.subst (fun index : Fin k =>
          shortBinaryNumeralTerm (values index.succ))
          (adjacentClosedShift k bound) = bound := by
    exact adjacentSubstituteClosedShift _ bound
  simp [explicitWitnessBodyAfterTail, hbound]

/-- Install a concrete bounded vector under an arbitrary valuation. -/
private noncomputable def
    buildAdjacentExplicitClosedBoundedVectorHybridCertificate
    {valuation : Nat -> Nat} :
    {k : Nat} ->
    (bound : Nat) ->
    (body : LO.FirstOrder.ArithmeticSemiformula Nat k) ->
    (values : Fin k -> Nat) ->
    (∀ index, values index <= bound) ->
    CheckedHybridValuationBoundedFormulaCertificate valuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)) ->
    CheckedHybridValuationBoundedFormulaCertificate valuation
      (adjacentExplicitClosedBoundedVectorFormula
        (shortBinaryNumeralTerm bound) k body)
  | 0, bound, body, values, hbounds, terminal => by
      simpa [adjacentExplicitClosedBoundedVectorFormula] using terminal
  | k + 1, bound, body, values, hbounds, terminal => by
      let tailValues : Fin k -> Nat := fun index => values index.succ
      let witnessBody := explicitWitnessBodyAfterTail body values
      let guard := adjacentWitnessGuardFormula bound (values 0)
      let guardCertificate :=
        adjacentWitnessGuardCertificate valuation bound (values 0)
          (hbounds 0)
      have hbodySubstitution :
          witnessBody/[shortBinaryNumeralTerm (values 0)] =
            body ⇜ fun index => shortBinaryNumeralTerm (values index) :=
        explicitWitnessBodyAfterTail_subst_head body values
      let installed : CheckedHybridValuationBoundedFormulaCertificate valuation
          (witnessBody/[shortBinaryNumeralTerm (values 0)]) :=
        .cast hbodySubstitution.symm terminal
      let guarded :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          guardCertificate installed
      let inner : CheckedHybridValuationBoundedFormulaCertificate valuation
          (witnessBody.bexsLTSucc
            (shortBinaryNumeralTerm bound)) := by
        let boundedMatrix : LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
          Semiformula.Operator.LT.lt.operator
              ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
                Rew.bShift
                  ‘!!(shortBinaryNumeralTerm bound) + 1’] ⋏
            witnessBody
        let direct : CheckedHybridValuationBoundedFormulaCertificate valuation
            (∃⁰ boundedMatrix) :=
          .existsWitness boundedMatrix (values 0) (.cast (by
            simp [boundedMatrix, guard, adjacentWitnessGuardFormula,
              ← TransitiveRewriting.comp_app]) guarded)
        exact .cast (by rfl) direct
      let recursiveTerminal :
          CheckedHybridValuationBoundedFormulaCertificate valuation
            ((body.bexsLTSucc
                (adjacentClosedShift k (shortBinaryNumeralTerm bound))) ⇜
              (fun index : Fin k =>
                shortBinaryNumeralTerm (tailValues index))) :=
        .cast
          (adjacentShortBinarySubstitution_bexsLTSucc_tail
            (shortBinaryNumeralTerm bound) body values).symm inner
      simpa only [adjacentExplicitClosedBoundedVectorFormula] using
        buildAdjacentExplicitClosedBoundedVectorHybridCertificate bound
          (body.bexsLTSucc
            (adjacentClosedShift k (shortBinaryNumeralTerm bound)))
          tailValues (fun index => hbounds index.succ) recursiveTerminal

private noncomputable def adjacentFixedWidthEntryCertificate
    (tableWidth table rowIndex value : Nat)
    (indexTerm : ValuationTerm)
    (hentry : CompactFixedWidthEntry table tableWidth
      (termValue (adjacentRowBranchValuation rowIndex) indexTerm) value) :
    CheckedHybridValuationBoundedFormulaCertificate
      (adjacentRowBranchValuation rowIndex)
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table)
        (shortBinaryNumeralTerm tableWidth)
        indexTerm
        (shortBinaryNumeralTerm value)) := by
  exact compactFixedWidthEntryAtValuationExplicitHybridCertificate
    (adjacentRowBranchValuation rowIndex)
    (shortBinaryNumeralTerm table)
    (shortBinaryNumeralTerm tableWidth)
    indexTerm
    (shortBinaryNumeralTerm value) (by
      simpa [termValue_shortBinaryNumeralTerm] using hentry)

private theorem adjacentCrossTableFixedCountData
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat}
    (hcross : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish) :
    let count := sourceFinish - sourceStart
    count <= sourceTokenCount ∧
      count <= targetTokenCount ∧
      sourceFinish = sourceStart + count ∧
      targetFinish = targetStart + count ∧
      sourceFinish <= sourceTokenCount ∧
      targetFinish <= targetTokenCount ∧
      ∀ offset < count, ∀ bitIndex < sourceWidth + targetWidth,
        (bitIndex < sourceWidth ∧
            sourceTable.testBit
              ((sourceStart + offset) * sourceWidth + bitIndex) = true) ↔
          (bitIndex < targetWidth ∧
            targetTable.testBit
              ((targetStart + offset) * targetWidth + bitIndex) = true) := by
  dsimp only
  rcases hcross with
    ⟨count, hsourceCount, htargetCount, hsourceEndpoint,
      htargetEndpoint, hsourceFinish, htargetFinish, hbits⟩
  have hcount : count = sourceFinish - sourceStart := by omega
  subst count
  exact ⟨hsourceCount, htargetCount, hsourceEndpoint, htargetEndpoint,
    hsourceFinish, htargetFinish, hbits⟩

private noncomputable def adjacentCrossTableCertificate
    (rowIndex sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat)
    (hcross : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish) :
    CheckedHybridValuationBoundedFormulaCertificate
      (adjacentRowBranchValuation rowIndex)
      (compactFixedWidthCrossTableSlicesEqAtValuationFormula
        (shortBinaryNumeralTerm sourceTable)
        (shortBinaryNumeralTerm sourceWidth)
        (shortBinaryNumeralTerm sourceTokenCount)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm sourceFinish)
        (shortBinaryNumeralTerm targetTable)
        (shortBinaryNumeralTerm targetWidth)
        (shortBinaryNumeralTerm targetTokenCount)
        (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm targetFinish)) := by
  let count := sourceFinish - sourceStart
  have hdata := adjacentCrossTableFixedCountData hcross
  exact compactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridCertificate
    (adjacentRowBranchValuation rowIndex)
    (shortBinaryNumeralTerm sourceTable)
    (shortBinaryNumeralTerm sourceWidth)
    (shortBinaryNumeralTerm sourceTokenCount)
    (shortBinaryNumeralTerm sourceStart)
    (shortBinaryNumeralTerm sourceFinish)
    (shortBinaryNumeralTerm targetTable)
    (shortBinaryNumeralTerm targetWidth)
    (shortBinaryNumeralTerm targetTokenCount)
    (shortBinaryNumeralTerm targetStart)
    (shortBinaryNumeralTerm targetFinish)
    count
    (by
      rw [termValue_shortBinaryNumeralTerm]
      exact hdata.1)
    (by
      rw [termValue_shortBinaryNumeralTerm]
      exact hdata.2.1)
    (by
      rw [termValue_shortBinaryNumeralTerm,
        termValue_shortBinaryNumeralTerm]
      exact hdata.2.2.1)
    (by
      rw [termValue_shortBinaryNumeralTerm,
        termValue_shortBinaryNumeralTerm]
      exact hdata.2.2.2.1)
    (by
      rw [termValue_shortBinaryNumeralTerm,
        termValue_shortBinaryNumeralTerm]
      exact hdata.2.2.2.2.1)
    (by
      rw [termValue_shortBinaryNumeralTerm,
        termValue_shortBinaryNumeralTerm]
      exact hdata.2.2.2.2.2.1)
    (by
      simpa only [termValue_shortBinaryNumeralTerm] using
        hdata.2.2.2.2.2.2)

/-- The exact terminal formula after all ten adjacent-row witnesses have been
installed. -/
def compactNumericVerifierStepWitnessTableAdjacentRowPostWitnessFormula
    (tableWidth table rowIndex : Nat)
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm table)
      (shortBinaryNumeralTerm tableWidth)
      (adjacentSourceTableIndexTerm (&0 : ValuationTerm))
      (shortBinaryNumeralTerm sourceTable) ⋏
    (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table)
        (shortBinaryNumeralTerm tableWidth)
        (adjacentSourceWidthIndexTerm (&0 : ValuationTerm))
        (shortBinaryNumeralTerm sourceWidth) ⋏
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm table)
          (shortBinaryNumeralTerm tableWidth)
          (adjacentSourceTokenCountIndexTerm (&0 : ValuationTerm))
          (shortBinaryNumeralTerm sourceTokenCount) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm table)
            (shortBinaryNumeralTerm tableWidth)
            (adjacentSourceStartIndexTerm (&0 : ValuationTerm))
            (shortBinaryNumeralTerm sourceStart) ⋏
          (compactFixedWidthEntryAtValuationFormula
              (shortBinaryNumeralTerm table)
              (shortBinaryNumeralTerm tableWidth)
              (adjacentSourceFinishIndexTerm (&0 : ValuationTerm))
              (shortBinaryNumeralTerm sourceFinish) ⋏
            (compactFixedWidthEntryAtValuationFormula
                (shortBinaryNumeralTerm table)
                (shortBinaryNumeralTerm tableWidth)
                (adjacentTargetTableIndexTerm (&0 : ValuationTerm))
                (shortBinaryNumeralTerm targetTable) ⋏
              (compactFixedWidthEntryAtValuationFormula
                  (shortBinaryNumeralTerm table)
                  (shortBinaryNumeralTerm tableWidth)
                  (adjacentTargetWidthIndexTerm (&0 : ValuationTerm))
                  (shortBinaryNumeralTerm targetWidth) ⋏
                (compactFixedWidthEntryAtValuationFormula
                    (shortBinaryNumeralTerm table)
                    (shortBinaryNumeralTerm tableWidth)
                    (adjacentTargetTokenCountIndexTerm (&0 : ValuationTerm))
                    (shortBinaryNumeralTerm targetTokenCount) ⋏
                  (compactFixedWidthEntryAtValuationFormula
                      (shortBinaryNumeralTerm table)
                      (shortBinaryNumeralTerm tableWidth)
                      (adjacentTargetStartIndexTerm (&0 : ValuationTerm))
                      (shortBinaryNumeralTerm targetStart) ⋏
                    (compactFixedWidthEntryAtValuationFormula
                        (shortBinaryNumeralTerm table)
                        (shortBinaryNumeralTerm tableWidth)
                        (adjacentTargetFinishIndexTerm (&0 : ValuationTerm))
                        (shortBinaryNumeralTerm targetFinish) ⋏
                      compactFixedWidthCrossTableSlicesEqAtValuationFormula
                        (shortBinaryNumeralTerm sourceTable)
                        (shortBinaryNumeralTerm sourceWidth)
                        (shortBinaryNumeralTerm sourceTokenCount)
                        (shortBinaryNumeralTerm sourceStart)
                        (shortBinaryNumeralTerm sourceFinish)
                        (shortBinaryNumeralTerm targetTable)
                        (shortBinaryNumeralTerm targetWidth)
                        (shortBinaryNumeralTerm targetTokenCount)
                        (shortBinaryNumeralTerm targetStart)
                        (shortBinaryNumeralTerm targetFinish))))))))))

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
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

private def adjacentRowGlobalTerms
    (tableWidth table valueBound : Nat) : Fin 4 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tableWidth,
    shortBinaryNumeralTerm table,
    shortBinaryNumeralTerm valueBound,
    (&0 : ValuationTerm)]

private def adjacentRowWitnessTerms
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    Fin 10 -> ValuationTerm :=
  ![shortBinaryNumeralTerm targetFinish,
    shortBinaryNumeralTerm targetStart,
    shortBinaryNumeralTerm targetTokenCount,
    shortBinaryNumeralTerm targetWidth,
    shortBinaryNumeralTerm targetTable,
    shortBinaryNumeralTerm sourceFinish,
    shortBinaryNumeralTerm sourceStart,
    shortBinaryNumeralTerm sourceTokenCount,
    shortBinaryNumeralTerm sourceWidth,
    shortBinaryNumeralTerm sourceTable]

private def adjacentRowInstalledTerms
    (tableWidth table valueBound
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    Fin 14 -> ValuationTerm :=
  ![shortBinaryNumeralTerm targetFinish,
    shortBinaryNumeralTerm targetStart,
    shortBinaryNumeralTerm targetTokenCount,
    shortBinaryNumeralTerm targetWidth,
    shortBinaryNumeralTerm targetTable,
    shortBinaryNumeralTerm sourceFinish,
    shortBinaryNumeralTerm sourceStart,
    shortBinaryNumeralTerm sourceTokenCount,
    shortBinaryNumeralTerm sourceWidth,
    shortBinaryNumeralTerm sourceTable,
    shortBinaryNumeralTerm tableWidth,
    shortBinaryNumeralTerm table,
    shortBinaryNumeralTerm valueBound,
    (&0 : ValuationTerm)]

private theorem adjacentRowInstalledRewriting_eq
    (tableWidth table valueBound
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    (Rew.subst (adjacentRowWitnessTerms sourceTable sourceWidth
      sourceTokenCount sourceStart sourceFinish targetTable targetWidth
      targetTokenCount targetStart targetFinish)).comp
        (adjacentNormalizedGlobalSubstitutionQpow
          (adjacentRowGlobalTerms tableWidth table valueBound) 10) =
      (Rew.subst (adjacentRowInstalledTerms tableWidth table valueBound
        sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
        targetTable targetWidth targetTokenCount targetStart targetFinish)).comp
          (Rew.emb : Rew ℒₒᵣ Empty 14 Nat 14) := by
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [adjacentNormalizedGlobalSubstitutionQpow,
        adjacentRowGlobalTerms, adjacentRowWitnessTerms,
        adjacentRowInstalledTerms, Rew.comp_app, Rew.subst_bvar, Rew.q]
    all_goals exact adjacentSubstituteClosedShift _ _
  · intro index
    exact Empty.elim index

private theorem adjacentRewriting_installedFormulaApp
    {predicateArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      LO.FirstOrder.ArithmeticSemiterm Empty 14)
    (installed : Fin 14 -> ValuationTerm) :
    ((Rew.subst installed).comp
        ((Rew.emb : Rew ℒₒᵣ Empty 14 Nat 14).comp
          (Rew.subst terms))) ▹ formula =
      ((Rew.subst
          (((Rew.subst installed).comp
            (Rew.emb : Rew ℒₒᵣ Empty 14 Nat 14)) ∘ terms)).comp
        (Rew.emb : Rew ℒₒᵣ Empty predicateArity Nat predicateArity)) ▹
          formula := by
  have hrew :
      (Rew.subst installed).comp
          ((Rew.emb : Rew ℒₒᵣ Empty 14 Nat 14).comp
            (Rew.subst terms)) =
        (Rew.subst
          (((Rew.subst installed).comp
            (Rew.emb : Rew ℒₒᵣ Empty 14 Nat 14)) ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity Nat predicateArity) := by
    apply Rew.ext
    · intro coordinate
      simp [Rew.comp_app]
    · intro index
      exact Empty.elim index
  exact congrArg (fun rewriting => rewriting ▹ formula) hrew


private def adjacentRowWitnessValues
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    Fin 10 -> Nat :=
  ![targetFinish, targetStart, targetTokenCount, targetWidth, targetTable,
    sourceFinish, sourceStart, sourceTokenCount, sourceWidth, sourceTable]

private theorem adjacentRowWitnessTerms_eq_values
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    adjacentRowWitnessTerms sourceTable sourceWidth sourceTokenCount
        sourceStart sourceFinish targetTable targetWidth targetTokenCount
        targetStart targetFinish =
      fun coordinate => shortBinaryNumeralTerm
        (adjacentRowWitnessValues sourceTable sourceWidth sourceTokenCount
          sourceStart sourceFinish targetTable targetWidth targetTokenCount
          targetStart targetFinish coordinate) := by
  funext coordinate
  fin_cases coordinate <;> rfl

private theorem adjacentRowDirectTerminal_alignment
    (tableWidth table valueBound rowIndex
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    (Rewriting.emb (ξ := Nat) adjacentRowRawCore) ⇜
        (adjacentRowInstalledTerms tableWidth table valueBound sourceTable
          sourceWidth sourceTokenCount sourceStart sourceFinish targetTable
          targetWidth targetTokenCount targetStart targetFinish) =
      compactNumericVerifierStepWitnessTableAdjacentRowPostWitnessFormula
        tableWidth table rowIndex sourceTable sourceWidth sourceTokenCount
        sourceStart sourceFinish targetTable targetWidth targetTokenCount
        targetStart targetFinish := by
  rw [adjacentRowRawCore_eq_directRawCore]
  unfold adjacentRowDirectRawCore
  unfold compactNumericVerifierStepWitnessTableAdjacentRowPostWitnessFormula
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactFixedWidthCrossTableSlicesEqAtValuationFormula
  unfold adjacentSourceTableIndexTerm adjacentSourceWidthIndexTerm
  unfold adjacentSourceTokenCountIndexTerm adjacentSourceStartIndexTerm
  unfold adjacentSourceFinishIndexTerm adjacentTargetTableIndexTerm
  unfold adjacentTargetWidthIndexTerm adjacentTargetTokenCountIndexTerm
  unfold adjacentTargetStartIndexTerm adjacentTargetFinishIndexTerm
  simp [adjacentRowInstalledTerms, adjacentRewriting_installedFormulaApp,
    Rew.comp_app, Function.comp_def,
    ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

private theorem adjacentRowOpenWitnessMatrix_substitution
    (tableWidth table rowIndex : Nat)
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    (adjacentRowOpenWitnessMatrix
        (shortBinaryNumeralTerm tableWidth)
        (shortBinaryNumeralTerm table)
        (shortBinaryNumeralTerm (2 ^ tableWidth))
        (&0 : ValuationTerm)) ⇜
        (fun coordinate => shortBinaryNumeralTerm
          (adjacentRowWitnessValues sourceTable sourceWidth sourceTokenCount
            sourceStart sourceFinish targetTable targetWidth targetTokenCount
            targetStart targetFinish coordinate)) =
      compactNumericVerifierStepWitnessTableAdjacentRowPostWitnessFormula
        tableWidth table rowIndex sourceTable sourceWidth sourceTokenCount
        sourceStart sourceFinish targetTable targetWidth targetTokenCount
        targetStart targetFinish := by
  rw [← adjacentRowWitnessTerms_eq_values]
  change
    (adjacentNormalizedGlobalSubstitutionQpow
        (adjacentRowGlobalTerms tableWidth table (2 ^ tableWidth)) 10 ▹
      adjacentRowRawCore) ⇜
        (adjacentRowWitnessTerms sourceTable sourceWidth sourceTokenCount
          sourceStart sourceFinish targetTable targetWidth targetTokenCount
          targetStart targetFinish) =
      compactNumericVerifierStepWitnessTableAdjacentRowPostWitnessFormula
        tableWidth table rowIndex sourceTable sourceWidth sourceTokenCount
        sourceStart sourceFinish targetTable targetWidth targetTokenCount
        targetStart targetFinish
  rw [show
    (adjacentNormalizedGlobalSubstitutionQpow
        (adjacentRowGlobalTerms tableWidth table (2 ^ tableWidth)) 10 ▹
      adjacentRowRawCore) ⇜
        (adjacentRowWitnessTerms sourceTable sourceWidth sourceTokenCount
          sourceStart sourceFinish targetTable targetWidth targetTokenCount
          targetStart targetFinish) =
      (Rewriting.emb (ξ := Nat) adjacentRowRawCore) ⇜
        (adjacentRowInstalledTerms tableWidth table (2 ^ tableWidth)
          sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
          targetTable targetWidth targetTokenCount targetStart targetFinish) by
    change
      (Rew.subst (adjacentRowWitnessTerms sourceTable sourceWidth
        sourceTokenCount sourceStart sourceFinish targetTable targetWidth
        targetTokenCount targetStart targetFinish)) ▹
          (adjacentNormalizedGlobalSubstitutionQpow
            (adjacentRowGlobalTerms tableWidth table (2 ^ tableWidth)) 10 ▹
              adjacentRowRawCore) =
        (Rew.subst (adjacentRowInstalledTerms tableWidth table
          (2 ^ tableWidth) sourceTable sourceWidth sourceTokenCount
          sourceStart sourceFinish targetTable targetWidth targetTokenCount
          targetStart targetFinish)) ▹
            ((Rew.emb : Rew ℒₒᵣ Empty 14 Nat 14) ▹
              adjacentRowRawCore)
    rw [← TransitiveRewriting.comp_app,
      ← TransitiveRewriting.comp_app, adjacentRowInstalledRewriting_eq]]
  exact adjacentRowDirectTerminal_alignment tableWidth table
    (2 ^ tableWidth) rowIndex sourceTable sourceWidth sourceTokenCount
    sourceStart sourceFinish targetTable targetWidth targetTokenCount
    targetStart targetFinish

private noncomputable def adjacentRowPostWitnessCertificate
    (tableWidth table rowIndex : Nat)
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat)
    (hsourceTable : CompactFixedWidthEntry table tableWidth
      (rowIndex * 429 + 0) sourceTable)
    (hsourceWidth : CompactFixedWidthEntry table tableWidth
      (rowIndex * 429 + 1) sourceWidth)
    (hsourceTokenCount : CompactFixedWidthEntry table tableWidth
      (rowIndex * 429 + 2) sourceTokenCount)
    (hsourceStart : CompactFixedWidthEntry table tableWidth
      (rowIndex * 429 + 24) sourceStart)
    (hsourceFinish : CompactFixedWidthEntry table tableWidth
      (rowIndex * 429 + 25) sourceFinish)
    (htargetTable : CompactFixedWidthEntry table tableWidth
      ((rowIndex + 1) * 429 + 0) targetTable)
    (htargetWidth : CompactFixedWidthEntry table tableWidth
      ((rowIndex + 1) * 429 + 1) targetWidth)
    (htargetTokenCount : CompactFixedWidthEntry table tableWidth
      ((rowIndex + 1) * 429 + 2) targetTokenCount)
    (htargetStart : CompactFixedWidthEntry table tableWidth
      ((rowIndex + 1) * 429 + 3) targetStart)
    (htargetFinish : CompactFixedWidthEntry table tableWidth
      ((rowIndex + 1) * 429 + 4) targetFinish)
    (hcross : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish) :
    CheckedHybridValuationBoundedFormulaCertificate
      (adjacentRowBranchValuation rowIndex)
      (compactNumericVerifierStepWitnessTableAdjacentRowPostWitnessFormula
        tableWidth table rowIndex sourceTable sourceWidth sourceTokenCount
        sourceStart sourceFinish targetTable targetWidth targetTokenCount
        targetStart targetFinish) := by
  unfold compactNumericVerifierStepWitnessTableAdjacentRowPostWitnessFormula
  exact .conjunction
    (adjacentFixedWidthEntryCertificate tableWidth table rowIndex sourceTable
      (adjacentSourceTableIndexTerm (&0 : ValuationTerm)) (by simpa using hsourceTable))
    (.conjunction
      (adjacentFixedWidthEntryCertificate tableWidth table rowIndex sourceWidth
        (adjacentSourceWidthIndexTerm (&0 : ValuationTerm)) (by simpa using hsourceWidth))
      (.conjunction
        (adjacentFixedWidthEntryCertificate tableWidth table rowIndex
          sourceTokenCount
          (adjacentSourceTokenCountIndexTerm (&0 : ValuationTerm))
          (by simpa using hsourceTokenCount))
        (.conjunction
          (adjacentFixedWidthEntryCertificate tableWidth table rowIndex sourceStart
            (adjacentSourceStartIndexTerm (&0 : ValuationTerm))
            (by simpa using hsourceStart))
          (.conjunction
            (adjacentFixedWidthEntryCertificate tableWidth table rowIndex sourceFinish
              (adjacentSourceFinishIndexTerm (&0 : ValuationTerm))
              (by simpa using hsourceFinish))
            (.conjunction
              (adjacentFixedWidthEntryCertificate tableWidth table rowIndex targetTable
                (adjacentTargetTableIndexTerm (&0 : ValuationTerm))
                (by simpa using htargetTable))
              (.conjunction
                (adjacentFixedWidthEntryCertificate tableWidth table rowIndex targetWidth
                  (adjacentTargetWidthIndexTerm (&0 : ValuationTerm))
                  (by simpa using htargetWidth))
                (.conjunction
                  (adjacentFixedWidthEntryCertificate tableWidth table rowIndex
                    targetTokenCount
                    (adjacentTargetTokenCountIndexTerm (&0 : ValuationTerm))
                    (by simpa using htargetTokenCount))
                  (.conjunction
                    (adjacentFixedWidthEntryCertificate tableWidth table rowIndex
                      targetStart
                      (adjacentTargetStartIndexTerm (&0 : ValuationTerm))
                      (by simpa using htargetStart))
                    (.conjunction
                      (adjacentFixedWidthEntryCertificate tableWidth table rowIndex
                        targetFinish
                        (adjacentTargetFinishIndexTerm (&0 : ValuationTerm))
                        (by simpa using htargetFinish))
                      (adjacentCrossTableCertificate rowIndex sourceTable sourceWidth
                        sourceTokenCount sourceStart sourceFinish targetTable targetWidth
                        targetTokenCount targetStart targetFinish hcross))))))))))

/-- A real explicit hybrid certificate for one adjacent row.  The ten witnesses
are the canonical decoded table columns, in the source formula's binder order. -/
noncomputable def
    compactNumericVerifierStepWitnessTableAdjacentRowExplicitHybridCertificate
    (tableWidth table rowIndex : Nat)
    (hcanonical : CompactNumericVerifierStepWitnessTableCanonicalAdjacent
      tableWidth table rowIndex) :
    CheckedHybridValuationBoundedFormulaCertificate
      (adjacentRowBranchValuation rowIndex)
      (compactNumericVerifierStepWitnessTableAdjacentRowAtValuationFormula
        (shortBinaryNumeralTerm tableWidth)
        (shortBinaryNumeralTerm table)
        (shortBinaryNumeralTerm (2 ^ tableWidth))
        (&0 : ValuationTerm)) := by
  let source := compactNumericVerifierStepWitnessTableFormulaEnvironment
    tableWidth table rowIndex
  let target := compactNumericVerifierStepWitnessTableFormulaEnvironment
    tableWidth table (rowIndex + 1)
  let sourceTable := source 0
  let sourceWidth := source 1
  let sourceTokenCount := source 2
  let sourceStart := source 24
  let sourceFinish := source 25
  let targetTable := target 0
  let targetWidth := target 1
  let targetTokenCount := target 2
  let targetStart := target 3
  let targetFinish := target 4
  have hsourceBound (column : Fin 429) : source column <= 2 ^ tableWidth := by
    change compactNumericVerifierStepWitnessTableColumnValue
      tableWidth table rowIndex column.val <= 2 ^ tableWidth
    exact compactNumericVerifierStepWitnessTableColumnValue_le_pow
      tableWidth table rowIndex column.val
  have htargetBound (column : Fin 429) : target column <= 2 ^ tableWidth := by
    change compactNumericVerifierStepWitnessTableColumnValue
      tableWidth table (rowIndex + 1) column.val <= 2 ^ tableWidth
    exact compactNumericVerifierStepWitnessTableColumnValue_le_pow
      tableWidth table (rowIndex + 1) column.val
  have hsourceEntry (column : Fin 429) :
      CompactFixedWidthEntry table tableWidth
        (rowIndex * 429 + column.val) (source column) := by
    change CompactFixedWidthEntry table tableWidth
      (rowIndex * 429 + column.val)
      (compactNumericVerifierStepWitnessTableColumnValue
        tableWidth table rowIndex column.val)
    simpa [compactNumericVerifierStepWitnessColumnCount] using
      compactNumericVerifierStepWitnessTableColumnValue_entry
        tableWidth table rowIndex column.val
  have htargetEntry (column : Fin 429) :
      CompactFixedWidthEntry table tableWidth
        ((rowIndex + 1) * 429 + column.val) (target column) := by
    change CompactFixedWidthEntry table tableWidth
      ((rowIndex + 1) * 429 + column.val)
      (compactNumericVerifierStepWitnessTableColumnValue
        tableWidth table (rowIndex + 1) column.val)
    simpa [compactNumericVerifierStepWitnessColumnCount] using
      compactNumericVerifierStepWitnessTableColumnValue_entry
        tableWidth table (rowIndex + 1) column.val
  have hcross : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish := by
    simpa [CompactNumericVerifierStepWitnessTableCanonicalAdjacent,
      source, target, sourceTable, sourceWidth, sourceTokenCount, sourceStart,
      sourceFinish, targetTable, targetWidth, targetTokenCount, targetStart,
      targetFinish] using hcanonical
  let values := adjacentRowWitnessValues sourceTable sourceWidth
    sourceTokenCount sourceStart sourceFinish targetTable targetWidth
    targetTokenCount targetStart targetFinish
  have hvaluesBound : ∀ coordinate, values coordinate <= 2 ^ tableWidth := by
    intro coordinate
    fin_cases coordinate
    · exact htargetBound 4
    · exact htargetBound 3
    · exact htargetBound 2
    · exact htargetBound 1
    · exact htargetBound 0
    · exact hsourceBound 25
    · exact hsourceBound 24
    · exact hsourceBound 2
    · exact hsourceBound 1
    · exact hsourceBound 0
  let terminalParts := adjacentRowPostWitnessCertificate
    tableWidth table rowIndex sourceTable sourceWidth sourceTokenCount
    sourceStart sourceFinish targetTable targetWidth targetTokenCount
    targetStart targetFinish
    (hsourceEntry 0) (hsourceEntry 1) (hsourceEntry 2)
    (hsourceEntry 24) (hsourceEntry 25)
    (htargetEntry 0) (htargetEntry 1) (htargetEntry 2)
    (htargetEntry 3) (htargetEntry 4) hcross
  let terminal : CheckedHybridValuationBoundedFormulaCertificate
      (adjacentRowBranchValuation rowIndex)
      ((adjacentRowOpenWitnessMatrix
          (shortBinaryNumeralTerm tableWidth)
          (shortBinaryNumeralTerm table)
          (shortBinaryNumeralTerm (2 ^ tableWidth))
          (&0 : ValuationTerm)) ⇜
        (fun coordinate => shortBinaryNumeralTerm (values coordinate))) :=
    .cast
      (adjacentRowOpenWitnessMatrix_substitution tableWidth table rowIndex
        sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
        targetTable targetWidth targetTokenCount targetStart targetFinish).symm
      terminalParts
  rw [adjacentRowAtValuationFormula_alignment]
  exact buildAdjacentExplicitClosedBoundedVectorHybridCertificate
    (valuation := adjacentRowBranchValuation rowIndex)
    (2 ^ tableWidth)
    (adjacentRowOpenWitnessMatrix
      (shortBinaryNumeralTerm tableWidth)
      (shortBinaryNumeralTerm table)
      (shortBinaryNumeralTerm (2 ^ tableWidth))
      (&0 : ValuationTerm))
    values hvaluesBound terminal

private def adjacentRowsNextGuardBody
    (rowCountTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 + 1 < !!(Rew.bShift rowCountTerm)”

private def adjacentRowsAdjacentBody
    (tableWidth table valueBound : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStepWitnessTableAdjacentRowDef.val) ⇜
    ![Rew.bShift (shortBinaryNumeralTerm tableWidth),
      Rew.bShift (shortBinaryNumeralTerm table),
      Rew.bShift (shortBinaryNumeralTerm valueBound),
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)]

/-- The condition body enumerated by the explicit row-count universal. -/
def compactNumericVerifierStepWitnessTableRowsAdjacentUniversalBody
    (tableWidth table valueBound : Nat) (rowCountTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  LO.Arrow.arrow (adjacentRowsNextGuardBody rowCountTerm)
    (adjacentRowsAdjacentBody tableWidth table valueBound)

private def adjacentRowsNextGuardFormula
    (rowCountTerm : ValuationTerm) : ValuationFormula :=
  “!!(&0 : ValuationTerm) + 1 < !!(Rew.shift rowCountTerm)”

private theorem adjacentRowsAdjacentBody_free_alignment
    (tableWidth table valueBound : Nat) :
    Rewriting.free (adjacentRowsAdjacentBody tableWidth table valueBound) =
      compactNumericVerifierStepWitnessTableAdjacentRowAtValuationFormula
        (shortBinaryNumeralTerm tableWidth)
        (shortBinaryNumeralTerm table)
        (shortBinaryNumeralTerm valueBound)
        (&0 : ValuationTerm) := by
  unfold adjacentRowsAdjacentBody
  rw [rewriting_embeddedFormulaSubstitution]
  unfold compactNumericVerifierStepWitnessTableAdjacentRowAtValuationFormula
  congr 1
  funext coordinate
  fin_cases coordinate <;> simp [Function.comp_def]

private theorem adjacentRowsUniversalBody_free_alignment
    (tableWidth table valueBound : Nat) (rowCountTerm : ValuationTerm) :
    Rewriting.free
        (compactNumericVerifierStepWitnessTableRowsAdjacentUniversalBody
          tableWidth table valueBound rowCountTerm) =
      (∼adjacentRowsNextGuardFormula rowCountTerm ⋎
        compactNumericVerifierStepWitnessTableAdjacentRowAtValuationFormula
          (shortBinaryNumeralTerm tableWidth)
          (shortBinaryNumeralTerm table)
          (shortBinaryNumeralTerm valueBound)
          (&0 : ValuationTerm)) := by
  simp [compactNumericVerifierStepWitnessTableRowsAdjacentUniversalBody,
    adjacentRowsNextGuardBody, adjacentRowsNextGuardFormula,
    LO.FirstOrder.Semiformula.imp_eq,
    adjacentRowsAdjacentBody_free_alignment]

/-- Strict alignment of the original rows-adjacent predicate with the explicit
row-count universal body. -/
theorem compactNumericVerifierStepWitnessTableRowsAdjacentAtValuationFormula_alignment
    (tableWidth table valueBound : Nat) (rowCountTerm : ValuationTerm) :
    compactNumericVerifierStepWitnessTableRowsAdjacentAtValuationFormula
        tableWidth table valueBound rowCountTerm =
      (compactNumericVerifierStepWitnessTableRowsAdjacentUniversalBody
        tableWidth table valueBound rowCountTerm).ballLT rowCountTerm := by
  unfold compactNumericVerifierStepWitnessTableRowsAdjacentAtValuationFormula
  unfold compactNumericVerifierStepWitnessTableRowsAdjacentUniversalBody
  unfold adjacentRowsNextGuardBody adjacentRowsAdjacentBody
  unfold compactNumericVerifierStepWitnessTableRowsAdjacentDef
  simp [LO.FirstOrder.Semiformula.ballLT, LO.FirstOrder.ball,
    LO.FirstOrder.Semiformula.imp_eq,
    rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app, Function.comp_def]
  apply Rewriting.smul_ext'
  apply Rew.ext
  · intro coordinate
    have htableWidth :
        (Rew.subst ![shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm table, rowCountTerm,
          shortBinaryNumeralTerm valueBound]).q
            (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 5) =
          Rew.bShift (shortBinaryNumeralTerm tableWidth) := by
      change
        (Rew.subst ![shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm table, rowCountTerm,
          shortBinaryNumeralTerm valueBound]).q
            (#((0 : Fin 4).succ)) = _
      rw [Rew.q_bvar_succ, Rew.subst_bvar]
      rfl
    have htable :
        (Rew.subst ![shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm table, rowCountTerm,
          shortBinaryNumeralTerm valueBound]).q
            (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 5) =
          Rew.bShift (shortBinaryNumeralTerm table) := by
      change
        (Rew.subst ![shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm table, rowCountTerm,
          shortBinaryNumeralTerm valueBound]).q
            (#((1 : Fin 4).succ)) = _
      rw [Rew.q_bvar_succ, Rew.subst_bvar]
      rfl
    have hvalueBound :
        (Rew.subst ![shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm table, rowCountTerm,
          shortBinaryNumeralTerm valueBound]).q
            (#4 : LO.FirstOrder.ArithmeticSemiterm Nat 5) =
          Rew.bShift (shortBinaryNumeralTerm valueBound) := by
      change
        (Rew.subst ![shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm table, rowCountTerm,
          shortBinaryNumeralTerm valueBound]).q
            (#((3 : Fin 4).succ)) = _
      rw [Rew.q_bvar_succ, Rew.subst_bvar]
      rfl
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar, htableWidth, htable,
        hvalueBound]
  · intro index
    exact Empty.elim index

private noncomputable def adjacentRowsNextGuardFalseCertificate
    (rowCountTerm : ValuationTerm) (rowIndex : Nat)
    (hnext : ¬rowIndex + 1 < termValue zeroValuation rowCountTerm) :
    CheckedHybridValuationBoundedFormulaCertificate
      (adjacentRowBranchValuation rowIndex)
      (∼adjacentRowsNextGuardFormula rowCountTerm) := by
  let leftTerm : ValuationTerm := ‘!!(&0 : ValuationTerm) + 1’
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
      (adjacentRowBranchValuation rowIndex) Language.ORing.Rel.lt
      ![leftTerm, Rew.shift rowCountTerm] (by
        change ¬termValue (adjacentRowBranchValuation rowIndex) leftTerm <
          termValue (adjacentRowBranchValuation rowIndex)
            (Rew.shift rowCountTerm)
        rw [termValue_arithmeticAdd, termValue_arithmeticOne]
        unfold adjacentRowBranchValuation
        rw [termValue_shift]
        change ¬rowIndex + 1 < termValue zeroValuation rowCountTerm
        exact hnext)
  exact .cast (by
    unfold adjacentRowsNextGuardFormula leftTerm
    rfl) direct

private noncomputable def adjacentRowsUniversalBranchCertificate
    (tableWidth table : Nat) (rowCountTerm : ValuationTerm)
    (rowIndex : Nat)
    (hcanonical : rowIndex + 1 < termValue zeroValuation rowCountTerm ->
      CompactNumericVerifierStepWitnessTableCanonicalAdjacent
        tableWidth table rowIndex) :
    CheckedHybridValuationBoundedFormulaCertificate
      (adjacentRowBranchValuation rowIndex)
      (Rewriting.free
        (compactNumericVerifierStepWitnessTableRowsAdjacentUniversalBody
          tableWidth table (2 ^ tableWidth) rowCountTerm)) := by
  rw [adjacentRowsUniversalBody_free_alignment]
  if hnext : rowIndex + 1 < termValue zeroValuation rowCountTerm then
    exact .disjunctionRight
      (left := ∼adjacentRowsNextGuardFormula rowCountTerm)
      (compactNumericVerifierStepWitnessTableAdjacentRowExplicitHybridCertificate
        tableWidth table rowIndex (hcanonical hnext))
  else
    exact .disjunctionLeft
      (right :=
        compactNumericVerifierStepWitnessTableAdjacentRowAtValuationFormula
          (shortBinaryNumeralTerm tableWidth)
          (shortBinaryNumeralTerm table)
          (shortBinaryNumeralTerm (2 ^ tableWidth))
          (&0 : ValuationTerm))
      (adjacentRowsNextGuardFalseCertificate rowCountTerm rowIndex hnext)

/-- Explicit finite branch closure of the original row-count bounded
universal, from canonical adjacency at every live branch. -/
noncomputable def
    compactNumericVerifierStepWitnessTableRowsAdjacentCanonicalExplicitHybridCertificate
    (tableWidth table : Nat) (rowCountTerm : ValuationTerm)
    (hcanonical : ∀ rowIndex < termValue zeroValuation rowCountTerm,
      rowIndex + 1 < termValue zeroValuation rowCountTerm ->
        CompactNumericVerifierStepWitnessTableCanonicalAdjacent
          tableWidth table rowIndex) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactNumericVerifierStepWitnessTableRowsAdjacentAtValuationFormula
        tableWidth table (2 ^ tableWidth) rowCountTerm) := by
  let body := compactNumericVerifierStepWitnessTableRowsAdjacentUniversalBody
    tableWidth table (2 ^ tableWidth) rowCountTerm
  let rowCount := termValue zeroValuation rowCountTerm
  let branches := buildExplicitHybridUniversalBranches rowCount
    (fun rowIndex hrowIndex =>
      adjacentRowsUniversalBranchCertificate tableWidth table rowCountTerm
        rowIndex (hcanonical rowIndex hrowIndex))
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      rowCountTerm body (by simpa [rowCount] using branches)
  let universal : CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (body.ballLT rowCountTerm) := .cast (by
        change (∀⁰ termBoundedUniversalBody (Rew.bShift rowCountTerm) body) =
          body.ballLT rowCountTerm
        rw [termBoundedUniversal_eq_ball]
        rfl) direct
  exact .cast
    (compactNumericVerifierStepWitnessTableRowsAdjacentAtValuationFormula_alignment
      tableWidth table (2 ^ tableWidth) rowCountTerm).symm universal

/-- Semantic rows-adjacent caller endpoint; witness selection remains the
canonical table decoding used by the single-row constructor. -/
noncomputable def
    compactNumericVerifierStepWitnessTableRowsAdjacentExplicitHybridCertificate
    (tableWidth table : Nat) (rowCountTerm : ValuationTerm)
    (hadjacent : CompactNumericVerifierStepWitnessTableRowsAdjacent
      tableWidth table (termValue zeroValuation rowCountTerm)
        (2 ^ tableWidth)) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactNumericVerifierStepWitnessTableRowsAdjacentAtValuationFormula
        tableWidth table (2 ^ tableWidth) rowCountTerm) := by
  apply
    compactNumericVerifierStepWitnessTableRowsAdjacentCanonicalExplicitHybridCertificate
  intro rowIndex hrowIndex hnext
  exact (compactNumericVerifierStepWitnessTableAdjacentRow_iff_canonical
    tableWidth table rowIndex).mp (hadjacent rowIndex hrowIndex hnext)

/-- Exact valuation-context proof compiled from the explicit row branches. -/
noncomputable def
    compileCompactNumericVerifierStepWitnessTableRowsAdjacentExplicitHybridContext
    (tableWidth table : Nat) (rowCountTerm : ValuationTerm)
    (hadjacent : CompactNumericVerifierStepWitnessTableRowsAdjacent
      tableWidth table (termValue zeroValuation rowCountTerm)
        (2 ^ tableWidth)) :
    CertifiedPAContextProof
      (valuationContext
        (compactNumericVerifierStepWitnessTableRowsAdjacentAtValuationFormula
          tableWidth table (2 ^ tableWidth) rowCountTerm).freeVariables
        zeroValuation)
      (compactNumericVerifierStepWitnessTableRowsAdjacentAtValuationFormula
        tableWidth table (2 ^ tableWidth) rowCountTerm) :=
  (compactNumericVerifierStepWitnessTableRowsAdjacentExplicitHybridCertificate
    tableWidth table rowCountTerm hadjacent).compile

/-- Proof-free recursive structural resource for all explicit row branches. -/
noncomputable def
    compactNumericVerifierStepWitnessTableRowsAdjacentExplicitHybridStructuralResource
    (tableWidth table : Nat) (rowCountTerm : ValuationTerm)
    (hadjacent : CompactNumericVerifierStepWitnessTableRowsAdjacent
      tableWidth table (termValue zeroValuation rowCountTerm)
        (2 ^ tableWidth)) : Nat :=
  CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
    (compactNumericVerifierStepWitnessTableRowsAdjacentExplicitHybridCertificate
      tableWidth table rowCountTerm hadjacent)

theorem
    compileCompactNumericVerifierStepWitnessTableRowsAdjacentExplicitHybridContext_payloadLength_le
    (tableWidth table : Nat) (rowCountTerm : ValuationTerm)
    (hadjacent : CompactNumericVerifierStepWitnessTableRowsAdjacent
      tableWidth table (termValue zeroValuation rowCountTerm)
        (2 ^ tableWidth)) :
    (compileCompactNumericVerifierStepWitnessTableRowsAdjacentExplicitHybridContext
      tableWidth table rowCountTerm hadjacent).payloadLength <=
      compactNumericVerifierStepWitnessTableRowsAdjacentExplicitHybridStructuralResource
        tableWidth table rowCountTerm hadjacent := by
  exact
    CheckedHybridValuationBoundedFormulaCertificate.compile_payloadLength_le_structuralPayloadBound
      (compactNumericVerifierStepWitnessTableRowsAdjacentExplicitHybridCertificate
        tableWidth table rowCountTerm hadjacent)

/-- Canonical bounded-trace endpoint at the concrete row-count numeral. -/
noncomputable def
    compactNumericVerifierBoundedStepWitnessTableRowsAdjacentExplicitHybridCertificate
    (fuel : Nat)
    (start :
      FoundationCompactNumericListedTaskMachine.CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : ∀ offset, offset < fuel ->
      ∃ row :
          FoundationCompactNumericListedDirectVerifierCheckedStepRow.CompactNumericVerifierCheckedStepRow,
        row.currentState =
            FoundationCompactNumericListedDirectTrace.compactNumericVerifierStateAt
              start offset ∧
          row.nextState =
            FoundationCompactNumericListedDirectTrace.compactNumericVerifierStateAt
              start (offset + 1) ∧
          ∀ coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) :
    let rows := compactNumericVerifierBoundedStepFormulaRows fuel start
      coordinateBound hrows
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactNumericVerifierStepWitnessTableRowsAdjacentAtValuationFormula
        tableWidth table (2 ^ tableWidth)
        (shortBinaryNumeralTerm fuel)) := by
  dsimp only
  apply
    compactNumericVerifierStepWitnessTableRowsAdjacentExplicitHybridCertificate
  simpa [termValue_shortBinaryNumeralTerm] using
    compactNumericVerifierBoundedStepWitnessTable_rowsAdjacent
      fuel start coordinateBound hrows

#print axioms
  compileCompactNumericVerifierStepWitnessTableRowsAdjacentExplicitHybridContext_payloadLength_le
#print axioms
  compactNumericVerifierBoundedStepWitnessTableRowsAdjacentExplicitHybridCertificate

end FoundationCompactNumericListedDirectVerifierStepWitnessTableRowsAdjacentExplicitHybridCertificate
