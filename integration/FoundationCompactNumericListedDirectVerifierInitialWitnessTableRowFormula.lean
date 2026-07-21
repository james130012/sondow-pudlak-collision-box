import integration.FoundationCompactNumericListedDirectBoundedVectorQuantifier
import integration.FoundationCompactNumericListedDirectVerifierInitialEnvironmentFormula
import integration.FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
import integration.FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge

/-!
# Row-zero witness-table formula for the exact verifier initial state

Only eleven step-environment columns are needed by the initial condition.
Each is bounded and tied to its exact cell in the 429-column witness table;
the two public input streams are then compared bit-for-bit with the state
prefixes stored in those cells.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierInitialWitnessTableRowFormula

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectBoundedVectorQuantifier
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectVerifierParseTaskHeadFormula
open FoundationCompactNumericListedDirectVerifierInitialEnvironmentFormula
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge

def compactNumericVerifierInitialStepCoordinate : Fin 11 -> Fin 429 :=
  ![0, 1, 2, 3, 5, 7, 10, 11, 13, 15, 21]

def CompactNumericVerifierInitialProjected
    (values : Fin 11 -> Nat)
    (proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) : Prop :=
  CompactFixedWidthCrossTableSlicesEq
      proofTable proofWidth proofTokenCount proofStart proofFinish
      (values 0) (values 1) (values 2) (values 3) (values 4) ∧
    CompactFixedWidthCrossTableSlicesEq
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish
      (values 0) (values 1) (values 2) (values 4) (values 5) ∧
    CompactNumericVerifierParseTaskHead
      (values 0) (values 1) (values 2) (values 7) (values 10) ∧
    values 6 = 1 ∧ values 8 = 0 ∧ values 9 = 0

def CompactNumericVerifierInitialWitnessTableRow
    (tableWidth table valueBound rowIndex
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) : Prop :=
  ∃ values : Fin 11 -> Nat,
    (∀ coordinate, values coordinate ≤ valueBound) ∧
      (∀ coordinate,
        CompactFixedWidthEntry table tableWidth
          (rowIndex * compactNumericVerifierStepWitnessColumnCount +
            (compactNumericVerifierInitialStepCoordinate coordinate).val)
          (values coordinate)) ∧
      CompactNumericVerifierInitialProjected values
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish

private def localVariable (coordinate : Fin 11) : Fin (14 + 11) :=
  Fin.castAdd 14 coordinate

private def globalVariable (coordinate : Fin 14) : Fin (14 + 11) :=
  Fin.natAdd 11 coordinate

@[simp] private theorem localVariable_val
    (values : Fin 11 -> Nat) (global : Fin 14 -> Nat)
    (coordinate : Fin 11) :
    Semiterm.val (Matrix.appendr values global) Empty.elim
        (#(localVariable coordinate) : ArithmeticSemiterm Empty (14 + 11)) =
      values coordinate := by
  simp [localVariable, Matrix.appendr, Matrix.vecAppend_eq_ite]

@[simp] private theorem globalVariable_val
    (values : Fin 11 -> Nat) (global : Fin 14 -> Nat)
    (coordinate : Fin 14) :
    Semiterm.val (Matrix.appendr values global) Empty.elim
        (#(globalVariable coordinate) : ArithmeticSemiterm Empty (14 + 11)) =
      global coordinate := by
  change Matrix.appendr values global (Fin.natAdd 11 coordinate) =
    global coordinate
  simp [Matrix.appendr, Matrix.vecAppend_eq_ite]

private def arithmeticNumeral (value : Nat) :
    ArithmeticSemiterm Empty (14 + 11) :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ value) ![]

private def arithmeticMul
    (left right : ArithmeticSemiterm Empty (14 + 11)) :
    ArithmeticSemiterm Empty (14 + 11) :=
  Semiterm.Operator.Mul.mul.operator ![left, right]

private def arithmeticAdd
    (left right : ArithmeticSemiterm Empty (14 + 11)) :
    ArithmeticSemiterm Empty (14 + 11) :=
  Semiterm.Operator.Add.add.operator ![left, right]

private def arithmeticEq
    (left right : ArithmeticSemiterm Empty (14 + 11)) :
    ArithmeticSemiformula Empty (14 + 11) :=
  Semiformula.Operator.Eq.eq.operator ![left, right]

private def tableIndexTerm (coordinate : Fin 11) :
    ArithmeticSemiterm Empty (14 + 11) :=
  arithmeticAdd
    (arithmeticMul (#(globalVariable 3))
      (arithmeticNumeral compactNumericVerifierStepWitnessColumnCount))
    (arithmeticNumeral
      (compactNumericVerifierInitialStepCoordinate coordinate).val)

private def tableEntryFormula (coordinate : Fin 11) :
    ArithmeticSemiformula Empty (14 + 11) :=
  compactFixedWidthEntryDef.val ⇜
    ![(#(globalVariable 1) : ArithmeticSemiterm Empty (14 + 11)),
      #(globalVariable 0), tableIndexTerm coordinate,
      #(localVariable coordinate)]

private def proofCrossTerms :
    Fin 10 -> ArithmeticSemiterm Empty (14 + 11) :=
  ![(#(globalVariable 4) : ArithmeticSemiterm Empty (14 + 11)),
    #(globalVariable 5), #(globalVariable 6), #(globalVariable 7),
    #(globalVariable 8),
    #(localVariable 0), #(localVariable 1), #(localVariable 2),
    #(localVariable 3), #(localVariable 4)]

private def certificateCrossTerms :
    Fin 10 -> ArithmeticSemiterm Empty (14 + 11) :=
  ![(#(globalVariable 9) : ArithmeticSemiterm Empty (14 + 11)),
    #(globalVariable 10), #(globalVariable 11), #(globalVariable 12),
    #(globalVariable 13),
    #(localVariable 0), #(localVariable 1), #(localVariable 2),
    #(localVariable 4), #(localVariable 5)]

private def parseTaskTerms :
    Fin 5 -> ArithmeticSemiterm Empty (14 + 11) :=
  ![(#(localVariable 0) : ArithmeticSemiterm Empty (14 + 11)),
    #(localVariable 1), #(localVariable 2),
    #(localVariable 7), #(localVariable 10)]

private def projectedFormula : ArithmeticSemiformula Empty (14 + 11) :=
  [compactFixedWidthCrossTableSlicesEqDef.val ⇜ proofCrossTerms,
    compactFixedWidthCrossTableSlicesEqDef.val ⇜ certificateCrossTerms,
    compactNumericVerifierParseTaskHeadDef.val ⇜ parseTaskTerms,
    arithmeticEq (#(localVariable 6)) (arithmeticNumeral 1),
    arithmeticEq (#(localVariable 8)) (arithmeticNumeral 0),
    arithmeticEq (#(localVariable 9)) (arithmeticNumeral 0)].conj₂

private def coreFormula : ArithmeticSemiformula Empty (14 + 11) :=
  (List.ofFn tableEntryFormula).conj₂ ⋏ projectedFormula

@[simp] private theorem arithmeticNumeral_val
    (values : Fin 11 -> Nat) (global : Fin 14 -> Nat) (value : Nat) :
    (arithmeticNumeral value).val
        (Matrix.appendr values global) Empty.elim = value := by
  simp [arithmeticNumeral]

@[simp] private theorem arithmeticMul_val
    (values : Fin 11 -> Nat) (global : Fin 14 -> Nat)
    (left right : ArithmeticSemiterm Empty (14 + 11)) :
    (arithmeticMul left right).val
        (Matrix.appendr values global) Empty.elim =
      left.val (Matrix.appendr values global) Empty.elim *
        right.val (Matrix.appendr values global) Empty.elim := by
  simp [arithmeticMul]

@[simp] private theorem arithmeticAdd_val
    (values : Fin 11 -> Nat) (global : Fin 14 -> Nat)
    (left right : ArithmeticSemiterm Empty (14 + 11)) :
    (arithmeticAdd left right).val
        (Matrix.appendr values global) Empty.elim =
      left.val (Matrix.appendr values global) Empty.elim +
        right.val (Matrix.appendr values global) Empty.elim := by
  simp [arithmeticAdd]

@[simp] private theorem arithmeticEq_eval
    (values : Fin 11 -> Nat) (global : Fin 14 -> Nat)
    (left right : ArithmeticSemiterm Empty (14 + 11)) :
    (arithmeticEq left right).Evalb (Matrix.appendr values global) ↔
      left.val (Matrix.appendr values global) Empty.elim =
        right.val (Matrix.appendr values global) Empty.elim := by
  simp [arithmeticEq]

@[simp] private theorem tableIndexTerm_val
    (values : Fin 11 -> Nat) (global : Fin 14 -> Nat)
    (coordinate : Fin 11) :
    (tableIndexTerm coordinate).val
        (Matrix.appendr values global) Empty.elim =
      global 3 * compactNumericVerifierStepWitnessColumnCount +
        (compactNumericVerifierInitialStepCoordinate coordinate).val := by
  simp only [tableIndexTerm, arithmeticAdd_val, arithmeticMul_val,
    globalVariable_val, arithmeticNumeral_val]

@[simp] private theorem tableEntryFormula_eval
    (values : Fin 11 -> Nat) (global : Fin 14 -> Nat)
    (coordinate : Fin 11) :
    (tableEntryFormula coordinate).Evalb
        (Matrix.appendr values global) ↔
      CompactFixedWidthEntry (global 1) (global 0)
        (global 3 * compactNumericVerifierStepWitnessColumnCount +
          (compactNumericVerifierInitialStepCoordinate coordinate).val)
        (values coordinate) := by
  rw [show tableEntryFormula coordinate =
      compactFixedWidthEntryDef.val ⇜
        ![(#(globalVariable 1) : ArithmeticSemiterm Empty (14 + 11)),
          #(globalVariable 0), tableIndexTerm coordinate,
          #(localVariable coordinate)] by rfl]
  rw [Semiformula.eval_substs]
  have henv :
      (Semiterm.val (Matrix.appendr values global) Empty.elim ∘
        ![(#(globalVariable 1) : ArithmeticSemiterm Empty (14 + 11)),
          #(globalVariable 0), tableIndexTerm coordinate,
          #(localVariable coordinate)]) =
        ![global 1, global 0,
          global 3 * compactNumericVerifierStepWitnessColumnCount +
            (compactNumericVerifierInitialStepCoordinate coordinate).val,
          values coordinate] := by
    funext index
    fin_cases index
    · change Semiterm.val (Matrix.appendr values global) Empty.elim
        (#(globalVariable 1) : ArithmeticSemiterm Empty (14 + 11)) = global 1
      exact globalVariable_val values global 1
    · change Semiterm.val (Matrix.appendr values global) Empty.elim
        (#(globalVariable 0) : ArithmeticSemiterm Empty (14 + 11)) = global 0
      exact globalVariable_val values global 0
    · exact tableIndexTerm_val values global coordinate
    · change Semiterm.val (Matrix.appendr values global) Empty.elim
        (#(localVariable coordinate) : ArithmeticSemiterm Empty (14 + 11)) =
          values coordinate
      exact localVariable_val values global coordinate
  rw [henv]
  exact compactFixedWidthEntryDef_spec
    (global 1) (global 0)
    (global 3 * compactNumericVerifierStepWitnessColumnCount +
      (compactNumericVerifierInitialStepCoordinate coordinate).val)
    (values coordinate)

private theorem proofCrossFormula_eval
    (values : Fin 11 -> Nat) (global : Fin 14 -> Nat) :
    (compactFixedWidthCrossTableSlicesEqDef.val ⇜ proofCrossTerms).Evalb
        (Matrix.appendr values global) ↔
      CompactFixedWidthCrossTableSlicesEq
        (global 4) (global 5) (global 6) (global 7) (global 8)
        (values 0) (values 1) (values 2) (values 3) (values 4) := by
  rw [Semiformula.eval_substs]
  have henv :
      (Semiterm.val (Matrix.appendr values global) Empty.elim ∘
        proofCrossTerms) =
        ![global 4, global 5, global 6, global 7, global 8,
          values 0, values 1, values 2, values 3, values 4] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [henv]
  exact compactFixedWidthCrossTableSlicesEqDef_spec
    (global 4) (global 5) (global 6) (global 7) (global 8)
    (values 0) (values 1) (values 2) (values 3) (values 4)

private theorem certificateCrossFormula_eval
    (values : Fin 11 -> Nat) (global : Fin 14 -> Nat) :
    (compactFixedWidthCrossTableSlicesEqDef.val ⇜
        certificateCrossTerms).Evalb (Matrix.appendr values global) ↔
      CompactFixedWidthCrossTableSlicesEq
        (global 9) (global 10) (global 11) (global 12) (global 13)
        (values 0) (values 1) (values 2) (values 4) (values 5) := by
  rw [Semiformula.eval_substs]
  have henv :
      (Semiterm.val (Matrix.appendr values global) Empty.elim ∘
        certificateCrossTerms) =
        ![global 9, global 10, global 11, global 12, global 13,
          values 0, values 1, values 2, values 4, values 5] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [henv]
  exact compactFixedWidthCrossTableSlicesEqDef_spec
    (global 9) (global 10) (global 11) (global 12) (global 13)
    (values 0) (values 1) (values 2) (values 4) (values 5)

private theorem parseTaskFormula_eval
    (values : Fin 11 -> Nat) (global : Fin 14 -> Nat) :
    (compactNumericVerifierParseTaskHeadDef.val ⇜ parseTaskTerms).Evalb
        (Matrix.appendr values global) ↔
      CompactNumericVerifierParseTaskHead
        (values 0) (values 1) (values 2) (values 7) (values 10) := by
  rw [Semiformula.eval_substs]
  have henv :
      (Semiterm.val (Matrix.appendr values global) Empty.elim ∘
        parseTaskTerms) =
        ![values 0, values 1, values 2, values 7, values 10] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [henv]
  exact compactNumericVerifierParseTaskHeadDef_spec
    (values 0) (values 1) (values 2) (values 7) (values 10)

private theorem projectedFormula_eval
    (values : Fin 11 -> Nat) (global : Fin 14 -> Nat) :
    projectedFormula.Evalb (Matrix.appendr values global) ↔
      CompactNumericVerifierInitialProjected values
        (global 4) (global 5) (global 6) (global 7) (global 8)
        (global 9) (global 10) (global 11) (global 12) (global 13) := by
  change
    ((compactFixedWidthCrossTableSlicesEqDef.val ⇜ proofCrossTerms).Evalb _ ∧
      (compactFixedWidthCrossTableSlicesEqDef.val ⇜
        certificateCrossTerms).Evalb _ ∧
      (compactNumericVerifierParseTaskHeadDef.val ⇜ parseTaskTerms).Evalb _ ∧
      (arithmeticEq (#(localVariable 6))
        (arithmeticNumeral 1)).Evalb (Matrix.appendr values global) ∧
      (arithmeticEq (#(localVariable 8))
        (arithmeticNumeral 0)).Evalb (Matrix.appendr values global) ∧
      (arithmeticEq (#(localVariable 9))
        (arithmeticNumeral 0)).Evalb (Matrix.appendr values global)) ↔ _
  rw [proofCrossFormula_eval, certificateCrossFormula_eval,
    parseTaskFormula_eval]
  simp only [arithmeticEq_eval, localVariable_val, arithmeticNumeral_val]
  rfl

private theorem coreFormula_eval
    (values : Fin 11 -> Nat) (global : Fin 14 -> Nat) :
    coreFormula.Evalb (Matrix.appendr values global) ↔
      (∀ coordinate,
        CompactFixedWidthEntry (global 1) (global 0)
          (global 3 * compactNumericVerifierStepWitnessColumnCount +
            (compactNumericVerifierInitialStepCoordinate coordinate).val)
          (values coordinate)) ∧
      CompactNumericVerifierInitialProjected values
        (global 4) (global 5) (global 6) (global 7) (global 8)
        (global 9) (global 10) (global 11) (global 12) (global 13) := by
  change
    ((List.ofFn tableEntryFormula).conj₂.Evalb
        (Matrix.appendr values global) ∧
      projectedFormula.Evalb (Matrix.appendr values global)) ↔ _
  rw [List.map_conj₂_prop, List.forall_mem_ofFn_iff, projectedFormula_eval]
  simp only [tableEntryFormula_eval]

private theorem coreFormula_sigmaZero :
    Hierarchy Polarity.sigma 0 coreFormula := by
  rw [show coreFormula =
      (List.ofFn tableEntryFormula).conj₂ ⋏ projectedFormula by rfl]
  rw [Hierarchy.and_iff, Hierarchy.list_conj₂_iff,
    List.forall_mem_ofFn_iff]
  constructor
  · intro coordinate
    simp [tableEntryFormula, tableIndexTerm,
      arithmeticAdd, arithmeticMul, arithmeticNumeral]
  · simp [projectedFormula, proofCrossTerms, certificateCrossTerms,
      parseTaskTerms, arithmeticEq, arithmeticNumeral]

def compactNumericVerifierInitialWitnessTableRowDef :
    HierarchySymbol.sigmaZero.Semisentence 14 := .mkSigma
  (boundedVectorBExs (#2 : ArithmeticSemiterm Empty 14) 11 coreFormula)
  (boundedVectorBExs_sigmaZero
    (#2 : ArithmeticSemiterm Empty 14) coreFormula coreFormula_sigmaZero)

@[simp] theorem compactNumericVerifierInitialWitnessTableRowDef_spec
    (tableWidth table valueBound rowIndex
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) :
    compactNumericVerifierInitialWitnessTableRowDef.val.Evalb
        ![tableWidth, table, valueBound, rowIndex,
          proofTable, proofWidth, proofTokenCount, proofStart, proofFinish,
          certificateTable, certificateWidth, certificateTokenCount,
          certificateStart, certificateFinish] ↔
      CompactNumericVerifierInitialWitnessTableRow
        tableWidth table valueBound rowIndex
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish := by
  rw [show compactNumericVerifierInitialWitnessTableRowDef.val =
      boundedVectorBExs (#2 : ArithmeticSemiterm Empty 14) 11 coreFormula by rfl]
  rw [evalb_boundedVectorBExs]
  change
    (∃ values : Fin 11 -> Nat,
      (∀ coordinate, values coordinate ≤ valueBound) ∧
        coreFormula.Evalb
          (Matrix.appendr values
            ![tableWidth, table, valueBound, rowIndex,
              proofTable, proofWidth, proofTokenCount, proofStart, proofFinish,
              certificateTable, certificateWidth, certificateTokenCount,
              certificateStart, certificateFinish])) ↔ _
  simp only [coreFormula_eval]
  rfl

theorem compactNumericVerifierInitialWitnessTableRowDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierInitialWitnessTableRowDef.val :=
  compactNumericVerifierInitialWitnessTableRowDef.sigma_prop

private theorem projected_eq_environment
    (environment : Fin 429 -> Nat) (values : Fin 11 -> Nat)
    (heq : ∀ coordinate,
      environment (compactNumericVerifierInitialStepCoordinate coordinate) =
        values coordinate)
    (proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) :
    CompactNumericVerifierInitialProjected values
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish ↔
      CompactNumericVerifierInitialEnvironment environment
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish := by
  have h0 := heq 0
  have h1 := heq 1
  have h2 := heq 2
  have h3 := heq 3
  have h4 := heq 4
  have h5 := heq 5
  have h6 := heq 6
  have h7 := heq 7
  have h8 := heq 8
  have h9 := heq 9
  have h10 := heq 10
  change environment 0 = values 0 at h0
  change environment 1 = values 1 at h1
  change environment 2 = values 2 at h2
  change environment 3 = values 3 at h3
  change environment 5 = values 4 at h4
  change environment 7 = values 5 at h5
  change environment 10 = values 6 at h6
  change environment 11 = values 7 at h7
  change environment 13 = values 8 at h8
  change environment 15 = values 9 at h9
  change environment 21 = values 10 at h10
  unfold CompactNumericVerifierInitialProjected
    CompactNumericVerifierInitialEnvironment
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5,
    ← h6, ← h7, ← h8, ← h9, ← h10]

theorem CompactNumericVerifierInitialWitnessTableRow.to_environment
    {tableWidth table valueBound rowIndex
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    (hbounded : CompactNumericVerifierStepWitnessTableBoundedRow
      tableWidth table valueBound rowIndex)
    (hinitial : CompactNumericVerifierInitialWitnessTableRow
      tableWidth table valueBound rowIndex
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish) :
    ∃ environment : Fin 429 -> Nat,
      compactNumericVerifierStepGraphDef.val.Evalb environment ∧
      CompactNumericVerifierInitialEnvironment environment
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish := by
  rcases hbounded with ⟨environment, _hbound, hentries, hformula⟩
  rcases hinitial with ⟨values, _hvaluesBound, hvalueEntries, hprojected⟩
  have heq (coordinate : Fin 11) :
      environment (compactNumericVerifierInitialStepCoordinate coordinate) =
        values coordinate :=
    (CompactFixedWidthEntry.value_eq_tableValue
      (hentries (compactNumericVerifierInitialStepCoordinate coordinate))).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        (hvalueEntries coordinate)).symm
  refine ⟨environment, hformula, ?_⟩
  exact (projected_eq_environment environment values heq
    proofTable proofWidth proofTokenCount proofStart proofFinish
    certificateTable certificateWidth certificateTokenCount
    certificateStart certificateFinish).mp hprojected

theorem CompactNumericVerifierInitialEnvironment.to_witnessTableRow
    {tableWidth table valueBound rowIndex
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    {environment : Fin 429 -> Nat}
    (hbound : ∀ coordinate, environment coordinate ≤ valueBound)
    (hentries : ∀ coordinate,
      CompactFixedWidthEntry table tableWidth
        (rowIndex * compactNumericVerifierStepWitnessColumnCount + coordinate.val)
        (environment coordinate))
    (hinitial : CompactNumericVerifierInitialEnvironment environment
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish) :
    CompactNumericVerifierInitialWitnessTableRow
      tableWidth table valueBound rowIndex
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish := by
  let values : Fin 11 -> Nat := fun coordinate =>
    environment (compactNumericVerifierInitialStepCoordinate coordinate)
  refine ⟨values, ?_, ?_, ?_⟩
  · intro coordinate
    exact hbound _
  · intro coordinate
    exact hentries _
  · apply (projected_eq_environment environment values ?_
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish).mpr hinitial
    intro coordinate
    rfl

theorem CompactNumericVerifierInitialWitnessTableRow.canonical_environment
    {tableWidth table valueBound rowIndex
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    (hinitial : CompactNumericVerifierInitialWitnessTableRow
      tableWidth table valueBound rowIndex
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish) :
    CompactNumericVerifierInitialEnvironment
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table rowIndex)
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish := by
  rcases hinitial with
    ⟨values, _hvaluesBound, hvalueEntries, hprojected⟩
  let environment := compactNumericVerifierStepWitnessTableFormulaEnvironment
    tableWidth table rowIndex
  have heq (coordinate : Fin 11) :
      environment (compactNumericVerifierInitialStepCoordinate coordinate) =
        values coordinate := by
    change compactNumericVerifierStepWitnessTableColumnValue
        tableWidth table rowIndex
          (compactNumericVerifierInitialStepCoordinate coordinate).val =
      values coordinate
    exact
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue
        (hvalueEntries coordinate)).symm
  exact (projected_eq_environment environment values heq
    proofTable proofWidth proofTokenCount proofStart proofFinish
    certificateTable certificateWidth certificateTokenCount
    certificateStart certificateFinish).mp hprojected

#print axioms compactNumericVerifierInitialWitnessTableRowDef_spec
#print axioms compactNumericVerifierInitialWitnessTableRowDef_sigmaZero
#print axioms CompactNumericVerifierInitialWitnessTableRow.to_environment
#print axioms CompactNumericVerifierInitialEnvironment.to_witnessTableRow
#print axioms
  CompactNumericVerifierInitialWitnessTableRow.canonical_environment

end FoundationCompactNumericListedDirectVerifierInitialWitnessTableRowFormula
