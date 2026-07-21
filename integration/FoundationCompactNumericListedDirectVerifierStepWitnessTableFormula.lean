import integration.FoundationCompactNumericListedDirectBoundedVectorQuantifier
import integration.FoundationCompactNumericListedDirectVerifierStepWitnessTable

/-!
# Bounded arithmetic formula for complete verifier-step witness rows

The formula binds all 429 values of one witness row under one explicit bound,
ties every value to its fixed-width table cell, and then evaluates the exact
complete verifier-step formula on those same values.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectBoundedVectorQuantifier
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTable

def CompactNumericVerifierStepWitnessTableBoundedRow
    (tableWidth table valueBound rowIndex : Nat) : Prop :=
  ∃ environment : Fin 429 -> Nat,
    (∀ coordinate, environment coordinate ≤ valueBound) ∧
      (∀ coordinate,
        CompactFixedWidthEntry table tableWidth
          (rowIndex * compactNumericVerifierStepWitnessColumnCount +
            coordinate.val)
          (environment coordinate)) ∧
      compactNumericVerifierStepGraphDef.val.Evalb environment

def CompactNumericVerifierStepWitnessTableBoundedGraph
    (tableWidth table rowCount valueBound : Nat) : Prop :=
  ∀ rowIndex < rowCount,
    CompactNumericVerifierStepWitnessTableBoundedRow
      tableWidth table valueBound rowIndex

private def witnessVariable (coordinate : Fin 429) : Fin (4 + 429) :=
  Fin.castAdd 4 coordinate

private def globalVariable (coordinate : Fin 4) : Fin (4 + 429) :=
  Fin.natAdd 429 coordinate

@[simp] private theorem witnessVariable_val
    (witnesses : Fin 429 -> Nat) (global : Fin 4 -> Nat)
    (coordinate : Fin 429) :
    Semiterm.val (Matrix.appendr witnesses global) Empty.elim
        (#(witnessVariable coordinate) : ArithmeticSemiterm Empty (4 + 429)) =
      witnesses coordinate := by
  simp [witnessVariable, Matrix.appendr, Matrix.vecAppend_eq_ite]

set_option maxRecDepth 4096 in
@[simp] private theorem globalVariable_val
    (witnesses : Fin 429 -> Nat) (global : Fin 4 -> Nat)
    (coordinate : Fin 4) :
    Semiterm.val (Matrix.appendr witnesses global) Empty.elim
      (#(globalVariable coordinate) : ArithmeticSemiterm Empty (4 + 429)) =
      global coordinate := by
  change Matrix.appendr witnesses global (Fin.natAdd 429 coordinate) =
    global coordinate
  simp [Matrix.appendr, Matrix.vecAppend_eq_ite]

private def arithmeticNumeral
    (value : Nat) : ArithmeticSemiterm Empty (4 + 429) :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ value) ![]

private def arithmeticMul
    (left right : ArithmeticSemiterm Empty (4 + 429)) :
    ArithmeticSemiterm Empty (4 + 429) :=
  Semiterm.Operator.Mul.mul.operator ![left, right]

private def arithmeticAdd
    (left right : ArithmeticSemiterm Empty (4 + 429)) :
    ArithmeticSemiterm Empty (4 + 429) :=
  Semiterm.Operator.Add.add.operator ![left, right]

private def witnessTableIndexTerm (coordinate : Fin 429) :
    ArithmeticSemiterm Empty (4 + 429) :=
  arithmeticAdd
    (arithmeticMul
      (#(globalVariable 3) : ArithmeticSemiterm Empty (4 + 429))
      (arithmeticNumeral compactNumericVerifierStepWitnessColumnCount))
    (arithmeticNumeral coordinate.val)

@[simp] private theorem arithmeticNumeral_val
    (witnesses : Fin 429 -> Nat) (global : Fin 4 -> Nat)
    (value : Nat) :
    (arithmeticNumeral value).val
        (Matrix.appendr witnesses global) Empty.elim = value := by
  simp [arithmeticNumeral]

@[simp] private theorem arithmeticMul_val
    (witnesses : Fin 429 -> Nat) (global : Fin 4 -> Nat)
    (left right : ArithmeticSemiterm Empty (4 + 429)) :
    (arithmeticMul left right).val
        (Matrix.appendr witnesses global) Empty.elim =
      left.val (Matrix.appendr witnesses global) Empty.elim *
        right.val (Matrix.appendr witnesses global) Empty.elim := by
  simp [arithmeticMul]

@[simp] private theorem arithmeticAdd_val
    (witnesses : Fin 429 -> Nat) (global : Fin 4 -> Nat)
    (left right : ArithmeticSemiterm Empty (4 + 429)) :
    (arithmeticAdd left right).val
        (Matrix.appendr witnesses global) Empty.elim =
      left.val (Matrix.appendr witnesses global) Empty.elim +
        right.val (Matrix.appendr witnesses global) Empty.elim := by
  simp [arithmeticAdd]

@[simp] private theorem witnessTableIndexTerm_val
    (witnesses : Fin 429 -> Nat) (global : Fin 4 -> Nat)
    (coordinate : Fin 429) :
    (witnessTableIndexTerm coordinate).val
        (Matrix.appendr witnesses global) Empty.elim =
      global 3 * compactNumericVerifierStepWitnessColumnCount +
        coordinate.val := by
  simp only [witnessTableIndexTerm, arithmeticAdd_val, arithmeticMul_val,
    arithmeticNumeral_val, globalVariable_val]

private def compactNumericVerifierStepWitnessTableEntryFormula
    (coordinate : Fin 429) :
    ArithmeticSemiformula Empty (4 + 429) :=
  compactFixedWidthEntryDef.val ⇜
    ![(#(globalVariable 1) : ArithmeticSemiterm Empty (4 + 429)),
      (#(globalVariable 0) : ArithmeticSemiterm Empty (4 + 429)),
      witnessTableIndexTerm coordinate,
      (#(witnessVariable coordinate) :
        ArithmeticSemiterm Empty (4 + 429))]

private def compactNumericVerifierStepFormulaOnWitnesses :
    ArithmeticSemiformula Empty (4 + 429) :=
  compactNumericVerifierStepGraphDef.val ⇜
    fun coordinate =>
      (#(witnessVariable coordinate) :
        ArithmeticSemiterm Empty (4 + 429))

private def compactNumericVerifierStepWitnessTableRowCoreFormula :
    ArithmeticSemiformula Empty (4 + 429) :=
  (List.ofFn compactNumericVerifierStepWitnessTableEntryFormula).conj₂ ⋏
    compactNumericVerifierStepFormulaOnWitnesses

private theorem compactNumericVerifierStepWitnessTableEntryFormula_sigmaZero
    (coordinate : Fin 429) :
    Hierarchy Polarity.sigma 0
      (compactNumericVerifierStepWitnessTableEntryFormula coordinate) := by
  simp [compactNumericVerifierStepWitnessTableEntryFormula]

private theorem compactNumericVerifierStepFormulaOnWitnesses_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierStepFormulaOnWitnesses := by
  simp [compactNumericVerifierStepFormulaOnWitnesses]

private theorem compactNumericVerifierStepWitnessTableRowCoreFormula_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierStepWitnessTableRowCoreFormula := by
  rw [show compactNumericVerifierStepWitnessTableRowCoreFormula =
      (List.ofFn
          compactNumericVerifierStepWitnessTableEntryFormula).conj₂ ⋏
        compactNumericVerifierStepFormulaOnWitnesses by rfl]
  rw [Hierarchy.and_iff, Hierarchy.list_conj₂_iff,
    List.forall_mem_ofFn_iff]
  exact ⟨compactNumericVerifierStepWitnessTableEntryFormula_sigmaZero,
    compactNumericVerifierStepFormulaOnWitnesses_sigmaZero⟩

def compactNumericVerifierStepWitnessTableBoundedRowDef :
    𝚺₀.Semisentence 4 :=
  .mkSigma
    (boundedVectorBExs (#2 : ArithmeticSemiterm Empty 4) 429
      compactNumericVerifierStepWitnessTableRowCoreFormula)
    (boundedVectorBExs_sigmaZero
      (#2 : ArithmeticSemiterm Empty 4)
      compactNumericVerifierStepWitnessTableRowCoreFormula
      compactNumericVerifierStepWitnessTableRowCoreFormula_sigmaZero)

private theorem compactFixedWidthEntryDef_eval_env
    (env : Fin 4 -> Nat) :
    compactFixedWidthEntryDef.val.Evalb env ↔
      CompactFixedWidthEntry (env 0) (env 1) (env 2) (env 3) := by
  let table := env 0
  let width := env 1
  let index := env 2
  let value := env 3
  have henv : env = ![table, width, index, value] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [henv]
  exact compactFixedWidthEntryDef_spec table width index value

private theorem compactNumericVerifierStepWitnessTableEntryFormula_eval
    (witnesses : Fin 429 -> Nat) (global : Fin 4 -> Nat)
    (coordinate : Fin 429) :
    (compactNumericVerifierStepWitnessTableEntryFormula coordinate).Evalb
        (Matrix.appendr witnesses global) ↔
      CompactFixedWidthEntry (global 1) (global 0)
        (global 3 * compactNumericVerifierStepWitnessColumnCount +
          coordinate.val)
        (witnesses coordinate) := by
  rw [show compactNumericVerifierStepWitnessTableEntryFormula coordinate =
      compactFixedWidthEntryDef.val ⇜
        ![(#(globalVariable 1) : ArithmeticSemiterm Empty (4 + 429)),
          (#(globalVariable 0) : ArithmeticSemiterm Empty (4 + 429)),
          witnessTableIndexTerm coordinate,
          (#(witnessVariable coordinate) :
            ArithmeticSemiterm Empty (4 + 429))] by rfl]
  rw [Semiformula.eval_substs]
  have henv :
      (Semiterm.val (Matrix.appendr witnesses global) Empty.elim ∘
        ![(#(globalVariable 1) : ArithmeticSemiterm Empty (4 + 429)),
          (#(globalVariable 0) : ArithmeticSemiterm Empty (4 + 429)),
          witnessTableIndexTerm coordinate,
          (#(witnessVariable coordinate) :
            ArithmeticSemiterm Empty (4 + 429))]) =
        ![global 1, global 0,
          global 3 * compactNumericVerifierStepWitnessColumnCount +
            coordinate.val,
          witnesses coordinate] := by
    funext index
    fin_cases index
    · change Semiterm.val (Matrix.appendr witnesses global) Empty.elim
        (#(globalVariable 1) : ArithmeticSemiterm Empty (4 + 429)) =
          global 1
      exact globalVariable_val witnesses global 1
    · change Semiterm.val (Matrix.appendr witnesses global) Empty.elim
        (#(globalVariable 0) : ArithmeticSemiterm Empty (4 + 429)) =
          global 0
      exact globalVariable_val witnesses global 0
    · exact witnessTableIndexTerm_val witnesses global coordinate
    · change Semiterm.val (Matrix.appendr witnesses global) Empty.elim
        (#(witnessVariable coordinate) :
          ArithmeticSemiterm Empty (4 + 429)) = witnesses coordinate
      exact witnessVariable_val witnesses global coordinate
  rw [henv]
  exact compactFixedWidthEntryDef_spec
    (global 1) (global 0)
    (global 3 * compactNumericVerifierStepWitnessColumnCount + coordinate.val)
    (witnesses coordinate)

private theorem compactNumericVerifierStepFormulaOnWitnesses_eval
    (witnesses : Fin 429 -> Nat) (global : Fin 4 -> Nat) :
    compactNumericVerifierStepFormulaOnWitnesses.Evalb
        (Matrix.appendr witnesses global) ↔
      compactNumericVerifierStepGraphDef.val.Evalb witnesses := by
  rw [show compactNumericVerifierStepFormulaOnWitnesses =
      compactNumericVerifierStepGraphDef.val ⇜
        (fun coordinate =>
          (#(witnessVariable coordinate) :
            ArithmeticSemiterm Empty (4 + 429))) by rfl]
  rw [Semiformula.eval_substs]
  have henv :
      (Semiterm.val (Matrix.appendr witnesses global) Empty.elim ∘
        fun coordinate =>
          (#(witnessVariable coordinate) :
            ArithmeticSemiterm Empty (4 + 429))) = witnesses := by
    funext coordinate
    exact witnessVariable_val witnesses global coordinate
  rw [henv]

private theorem compactNumericVerifierStepWitnessTableRowCoreFormula_eval
    (witnesses : Fin 429 -> Nat) (global : Fin 4 -> Nat) :
    compactNumericVerifierStepWitnessTableRowCoreFormula.Evalb
        (Matrix.appendr witnesses global) ↔
      (∀ coordinate,
        CompactFixedWidthEntry (global 1) (global 0)
          (global 3 * compactNumericVerifierStepWitnessColumnCount +
            coordinate.val)
          (witnesses coordinate)) ∧
        compactNumericVerifierStepGraphDef.val.Evalb witnesses := by
  change
    ((List.ofFn compactNumericVerifierStepWitnessTableEntryFormula).conj₂.Evalb
        (Matrix.appendr witnesses global) ∧
      compactNumericVerifierStepFormulaOnWitnesses.Evalb
        (Matrix.appendr witnesses global)) ↔ _
  rw [List.map_conj₂_prop, List.forall_mem_ofFn_iff,
    compactNumericVerifierStepFormulaOnWitnesses_eval]
  simp only [compactNumericVerifierStepWitnessTableEntryFormula_eval]

set_option maxRecDepth 8192 in
@[simp] theorem compactNumericVerifierStepWitnessTableBoundedRowDef_spec
    (tableWidth table valueBound rowIndex : Nat) :
    compactNumericVerifierStepWitnessTableBoundedRowDef.val.Evalb
        ![tableWidth, table, valueBound, rowIndex] ↔
      CompactNumericVerifierStepWitnessTableBoundedRow
        tableWidth table valueBound rowIndex := by
  rw [show compactNumericVerifierStepWitnessTableBoundedRowDef.val =
      boundedVectorBExs (#2)
        429
        compactNumericVerifierStepWitnessTableRowCoreFormula by rfl]
  rw [evalb_boundedVectorBExs]
  change
    (∃ witnesses : Fin 429 -> Nat,
      (∀ coordinate, witnesses coordinate ≤ valueBound) ∧
        compactNumericVerifierStepWitnessTableRowCoreFormula.Evalb
          (Matrix.appendr witnesses
            ![tableWidth, table, valueBound, rowIndex])) ↔ _
  constructor
  · rintro ⟨witnesses, hbound, hcore⟩
    rcases
        (compactNumericVerifierStepWitnessTableRowCoreFormula_eval
          witnesses ![tableWidth, table, valueBound, rowIndex]).mp hcore with
      ⟨hentries, hformula⟩
    exact ⟨witnesses, hbound, by simpa using hentries, hformula⟩
  · rintro ⟨witnesses, hbound, hentries, hformula⟩
    refine ⟨witnesses, hbound, ?_⟩
    apply
      (compactNumericVerifierStepWitnessTableRowCoreFormula_eval
        witnesses ![tableWidth, table, valueBound, rowIndex]).mpr
    exact ⟨by simpa using hentries, hformula⟩

def compactNumericVerifierStepWitnessTableBoundedGraphDef :
    𝚺₀.Semisentence 4 := .mkSigma
  “tableWidth table rowCount valueBound.
    ∀ rowIndex < rowCount,
      !(compactNumericVerifierStepWitnessTableBoundedRowDef)
        tableWidth table valueBound rowIndex”

@[simp] theorem compactNumericVerifierStepWitnessTableBoundedGraphDef_spec
    (tableWidth table rowCount valueBound : Nat) :
    compactNumericVerifierStepWitnessTableBoundedGraphDef.val.Evalb
        ![tableWidth, table, rowCount, valueBound] ↔
      CompactNumericVerifierStepWitnessTableBoundedGraph
        tableWidth table rowCount valueBound := by
  simp [compactNumericVerifierStepWitnessTableBoundedGraphDef,
    CompactNumericVerifierStepWitnessTableBoundedGraph]

theorem compactNumericVerifierStepWitnessTableBoundedRowDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierStepWitnessTableBoundedRowDef.val := by
  exact compactNumericVerifierStepWitnessTableBoundedRowDef.sigma_prop

theorem compactNumericVerifierStepWitnessTableBoundedGraphDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierStepWitnessTableBoundedGraphDef.val := by
  simp [compactNumericVerifierStepWitnessTableBoundedGraphDef]

#print axioms compactNumericVerifierStepWitnessTableBoundedRowDef_spec
#print axioms compactNumericVerifierStepWitnessTableBoundedGraphDef_spec
#print axioms compactNumericVerifierStepWitnessTableBoundedRowDef_sigmaZero
#print axioms compactNumericVerifierStepWitnessTableBoundedGraphDef_sigmaZero

end FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
