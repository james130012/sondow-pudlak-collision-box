import integration.FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectCrossTableSliceExplicitHybridCertificate
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceTableClosedDecomposition

/-!
# Explicit hybrid certificate for the verifier initial witness-table row

The eleven outer witnesses are the canonical decoded values of row zero at
columns `0, 1, 2, 3, 5, 7, 10, 11, 13, 15, 21`.  The parse-task witnesses are
supplied independently and explicitly; no witness is selected from the
semantic parse predicate contained in the initial-environment hypothesis.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierInitialWitnessTableRowExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectBoundedVectorQuantifier
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectCrossTableSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierParseTaskHeadFormula
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierInitialEnvironmentFormula
open FoundationCompactNumericListedDirectVerifierInitialWitnessTableRowFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge
open FoundationCompactNumericListedDirectVerifierAcceptedTraceTableClosedDecomposition
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAFixedWidthEntryHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

private def initialRowZeroValuation : Nat -> Nat := fun _ => 0

private abbrev InitialRowHybridCertificate
    (formula : ArithmeticProposition) :=
  CheckedHybridValuationBoundedFormulaCertificate
    initialRowZeroValuation formula

private def localVariable (coordinate : Fin 11) : Fin (14 + 11) :=
  Fin.castAdd 14 coordinate

private def globalVariable (coordinate : Fin 14) : Fin (14 + 11) :=
  Fin.natAdd 11 coordinate

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

/-- A public, definitionally exact copy of the source definition's private
`14 + 11` matrix. -/
def compactNumericVerifierInitialWitnessTableRowRawCore :
    ArithmeticSemiformula Empty (14 + 11) :=
  (List.ofFn tableEntryFormula).conj₂ ⋏ projectedFormula

theorem compactNumericVerifierInitialWitnessTableRowDef_val_eq_boundedVector :
    compactNumericVerifierInitialWitnessTableRowDef.val =
      boundedVectorBExs (#2 : ArithmeticSemiterm Empty 14) 11
        compactNumericVerifierInitialWitnessTableRowRawCore := by
  rfl

private def initialRowGlobalTerms
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) : Fin 14 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tableWidth,
    shortBinaryNumeralTerm table,
    shortBinaryNumeralTerm valueBound,
    (‘0’ : ValuationTerm),
    shortBinaryNumeralTerm proofTable,
    shortBinaryNumeralTerm proofWidth,
    shortBinaryNumeralTerm proofTokenCount,
    shortBinaryNumeralTerm proofStart,
    shortBinaryNumeralTerm proofFinish,
    shortBinaryNumeralTerm certificateTable,
    shortBinaryNumeralTerm certificateWidth,
    shortBinaryNumeralTerm certificateTokenCount,
    shortBinaryNumeralTerm certificateStart,
    shortBinaryNumeralTerm certificateFinish]

private def initialRowNormalizedGlobalSubstitutionQpow
    (terms : Fin 14 -> ValuationTerm) :
    (depth : Nat) -> Rew ℒₒᵣ Empty (14 + depth) Nat depth
  | 0 => (Rew.subst terms).comp
      (Rew.emb : Rew ℒₒᵣ Empty 14 Nat 14)
  | depth + 1 =>
      (initialRowNormalizedGlobalSubstitutionQpow terms depth).q

/-- The copied core after closing exactly the fourteen public coordinates. -/
def compactNumericVerifierInitialWitnessTableRowOpenWitnessMatrix
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) :
    ArithmeticSemiformula Nat 11 :=
  initialRowNormalizedGlobalSubstitutionQpow
    (initialRowGlobalTerms tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish) 11 ▹
    compactNumericVerifierInitialWitnessTableRowRawCore

private abbrev initialRowClosedShift :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.closedShift

@[simp] private theorem initialRowRewriting_bexsLTSucc
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (bound : ArithmeticSemiterm sourceVariables sourceArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1)) :
    rewriting ▹ body.bexsLTSucc bound =
      (rewriting.q ▹ body).bexsLTSucc (rewriting bound) := by
  simp [LO.FirstOrder.Semiformula.bexsLTSucc,
    LO.FirstOrder.Semiformula.bexsLT]

private def initialRowShiftedValueBoundVariable :
    (depth : Nat) -> Fin (14 + depth)
  | 0 => 2
  | depth + 1 => (initialRowShiftedValueBoundVariable depth).succ

@[simp] private theorem initialRowShiftedValueBoundVariable_val
    (depth : Nat) :
    (initialRowShiftedValueBoundVariable depth).val = 2 + depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp [initialRowShiftedValueBoundVariable, ih]
      omega

private theorem initialRowLiftPast_valueBound (depth : Nat) :
    liftPast depth (#2 : ArithmeticSemiterm Empty 14) =
      (#(initialRowShiftedValueBoundVariable depth) :
        ArithmeticSemiterm Empty (14 + depth)) := by
  unfold liftPast
  rw [Rew.subst_bvar]
  congr 1
  apply Fin.ext
  simp [initialRowShiftedValueBoundVariable]

@[simp] private theorem initialRowNormalizedGlobalSubstitution_valueBound
    (terms : Fin 14 -> ValuationTerm) (depth : Nat) :
    initialRowNormalizedGlobalSubstitutionQpow terms depth
        (#(initialRowShiftedValueBoundVariable depth) :
          ArithmeticSemiterm Empty (14 + depth)) =
      initialRowClosedShift depth (terms 2) := by
  induction depth with
  | zero =>
      simp [initialRowNormalizedGlobalSubstitutionQpow,
        initialRowShiftedValueBoundVariable, initialRowClosedShift,
        FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.closedShift,
        Rew.comp_app, Rew.subst_bvar]
  | succ depth ih =>
      change (initialRowNormalizedGlobalSubstitutionQpow terms depth).q
          (#(initialRowShiftedValueBoundVariable depth).succ) = _
      rw [Rew.q_bvar_succ, ih]
      rfl

private theorem initialRowClosedMatrixRewriting_eq_openWitnessMatrix
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) :
    initialRowNormalizedGlobalSubstitutionQpow
        (initialRowGlobalTerms tableWidth table valueBound
          proofTable proofWidth proofTokenCount proofStart proofFinish
          certificateTable certificateWidth certificateTokenCount
          certificateStart certificateFinish) 11 ▹
      compactNumericVerifierInitialWitnessTableRowRawCore =
        compactNumericVerifierInitialWitnessTableRowOpenWitnessMatrix
          tableWidth table valueBound
          proofTable proofWidth proofTokenCount proofStart proofFinish
          certificateTable certificateWidth certificateTokenCount
          certificateStart certificateFinish := by
  rfl

private theorem initialRowBoundedVectorRewriting_alignment
    (terms : Fin 14 -> ValuationTerm) :
    (k : Nat) ->
    (body : ArithmeticSemiformula Empty (14 + k)) ->
    (Rewriting.emb (ξ := Nat)
        (boundedVectorBExs
          (#2 : ArithmeticSemiterm Empty 14) k body)) ⇜ terms =
      explicitClosedBoundedVectorFormula (terms 2) k
        (initialRowNormalizedGlobalSubstitutionQpow terms k ▹ body)
  | 0, body => by
      simp only [boundedVectorBExs, explicitClosedBoundedVectorFormula,
        initialRowNormalizedGlobalSubstitutionQpow]
      rw [TransitiveRewriting.comp_app]
  | k + 1, body => by
      simp only [boundedVectorBExs, explicitClosedBoundedVectorFormula]
      rw [initialRowBoundedVectorRewriting_alignment terms k]
      congr 1
      rw [initialRowRewriting_bexsLTSucc]
      congr 1
      rw [initialRowLiftPast_valueBound,
        initialRowNormalizedGlobalSubstitution_valueBound]

/-- Exact alignment of the original InitialRow formula with the public
eleven-witness explicit bounded-vector syntax. -/
theorem compactNumericVerifierInitialWitnessTableRowClosedFormula_alignment
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) :
    compactNumericVerifierInitialWitnessTableRowClosedFormula
        tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish =
      explicitClosedBoundedVectorFormula
        (shortBinaryNumeralTerm valueBound) 11
        (compactNumericVerifierInitialWitnessTableRowOpenWitnessMatrix
          tableWidth table valueBound
          proofTable proofWidth proofTokenCount proofStart proofFinish
          certificateTable certificateWidth certificateTokenCount
          certificateStart certificateFinish) := by
  unfold compactNumericVerifierInitialWitnessTableRowClosedFormula
  rw [compactNumericVerifierInitialWitnessTableRowDef_val_eq_boundedVector]
  calc
    _ = explicitClosedBoundedVectorFormula
          (shortBinaryNumeralTerm valueBound) 11
          (initialRowNormalizedGlobalSubstitutionQpow
            (initialRowGlobalTerms tableWidth table valueBound
              proofTable proofWidth proofTokenCount proofStart proofFinish
              certificateTable certificateWidth certificateTokenCount
              certificateStart certificateFinish) 11 ▹
            compactNumericVerifierInitialWitnessTableRowRawCore) := by
      simpa [initialRowGlobalTerms] using
        (initialRowBoundedVectorRewriting_alignment
          (initialRowGlobalTerms tableWidth table valueBound
            proofTable proofWidth proofTokenCount proofStart proofFinish
            certificateTable certificateWidth certificateTokenCount
            certificateStart certificateFinish) 11
          compactNumericVerifierInitialWitnessTableRowRawCore)
    _ = _ := congrArg
      (explicitClosedBoundedVectorFormula
        (shortBinaryNumeralTerm valueBound) 11)
      (initialRowClosedMatrixRewriting_eq_openWitnessMatrix
        tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish)

/-- The eleven outer witnesses, in binder order, are fixed directly to the
canonical row-zero environment at columns
`[0, 1, 2, 3, 5, 7, 10, 11, 13, 15, 21]`. -/
def compactNumericVerifierInitialWitnessTableRowExplicitValues
    (tableWidth table : Nat) : Fin 11 -> Nat :=
  let environment :=
    compactNumericVerifierStepWitnessTableFormulaEnvironment
      tableWidth table 0
  ![environment 0, environment 1, environment 2, environment 3,
    environment 5, environment 7, environment 10, environment 11,
    environment 13, environment 15, environment 21]

@[simp] theorem compactNumericVerifierInitialWitnessTableRowExplicitValues_eq
    (tableWidth table : Nat) (coordinate : Fin 11) :
    compactNumericVerifierInitialWitnessTableRowExplicitValues
        tableWidth table coordinate =
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0
          (compactNumericVerifierInitialStepCoordinate coordinate) := by
  fin_cases coordinate <;>
    rfl

private def initialRowWitnessTerms
    (tableWidth table : Nat) : Fin 11 -> ValuationTerm :=
  fun coordinate => shortBinaryNumeralTerm
    (compactNumericVerifierInitialWitnessTableRowExplicitValues
      tableWidth table coordinate)

private def initialRowInstalledTerms
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) : Fin 25 -> ValuationTerm :=
  let values :=
    compactNumericVerifierInitialWitnessTableRowExplicitValues
      tableWidth table
  ![shortBinaryNumeralTerm (values 0),
    shortBinaryNumeralTerm (values 1),
    shortBinaryNumeralTerm (values 2),
    shortBinaryNumeralTerm (values 3),
    shortBinaryNumeralTerm (values 4),
    shortBinaryNumeralTerm (values 5),
    shortBinaryNumeralTerm (values 6),
    shortBinaryNumeralTerm (values 7),
    shortBinaryNumeralTerm (values 8),
    shortBinaryNumeralTerm (values 9),
    shortBinaryNumeralTerm (values 10),
    shortBinaryNumeralTerm tableWidth,
    shortBinaryNumeralTerm table,
    shortBinaryNumeralTerm valueBound,
    (‘0’ : ValuationTerm),
    shortBinaryNumeralTerm proofTable,
    shortBinaryNumeralTerm proofWidth,
    shortBinaryNumeralTerm proofTokenCount,
    shortBinaryNumeralTerm proofStart,
    shortBinaryNumeralTerm proofFinish,
    shortBinaryNumeralTerm certificateTable,
    shortBinaryNumeralTerm certificateWidth,
    shortBinaryNumeralTerm certificateTokenCount,
    shortBinaryNumeralTerm certificateStart,
    shortBinaryNumeralTerm certificateFinish]

private theorem initialRowInstalledRewriting_eq
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) :
    (Rew.subst (initialRowWitnessTerms tableWidth table)).comp
        (initialRowNormalizedGlobalSubstitutionQpow
          (initialRowGlobalTerms tableWidth table valueBound
            proofTable proofWidth proofTokenCount proofStart proofFinish
            certificateTable certificateWidth certificateTokenCount
            certificateStart certificateFinish) 11) =
      (Rew.subst (initialRowInstalledTerms tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish)).comp
          (Rew.emb : Rew ℒₒᵣ Empty 25 Nat 25) := by
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [initialRowNormalizedGlobalSubstitutionQpow,
        initialRowGlobalTerms, initialRowWitnessTerms,
        initialRowInstalledTerms,
        compactNumericVerifierInitialWitnessTableRowExplicitValues,
        Rew.comp_app, Rew.subst_bvar, Rew.q]
    all_goals
      exact
        FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.substitute_closedShift
          _ _
  · intro coordinate
    exact Empty.elim coordinate

private def closedArithmeticNumeral (value : Nat) : ValuationTerm :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ value) ![]

private def closedArithmeticMul
    (left right : ValuationTerm) : ValuationTerm :=
  Semiterm.Operator.Mul.mul.operator ![left, right]

private def closedArithmeticAdd
    (left right : ValuationTerm) : ValuationTerm :=
  Semiterm.Operator.Add.add.operator ![left, right]

/-- The original, unreduced table index syntax `0 * 429 + column`. -/
def compactNumericVerifierInitialWitnessTableRowIndexTerm
    (coordinate : Fin 11) : ValuationTerm :=
  closedArithmeticAdd
    (closedArithmeticMul (‘0’ : ValuationTerm)
      (closedArithmeticNumeral
        compactNumericVerifierStepWitnessColumnCount))
    (closedArithmeticNumeral
      (compactNumericVerifierInitialStepCoordinate coordinate).val)

private theorem termValue_closedArithmeticNumeral
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (closedArithmeticNumeral value) = value := by
  unfold closedArithmeticNumeral termValue
  rw [LO.FirstOrder.Semiterm.val_operator]
  have hempty :
      (LO.FirstOrder.Semiterm.val ![] valuation ∘
        (![] : Fin 0 -> ValuationTerm)) = ![] := by
    funext coordinate
    exact Fin.elim0 coordinate
  rw [hempty]
  simpa using (LO.FirstOrder.Structure.numeral_eq_numeral
    (L := ℒₒᵣ) (M := Nat) value)

private theorem termValue_closedArithmeticMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (closedArithmeticMul left right) =
      termValue valuation left * termValue valuation right := by
  simp [closedArithmeticMul, termValue,
    LO.FirstOrder.Semiterm.val_operator]

private theorem termValue_closedArithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (closedArithmeticAdd left right) =
      termValue valuation left + termValue valuation right := by
  simp [closedArithmeticAdd, termValue,
    LO.FirstOrder.Semiterm.val_operator]

private theorem termValue_arithmeticZero (valuation : Nat -> Nat) :
    termValue valuation (‘0’ : ValuationTerm) = 0 := by
  exact termValue_zero valuation ![]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

@[simp] theorem
    termValue_compactNumericVerifierInitialWitnessTableRowIndexTerm
    (coordinate : Fin 11) :
    termValue initialRowZeroValuation
        (compactNumericVerifierInitialWitnessTableRowIndexTerm coordinate) =
      0 * compactNumericVerifierStepWitnessColumnCount +
        (compactNumericVerifierInitialStepCoordinate coordinate).val := by
  simp [compactNumericVerifierInitialWitnessTableRowIndexTerm,
    termValue_closedArithmeticAdd, termValue_closedArithmeticMul,
    termValue_closedArithmeticNumeral, termValue_arithmeticZero]

def compactNumericVerifierInitialWitnessTableRowEntryClosedFormula
    (tableWidth table : Nat) (coordinate : Fin 11) :
    ArithmeticProposition :=
  compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm table)
    (shortBinaryNumeralTerm tableWidth)
    (compactNumericVerifierInitialWitnessTableRowIndexTerm coordinate)
    (shortBinaryNumeralTerm
      (compactNumericVerifierInitialWitnessTableRowExplicitValues
        tableWidth table coordinate))

def compactNumericVerifierInitialWitnessTableRowEntriesClosedFormula
    (tableWidth table : Nat) : ArithmeticProposition :=
  [compactNumericVerifierInitialWitnessTableRowEntryClosedFormula
      tableWidth table 0,
    compactNumericVerifierInitialWitnessTableRowEntryClosedFormula
      tableWidth table 1,
    compactNumericVerifierInitialWitnessTableRowEntryClosedFormula
      tableWidth table 2,
    compactNumericVerifierInitialWitnessTableRowEntryClosedFormula
      tableWidth table 3,
    compactNumericVerifierInitialWitnessTableRowEntryClosedFormula
      tableWidth table 4,
    compactNumericVerifierInitialWitnessTableRowEntryClosedFormula
      tableWidth table 5,
    compactNumericVerifierInitialWitnessTableRowEntryClosedFormula
      tableWidth table 6,
    compactNumericVerifierInitialWitnessTableRowEntryClosedFormula
      tableWidth table 7,
    compactNumericVerifierInitialWitnessTableRowEntryClosedFormula
      tableWidth table 8,
    compactNumericVerifierInitialWitnessTableRowEntryClosedFormula
      tableWidth table 9,
    compactNumericVerifierInitialWitnessTableRowEntryClosedFormula
      tableWidth table 10].conj₂

def compactNumericVerifierInitialWitnessTableRowProjectedClosedFormula
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) : ArithmeticProposition :=
  let values :=
    compactNumericVerifierInitialWitnessTableRowExplicitValues
      tableWidth table
  [compactFixedWidthCrossTableSlicesEqClosedFormula
      proofTable proofWidth proofTokenCount proofStart proofFinish
      (values 0) (values 1) (values 2) (values 3) (values 4),
    compactFixedWidthCrossTableSlicesEqClosedFormula
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish
      (values 0) (values 1) (values 2) (values 4) (values 5),
    compactNumericVerifierParseTaskHeadClosedFormula
      (values 0) (values 1) (values 2) (values 7) (values 10),
    “!!(shortBinaryNumeralTerm (values 6)) = 1”,
    “!!(shortBinaryNumeralTerm (values 8)) = 0”,
    “!!(shortBinaryNumeralTerm (values 9)) = 0”].conj₂

def compactNumericVerifierInitialWitnessTableRowTerminalClosedFormula
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) : ArithmeticProposition :=
  compactNumericVerifierInitialWitnessTableRowEntriesClosedFormula
      tableWidth table ⋏
    compactNumericVerifierInitialWitnessTableRowProjectedClosedFormula
      tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish

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

/-- Substituting the eleven canonical values into the copied core exposes
exactly the original entry indices and the six projected conjuncts. -/
theorem compactNumericVerifierInitialWitnessTableRowTerminalFormula_alignment
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) :
    compactNumericVerifierInitialWitnessTableRowOpenWitnessMatrix
        tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish ⇜
      (fun coordinate => shortBinaryNumeralTerm
        (compactNumericVerifierInitialWitnessTableRowExplicitValues
          tableWidth table coordinate)) =
      compactNumericVerifierInitialWitnessTableRowTerminalClosedFormula
        tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish := by
  change
    (initialRowNormalizedGlobalSubstitutionQpow
        (initialRowGlobalTerms tableWidth table valueBound
          proofTable proofWidth proofTokenCount proofStart proofFinish
          certificateTable certificateWidth certificateTokenCount
          certificateStart certificateFinish) 11 ▹
      compactNumericVerifierInitialWitnessTableRowRawCore) ⇜
        initialRowWitnessTerms tableWidth table =
      compactNumericVerifierInitialWitnessTableRowTerminalClosedFormula
        tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish
  rw [show
    (initialRowNormalizedGlobalSubstitutionQpow
        (initialRowGlobalTerms tableWidth table valueBound
          proofTable proofWidth proofTokenCount proofStart proofFinish
          certificateTable certificateWidth certificateTokenCount
          certificateStart certificateFinish) 11 ▹
      compactNumericVerifierInitialWitnessTableRowRawCore) ⇜
        initialRowWitnessTerms tableWidth table =
      (Rewriting.emb (ξ := Nat)
        compactNumericVerifierInitialWitnessTableRowRawCore) ⇜
        initialRowInstalledTerms tableWidth table valueBound
          proofTable proofWidth proofTokenCount proofStart proofFinish
          certificateTable certificateWidth certificateTokenCount
          certificateStart certificateFinish by
    change
      Rew.subst (initialRowWitnessTerms tableWidth table) ▹
          (initialRowNormalizedGlobalSubstitutionQpow
            (initialRowGlobalTerms tableWidth table valueBound
              proofTable proofWidth proofTokenCount proofStart proofFinish
              certificateTable certificateWidth certificateTokenCount
              certificateStart certificateFinish) 11 ▹
            compactNumericVerifierInitialWitnessTableRowRawCore) =
        Rew.subst (initialRowInstalledTerms tableWidth table valueBound
          proofTable proofWidth proofTokenCount proofStart proofFinish
          certificateTable certificateWidth certificateTokenCount
          certificateStart certificateFinish) ▹
            ((Rew.emb : Rew ℒₒᵣ Empty 25 Nat 25) ▹
              compactNumericVerifierInitialWitnessTableRowRawCore)
    rw [← TransitiveRewriting.comp_app,
      ← TransitiveRewriting.comp_app,
      initialRowInstalledRewriting_eq]]
  unfold compactNumericVerifierInitialWitnessTableRowRawCore
  unfold compactNumericVerifierInitialWitnessTableRowTerminalClosedFormula
  unfold compactNumericVerifierInitialWitnessTableRowEntriesClosedFormula
  unfold compactNumericVerifierInitialWitnessTableRowProjectedClosedFormula
  unfold compactNumericVerifierInitialWitnessTableRowEntryClosedFormula
  unfold compactNumericVerifierInitialWitnessTableRowIndexTerm
  unfold initialRowInstalledTerms
  unfold compactNumericVerifierInitialWitnessTableRowExplicitValues
  unfold tableEntryFormula tableIndexTerm projectedFormula
  unfold proofCrossTerms certificateCrossTerms parseTaskTerms
  unfold localVariable globalVariable
  unfold arithmeticEq arithmeticAdd arithmeticMul arithmeticNumeral
  unfold closedArithmeticAdd closedArithmeticMul closedArithmeticNumeral
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactFixedWidthCrossTableSlicesEqClosedFormula
  unfold compactNumericVerifierParseTaskHeadClosedFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    compactNumericVerifierInitialStepCoordinate,
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

private noncomputable def shortBinaryEqOneCertificate
    (value : Nat) (heq : value = 1) :
    InitialRowHybridCertificate
      “!!(shortBinaryNumeralTerm value) = 1” := by
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      initialRowZeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm value, (‘1’ : ValuationTerm)] (by
        change termValue initialRowZeroValuation
            (shortBinaryNumeralTerm value) =
          termValue initialRowZeroValuation (‘1’ : ValuationTerm)
        simpa [termValue_shortBinaryNumeralTerm,
          termValue_arithmeticOne] using heq)
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

private noncomputable def shortBinaryEqZeroCertificate
    (value : Nat) (heq : value = 0) :
    InitialRowHybridCertificate
      “!!(shortBinaryNumeralTerm value) = 0” := by
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      initialRowZeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm value, (‘0’ : ValuationTerm)] (by
        change termValue initialRowZeroValuation
            (shortBinaryNumeralTerm value) =
          termValue initialRowZeroValuation (‘0’ : ValuationTerm)
        simpa [termValue_shortBinaryNumeralTerm,
          termValue_arithmeticZero] using heq)
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

private theorem compactFixedWidthCrossTableSlicesEq_explicitData
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat)
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
  rcases hcross with
    ⟨count, hsourceCount, htargetCount, hsourceEndpoint, htargetEndpoint,
      hsourceFinish, htargetFinish, hbits⟩
  have hcount : sourceFinish - sourceStart = count := by
    omega
  simpa only [hcount] using
    And.intro hsourceCount
      (And.intro htargetCount
        (And.intro hsourceEndpoint
          (And.intro htargetEndpoint
            (And.intro hsourceFinish
              (And.intro htargetFinish hbits)))))

private noncomputable def
    compactFixedWidthCrossTableSlicesEqExplicitHybridCertificateOfSemantic
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat)
    (hcross : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish) :
    InitialRowHybridCertificate
      (compactFixedWidthCrossTableSlicesEqClosedFormula
        sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
        targetTable targetWidth targetTokenCount targetStart targetFinish) := by
  let count := sourceFinish - sourceStart
  have hdata := compactFixedWidthCrossTableSlicesEq_explicitData
    sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
    targetTable targetWidth targetTokenCount targetStart targetFinish hcross
  exact compactFixedWidthCrossTableSlicesEqExplicitHybridCertificate
    sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
    targetTable targetWidth targetTokenCount targetStart targetFinish count
    hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1
    hdata.2.2.2.2.1 hdata.2.2.2.2.2.1 hdata.2.2.2.2.2.2

private noncomputable def
    compactNumericVerifierInitialWitnessTableRowEntryExplicitHybridCertificate
    (tableWidth table : Nat) (coordinate : Fin 11) :
    InitialRowHybridCertificate
      (compactNumericVerifierInitialWitnessTableRowEntryClosedFormula
        tableWidth table coordinate) := by
  apply compactFixedWidthEntryAtValuationExplicitHybridCertificate
  simpa only [termValue_shortBinaryNumeralTerm,
    termValue_compactNumericVerifierInitialWitnessTableRowIndexTerm,
    compactNumericVerifierInitialWitnessTableRowExplicitValues_eq,
    compactNumericVerifierStepWitnessTableFormulaEnvironment] using
    compactNumericVerifierStepWitnessTableColumnValue_entry
      tableWidth table 0
        (compactNumericVerifierInitialStepCoordinate coordinate).val

private theorem compactNumericVerifierInitialWitnessTableRowExplicitValues_le_pow
    (tableWidth table : Nat) (coordinate : Fin 11) :
    compactNumericVerifierInitialWitnessTableRowExplicitValues
        tableWidth table coordinate <= 2 ^ tableWidth := by
  rw [compactNumericVerifierInitialWitnessTableRowExplicitValues_eq]
  exact compactNumericVerifierStepWitnessTableColumnValue_le_pow
    tableWidth table 0
      (compactNumericVerifierInitialStepCoordinate coordinate).val

/-- Explicit InitialRow certificate.  Parse coordinates and their bounded-head
proof are caller-supplied; the existential parse fact inside `hinitial` is not
inspected. -/
noncomputable def
    compactNumericVerifierInitialWitnessTableRowExplicitHybridCertificateOfExplicitParse
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth)
    (hinitial : CompactNumericVerifierInitialEnvironment
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0)
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness)
    (hhead : CompactNumericVerifierTaskBoundedHead
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 0)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 1)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 2)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 11)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 21)
      coordinates sizeWitness)
    (htag : coordinates.tag = 10)
    (hgammaCount : coordinates.gammaCount = 0)
    (hfirstCount : coordinates.firstCount = 0)
    (hsecondCount : coordinates.secondCount = 0)
    (hwitnessCount : coordinates.witnessCount = 0)
    (hsuffixCount : coordinates.suffixCount = 0) :
    InitialRowHybridCertificate
      (compactNumericVerifierInitialWitnessTableRowClosedFormula
        tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish) := by
  let values :=
    compactNumericVerifierInitialWitnessTableRowExplicitValues
      tableWidth table
  have hproofCross : CompactFixedWidthCrossTableSlicesEq
      proofTable proofWidth proofTokenCount proofStart proofFinish
      (values 0) (values 1) (values 2) (values 3) (values 4) := by
    simpa [values,
      compactNumericVerifierInitialWitnessTableRowExplicitValues_eq,
      compactNumericVerifierInitialStepCoordinate] using
      hinitial.1
  have hcertificateCross : CompactFixedWidthCrossTableSlicesEq
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish
      (values 0) (values 1) (values 2) (values 4) (values 5) := by
    simpa [values,
      compactNumericVerifierInitialWitnessTableRowExplicitValues_eq,
      compactNumericVerifierInitialStepCoordinate] using
      hinitial.2.1
  have hvalue6 : values 6 = 1 := by
    simpa [values,
      compactNumericVerifierInitialWitnessTableRowExplicitValues_eq,
      compactNumericVerifierInitialStepCoordinate] using
      hinitial.2.2.2.1
  have hvalue8 : values 8 = 0 := by
    simpa [values,
      compactNumericVerifierInitialWitnessTableRowExplicitValues_eq,
      compactNumericVerifierInitialStepCoordinate] using
      hinitial.2.2.2.2.1
  have hvalue9 : values 9 = 0 := by
    simpa [values,
      compactNumericVerifierInitialWitnessTableRowExplicitValues_eq,
      compactNumericVerifierInitialStepCoordinate] using
      hinitial.2.2.2.2.2
  let entries :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactNumericVerifierInitialWitnessTableRowEntryExplicitHybridCertificate
        tableWidth table 0)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactNumericVerifierInitialWitnessTableRowEntryExplicitHybridCertificate
          tableWidth table 1)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactNumericVerifierInitialWitnessTableRowEntryExplicitHybridCertificate
            tableWidth table 2)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactNumericVerifierInitialWitnessTableRowEntryExplicitHybridCertificate
              tableWidth table 3)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactNumericVerifierInitialWitnessTableRowEntryExplicitHybridCertificate
                tableWidth table 4)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactNumericVerifierInitialWitnessTableRowEntryExplicitHybridCertificate
                  tableWidth table 5)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (compactNumericVerifierInitialWitnessTableRowEntryExplicitHybridCertificate
                    tableWidth table 6)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (compactNumericVerifierInitialWitnessTableRowEntryExplicitHybridCertificate
                      tableWidth table 7)
                    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                      (compactNumericVerifierInitialWitnessTableRowEntryExplicitHybridCertificate
                        tableWidth table 8)
                      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                        (compactNumericVerifierInitialWitnessTableRowEntryExplicitHybridCertificate
                          tableWidth table 9)
                        (compactNumericVerifierInitialWitnessTableRowEntryExplicitHybridCertificate
                          tableWidth table 10))))))))))
  let projected :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthCrossTableSlicesEqExplicitHybridCertificateOfSemantic
        proofTable proofWidth proofTokenCount proofStart proofFinish
        (values 0) (values 1) (values 2) (values 3) (values 4)
        hproofCross)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthCrossTableSlicesEqExplicitHybridCertificateOfSemantic
          certificateTable certificateWidth certificateTokenCount
          certificateStart certificateFinish
          (values 0) (values 1) (values 2) (values 4) (values 5)
          hcertificateCross)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactNumericVerifierParseTaskHeadExplicitHybridCertificate
            (values 0) (values 1) (values 2) (values 7) (values 10)
            coordinates sizeWitness (by
              simpa [values,
                compactNumericVerifierInitialWitnessTableRowExplicitValues_eq,
                compactNumericVerifierInitialStepCoordinate]
                using hhead)
            htag hgammaCount hfirstCount hsecondCount hwitnessCount
            hsuffixCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (shortBinaryEqOneCertificate (values 6) hvalue6)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (shortBinaryEqZeroCertificate (values 8) hvalue8)
              (shortBinaryEqZeroCertificate (values 9) hvalue9)))))
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      entries projected
  let terminal : InitialRowHybridCertificate
      (compactNumericVerifierInitialWitnessTableRowOpenWitnessMatrix
          tableWidth table valueBound
          proofTable proofWidth proofTokenCount proofStart proofFinish
          certificateTable certificateWidth certificateTokenCount
          certificateStart certificateFinish ⇜
        (fun coordinate => shortBinaryNumeralTerm (values coordinate))) :=
    .cast
      (compactNumericVerifierInitialWitnessTableRowTerminalFormula_alignment
        tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish).symm terminalParts
  let vectorCertificate :=
    buildExplicitClosedBoundedVectorHybridCertificate valueBound
      (compactNumericVerifierInitialWitnessTableRowOpenWitnessMatrix
        tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish)
      values
      (fun coordinate => by
        rw [hvalueBound]
        exact
          compactNumericVerifierInitialWitnessTableRowExplicitValues_le_pow
            tableWidth table coordinate)
      terminal
  exact .cast
    (compactNumericVerifierInitialWitnessTableRowClosedFormula_alignment
      tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish).symm vectorCertificate

theorem
    compactNumericVerifierInitialWitnessTableRowClosedFormula_freeVariables_eq_empty
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) :
    (compactNumericVerifierInitialWitnessTableRowClosedFormula
      tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish).freeVariables = ∅ := by
  unfold compactNumericVerifierInitialWitnessTableRowClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    simp [shortBinaryNumeralTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm,
      FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
      FoundationCompactBinaryNumeralTerm.arithmeticZeroTerm,
      LO.FirstOrder.Semiterm.Operator.operator,
      LO.FirstOrder.Semiterm.Operator.numeral_zero,
      LO.FirstOrder.Semiterm.Operator.Zero.term_eq]

/-- Empty-context PA proof compiled from the explicit InitialRow certificate. -/
noncomputable def
    compileCompactNumericVerifierInitialWitnessTableRowExplicitHybridContext
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth)
    (hinitial : CompactNumericVerifierInitialEnvironment
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0)
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness)
    (hhead : CompactNumericVerifierTaskBoundedHead
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 0)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 1)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 2)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 11)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 21)
      coordinates sizeWitness)
    (htag : coordinates.tag = 10)
    (hgammaCount : coordinates.gammaCount = 0)
    (hfirstCount : coordinates.firstCount = 0)
    (hsecondCount : coordinates.secondCount = 0)
    (hwitnessCount : coordinates.witnessCount = 0)
    (hsuffixCount : coordinates.suffixCount = 0) :
    CertifiedPAContextProof ∅
      (compactNumericVerifierInitialWitnessTableRowClosedFormula
        tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish) := by
  let raw :=
    (compactNumericVerifierInitialWitnessTableRowExplicitHybridCertificateOfExplicitParse
      tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish hvalueBound hinitial
      coordinates sizeWitness hhead htag hgammaCount hfirstCount
      hsecondCount hwitnessCount hsuffixCount).compile
  have hcontext :
      valuationContext
          (compactNumericVerifierInitialWitnessTableRowClosedFormula
            tableWidth table valueBound
            proofTable proofWidth proofTokenCount proofStart proofFinish
            certificateTable certificateWidth certificateTokenCount
            certificateStart certificateFinish).freeVariables
          initialRowZeroValuation = ∅ := by
    rw [
      compactNumericVerifierInitialWitnessTableRowClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext raw

/-- Proof-free recursive resource for the fully explicit InitialRow
certificate. -/
noncomputable def
    compactNumericVerifierInitialWitnessTableRowExplicitHybridStructuralResource
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth)
    (hinitial : CompactNumericVerifierInitialEnvironment
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0)
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness)
    (hhead : CompactNumericVerifierTaskBoundedHead
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 0)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 1)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 2)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 11)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 21)
      coordinates sizeWitness)
    (htag : coordinates.tag = 10)
    (hgammaCount : coordinates.gammaCount = 0)
    (hfirstCount : coordinates.firstCount = 0)
    (hsecondCount : coordinates.secondCount = 0)
    (hwitnessCount : coordinates.witnessCount = 0)
    (hsuffixCount : coordinates.suffixCount = 0) : Nat :=
  CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
    (compactNumericVerifierInitialWitnessTableRowExplicitHybridCertificateOfExplicitParse
      tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish hvalueBound hinitial
      coordinates sizeWitness hhead htag hgammaCount hfirstCount
      hsecondCount hwitnessCount hsuffixCount)

theorem
    compileCompactNumericVerifierInitialWitnessTableRowExplicitHybridContext_payloadLength_le
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth)
    (hinitial : CompactNumericVerifierInitialEnvironment
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0)
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness)
    (hhead : CompactNumericVerifierTaskBoundedHead
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 0)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 1)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 2)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 11)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0 21)
      coordinates sizeWitness)
    (htag : coordinates.tag = 10)
    (hgammaCount : coordinates.gammaCount = 0)
    (hfirstCount : coordinates.firstCount = 0)
    (hsecondCount : coordinates.secondCount = 0)
    (hwitnessCount : coordinates.witnessCount = 0)
    (hsuffixCount : coordinates.suffixCount = 0) :
    (compileCompactNumericVerifierInitialWitnessTableRowExplicitHybridContext
      tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish hvalueBound hinitial
      coordinates sizeWitness hhead htag hgammaCount hfirstCount
      hsecondCount hwitnessCount hsuffixCount).payloadLength <=
      compactNumericVerifierInitialWitnessTableRowExplicitHybridStructuralResource
        tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish hvalueBound hinitial
        coordinates sizeWitness hhead htag hgammaCount hfirstCount
        hsecondCount hwitnessCount hsuffixCount := by
  unfold
    compileCompactNumericVerifierInitialWitnessTableRowExplicitHybridContext
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact
    CheckedHybridValuationBoundedFormulaCertificate.compile_payloadLength_le_structuralPayloadBound
      (compactNumericVerifierInitialWitnessTableRowExplicitHybridCertificateOfExplicitParse
        tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish hvalueBound hinitial
        coordinates sizeWitness hhead htag hgammaCount hfirstCount
        hsecondCount hwitnessCount hsuffixCount)

#print axioms
  compactNumericVerifierInitialWitnessTableRowExplicitHybridCertificateOfExplicitParse
#print axioms
  compileCompactNumericVerifierInitialWitnessTableRowExplicitHybridContext
#print axioms
  compactNumericVerifierInitialWitnessTableRowExplicitHybridStructuralResource
#print axioms
  compileCompactNumericVerifierInitialWitnessTableRowExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectVerifierInitialWitnessTableRowExplicitHybridCertificate
