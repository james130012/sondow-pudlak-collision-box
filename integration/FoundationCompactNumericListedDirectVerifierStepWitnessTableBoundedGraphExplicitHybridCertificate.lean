import integration.FoundationCompactNumericListedDirectVerifierStepWitnessTableRowsAdjacentExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceTableClosedDecomposition
import integration.FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
import integration.FoundationCompactPAExplicitHybridOfFnConjunction

/-!
# Explicit outer certificate for the bounded verifier-step graph

This file closes the table-entry and bounded-row layers around one concrete
`StepGraph` certificate.  The step certificate itself remains separate so that
the four executable verifier branches can be implemented without semantic
truth selection.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierStepWitnessTableBoundedGraphExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectBoundedVectorQuantifier
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge
open FoundationCompactNumericListedDirectVerifierAcceptedTraceTableClosedDecomposition
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAExplicitHybridOfFnConjunction
open FoundationCompactPAExplicitWitnessExsClosureBuilder

/-- Valuation outside the row-count bounded universal. -/
def zeroValuation : Nat -> Nat := fun _ => 0

/-- Valuation in the branch for a concrete row index. -/
def boundedGraphRowBranchValuation (rowIndex : Nat) : Nat -> Nat :=
  extendValuation rowIndex zeroValuation

private def witnessVariable (coordinate : Fin 429) : Fin (4 + 429) :=
  Fin.castAdd 4 coordinate

private def globalVariable (coordinate : Fin 4) : Fin (4 + 429) :=
  Fin.natAdd 429 coordinate

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
    (arithmeticMul (#(globalVariable 3))
      (arithmeticNumeral compactNumericVerifierStepWitnessColumnCount))
    (arithmeticNumeral coordinate.val)

private def boundedGraphEntryFormula (coordinate : Fin 429) :
    ArithmeticSemiformula Empty (4 + 429) :=
  compactFixedWidthEntryDef.val ⇜
    ![(#(globalVariable 1) : ArithmeticSemiterm Empty (4 + 429)),
      #(globalVariable 0),
      witnessTableIndexTerm coordinate,
      #(witnessVariable coordinate)]

private def boundedGraphStepFormula :
    ArithmeticSemiformula Empty (4 + 429) :=
  compactNumericVerifierStepGraphDef.val ⇜
    fun coordinate => (#(witnessVariable coordinate) :
      ArithmeticSemiterm Empty (4 + 429))

/-- Definitionally exact public copy of the source row's private 433-variable
matrix. -/
def compactNumericVerifierStepWitnessTableBoundedRowRawCore :
    ArithmeticSemiformula Empty (4 + 429) :=
  (List.ofFn boundedGraphEntryFormula).conj₂ ⋏ boundedGraphStepFormula

theorem compactNumericVerifierStepWitnessTableBoundedRowDef_val_eq_boundedVector :
    compactNumericVerifierStepWitnessTableBoundedRowDef.val =
      boundedVectorBExs (#2 : ArithmeticSemiterm Empty 4) 429
        compactNumericVerifierStepWitnessTableBoundedRowRawCore := by
  rfl

private def boundedGraphGlobalTerms
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm) : Fin 4 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tableWidth,
    shortBinaryNumeralTerm table,
    valueBoundTerm,
    rowIndexTerm]

private def normalizedGlobalSubstitutionQpow
    (terms : Fin 4 -> ValuationTerm) :
    (depth : Nat) -> Rew ℒₒᵣ Empty (4 + depth) Nat depth
  | 0 => (Rew.subst terms).comp
      (Rew.emb : Rew ℒₒᵣ Empty 4 Nat 4)
  | depth + 1 => (normalizedGlobalSubstitutionQpow terms depth).q

/-- The copied row matrix after closing exactly its four public coordinates. -/
def compactNumericVerifierStepWitnessTableBoundedRowOpenWitnessMatrix
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm) :
    ArithmeticSemiformula Nat 429 :=
  normalizedGlobalSubstitutionQpow
      (boundedGraphGlobalTerms tableWidth table valueBoundTerm rowIndexTerm) 429 ▹
    compactNumericVerifierStepWitnessTableBoundedRowRawCore

@[simp] private theorem rewriting_bexsLTSucc
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

private def shiftedValueBoundVariable :
    (depth : Nat) -> Fin (4 + depth)
  | 0 => 2
  | depth + 1 => (shiftedValueBoundVariable depth).succ

@[simp] private theorem shiftedValueBoundVariable_val (depth : Nat) :
    (shiftedValueBoundVariable depth).val = 2 + depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp [shiftedValueBoundVariable, ih]
      omega

private theorem liftPast_valueBound (depth : Nat) :
    liftPast depth (#2 : ArithmeticSemiterm Empty 4) =
      (#(shiftedValueBoundVariable depth) :
        ArithmeticSemiterm Empty (4 + depth)) := by
  unfold liftPast
  rw [Rew.subst_bvar]
  congr 1
  apply Fin.ext
  simp [shiftedValueBoundVariable]

@[simp] private theorem normalizedGlobalSubstitution_valueBound
    (terms : Fin 4 -> ValuationTerm) (depth : Nat) :
    normalizedGlobalSubstitutionQpow terms depth
        (#(shiftedValueBoundVariable depth) :
          ArithmeticSemiterm Empty (4 + depth)) =
      closedShift depth (terms 2) := by
  induction depth with
  | zero =>
      simp [normalizedGlobalSubstitutionQpow,
        shiftedValueBoundVariable, closedShift,
        Rew.comp_app, Rew.subst_bvar]
  | succ depth ih =>
      change (normalizedGlobalSubstitutionQpow terms depth).q
          (#(shiftedValueBoundVariable depth).succ) = _
      rw [Rew.q_bvar_succ, ih]
      rfl

private theorem boundedVectorRewriting_alignment
    (terms : Fin 4 -> ValuationTerm) :
    (depth : Nat) ->
    (body : ArithmeticSemiformula Empty (4 + depth)) ->
    (Rewriting.emb (ξ := Nat)
        (boundedVectorBExs
          (#2 : ArithmeticSemiterm Empty 4) depth body)) ⇜ terms =
      explicitClosedBoundedVectorFormula (terms 2) depth
        (normalizedGlobalSubstitutionQpow terms depth ▹ body)
  | 0, body => by
      simp only [boundedVectorBExs, explicitClosedBoundedVectorFormula,
        normalizedGlobalSubstitutionQpow]
      rw [TransitiveRewriting.comp_app]
  | depth + 1, body => by
      simp only [boundedVectorBExs, explicitClosedBoundedVectorFormula]
      rw [boundedVectorRewriting_alignment terms depth]
      congr 1
      rw [rewriting_bexsLTSucc]
      congr 1
      rw [liftPast_valueBound,
        normalizedGlobalSubstitution_valueBound]

/-- One bounded row at the caller's original row-index term. -/
def compactNumericVerifierStepWitnessTableBoundedRowAtValuationFormula
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStepWitnessTableBoundedRowDef.val) ⇜
    boundedGraphGlobalTerms tableWidth table valueBoundTerm rowIndexTerm

/-- Exact normalization of the source row formula to an explicit 429-witness
bounded vector. -/
theorem compactNumericVerifierStepWitnessTableBoundedRowAtValuationFormula_alignment
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm) :
    compactNumericVerifierStepWitnessTableBoundedRowAtValuationFormula
        tableWidth table valueBoundTerm rowIndexTerm =
      explicitClosedBoundedVectorFormula valueBoundTerm 429
        (compactNumericVerifierStepWitnessTableBoundedRowOpenWitnessMatrix
          tableWidth table valueBoundTerm rowIndexTerm) := by
  unfold compactNumericVerifierStepWitnessTableBoundedRowAtValuationFormula
  rw [compactNumericVerifierStepWitnessTableBoundedRowDef_val_eq_boundedVector]
  simpa [compactNumericVerifierStepWitnessTableBoundedRowOpenWitnessMatrix,
    boundedGraphGlobalTerms] using
    (boundedVectorRewriting_alignment
      (boundedGraphGlobalTerms tableWidth table valueBoundTerm rowIndexTerm)
      429 compactNumericVerifierStepWitnessTableBoundedRowRawCore)

/-! ## Exact coordinate installation -/

private def normalizedBVarResult
    (terms : Fin 4 -> ValuationTerm) (depth : Nat)
    (index : Fin (4 + depth)) : ArithmeticSemiterm Nat depth :=
  if hlocal : index.val < depth then
    (#(⟨index.val, hlocal⟩ : Fin depth) : ArithmeticSemiterm Nat depth)
  else
    closedShift depth
      (terms ⟨index.val - depth, by omega⟩)

private theorem normalizedBVarResult_eq
    (terms : Fin 4 -> ValuationTerm) :
    forall (depth : Nat) (index : Fin (4 + depth)),
      normalizedBVarResult terms depth index =
        normalizedGlobalSubstitutionQpow terms depth
          (#index : ArithmeticSemiterm Empty (4 + depth)) := by
  intro depth
  induction depth with
  | zero =>
      intro index
      simp [normalizedBVarResult, normalizedGlobalSubstitutionQpow,
        closedShift, Rew.comp_app, Rew.subst_bvar]
  | succ depth ih =>
      intro index
      cases index using Fin.cases with
      | zero =>
          simp [normalizedBVarResult, normalizedGlobalSubstitutionQpow]
      | succ index =>
          rw [show
            normalizedGlobalSubstitutionQpow terms (depth + 1)
                (#index.succ : ArithmeticSemiterm Empty (4 + (depth + 1))) =
              Rew.bShift
                (normalizedGlobalSubstitutionQpow terms depth
                  (#index : ArithmeticSemiterm Empty (4 + depth))) by
            change (normalizedGlobalSubstitutionQpow terms depth).q
                (#index.succ) = _
            rw [Rew.q_bvar_succ]]
          rw [← ih index]
          by_cases hlocal : index.val < depth
          · have hlocalSucc : index.val + 1 < depth + 1 := by omega
            simp [normalizedBVarResult, hlocal, hlocalSucc]
          · have hlocalSucc : ¬index.val + 1 < depth + 1 := by omega
            simp [normalizedBVarResult, hlocal, hlocalSucc, closedShift]

private def boundedGraphWitnessTerms
    (values : Fin 429 -> Nat) : Fin 429 -> ValuationTerm :=
  fun coordinate => shortBinaryNumeralTerm (values coordinate)

private def boundedGraphInstalledRewriting
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm)
    (values : Fin 429 -> Nat) :
    Rew ℒₒᵣ Empty (4 + 429) Nat 0 :=
  (Rew.subst (boundedGraphWitnessTerms values)).comp
    (normalizedGlobalSubstitutionQpow
      (boundedGraphGlobalTerms tableWidth table valueBoundTerm rowIndexTerm) 429)

private theorem boundedGraphInstalledRewriting_witness
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm)
    (values : Fin 429 -> Nat) (coordinate : Fin 429) :
    boundedGraphInstalledRewriting tableWidth table valueBoundTerm rowIndexTerm
        values
        (#(witnessVariable coordinate) :
          ArithmeticSemiterm Empty (4 + 429)) =
      shortBinaryNumeralTerm (values coordinate) := by
  unfold boundedGraphInstalledRewriting
  rw [Rew.comp_app]
  rw [← normalizedBVarResult_eq]
  simp [normalizedBVarResult, witnessVariable,
    boundedGraphWitnessTerms]

private theorem boundedGraphInstalledRewriting_global
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm)
    (values : Fin 429 -> Nat) (coordinate : Fin 4) :
    boundedGraphInstalledRewriting tableWidth table valueBoundTerm rowIndexTerm
        values
        (#(globalVariable coordinate) :
          ArithmeticSemiterm Empty (4 + 429)) =
      boundedGraphGlobalTerms tableWidth table valueBoundTerm rowIndexTerm
        coordinate := by
  unfold boundedGraphInstalledRewriting
  rw [Rew.comp_app]
  rw [← normalizedBVarResult_eq]
  simp [normalizedBVarResult, globalVariable]
  exact substitute_closedShift _ _

private def boundedGraphInstalledTerms
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm)
    (values : Fin 429 -> Nat) : Fin (4 + 429) -> ValuationTerm :=
  fun index =>
    if hlocal : index.val < 429 then
      shortBinaryNumeralTerm (values ⟨index.val, hlocal⟩)
    else
      boundedGraphGlobalTerms tableWidth table valueBoundTerm rowIndexTerm
        ⟨index.val - 429, by omega⟩

@[simp] private theorem boundedGraphInstalledTerms_witness
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm)
    (values : Fin 429 -> Nat) (coordinate : Fin 429) :
    boundedGraphInstalledTerms tableWidth table valueBoundTerm rowIndexTerm
        values (witnessVariable coordinate) =
      shortBinaryNumeralTerm (values coordinate) := by
  simp [boundedGraphInstalledTerms, witnessVariable]

@[simp] private theorem boundedGraphInstalledTerms_global
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm)
    (values : Fin 429 -> Nat) (coordinate : Fin 4) :
    boundedGraphInstalledTerms tableWidth table valueBoundTerm rowIndexTerm
        values (globalVariable coordinate) =
      boundedGraphGlobalTerms tableWidth table valueBoundTerm rowIndexTerm
        coordinate := by
  simp [boundedGraphInstalledTerms, globalVariable]

private theorem boundedGraphInstalledRewriting_eq_substitution
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm)
    (values : Fin 429 -> Nat) :
    boundedGraphInstalledRewriting tableWidth table valueBoundTerm rowIndexTerm
        values =
      (Rew.subst
        (boundedGraphInstalledTerms tableWidth table valueBoundTerm rowIndexTerm
          values)).comp
        (Rew.emb : Rew ℒₒᵣ Empty (4 + 429) Nat (4 + 429)) := by
  apply Rew.ext
  · intro index
    simp only [Rew.comp_app, Rew.emb_bvar, Rew.subst_bvar]
    by_cases hlocal : index.val < 429
    · have hindex :
          (⟨index.val, hlocal⟩ : Fin 429) =
            ⟨index.val, hlocal⟩ := rfl
      unfold boundedGraphInstalledRewriting
      rw [Rew.comp_app, ← normalizedBVarResult_eq]
      simp [normalizedBVarResult, boundedGraphWitnessTerms,
        boundedGraphInstalledTerms, hlocal, hindex, Rew.subst_bvar]
    · unfold boundedGraphInstalledRewriting
      rw [Rew.comp_app, ← normalizedBVarResult_eq]
      simp [normalizedBVarResult, boundedGraphInstalledTerms, hlocal]
      exact substitute_closedShift _ _
  · intro index
    exact Empty.elim index

private theorem boundedGraphInstalledFormulaRewriting
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm)
    (values : Fin 429 -> Nat)
    (formula : ArithmeticSemiformula Empty (4 + 429)) :
    boundedGraphInstalledRewriting tableWidth table valueBoundTerm rowIndexTerm
        values ▹ formula =
      (Rewriting.emb (ξ := Nat) formula) ⇜
        boundedGraphInstalledTerms tableWidth table valueBoundTerm rowIndexTerm
          values := by
  rw [boundedGraphInstalledRewriting_eq_substitution]
  rw [TransitiveRewriting.comp_app]

private def closedArithmeticNumeral (value : Nat) : ValuationTerm :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ value) ![]

private def closedArithmeticMul
    (left right : ValuationTerm) : ValuationTerm :=
  Semiterm.Operator.Mul.mul.operator ![left, right]

private def closedArithmeticAdd
    (left right : ValuationTerm) : ValuationTerm :=
  Semiterm.Operator.Add.add.operator ![left, right]

/-- The original row-table index term, with the row variable left open. -/
def compactNumericVerifierStepWitnessTableBoundedRowIndexTerm
    (rowIndexTerm : ValuationTerm) (coordinate : Fin 429) : ValuationTerm :=
  closedArithmeticAdd
    (closedArithmeticMul rowIndexTerm
      (closedArithmeticNumeral compactNumericVerifierStepWitnessColumnCount))
    (closedArithmeticNumeral coordinate.val)

/-- One canonical decoded row entry at the exact source index term. -/
def compactNumericVerifierStepWitnessTableBoundedRowEntryFormula
    (tableWidth table : Nat) (rowIndexTerm : ValuationTerm)
    (values : Fin 429 -> Nat) (coordinate : Fin 429) : ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm table)
    (shortBinaryNumeralTerm tableWidth)
    (compactNumericVerifierStepWitnessTableBoundedRowIndexTerm
      rowIndexTerm coordinate)
    (shortBinaryNumeralTerm (values coordinate))

/-- The complete 429-entry conjunction after installing canonical values. -/
def compactNumericVerifierStepWitnessTableBoundedRowEntriesFormula
    (tableWidth table : Nat) (rowIndexTerm : ValuationTerm)
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (List.ofFn fun coordinate =>
    compactNumericVerifierStepWitnessTableBoundedRowEntryFormula
      tableWidth table rowIndexTerm values coordinate).conj₂

/-- The complete step graph after installing all 429 canonical values. -/
def compactNumericVerifierStepGraphAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericVerifierStepGraphDef.val) ⇜
    fun coordinate => shortBinaryNumeralTerm (values coordinate)

/-- Exact terminal conjunction below all 429 row witnesses. -/
def compactNumericVerifierStepWitnessTableBoundedRowTerminalFormula
    (tableWidth table : Nat) (rowIndexTerm : ValuationTerm)
    (values : Fin 429 -> Nat) : ValuationFormula :=
  compactNumericVerifierStepWitnessTableBoundedRowEntriesFormula
      tableWidth table rowIndexTerm values ⋏
    compactNumericVerifierStepGraphAtEnvironmentFormula values

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

private theorem rewriting_closedFormulaSubstitution
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Empty sourceArity Nat targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (sourceTerms : Fin predicateArity ->
      ArithmeticSemiterm Empty sourceArity)
    (targetTerms : Fin predicateArity ->
      ArithmeticSemiterm Nat targetArity)
    (hterms : rewriting ∘ sourceTerms = targetTerms) :
    rewriting ▹ (formula ⇜ sourceTerms) =
      (Rewriting.emb (ξ := Nat) formula) ⇜ targetTerms := by
  have hcomposition :
      rewriting.comp (Rew.subst sourceTerms) =
        (Rew.subst targetTerms).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity Nat predicateArity) := by
    apply Rew.ext
    · intro coordinate
      simp only [Rew.comp_app, Rew.subst_bvar, Rew.emb_bvar]
      exact congrFun hterms coordinate
    · intro coordinate
      exact Empty.elim coordinate
  calc
    rewriting ▹ (formula ⇜ sourceTerms) =
        (rewriting.comp (Rew.subst sourceTerms)) ▹ formula := by
      rw [TransitiveRewriting.comp_app]
    _ = ((Rew.subst targetTerms).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity Nat predicateArity)) ▹
        formula := by rw [hcomposition]
    _ = (Rewriting.emb (ξ := Nat) formula) ⇜ targetTerms := by
      rw [TransitiveRewriting.comp_app]

private theorem boundedGraphInstalledRewriting_index
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm)
    (values : Fin 429 -> Nat) (coordinate : Fin 429) :
    boundedGraphInstalledRewriting tableWidth table valueBoundTerm rowIndexTerm
        values (witnessTableIndexTerm coordinate) =
      compactNumericVerifierStepWitnessTableBoundedRowIndexTerm
        rowIndexTerm coordinate := by
  unfold witnessTableIndexTerm arithmeticAdd arithmeticMul arithmeticNumeral
  unfold compactNumericVerifierStepWitnessTableBoundedRowIndexTerm
  unfold closedArithmeticAdd closedArithmeticMul closedArithmeticNumeral
  simp [boundedGraphInstalledRewriting_global, boundedGraphGlobalTerms]

private theorem boundedGraphInstalledRewriting_entry
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm)
    (values : Fin 429 -> Nat) (coordinate : Fin 429) :
    boundedGraphInstalledRewriting tableWidth table valueBoundTerm rowIndexTerm
        values ▹ boundedGraphEntryFormula coordinate =
    compactNumericVerifierStepWitnessTableBoundedRowEntryFormula
        tableWidth table rowIndexTerm values coordinate := by
  unfold boundedGraphEntryFormula
  unfold compactNumericVerifierStepWitnessTableBoundedRowEntryFormula
  unfold compactFixedWidthEntryAtValuationFormula
  apply rewriting_closedFormulaSubstitution
  funext index
  fin_cases index
  · simpa [boundedGraphGlobalTerms] using
      boundedGraphInstalledRewriting_global tableWidth table
        valueBoundTerm rowIndexTerm values 1
  · simpa [boundedGraphGlobalTerms] using
      boundedGraphInstalledRewriting_global tableWidth table
        valueBoundTerm rowIndexTerm values 0
  · exact boundedGraphInstalledRewriting_index tableWidth table
      valueBoundTerm rowIndexTerm values coordinate
  · exact boundedGraphInstalledRewriting_witness tableWidth table
      valueBoundTerm rowIndexTerm values coordinate

private theorem boundedGraphInstalledRewriting_step
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm)
    (values : Fin 429 -> Nat) :
    boundedGraphInstalledRewriting tableWidth table valueBoundTerm rowIndexTerm
        values ▹ boundedGraphStepFormula =
      compactNumericVerifierStepGraphAtEnvironmentFormula values := by
  unfold boundedGraphStepFormula
  unfold compactNumericVerifierStepGraphAtEnvironmentFormula
  apply rewriting_closedFormulaSubstitution
  funext coordinate
  exact boundedGraphInstalledRewriting_witness tableWidth table
    valueBoundTerm rowIndexTerm values coordinate

/-- Installing the canonical value vector exposes exactly the 429 table entries
and the concrete `StepGraph` formula. -/
theorem compactNumericVerifierStepWitnessTableBoundedRowOpenWitnessMatrix_substitution
    (tableWidth table : Nat)
    (valueBoundTerm rowIndexTerm : ValuationTerm)
    (values : Fin 429 -> Nat) :
    compactNumericVerifierStepWitnessTableBoundedRowOpenWitnessMatrix
        tableWidth table valueBoundTerm rowIndexTerm ⇜
      boundedGraphWitnessTerms values =
    compactNumericVerifierStepWitnessTableBoundedRowTerminalFormula
      tableWidth table rowIndexTerm values := by
  change
    Rew.subst (boundedGraphWitnessTerms values) ▹
        (normalizedGlobalSubstitutionQpow
          (boundedGraphGlobalTerms tableWidth table valueBoundTerm rowIndexTerm)
          429 ▹ compactNumericVerifierStepWitnessTableBoundedRowRawCore) = _
  rw [← TransitiveRewriting.comp_app]
  change boundedGraphInstalledRewriting tableWidth table valueBoundTerm
      rowIndexTerm values ▹
        compactNumericVerifierStepWitnessTableBoundedRowRawCore = _
  unfold compactNumericVerifierStepWitnessTableBoundedRowRawCore
  unfold compactNumericVerifierStepWitnessTableBoundedRowTerminalFormula
  unfold compactNumericVerifierStepWitnessTableBoundedRowEntriesFormula
  change
    (boundedGraphInstalledRewriting tableWidth table valueBoundTerm rowIndexTerm
        values ▹ (List.ofFn boundedGraphEntryFormula).conj₂) ⋏
      (boundedGraphInstalledRewriting tableWidth table valueBoundTerm rowIndexTerm
        values ▹ boundedGraphStepFormula) = _
  rw [List.map_conj₂]
  rw [List.map_ofFn]
  change
    (List.ofFn fun coordinate =>
        boundedGraphInstalledRewriting tableWidth table valueBoundTerm
          rowIndexTerm values ▹ boundedGraphEntryFormula coordinate).conj₂ ⋏
      (boundedGraphInstalledRewriting tableWidth table valueBoundTerm
        rowIndexTerm values ▹ boundedGraphStepFormula) = _
  rw [boundedGraphInstalledRewriting_step]
  congr 1
  exact congrArg List.conj₂ (congrArg List.ofFn (funext fun coordinate =>
    boundedGraphInstalledRewriting_entry tableWidth table
      valueBoundTerm rowIndexTerm values coordinate))

/-! ## Explicit row certificate -/

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left + !!right’) =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private def boundedGraphWitnessGuardFormula
    (valueBound value : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) <
    !!(shortBinaryNumeralTerm valueBound) + 1”

private noncomputable def boundedGraphWitnessGuardCertificate
    (valuation : Nat -> Nat) (valueBound value : Nat)
    (hvalue : value <= valueBound) :
    CheckedHybridValuationBoundedFormulaCertificate valuation
      (boundedGraphWitnessGuardFormula valueBound value) := by
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
    unfold boundedGraphWitnessGuardFormula
    exact (Semiformula.Operator.lt_def _ _).symm) direct

private theorem shortBinarySubstitution_bexsLTSucc_tail
    {arity : Nat}
    (bound : ValuationTerm)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat) :
    (body.bexsLTSucc (closedShift arity bound)) ⇜
        (fun index : Fin arity =>
          shortBinaryNumeralTerm (values index.succ)) =
      (explicitWitnessBodyAfterTail body values).bexsLTSucc bound := by
  unfold Semiformula.bexsLTSucc Semiformula.bexsLT
  have hbound :
      Rew.subst (fun index : Fin arity =>
          shortBinaryNumeralTerm (values index.succ))
          (closedShift arity bound) = bound := by
    exact substitute_closedShift _ bound
  simp [explicitWitnessBodyAfterTail, hbound]

/-- Install a concrete bounded vector under an arbitrary valuation. -/
private noncomputable def buildBoundedGraphExplicitClosedBoundedVectorCertificate
    {valuation : Nat -> Nat} :
    {arity : Nat} ->
    (bound : Nat) ->
    (body : ArithmeticSemiformula Nat arity) ->
    (values : Fin arity -> Nat) ->
    (forall index, values index <= bound) ->
    CheckedHybridValuationBoundedFormulaCertificate valuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)) ->
    CheckedHybridValuationBoundedFormulaCertificate valuation
      (explicitClosedBoundedVectorFormula
        (shortBinaryNumeralTerm bound) arity body)
  | 0, bound, body, values, hbounds, terminal => by
      simpa [explicitClosedBoundedVectorFormula] using terminal
  | arity + 1, bound, body, values, hbounds, terminal => by
      let tailValues : Fin arity -> Nat := fun index => values index.succ
      let witnessBody := explicitWitnessBodyAfterTail body values
      let guard := boundedGraphWitnessGuardFormula bound (values 0)
      let guardCertificate :=
        boundedGraphWitnessGuardCertificate valuation bound (values 0)
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
          (witnessBody.bexsLTSucc (shortBinaryNumeralTerm bound)) := by
        let boundedMatrix : ArithmeticSemiformula Nat 1 :=
          Semiformula.Operator.LT.lt.operator
              ![(#0 : ArithmeticSemiterm Nat 1),
                Rew.bShift
                  ‘!!(shortBinaryNumeralTerm bound) + 1’] ⋏
            witnessBody
        let direct : CheckedHybridValuationBoundedFormulaCertificate valuation
            (∃⁰ boundedMatrix) :=
          .existsWitness boundedMatrix (values 0) (.cast (by
            simp [boundedMatrix, guard, boundedGraphWitnessGuardFormula,
              ← TransitiveRewriting.comp_app]) guarded)
        exact .cast (by rfl) direct
      let recursiveTerminal :
          CheckedHybridValuationBoundedFormulaCertificate valuation
            ((body.bexsLTSucc
                (closedShift arity (shortBinaryNumeralTerm bound))) ⇜
              (fun index : Fin arity =>
                shortBinaryNumeralTerm (tailValues index))) :=
        .cast
          (shortBinarySubstitution_bexsLTSucc_tail
            (shortBinaryNumeralTerm bound) body values).symm inner
      simpa only [explicitClosedBoundedVectorFormula] using
        buildBoundedGraphExplicitClosedBoundedVectorCertificate bound
          (body.bexsLTSucc
            (closedShift arity (shortBinaryNumeralTerm bound)))
          tailValues (fun index => hbounds index.succ) recursiveTerminal

@[simp] private theorem termValue_closedArithmeticNumeral
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (closedArithmeticNumeral value) = value := by
  unfold closedArithmeticNumeral termValue
  rw [Semiterm.val_operator]
  have hempty :
      (Semiterm.val ![] valuation ∘
        (![] : Fin 0 -> ValuationTerm)) = ![] := by
    funext coordinate
    exact Fin.elim0 coordinate
  rw [hempty]
  simpa using (Structure.numeral_eq_numeral
    (L := ℒₒᵣ) (M := Nat) value)

@[simp] private theorem termValue_closedArithmeticMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (closedArithmeticMul left right) =
      termValue valuation left * termValue valuation right := by
  simp [closedArithmeticMul, termValue, Semiterm.val_operator]

@[simp] private theorem termValue_closedArithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (closedArithmeticAdd left right) =
      termValue valuation left + termValue valuation right := by
  simp [closedArithmeticAdd, termValue, Semiterm.val_operator]

@[simp] theorem termValue_compactNumericVerifierStepWitnessTableBoundedRowIndexTerm
    (rowIndex coordinate : Nat) (hcoordinate : coordinate < 429) :
    termValue (boundedGraphRowBranchValuation rowIndex)
        (compactNumericVerifierStepWitnessTableBoundedRowIndexTerm
          (&0 : ValuationTerm) ⟨coordinate, hcoordinate⟩) =
      rowIndex * compactNumericVerifierStepWitnessColumnCount + coordinate := by
  unfold compactNumericVerifierStepWitnessTableBoundedRowIndexTerm
  rw [termValue_closedArithmeticAdd, termValue_closedArithmeticMul,
    termValue_closedArithmeticNumeral, termValue_closedArithmeticNumeral]
  change boundedGraphRowBranchValuation rowIndex 0 *
      compactNumericVerifierStepWitnessColumnCount + coordinate = _
  simp [boundedGraphRowBranchValuation]

@[simp] private theorem
    termValue_compactNumericVerifierStepWitnessTableBoundedRowIndexTerm_fin
    (rowIndex : Nat) (coordinate : Fin 429) :
    termValue (boundedGraphRowBranchValuation rowIndex)
        (compactNumericVerifierStepWitnessTableBoundedRowIndexTerm
          (&0 : ValuationTerm) coordinate) =
      rowIndex * compactNumericVerifierStepWitnessColumnCount +
        coordinate.val := by
  simpa using
    termValue_compactNumericVerifierStepWitnessTableBoundedRowIndexTerm
      rowIndex coordinate.val coordinate.isLt

private noncomputable def boundedGraphRowEntryCertificate
    (tableWidth table rowIndex : Nat) (coordinate : Fin 429) :
    CheckedHybridValuationBoundedFormulaCertificate
      (boundedGraphRowBranchValuation rowIndex)
      (compactNumericVerifierStepWitnessTableBoundedRowEntryFormula
        tableWidth table (&0 : ValuationTerm)
        (compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table rowIndex) coordinate) := by
  apply compactFixedWidthEntryAtValuationExplicitHybridCertificate
  rw [termValue_shortBinaryNumeralTerm,
    termValue_shortBinaryNumeralTerm,
    termValue_shortBinaryNumeralTerm,
    termValue_compactNumericVerifierStepWitnessTableBoundedRowIndexTerm_fin]
  simpa only [compactNumericVerifierStepWitnessTableFormulaEnvironment] using
    compactNumericVerifierStepWitnessTableColumnValue_entry
      tableWidth table rowIndex coordinate.val

private noncomputable def boundedGraphRowEntriesCertificate
    (tableWidth table rowIndex : Nat) :
    CheckedHybridValuationBoundedFormulaCertificate
      (boundedGraphRowBranchValuation rowIndex)
      (compactNumericVerifierStepWitnessTableBoundedRowEntriesFormula
        tableWidth table (&0 : ValuationTerm)
        (compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table rowIndex)) := by
  unfold compactNumericVerifierStepWitnessTableBoundedRowEntriesFormula
  exact buildExplicitHybridOfFnConjunctionCertificate
    (formulas := fun coordinate =>
      compactNumericVerifierStepWitnessTableBoundedRowEntryFormula
        tableWidth table (&0 : ValuationTerm)
        (compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table rowIndex) coordinate)
    (certificates := fun coordinate =>
      boundedGraphRowEntryCertificate tableWidth table rowIndex coordinate)

/-- One complete bounded row, assuming only an explicit certificate for the
same concrete 429-coordinate `StepGraph`. -/
noncomputable def compactNumericVerifierStepWitnessTableBoundedRowExplicitHybridCertificateOfStep
    (tableWidth table rowIndex : Nat)
    (hstep : CheckedHybridValuationBoundedFormulaCertificate
      (boundedGraphRowBranchValuation rowIndex)
      (compactNumericVerifierStepGraphAtEnvironmentFormula
        (compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table rowIndex))) :
    CheckedHybridValuationBoundedFormulaCertificate
      (boundedGraphRowBranchValuation rowIndex)
      (compactNumericVerifierStepWitnessTableBoundedRowAtValuationFormula
        tableWidth table (shortBinaryNumeralTerm (2 ^ tableWidth))
          (&0 : ValuationTerm)) := by
  let values := compactNumericVerifierStepWitnessTableFormulaEnvironment
    tableWidth table rowIndex
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (boundedGraphRowEntriesCertificate tableWidth table rowIndex) hstep
  let terminal : CheckedHybridValuationBoundedFormulaCertificate
      (boundedGraphRowBranchValuation rowIndex)
      (compactNumericVerifierStepWitnessTableBoundedRowOpenWitnessMatrix
          tableWidth table (shortBinaryNumeralTerm (2 ^ tableWidth))
            (&0 : ValuationTerm) ⇜ boundedGraphWitnessTerms values) :=
    .cast
      (compactNumericVerifierStepWitnessTableBoundedRowOpenWitnessMatrix_substitution
        tableWidth table (shortBinaryNumeralTerm (2 ^ tableWidth))
          (&0 : ValuationTerm) values).symm terminalParts
  rw [compactNumericVerifierStepWitnessTableBoundedRowAtValuationFormula_alignment]
  exact buildBoundedGraphExplicitClosedBoundedVectorCertificate
    (valuation := boundedGraphRowBranchValuation rowIndex)
    (2 ^ tableWidth)
    (compactNumericVerifierStepWitnessTableBoundedRowOpenWitnessMatrix
      tableWidth table (shortBinaryNumeralTerm (2 ^ tableWidth))
        (&0 : ValuationTerm))
    values
    (fun coordinate =>
      compactNumericVerifierStepWitnessTableColumnValue_le_pow
        tableWidth table rowIndex coordinate.val)
    terminal

/-! ## Explicit row-count universal -/

/-- The exact row body enumerated by the source bounded graph. -/
def compactNumericVerifierStepWitnessTableBoundedGraphUniversalBody
    (tableWidth table valueBound : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStepWitnessTableBoundedRowDef.val) ⇜
    ![Rew.bShift (shortBinaryNumeralTerm tableWidth),
      Rew.bShift (shortBinaryNumeralTerm table),
      Rew.bShift (shortBinaryNumeralTerm valueBound),
      (#0 : ArithmeticSemiterm Nat 1)]

private theorem boundedGraphUniversalBody_free_alignment
    (tableWidth table valueBound : Nat) :
    Rewriting.free
        (compactNumericVerifierStepWitnessTableBoundedGraphUniversalBody
          tableWidth table valueBound) =
      compactNumericVerifierStepWitnessTableBoundedRowAtValuationFormula
        tableWidth table (shortBinaryNumeralTerm valueBound)
          (&0 : ValuationTerm) := by
  unfold compactNumericVerifierStepWitnessTableBoundedGraphUniversalBody
  rw [rewriting_embeddedFormulaSubstitution]
  unfold compactNumericVerifierStepWitnessTableBoundedRowAtValuationFormula
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_def, boundedGraphGlobalTerms]

/-- Strict alignment of the original bounded-graph predicate with the explicit
row-count bounded universal. -/
theorem compactNumericVerifierStepWitnessTableBoundedGraphAtValuationFormula_alignment
    (tableWidth table valueBound : Nat) (rowCountTerm : ValuationTerm) :
    compactNumericVerifierStepWitnessTableBoundedGraphAtValuationFormula
        tableWidth table valueBound rowCountTerm =
      (compactNumericVerifierStepWitnessTableBoundedGraphUniversalBody
        tableWidth table valueBound).ballLT rowCountTerm := by
  unfold compactNumericVerifierStepWitnessTableBoundedGraphAtValuationFormula
  unfold compactNumericVerifierStepWitnessTableBoundedGraphUniversalBody
  unfold compactNumericVerifierStepWitnessTableBoundedGraphDef
  simp [Semiformula.ballLT, LO.FirstOrder.ball,
    rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app, Function.comp_def]
  apply Rewriting.smul_ext'
  apply Rew.ext
  · intro coordinate
    have htableWidth :
        (Rew.subst ![shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm table, rowCountTerm,
          shortBinaryNumeralTerm valueBound]).q
            (#1 : ArithmeticSemiterm Nat 5) =
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
            (#2 : ArithmeticSemiterm Nat 5) =
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
            (#4 : ArithmeticSemiterm Nat 5) =
          Rew.bShift (shortBinaryNumeralTerm valueBound) := by
      change
        (Rew.subst ![shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm table, rowCountTerm,
          shortBinaryNumeralTerm valueBound]).q
            (#((3 : Fin 4).succ)) = _
      rw [Rew.q_bvar_succ, Rew.subst_bvar]
      rfl
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        htableWidth, htable, hvalueBound]
  · intro index
    exact Empty.elim index

private noncomputable def boundedGraphUniversalBranchCertificate
    (tableWidth table rowIndex : Nat)
    (hstep : CheckedHybridValuationBoundedFormulaCertificate
      (boundedGraphRowBranchValuation rowIndex)
      (compactNumericVerifierStepGraphAtEnvironmentFormula
        (compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table rowIndex))) :
    CheckedHybridValuationBoundedFormulaCertificate
      (boundedGraphRowBranchValuation rowIndex)
      (Rewriting.free
        (compactNumericVerifierStepWitnessTableBoundedGraphUniversalBody
          tableWidth table (2 ^ tableWidth))) := by
  exact .cast
    (boundedGraphUniversalBody_free_alignment
      tableWidth table (2 ^ tableWidth)).symm
    (compactNumericVerifierStepWitnessTableBoundedRowExplicitHybridCertificateOfStep
      tableWidth table rowIndex hstep)

/-- Complete explicit bounded-graph certificate from one explicit `StepGraph`
certificate for every concrete row.  This is the canonical outer shell; no
semantic truth or existential package is converted into certificate data. -/
noncomputable def
    compactNumericVerifierStepWitnessTableBoundedGraphExplicitHybridCertificateOfSteps
    (tableWidth table : Nat) (rowCountTerm : ValuationTerm)
    (hsteps : ∀ rowIndex < termValue zeroValuation rowCountTerm,
      CheckedHybridValuationBoundedFormulaCertificate
        (boundedGraphRowBranchValuation rowIndex)
        (compactNumericVerifierStepGraphAtEnvironmentFormula
          (compactNumericVerifierStepWitnessTableFormulaEnvironment
            tableWidth table rowIndex))) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactNumericVerifierStepWitnessTableBoundedGraphAtValuationFormula
        tableWidth table (2 ^ tableWidth) rowCountTerm) := by
  let body := compactNumericVerifierStepWitnessTableBoundedGraphUniversalBody
    tableWidth table (2 ^ tableWidth)
  let rowCount := termValue zeroValuation rowCountTerm
  let branches := buildExplicitHybridUniversalBranches rowCount
    (fun rowIndex hrowIndex =>
      boundedGraphUniversalBranchCertificate tableWidth table rowIndex
        (hsteps rowIndex hrowIndex))
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      rowCountTerm body (by simpa [rowCount] using branches)
  let universal : CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (body.ballLT rowCountTerm) := .cast (by
        change (∀⁰ termBoundedUniversalBody
          (Rew.bShift rowCountTerm) body) = body.ballLT rowCountTerm
        rw [termBoundedUniversal_eq_ball]
        rfl) direct
  exact .cast
    (compactNumericVerifierStepWitnessTableBoundedGraphAtValuationFormula_alignment
      tableWidth table (2 ^ tableWidth) rowCountTerm).symm universal

#print axioms compactNumericVerifierStepWitnessTableBoundedRowDef_val_eq_boundedVector
#print axioms compactNumericVerifierStepWitnessTableBoundedRowAtValuationFormula_alignment
#print axioms boundedGraphInstalledRewriting_witness
#print axioms boundedGraphInstalledRewriting_global
#print axioms
  compactNumericVerifierStepWitnessTableBoundedRowOpenWitnessMatrix_substitution
#print axioms
  compactNumericVerifierStepWitnessTableBoundedRowExplicitHybridCertificateOfStep
#print axioms
  compactNumericVerifierStepWitnessTableBoundedGraphAtValuationFormula_alignment
#print axioms
  compactNumericVerifierStepWitnessTableBoundedGraphExplicitHybridCertificateOfSteps

end FoundationCompactNumericListedDirectVerifierStepWitnessTableBoundedGraphExplicitHybridCertificate
