import integration.FoundationCompactNumericListedDirectBoundedVectorQuantifier
import integration.FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula

/-!
# Bounded arithmetic formula for the unique initial parse task

The verifier starts with one task whose tag is `10` and whose five list
fields are empty.  This file binds every coordinate of that task row and
checks the condition inside arithmetic; no semantic task predicate is used
as a formula atom.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseTaskHeadFormula

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectBoundedVectorQuantifier
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula

def CompactNumericVerifierParseTaskHead
    (tokenTable width tokenCount taskBoundary valueBound : Nat) : Prop :=
  ∃ coordinates : CompactNumericVerifierTaskRowCoordinates,
  ∃ sizeWitness : CompactNumericVerifierTaskSizeWitness,
    CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
        coordinates sizeWitness ∧
      coordinates.tag = 10 ∧
      coordinates.gammaCount = 0 ∧
      coordinates.firstCount = 0 ∧
      coordinates.secondCount = 0 ∧
      coordinates.witnessCount = 0 ∧
      coordinates.suffixCount = 0

private def localVariable (coordinate : Fin 14) : Fin (5 + 14) :=
  Fin.castAdd 5 coordinate

private def globalVariable (coordinate : Fin 5) : Fin (5 + 14) :=
  Fin.natAdd 14 coordinate

@[simp] private theorem localVariable_val
    (locals : Fin 14 -> Nat) (global : Fin 5 -> Nat)
    (coordinate : Fin 14) :
    Semiterm.val (Matrix.appendr locals global) Empty.elim
        (#(localVariable coordinate) : ArithmeticSemiterm Empty (5 + 14)) =
      locals coordinate := by
  simp [localVariable, Matrix.appendr, Matrix.vecAppend_eq_ite]

@[simp] private theorem globalVariable_val
    (locals : Fin 14 -> Nat) (global : Fin 5 -> Nat)
    (coordinate : Fin 5) :
    Semiterm.val (Matrix.appendr locals global) Empty.elim
        (#(globalVariable coordinate) : ArithmeticSemiterm Empty (5 + 14)) =
      global coordinate := by
  change Matrix.appendr locals global (Fin.natAdd 14 coordinate) =
    global coordinate
  simp [Matrix.appendr, Matrix.vecAppend_eq_ite]

private def arithmeticNumeral (value : Nat) :
    ArithmeticSemiterm Empty (5 + 14) :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ value) ![]

private def arithmeticEq
    (left right : ArithmeticSemiterm Empty (5 + 14)) :
    ArithmeticSemiformula Empty (5 + 14) :=
  Semiformula.Operator.Eq.eq.operator ![left, right]

@[simp] private theorem arithmeticNumeral_val
    (locals : Fin 14 -> Nat) (global : Fin 5 -> Nat) (value : Nat) :
    (arithmeticNumeral value).val
        (Matrix.appendr locals global) Empty.elim = value := by
  simp [arithmeticNumeral]

@[simp] private theorem arithmeticEq_eval
    (locals : Fin 14 -> Nat) (global : Fin 5 -> Nat)
    (left right : ArithmeticSemiterm Empty (5 + 14)) :
    (arithmeticEq left right).Evalb (Matrix.appendr locals global) ↔
      left.val (Matrix.appendr locals global) Empty.elim =
        right.val (Matrix.appendr locals global) Empty.elim := by
  simp [arithmeticEq]

private def compactNumericVerifierParseTaskHeadTerms :
    Fin 19 -> ArithmeticSemiterm Empty (5 + 14) :=
  ![(#(globalVariable 0) : ArithmeticSemiterm Empty (5 + 14)),
    #(globalVariable 1), #(globalVariable 2), #(globalVariable 3),
    #(globalVariable 4),
    #(localVariable 0), #(localVariable 1), #(localVariable 2),
    #(localVariable 3), #(localVariable 4), #(localVariable 5),
    #(localVariable 6), #(localVariable 7), #(localVariable 8),
    #(localVariable 9), #(localVariable 10), #(localVariable 11),
    #(localVariable 12), #(localVariable 13)]

private def compactNumericVerifierParseTaskHeadCoreFormula :
    ArithmeticSemiformula Empty (5 + 14) :=
  [compactNumericVerifierTaskBoundedHeadDef.val ⇜
      compactNumericVerifierParseTaskHeadTerms,
    arithmeticEq (#(localVariable 2)) (arithmeticNumeral 10),
    arithmeticEq (#(localVariable 4)) (arithmeticNumeral 0),
    arithmeticEq (#(localVariable 7)) (arithmeticNumeral 0),
    arithmeticEq (#(localVariable 9)) (arithmeticNumeral 0),
    arithmeticEq (#(localVariable 11)) (arithmeticNumeral 0),
    arithmeticEq (#(localVariable 12)) (arithmeticNumeral 0)].conj₂

private theorem compactNumericVerifierParseTaskHeadPredicate_eval
    (locals : Fin 14 -> Nat) (global : Fin 5 -> Nat) :
    (compactNumericVerifierTaskBoundedHeadDef.val ⇜
        compactNumericVerifierParseTaskHeadTerms).Evalb
        (Matrix.appendr locals global) ↔
      CompactNumericVerifierTaskBoundedHead
        (global 0) (global 1) (global 2) (global 3) (global 4)
        (compactNumericVerifierTaskRowCoordinatesOf
          (locals 0) (locals 1) (locals 2) (locals 3) (locals 4)
          (locals 5) (locals 6) (locals 7) (locals 8) (locals 9)
          (locals 10) (locals 11) (locals 12))
        { gammaBoundarySize := locals 13 } := by
  rw [Semiformula.eval_substs]
  have henv :
      (Semiterm.val (Matrix.appendr locals global) Empty.elim ∘
        compactNumericVerifierParseTaskHeadTerms) =
        compactNumericVerifierTaskBoundedHeadEnvironment
          (global 0) (global 1) (global 2) (global 3) (global 4)
          (locals 0) (locals 1) (locals 2) (locals 3) (locals 4)
          (locals 5) (locals 6) (locals 7) (locals 8) (locals 9)
          (locals 10) (locals 11) (locals 12) (locals 13) := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [henv]
  exact compactNumericVerifierTaskBoundedHeadDef_spec
    (global 0) (global 1) (global 2) (global 3) (global 4)
    (locals 0) (locals 1) (locals 2) (locals 3) (locals 4)
    (locals 5) (locals 6) (locals 7) (locals 8) (locals 9)
    (locals 10) (locals 11) (locals 12) (locals 13)

private theorem compactNumericVerifierParseTaskHeadCoreFormula_eval
    (locals : Fin 14 -> Nat) (global : Fin 5 -> Nat) :
    compactNumericVerifierParseTaskHeadCoreFormula.Evalb
        (Matrix.appendr locals global) ↔
      CompactNumericVerifierTaskBoundedHead
        (global 0) (global 1) (global 2) (global 3) (global 4)
        (compactNumericVerifierTaskRowCoordinatesOf
          (locals 0) (locals 1) (locals 2) (locals 3) (locals 4)
          (locals 5) (locals 6) (locals 7) (locals 8) (locals 9)
          (locals 10) (locals 11) (locals 12))
        { gammaBoundarySize := locals 13 } ∧
      locals 2 = 10 ∧ locals 4 = 0 ∧ locals 7 = 0 ∧
      locals 9 = 0 ∧ locals 11 = 0 ∧ locals 12 = 0 := by
  change
    ((compactNumericVerifierTaskBoundedHeadDef.val ⇜
        compactNumericVerifierParseTaskHeadTerms).Evalb
        (Matrix.appendr locals global) ∧
      (arithmeticEq (#(localVariable 2))
        (arithmeticNumeral 10)).Evalb (Matrix.appendr locals global) ∧
      (arithmeticEq (#(localVariable 4))
        (arithmeticNumeral 0)).Evalb (Matrix.appendr locals global) ∧
      (arithmeticEq (#(localVariable 7))
        (arithmeticNumeral 0)).Evalb (Matrix.appendr locals global) ∧
      (arithmeticEq (#(localVariable 9))
        (arithmeticNumeral 0)).Evalb (Matrix.appendr locals global) ∧
      (arithmeticEq (#(localVariable 11))
        (arithmeticNumeral 0)).Evalb (Matrix.appendr locals global) ∧
      (arithmeticEq (#(localVariable 12))
        (arithmeticNumeral 0)).Evalb (Matrix.appendr locals global)) ↔ _
  rw [compactNumericVerifierParseTaskHeadPredicate_eval]
  simp only [arithmeticEq_eval, localVariable_val, arithmeticNumeral_val]

private theorem compactNumericVerifierParseTaskHeadCoreFormula_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierParseTaskHeadCoreFormula := by
  simp [compactNumericVerifierParseTaskHeadCoreFormula,
    compactNumericVerifierParseTaskHeadTerms, arithmeticEq,
    arithmeticNumeral]

def compactNumericVerifierParseTaskHeadDef :
    HierarchySymbol.sigmaZero.Semisentence 5 :=
  .mkSigma
    (boundedVectorBExs (#4 : ArithmeticSemiterm Empty 5) 14
      compactNumericVerifierParseTaskHeadCoreFormula)
    (boundedVectorBExs_sigmaZero
      (#4 : ArithmeticSemiterm Empty 5)
      compactNumericVerifierParseTaskHeadCoreFormula
      compactNumericVerifierParseTaskHeadCoreFormula_sigmaZero)

@[simp] theorem compactNumericVerifierParseTaskHeadDef_spec
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    compactNumericVerifierParseTaskHeadDef.val.Evalb
        ![tokenTable, width, tokenCount, taskBoundary, valueBound] ↔
      CompactNumericVerifierParseTaskHead
        tokenTable width tokenCount taskBoundary valueBound := by
  rw [show compactNumericVerifierParseTaskHeadDef.val =
      boundedVectorBExs (#4 : ArithmeticSemiterm Empty 5) 14
        compactNumericVerifierParseTaskHeadCoreFormula by rfl]
  rw [evalb_boundedVectorBExs]
  change
    (∃ locals : Fin 14 -> Nat,
      (∀ coordinate, locals coordinate ≤ valueBound) ∧
        compactNumericVerifierParseTaskHeadCoreFormula.Evalb
          (Matrix.appendr locals
            ![tokenTable, width, tokenCount, taskBoundary, valueBound])) ↔ _
  rw [show CompactNumericVerifierParseTaskHead
      tokenTable width tokenCount taskBoundary valueBound =
      ∃ locals : Fin 14 -> Nat,
        CompactNumericVerifierTaskBoundedHead
          tokenTable width tokenCount taskBoundary valueBound
          (compactNumericVerifierTaskRowCoordinatesOf
            (locals 0) (locals 1) (locals 2) (locals 3) (locals 4)
            (locals 5) (locals 6) (locals 7) (locals 8) (locals 9)
            (locals 10) (locals 11) (locals 12))
          { gammaBoundarySize := locals 13 } ∧
        locals 2 = 10 ∧ locals 4 = 0 ∧ locals 7 = 0 ∧
        locals 9 = 0 ∧ locals 11 = 0 ∧ locals 12 = 0 by
    apply propext
    constructor
    · rintro ⟨coordinates, sizeWitness, hhead, htag, hgamma,
        hfirst, hsecond, hwitness, hsuffix⟩
      let locals : Fin 14 -> Nat :=
        ![coordinates.start, coordinates.finish, coordinates.tag,
          coordinates.gammaFinish, coordinates.gammaCount,
          coordinates.gammaBoundary, coordinates.firstFinish,
          coordinates.firstCount, coordinates.secondFinish,
          coordinates.secondCount, coordinates.witnessFinish,
          coordinates.witnessCount, coordinates.suffixCount,
          sizeWitness.gammaBoundarySize]
      refine ⟨locals, ?_, htag, hgamma, hfirst, hsecond, hwitness, hsuffix⟩
      simpa [locals, compactNumericVerifierTaskRowCoordinatesOf] using hhead
    · rintro ⟨locals, hhead, htag, hgamma, hfirst, hsecond,
        hwitness, hsuffix⟩
      exact ⟨compactNumericVerifierTaskRowCoordinatesOf
          (locals 0) (locals 1) (locals 2) (locals 3) (locals 4)
          (locals 5) (locals 6) (locals 7) (locals 8) (locals 9)
          (locals 10) (locals 11) (locals 12),
        { gammaBoundarySize := locals 13 }, hhead,
        htag, hgamma, hfirst, hsecond, hwitness, hsuffix⟩]
  constructor
  · rintro ⟨locals, _hbound, hcore⟩
    exact ⟨locals,
      (compactNumericVerifierParseTaskHeadCoreFormula_eval
        locals ![tokenTable, width, tokenCount, taskBoundary, valueBound]).mp
        hcore⟩
  · rintro ⟨locals, hcore⟩
    refine ⟨locals, ?_, ?_⟩
    · intro coordinate
      rcases hcore.1 with
        ⟨hstart, hfinish, htag, hgammaFinish, hgammaCount,
          hgammaBoundary, hfirstFinish, hfirstCount,
          hsecondFinish, hsecondCount, hwitnessFinish,
          hwitnessCount, hsuffixCount, hgammaBoundarySize, _hrest⟩
      fin_cases coordinate
      · exact hstart
      · exact hfinish
      · exact htag
      · exact hgammaFinish
      · exact hgammaCount
      · exact hgammaBoundary
      · exact hfirstFinish
      · exact hfirstCount
      · exact hsecondFinish
      · exact hsecondCount
      · exact hwitnessFinish
      · exact hwitnessCount
      · exact hsuffixCount
      · exact hgammaBoundarySize
    · exact
        (compactNumericVerifierParseTaskHeadCoreFormula_eval
          locals ![tokenTable, width, tokenCount, taskBoundary, valueBound]).mpr
          hcore

theorem compactNumericVerifierParseTaskHeadDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierParseTaskHeadDef.val :=
  compactNumericVerifierParseTaskHeadDef.sigma_prop

private theorem list_eq_singleton_of_length_getI
    {alpha : Type*} [Inhabited alpha] {values : List alpha} {value : alpha}
    (hlength : values.length = 1)
    (hvalue : values.getI 0 = value) :
    values = [value] := by
  cases values with
  | nil => simp at hlength
  | cons head tail =>
      cases tail with
      | nil =>
          simp only [List.getI_cons_zero] at hvalue
          subst head
          rfl
      | cons next rest => simp at hlength

theorem CompactNumericVerifierParseTaskHead.taskList_eq_singleton
    {tokenTable width tokenCount taskBoundary valueBound : Nat}
    {tasks : List CompactNumericVerifierTask}
    (hparse : CompactNumericVerifierParseTaskHead
      tokenTable width tokenCount taskBoundary valueBound)
    (hlength : tasks.length = 1)
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        taskBoundary tasks) :
    tasks = [compactNumericParseTask] := by
  rcases hparse with
    ⟨coordinates, sizeWitness, hhead, htag, hgamma,
      hfirst, hsecond, hwitness, hsuffix⟩
  have hnonempty : 0 < tasks.length := by omega
  rcases hhead.realize_actualHeadWithFields hnonempty hrows with
    ⟨task, htask, htaskTag, _htaskLayout,
      _hgammaRows, hgammaLength,
      _hfirstLayout, hfirstLength,
      _hsecondLayout, hsecondLength,
      _hwitnessLayout, hwitnessLength,
      _hsuffixLayout, hsuffixLength⟩
  have htaskTag' : task.1 = 10 := htaskTag.trans htag
  have hgammaEmpty : task.2.1 = [] :=
    List.length_eq_zero_iff.mp (hgammaLength.trans hgamma)
  have hfirstEmpty : task.2.2.1 = [] :=
    List.length_eq_zero_iff.mp (hfirstLength.trans hfirst)
  have hsecondEmpty : task.2.2.2.1 = [] :=
    List.length_eq_zero_iff.mp (hsecondLength.trans hsecond)
  have hwitnessEmpty : task.2.2.2.2.1 = [] :=
    List.length_eq_zero_iff.mp (hwitnessLength.trans hwitness)
  have hsuffixEmpty : task.2.2.2.2.2 = [] :=
    List.length_eq_zero_iff.mp (hsuffixLength.trans hsuffix)
  have htaskParse : task = compactNumericParseTask := by
    rcases task with ⟨tag, gamma, first, second, witness, suffix⟩
    change tag = 10 at htaskTag'
    change gamma = [] at hgammaEmpty
    change first = [] at hfirstEmpty
    change second = [] at hsecondEmpty
    change witness = [] at hwitnessEmpty
    change suffix = [] at hsuffixEmpty
    subst tag
    subst gamma
    subst first
    subst second
    subst witness
    subst suffix
    rfl
  exact list_eq_singleton_of_length_getI hlength
    (htask.symm.trans htaskParse)

theorem exists_compactNumericVerifierParseTaskHead_of_rows
    {tokenTable width tokenCount taskBoundary tableWidth valueBound : Nat}
    (hgraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount taskBoundary 1 tableWidth valueBound)
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        taskBoundary [compactNumericParseTask]) :
    CompactNumericVerifierParseTaskHead
      tokenTable width tokenCount taskBoundary valueBound := by
  have hrow := hgraph.2 0 (by omega)
  rcases
      FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula.CompactNumericVerifierTaskBoundedRow.exists_boundedHead
        hrow with
    ⟨coordinates, sizeWitness, hhead⟩
  rcases hhead.realize_actualHeadWithFields (by simp) hrows with
    ⟨task, htask, htaskTag, _htaskLayout,
      _hgammaRows, hgammaLength,
      _hfirstLayout, hfirstLength,
      _hsecondLayout, hsecondLength,
      _hwitnessLayout, hwitnessLength,
      _hsuffixLayout, hsuffixLength⟩
  have htaskParse : task = compactNumericParseTask := by
    simpa using htask
  subst task
  refine ⟨coordinates, sizeWitness, hhead, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [compactNumericParseTask,
      compactNumericEmptyNodeFields] using htaskTag.symm
  · simpa [compactNumericParseTask,
      compactNumericEmptyNodeFields] using hgammaLength.symm
  · simpa [compactNumericParseTask,
      compactNumericEmptyNodeFields] using hfirstLength.symm
  · simpa [compactNumericParseTask,
      compactNumericEmptyNodeFields] using hsecondLength.symm
  · simpa [compactNumericParseTask,
      compactNumericEmptyNodeFields] using hwitnessLength.symm
  · simpa [compactNumericParseTask,
      compactNumericEmptyNodeFields] using hsuffixLength.symm

#print axioms compactNumericVerifierParseTaskHeadDef_spec
#print axioms compactNumericVerifierParseTaskHeadDef_sigmaZero
#print axioms CompactNumericVerifierParseTaskHead.taskList_eq_singleton
#print axioms exists_compactNumericVerifierParseTaskHead_of_rows

end FoundationCompactNumericListedDirectVerifierParseTaskHeadFormula
