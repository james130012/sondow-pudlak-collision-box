import integration.FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
import integration.FoundationCompactNumericListedDirectChildResultRowEquality

/-!
# Public coordinates for bounded verifier child-result rows

This refines a bounded child-result row by making every row coordinate an
arithmetic parameter, while retaining the row bounds, boundary-table entries,
and child-result core graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectChildResultBoundedRowExposedFormula

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectChildResultRowEquality

def CompactNumericChildResultBoundedRowExposed
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      start finish gammaFinish gammaCount gammaBoundary boolValue
      gammaBoundarySize : Nat) : Prop :=
  start ≤ valueBound ∧
    finish ≤ valueBound ∧
    gammaFinish ≤ valueBound ∧
    gammaCount ≤ valueBound ∧
    gammaBoundary ≤ valueBound ∧
    boolValue ≤ valueBound ∧
    gammaBoundarySize ≤ valueBound ∧
    CompactFixedWidthEntry valueBoundary tokenCount rowIndex start ∧
    CompactFixedWidthEntry valueBoundary tokenCount (rowIndex + 1) finish ∧
    CompactNumericChildResultCoreGraph tokenTable width tokenCount
      (compactNumericChildResultRowCoordinatesOf
        start finish gammaFinish gammaCount gammaBoundary boolValue)
      { gammaBoundarySize := gammaBoundarySize }

def compactNumericChildResultBoundedRowExposedDef :
    𝚺₀.Semisentence 13 := .mkSigma
  “tokenTable width tokenCount valueBoundary valueBound rowIndex
      start finish gammaFinish gammaCount gammaBoundary boolValue
      gammaBoundarySize.
    start ≤ valueBound ∧
    finish ≤ valueBound ∧
    gammaFinish ≤ valueBound ∧
    gammaCount ≤ valueBound ∧
    gammaBoundary ≤ valueBound ∧
    boolValue ≤ valueBound ∧
    gammaBoundarySize ≤ valueBound ∧
    !(compactFixedWidthEntryDef)
      valueBoundary tokenCount rowIndex start ∧
    !(compactFixedWidthEntryDef)
      valueBoundary tokenCount (rowIndex + 1) finish ∧
    !(compactNumericChildResultCoreGraphDef)
      tokenTable width tokenCount start finish gammaFinish gammaCount
      gammaBoundary boolValue gammaBoundarySize”

@[simp] theorem compactNumericChildResultBoundedRowExposedDef_spec
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      start finish gammaFinish gammaCount gammaBoundary boolValue
      gammaBoundarySize : Nat) :
    compactNumericChildResultBoundedRowExposedDef.val.Evalb
        ![tokenTable, width, tokenCount, valueBoundary, valueBound, rowIndex,
          start, finish, gammaFinish, gammaCount, gammaBoundary, boolValue,
          gammaBoundarySize] ↔
      CompactNumericChildResultBoundedRowExposed
        tokenTable width tokenCount valueBoundary valueBound rowIndex
        start finish gammaFinish gammaCount gammaBoundary boolValue
        gammaBoundarySize := by
  have hcore :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount, valueBoundary, valueBound,
                rowIndex, start, finish, gammaFinish, gammaCount,
                gammaBoundary, boolValue, gammaBoundarySize]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2, #6, #7, #8, #9,
              #10, #11, #12])
          Empty.elim)
        compactNumericChildResultCoreGraphDef.val ↔
      CompactNumericChildResultCoreGraph tokenTable width tokenCount
        (compactNumericChildResultRowCoordinatesOf
          start finish gammaFinish gammaCount gammaBoundary boolValue)
        { gammaBoundarySize := gammaBoundarySize } := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount, valueBoundary, valueBound,
              rowIndex, start, finish, gammaFinish, gammaCount,
              gammaBoundary, boolValue, gammaBoundarySize]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2, #6, #7, #8, #9,
            #10, #11, #12]) =
          compactNumericChildResultCoreFormulaEnvironment
            tokenTable width tokenCount start finish gammaFinish gammaCount
            gammaBoundary boolValue gammaBoundarySize := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactNumericChildResultCoreGraphDef_spec
      tokenTable width tokenCount start finish gammaFinish gammaCount
      gammaBoundary boolValue gammaBoundarySize
  simp [compactNumericChildResultBoundedRowExposedDef,
    CompactNumericChildResultBoundedRowExposed, hcore]

theorem compactNumericChildResultBoundedRowExposedDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericChildResultBoundedRowExposedDef.val := by
  simp [compactNumericChildResultBoundedRowExposedDef]

theorem CompactNumericChildResultBoundedRowExposed.to_boundedRow
    {tokenTable width tokenCount valueBoundary valueBound rowIndex
      start finish gammaFinish gammaCount gammaBoundary boolValue
      gammaBoundarySize : Nat}
    (hexposed : CompactNumericChildResultBoundedRowExposed
      tokenTable width tokenCount valueBoundary valueBound rowIndex
      start finish gammaFinish gammaCount gammaBoundary boolValue
      gammaBoundarySize) :
    CompactNumericChildResultBoundedRow
      tokenTable width tokenCount valueBoundary valueBound rowIndex := by
  rcases hexposed with
    ⟨hstart, hfinish, hgammaFinish, hgammaCount, hgammaBoundary,
      hboolValue, hgammaBoundarySize, hstartEntry, hfinishEntry, hcore⟩
  exact ⟨start, hstart, finish, hfinish, gammaFinish, hgammaFinish,
    gammaCount, hgammaCount, gammaBoundary, hgammaBoundary,
    boolValue, hboolValue, gammaBoundarySize, hgammaBoundarySize,
    hstartEntry, hfinishEntry, hcore⟩

theorem CompactNumericChildResultBoundedRow.exists_exposed
    {tokenTable width tokenCount valueBoundary valueBound rowIndex : Nat}
    (hrow : CompactNumericChildResultBoundedRow
      tokenTable width tokenCount valueBoundary valueBound rowIndex) :
    ∃ start finish gammaFinish gammaCount gammaBoundary boolValue
      gammaBoundarySize,
      CompactNumericChildResultBoundedRowExposed
        tokenTable width tokenCount valueBoundary valueBound rowIndex
        start finish gammaFinish gammaCount gammaBoundary boolValue
        gammaBoundarySize := by
  rcases hrow with
    ⟨start, hstart, finish, hfinish, gammaFinish, hgammaFinish,
      gammaCount, hgammaCount, gammaBoundary, hgammaBoundary,
      boolValue, hboolValue, gammaBoundarySize, hgammaBoundarySize,
      hstartEntry, hfinishEntry, hcore⟩
  exact ⟨start, finish, gammaFinish, gammaCount, gammaBoundary, boolValue,
    gammaBoundarySize, hstart, hfinish, hgammaFinish, hgammaCount,
    hgammaBoundary, hboolValue, hgammaBoundarySize, hstartEntry,
    hfinishEntry, hcore⟩

theorem CompactNumericChildResultListRowsGraph.exists_exposed
    {tokenTable width tokenCount valueBoundary valueCount tableWidth
      valueBound rowIndex : Nat}
    (hgraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount valueBoundary valueCount tableWidth valueBound)
    (hrowIndex : rowIndex < valueCount) :
    ∃ start finish gammaFinish gammaCount gammaBoundary boolValue
      gammaBoundarySize,
      CompactNumericChildResultBoundedRowExposed
        tokenTable width tokenCount valueBoundary valueBound rowIndex
        start finish gammaFinish gammaCount gammaBoundary boolValue
        gammaBoundarySize := by
  rcases hgraph.2 rowIndex hrowIndex with
    ⟨start, hstart, finish, hfinish, gammaFinish, hgammaFinish,
      gammaCount, hgammaCount, gammaBoundary, hgammaBoundary,
      boolValue, hboolValue, gammaBoundarySize, hgammaBoundarySize,
      hstartEntry, hfinishEntry, hcore⟩
  exact ⟨start, finish, gammaFinish, gammaCount, gammaBoundary, boolValue,
    gammaBoundarySize, hstart, hfinish, hgammaFinish, hgammaCount,
    hgammaBoundary, hboolValue, hgammaBoundarySize, hstartEntry,
    hfinishEntry, hcore⟩

theorem CompactNumericChildResultBoundedRowExposed.realize_actual
    {tokenTable width tokenCount valueBoundary valueBound rowIndex
      start finish gammaFinish gammaCount gammaBoundary boolValue
      gammaBoundarySize : Nat}
    {target : List CompactNumericChildResult}
    (hexposed : CompactNumericChildResultBoundedRowExposed
      tokenTable width tokenCount valueBoundary valueBound rowIndex
      start finish gammaFinish gammaCount gammaBoundary boolValue
      gammaBoundarySize)
    (hrowIndex : rowIndex < target.length)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        valueBoundary target) :
    exists value : CompactNumericChildResult,
      target.getI rowIndex = value ∧
      CompactNumericChildResultDirectLayout
        tokenTable width tokenCount start finish value ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          gammaBoundary value.1 ∧
      value.1.length = gammaCount ∧
      compactAdditiveBoolTag value.2 = boolValue := by
  rcases hexposed with
    ⟨_hstart, _hfinish, _hgammaFinish, _hgammaCount,
      _hgammaBoundary, _hboolValue, _hgammaBoundarySize,
      hstartEntry, hfinishEntry, hcore⟩
  rcases htargetRows rowIndex hrowIndex with
    ⟨actualStart, _hactualStart, actualFinish, _hactualFinish,
      hactualStartEntry, hactualFinishEntry, hactualLayout⟩
  have hstartEq : start = actualStart :=
    (CompactFixedWidthEntry.value_eq_tableValue hstartEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue hactualStartEntry).symm
  have hfinishEq : finish = actualFinish :=
    (CompactFixedWidthEntry.value_eq_tableValue hfinishEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue hactualFinishEntry).symm
  rw [← hstartEq, ← hfinishEq] at hactualLayout
  rcases CompactNumericChildResultCoreGraph.realizeDirectLayoutWithRows
      hcore with
    ⟨value, hvalueLayout, hvalueRows, hvalueLength, hvalueBool⟩
  have hvalueActual : value = target.getI rowIndex :=
    CompactNumericChildResultCoreGraph.realizedValue_eq
      hcore hactualLayout hvalueLayout
  exact ⟨value, hvalueActual.symm, hvalueLayout, hvalueRows,
    hvalueLength, hvalueBool⟩

#print axioms compactNumericChildResultBoundedRowExposedDef_spec
#print axioms compactNumericChildResultBoundedRowExposedDef_sigmaZero
#print axioms CompactNumericChildResultBoundedRow.exists_exposed
#print axioms CompactNumericChildResultBoundedRowExposed.realize_actual

end FoundationCompactNumericListedDirectChildResultBoundedRowExposedFormula
