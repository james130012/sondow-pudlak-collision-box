import integration.FoundationCompactNumericListedDirectVerifierChildResultFormula

/-!
# Bounded row formula for verifier child-result lists

Each row carries seven bounded coordinates: its two public boundaries, the
nested context layout, its Boolean token, and the context boundary-code size.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectVerifierChildResultFormula

def CompactNumericChildResultBoundedRow
    (tokenTable width tokenCount valueBoundary valueBound rowIndex : Nat) :
    Prop :=
  ∃ start, start ≤ valueBound ∧
  ∃ finish, finish ≤ valueBound ∧
  ∃ gammaFinish, gammaFinish ≤ valueBound ∧
  ∃ gammaCount, gammaCount ≤ valueBound ∧
  ∃ gammaBoundary, gammaBoundary ≤ valueBound ∧
  ∃ boolValue, boolValue ≤ valueBound ∧
  ∃ gammaBoundarySize, gammaBoundarySize ≤ valueBound ∧
    CompactFixedWidthEntry valueBoundary tokenCount rowIndex start ∧
    CompactFixedWidthEntry valueBoundary tokenCount (rowIndex + 1) finish ∧
    CompactNumericChildResultCoreGraph tokenTable width tokenCount
      (compactNumericChildResultRowCoordinatesOf
        start finish gammaFinish gammaCount gammaBoundary boolValue)
      { gammaBoundarySize := gammaBoundarySize }

def CompactNumericChildResultListRowsGraph
    (tokenTable width tokenCount valueBoundary valueCount
      tableWidth valueBound : Nat) : Prop :=
  valueBound = 2 ^ tableWidth ∧
    ∀ rowIndex < valueCount,
      CompactNumericChildResultBoundedRow
        tokenTable width tokenCount valueBoundary valueBound rowIndex

def compactNumericChildResultBoundedRowDef :
    𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount valueBoundary valueBound rowIndex.
    ∃ start <⁺ valueBound,
    ∃ finish <⁺ valueBound,
    ∃ gammaFinish <⁺ valueBound,
    ∃ gammaCount <⁺ valueBound,
    ∃ gammaBoundary <⁺ valueBound,
    ∃ boolValue <⁺ valueBound,
    ∃ gammaBoundarySize <⁺ valueBound,
      !(compactFixedWidthEntryDef)
        valueBoundary tokenCount rowIndex start ∧
      !(compactFixedWidthEntryDef)
        valueBoundary tokenCount (rowIndex + 1) finish ∧
      !(compactNumericChildResultCoreGraphDef)
        tokenTable width tokenCount start finish
        gammaFinish gammaCount gammaBoundary boolValue gammaBoundarySize”

@[simp] theorem compactNumericChildResultBoundedRowDef_spec
    (tokenTable width tokenCount valueBoundary valueBound rowIndex : Nat) :
    compactNumericChildResultBoundedRowDef.val.Evalb
        ![tokenTable, width, tokenCount, valueBoundary,
          valueBound, rowIndex] ↔
      CompactNumericChildResultBoundedRow
        tokenTable width tokenCount valueBoundary valueBound rowIndex := by
  have hcore
      (gammaBoundarySize boolValue gammaBoundary gammaCount gammaFinish
        finish start : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![gammaBoundarySize, boolValue, gammaBoundary, gammaCount,
                gammaFinish, finish, start, tokenTable, width, tokenCount,
                valueBoundary, valueBound, rowIndex]
              Empty.elim ∘
            ![(#7 : Semiterm ℒₒᵣ Empty 13), #8, #9,
              #6, #5, #4, #3, #2, #1, #0])
          Empty.elim)
        compactNumericChildResultCoreGraphDef.val ↔
      CompactNumericChildResultCoreGraph tokenTable width tokenCount
        (compactNumericChildResultRowCoordinatesOf
          start finish gammaFinish gammaCount gammaBoundary boolValue)
        { gammaBoundarySize := gammaBoundarySize } := by
    have henv :
        (Semiterm.val
            ![gammaBoundarySize, boolValue, gammaBoundary, gammaCount,
              gammaFinish, finish, start, tokenTable, width, tokenCount,
              valueBoundary, valueBound, rowIndex]
            Empty.elim ∘
          ![(#7 : Semiterm ℒₒᵣ Empty 13), #8, #9,
            #6, #5, #4, #3, #2, #1, #0]) =
          compactNumericChildResultCoreFormulaEnvironment
            tokenTable width tokenCount start finish
            gammaFinish gammaCount gammaBoundary boolValue
            gammaBoundarySize := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactNumericChildResultCoreGraphDef_spec
      tokenTable width tokenCount start finish
      gammaFinish gammaCount gammaBoundary boolValue gammaBoundarySize
  simp [compactNumericChildResultBoundedRowDef,
    CompactNumericChildResultBoundedRow, hcore]

def CompactNumericChildResultBoundedRowWithBool
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat) : Prop :=
  ∃ start, start ≤ valueBound ∧
  ∃ finish, finish ≤ valueBound ∧
  ∃ gammaFinish, gammaFinish ≤ valueBound ∧
  ∃ gammaCount, gammaCount ≤ valueBound ∧
  ∃ gammaBoundary, gammaBoundary ≤ valueBound ∧
  ∃ gammaBoundarySize, gammaBoundarySize ≤ valueBound ∧
    expectedBool ≤ valueBound ∧
    CompactFixedWidthEntry valueBoundary tokenCount rowIndex start ∧
    CompactFixedWidthEntry valueBoundary tokenCount (rowIndex + 1) finish ∧
    CompactNumericChildResultCoreGraph tokenTable width tokenCount
      (compactNumericChildResultRowCoordinatesOf
        start finish gammaFinish gammaCount gammaBoundary expectedBool)
      { gammaBoundarySize := gammaBoundarySize }

def compactNumericChildResultBoundedRowWithBoolDef :
    𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount valueBoundary valueBound rowIndex expectedBool.
    ∃ start <⁺ valueBound,
    ∃ finish <⁺ valueBound,
    ∃ gammaFinish <⁺ valueBound,
    ∃ gammaCount <⁺ valueBound,
    ∃ gammaBoundary <⁺ valueBound,
    ∃ gammaBoundarySize <⁺ valueBound,
      expectedBool ≤ valueBound ∧
      !(compactFixedWidthEntryDef)
        valueBoundary tokenCount rowIndex start ∧
      !(compactFixedWidthEntryDef)
        valueBoundary tokenCount (rowIndex + 1) finish ∧
      !(compactNumericChildResultCoreGraphDef)
        tokenTable width tokenCount start finish
        gammaFinish gammaCount gammaBoundary expectedBool gammaBoundarySize”

@[simp] theorem compactNumericChildResultBoundedRowWithBoolDef_spec
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat) :
    compactNumericChildResultBoundedRowWithBoolDef.val.Evalb
        ![tokenTable, width, tokenCount, valueBoundary,
          valueBound, rowIndex, expectedBool] ↔
      CompactNumericChildResultBoundedRowWithBool
        tokenTable width tokenCount valueBoundary valueBound rowIndex
        expectedBool := by
  have hcore
      (gammaBoundarySize gammaBoundary gammaCount gammaFinish finish start : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![gammaBoundarySize, gammaBoundary, gammaCount, gammaFinish,
                finish, start, tokenTable, width, tokenCount,
                valueBoundary, valueBound, rowIndex, expectedBool]
              Empty.elim ∘
            ![(#6 : Semiterm ℒₒᵣ Empty 13), #7, #8,
              #5, #4, #3, #2, #1, #12, #0])
          Empty.elim)
        compactNumericChildResultCoreGraphDef.val ↔
      CompactNumericChildResultCoreGraph tokenTable width tokenCount
        (compactNumericChildResultRowCoordinatesOf
          start finish gammaFinish gammaCount gammaBoundary expectedBool)
        { gammaBoundarySize := gammaBoundarySize } := by
    have henv :
        (Semiterm.val
            ![gammaBoundarySize, gammaBoundary, gammaCount, gammaFinish,
              finish, start, tokenTable, width, tokenCount,
              valueBoundary, valueBound, rowIndex, expectedBool]
            Empty.elim ∘
          ![(#6 : Semiterm ℒₒᵣ Empty 13), #7, #8,
            #5, #4, #3, #2, #1, #12, #0]) =
          compactNumericChildResultCoreFormulaEnvironment
            tokenTable width tokenCount start finish
            gammaFinish gammaCount gammaBoundary expectedBool
            gammaBoundarySize := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactNumericChildResultCoreGraphDef_spec
      tokenTable width tokenCount start finish
      gammaFinish gammaCount gammaBoundary expectedBool gammaBoundarySize
  simp [compactNumericChildResultBoundedRowWithBoolDef,
    CompactNumericChildResultBoundedRowWithBool, hcore]

def compactNumericChildResultListRowsGraphDef :
    𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount valueBoundary valueCount tableWidth valueBound.
    !expDef valueBound tableWidth ∧
    ∀ rowIndex < valueCount,
      !(compactNumericChildResultBoundedRowDef)
        tokenTable width tokenCount valueBoundary valueBound rowIndex”

@[simp] theorem compactNumericChildResultListRowsGraphDef_spec
    (tokenTable width tokenCount valueBoundary valueCount
      tableWidth valueBound : Nat) :
    compactNumericChildResultListRowsGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, valueBoundary,
          valueCount, tableWidth, valueBound] ↔
      CompactNumericChildResultListRowsGraph
        tokenTable width tokenCount valueBoundary valueCount
        tableWidth valueBound := by
  have hrow (rowIndex : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![rowIndex, tokenTable, width, tokenCount, valueBoundary,
                valueCount, tableWidth, valueBound]
              Empty.elim ∘
            ![(#1 : Semiterm ℒₒᵣ Empty 8), #2, #3, #4, #7, #0])
          Empty.elim)
        compactNumericChildResultBoundedRowDef.val ↔
      CompactNumericChildResultBoundedRow
        tokenTable width tokenCount valueBoundary valueBound rowIndex := by
    have henv :
        (Semiterm.val
            ![rowIndex, tokenTable, width, tokenCount, valueBoundary,
              valueCount, tableWidth, valueBound]
            Empty.elim ∘
          ![(#1 : Semiterm ℒₒᵣ Empty 8), #2, #3, #4, #7, #0]) =
          ![tokenTable, width, tokenCount, valueBoundary,
            valueBound, rowIndex] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactNumericChildResultBoundedRowDef_spec
      tokenTable width tokenCount valueBoundary valueBound rowIndex
  simp [compactNumericChildResultListRowsGraphDef,
    CompactNumericChildResultListRowsGraph, hrow]

theorem compactNumericChildResultBoundedRowDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericChildResultBoundedRowDef.val := by
  simp [compactNumericChildResultBoundedRowDef]

theorem compactNumericChildResultBoundedRowWithBoolDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericChildResultBoundedRowWithBoolDef.val := by
  simp [compactNumericChildResultBoundedRowWithBoolDef]

theorem compactNumericChildResultListRowsGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericChildResultListRowsGraphDef.val := by
  simp [compactNumericChildResultListRowsGraphDef]

def compactNumericChildResultRowTableWidth
    (width tokenCount : Nat) : Nat :=
  (tokenCount + 1) * tokenCount + width + tokenCount + 3

theorem CompactAdditiveStructuredListElementRowLayouts.childResultBoundedRowWithBool
    {tokenTable width tokenCount valueBoundary : Nat}
    {values : List CompactNumericChildResult}
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
      valueBoundary values)
    (rowIndex : Nat) (hrowIndex : rowIndex < values.length) :
    CompactNumericChildResultBoundedRowWithBool
      tokenTable width tokenCount valueBoundary
      (2 ^ compactNumericChildResultRowTableWidth width tokenCount)
      rowIndex (compactAdditiveBoolTag (values.getI rowIndex).2) := by
  let tableWidth :=
    compactNumericChildResultRowTableWidth width tokenCount
  rcases hrows rowIndex hrowIndex with
    ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, hlayout⟩
  rcases CompactNumericChildResultDirectLayout.toCoreGraph hlayout with
    ⟨coordinates, sizeWitness,
      hstart, hfinish, hbool, hcore⟩
  have hbounds := CompactNumericChildResultCoreGraph.bounds hcore
  have htokenWidth : tokenCount ≤ tableWidth := by
    dsimp only [tableWidth, compactNumericChildResultRowTableWidth]
    omega
  have hareaWidth : (tokenCount + 1) * tokenCount ≤ tableWidth := by
    dsimp only [tableWidth, compactNumericChildResultRowTableWidth]
    omega
  have honeWidth : 1 ≤ tableWidth := by
    dsimp only [tableWidth, compactNumericChildResultRowTableWidth]
    omega
  have hwidthPower : tableWidth ≤ 2 ^ tableWidth :=
    Nat.le_of_lt tableWidth.lt_two_pow_self
  have hsmall {value : Nat} (hvalue : value ≤ tokenCount) :
      value ≤ 2 ^ tableWidth :=
    (hvalue.trans htokenWidth).trans hwidthPower
  have hgammaArea :
      (coordinates.gammaCount + 1) * tokenCount ≤
        (tokenCount + 1) * tokenCount :=
    Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right hbounds.gammaCount_le 1)
  have hgammaBoundarySize :
      Nat.size coordinates.gammaBoundary ≤ tableWidth :=
    hbounds.gammaBoundary_size_le.trans
      (hgammaArea.trans hareaWidth)
  have hgammaBoundaryBound :
      coordinates.gammaBoundary ≤ 2 ^ tableWidth :=
    (Nat.size_le.mp hgammaBoundarySize).le
  have hgammaSizeBound :
      sizeWitness.gammaBoundarySize ≤ 2 ^ tableWidth :=
    (hbounds.gammaBoundarySize_le.trans
      (hgammaArea.trans hareaWidth)).trans hwidthPower
  have hboolBound :
      compactAdditiveBoolTag (values.getI rowIndex).2 ≤
        2 ^ tableWidth := by
    rw [← hbool]
    exact (hbounds.boolValue_le_one.trans honeWidth).trans hwidthPower
  have hcoordinates :
      compactNumericChildResultRowCoordinatesOf
          coordinates.start coordinates.finish coordinates.gammaFinish
          coordinates.gammaCount coordinates.gammaBoundary
          (compactAdditiveBoolTag (values.getI rowIndex).2) =
        coordinates := by
    cases coordinates
    simp_all [compactNumericChildResultRowCoordinatesOf]
  have hsizeWitness :
      ({ gammaBoundarySize := sizeWitness.gammaBoundarySize } :
        CompactNumericChildResultSizeWitness) = sizeWitness := by
    cases sizeWitness
    rfl
  refine ⟨coordinates.start, hsmall hbounds.start_le,
    coordinates.finish, hsmall hbounds.finish_le,
    coordinates.gammaFinish, hsmall hbounds.gammaFinish_le,
    coordinates.gammaCount, hsmall hbounds.gammaCount_le,
    coordinates.gammaBoundary, hgammaBoundaryBound,
    sizeWitness.gammaBoundarySize, hgammaSizeBound,
    hboolBound, ?_, ?_, ?_⟩
  · simpa only [hstart] using hleftEntry
  · simpa only [hfinish] using hrightEntry
  · rw [hcoordinates, hsizeWitness]
    exact hcore

theorem CompactAdditiveStructuredListElementRowLayouts.childResultListRowsGraph
    {tokenTable width tokenCount valueBoundary : Nat}
    {values : List CompactNumericChildResult}
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
      valueBoundary values) :
    CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount valueBoundary values.length
      (compactNumericChildResultRowTableWidth width tokenCount)
      (2 ^ compactNumericChildResultRowTableWidth width tokenCount) := by
  let tableWidth :=
    compactNumericChildResultRowTableWidth width tokenCount
  refine ⟨rfl, ?_⟩
  intro rowIndex hrowIndex
  rcases hrows rowIndex hrowIndex with
    ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, hlayout⟩
  rcases CompactNumericChildResultDirectLayout.toCoreGraph hlayout with
    ⟨coordinates, sizeWitness,
      hstart, hfinish, _hbool, hcore⟩
  have hbounds := CompactNumericChildResultCoreGraph.bounds hcore
  have htokenWidth : tokenCount ≤ tableWidth := by
    dsimp only [tableWidth, compactNumericChildResultRowTableWidth]
    omega
  have hareaWidth : (tokenCount + 1) * tokenCount ≤ tableWidth := by
    dsimp only [tableWidth, compactNumericChildResultRowTableWidth]
    omega
  have honeWidth : 1 ≤ tableWidth := by
    dsimp only [tableWidth, compactNumericChildResultRowTableWidth]
    omega
  have hwidthPower : tableWidth ≤ 2 ^ tableWidth :=
    Nat.le_of_lt tableWidth.lt_two_pow_self
  have hsmall {value : Nat} (hvalue : value ≤ tokenCount) :
      value ≤ 2 ^ tableWidth :=
    (hvalue.trans htokenWidth).trans hwidthPower
  have hgammaArea :
      (coordinates.gammaCount + 1) * tokenCount ≤
        (tokenCount + 1) * tokenCount :=
    Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right hbounds.gammaCount_le 1)
  have hgammaBoundarySize :
      Nat.size coordinates.gammaBoundary ≤ tableWidth :=
    hbounds.gammaBoundary_size_le.trans
      (hgammaArea.trans hareaWidth)
  have hgammaBoundaryBound :
      coordinates.gammaBoundary ≤ 2 ^ tableWidth :=
    (Nat.size_le.mp hgammaBoundarySize).le
  have hgammaSizeBound :
      sizeWitness.gammaBoundarySize ≤ 2 ^ tableWidth :=
    (hbounds.gammaBoundarySize_le.trans
      (hgammaArea.trans hareaWidth)).trans hwidthPower
  have hboolBound : coordinates.boolValue ≤ 2 ^ tableWidth :=
    (hbounds.boolValue_le_one.trans honeWidth).trans hwidthPower
  refine ⟨coordinates.start, hsmall hbounds.start_le,
    coordinates.finish, hsmall hbounds.finish_le,
    coordinates.gammaFinish, hsmall hbounds.gammaFinish_le,
    coordinates.gammaCount, hsmall hbounds.gammaCount_le,
    coordinates.gammaBoundary, hgammaBoundaryBound,
    coordinates.boolValue, hboolBound,
    sizeWitness.gammaBoundarySize, hgammaSizeBound, ?_, ?_, hcore⟩
  · simpa only [hstart] using hleftEntry
  · simpa only [hfinish] using hrightEntry

#print axioms compactNumericChildResultBoundedRowDef_spec
#print axioms compactNumericChildResultListRowsGraphDef_spec
#print axioms compactNumericChildResultBoundedRowDef_sigmaZero
#print axioms compactNumericChildResultBoundedRowWithBoolDef_spec
#print axioms compactNumericChildResultBoundedRowWithBoolDef_sigmaZero
#print axioms compactNumericChildResultListRowsGraphDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.childResultBoundedRowWithBool
#print axioms CompactAdditiveStructuredListElementRowLayouts.childResultListRowsGraph

end FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
