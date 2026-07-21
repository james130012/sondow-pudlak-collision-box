import integration.FoundationCompactNumericListedDirectCrossTableSliceEquality
import integration.FoundationCompactNumericListedDirectFormulaSetChecks

/-!
# Cross-table formula-set equality against one raw formula stream

The accepted verifier state stores its conclusion as a structured list of
formula-token lists, each with one additive list header.  The public formula
code decodes to the raw token body without that header.  This bounded graph
requires a nonempty conclusion and compares every stored formula body with the
same raw public formula stream across two independently packed tables.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCrossTableFormulaSetSingleton

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectCrossTableSliceEquality

def CompactCrossTableFormulaSetEqSingleton
    (actualTable actualWidth actualTokenCount actualBoundary actualCount
      formulaTable formulaWidth formulaTokenCount : Nat) : Prop :=
  0 < actualCount /\
    forall index, index < actualCount ->
      exists formulaStart, formulaStart <= actualTokenCount /\
      exists formulaFinish, formulaFinish <= actualTokenCount /\
        CompactFixedWidthEntry actualBoundary actualTokenCount
          index formulaStart /\
        CompactFixedWidthEntry actualBoundary actualTokenCount
          (index + 1) formulaFinish /\
        CompactFixedWidthCrossTableSlicesEq
          actualTable actualWidth actualTokenCount
            (formulaStart + 1) formulaFinish
          formulaTable formulaWidth formulaTokenCount 0 formulaTokenCount

def compactCrossTableFormulaSetEqSingletonDef :
    HierarchySymbol.sigmaZero.Semisentence 8 := .mkSigma
  “actualTable actualWidth actualTokenCount actualBoundary actualCount
      formulaTable formulaWidth formulaTokenCount.
    0 < actualCount ∧
    ∀ index < actualCount,
      ∃ formulaStart <⁺ actualTokenCount,
        ∃ formulaFinish <⁺ actualTokenCount,
          !(compactFixedWidthEntryDef)
            actualBoundary actualTokenCount index formulaStart ∧
          !(compactFixedWidthEntryDef)
            actualBoundary actualTokenCount (index + 1) formulaFinish ∧
          !(compactFixedWidthCrossTableSlicesEqDef)
            actualTable actualWidth actualTokenCount
              (formulaStart + 1) formulaFinish
            formulaTable formulaWidth formulaTokenCount 0 formulaTokenCount”

@[simp] theorem compactCrossTableFormulaSetEqSingletonDef_spec
    (actualTable actualWidth actualTokenCount actualBoundary actualCount
      formulaTable formulaWidth formulaTokenCount : Nat) :
    compactCrossTableFormulaSetEqSingletonDef.val.Evalb
        ![actualTable, actualWidth, actualTokenCount,
          actualBoundary, actualCount,
          formulaTable, formulaWidth, formulaTokenCount] ↔
      CompactCrossTableFormulaSetEqSingleton
        actualTable actualWidth actualTokenCount actualBoundary actualCount
        formulaTable formulaWidth formulaTokenCount := by
  have hcross (formulaFinish formulaStart index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![formulaFinish, formulaStart, index,
                actualTable, actualWidth, actualTokenCount,
                actualBoundary, actualCount,
                formulaTable, formulaWidth, formulaTokenCount]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 11), #4, #5,
              ‘#1 + 1’, #0, #8, #9, #10, (↑(0 : Nat)), #10])
          Empty.elim) compactFixedWidthCrossTableSlicesEqDef.val ↔
        CompactFixedWidthCrossTableSlicesEq
          actualTable actualWidth actualTokenCount
            (formulaStart + 1) formulaFinish
          formulaTable formulaWidth formulaTokenCount 0 formulaTokenCount := by
    have henv :
        (Semiterm.val
            ![formulaFinish, formulaStart, index,
              actualTable, actualWidth, actualTokenCount,
              actualBoundary, actualCount,
              formulaTable, formulaWidth, formulaTokenCount]
            Empty.elim ∘
          ![(#3 : Semiterm ℒₒᵣ Empty 11), #4, #5,
            ‘#1 + 1’, #0, #8, #9, #10, (↑(0 : Nat)), #10]) =
          ![actualTable, actualWidth, actualTokenCount,
            formulaStart + 1, formulaFinish,
            formulaTable, formulaWidth, formulaTokenCount,
            0, formulaTokenCount] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactFixedWidthCrossTableSlicesEqDef_spec
      actualTable actualWidth actualTokenCount
      (formulaStart + 1) formulaFinish
      formulaTable formulaWidth formulaTokenCount 0 formulaTokenCount
  simp [compactCrossTableFormulaSetEqSingletonDef,
    CompactCrossTableFormulaSetEqSingleton, hcross]

theorem compactCrossTableFormulaSetEqSingletonDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactCrossTableFormulaSetEqSingletonDef.val :=
  compactCrossTableFormulaSetEqSingletonDef.sigma_prop

private theorem formula_eq_of_crossTable
    {actualTable actualWidth actualTokenCount formulaStart formulaFinish
      formulaTable formulaWidth formulaTokenCount : Nat}
    {actualFormula formulaTokens : List Nat}
    (hcross : CompactFixedWidthCrossTableSlicesEq
      actualTable actualWidth actualTokenCount
        (formulaStart + 1) formulaFinish
      formulaTable formulaWidth formulaTokenCount 0 formulaTokenCount)
    (hactual : CompactAdditiveNatListDirectLayout
      actualTable actualWidth actualTokenCount
      formulaStart formulaFinish actualFormula)
    (hformulaLength : formulaTokens.length = formulaTokenCount)
    (hformulaEntry : forall index, index < formulaTokens.length ->
      CompactFixedWidthEntry formulaTable formulaWidth
        index (formulaTokens.getI index)) :
    actualFormula = formulaTokens := by
  have hactualFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hactual
  rcases hcross with
    ⟨count, _hactualCount, _hformulaCount,
      hactualCrossFinish, hformulaCrossFinish,
      hactualBound, hformulaBound, hbits⟩
  have hlength : actualFormula.length = formulaTokens.length := by omega
  let hcross' : CompactFixedWidthCrossTableSlicesEq
      actualTable actualWidth actualTokenCount
        (formulaStart + 1) formulaFinish
      formulaTable formulaWidth formulaTokenCount 0 formulaTokenCount :=
    ⟨count, _hactualCount, _hformulaCount,
      hactualCrossFinish, hformulaCrossFinish,
      hactualBound, hformulaBound, hbits⟩
  apply List.ext_getElem
  · exact hlength
  · intro index hactualIndex hformulaIndex
    have hactualEntry :=
      CompactAdditiveNatListDirectLayout.valueEntry
        hactual index hactualIndex
    have hactualEntry' : CompactFixedWidthEntry
        actualTable actualWidth (formulaStart + 1 + index)
          (actualFormula.getI index) := by
      simpa [Nat.add_assoc] using hactualEntry
    have hformulaEntry' : CompactFixedWidthEntry
        formulaTable formulaWidth (0 + index)
          (formulaTokens.getI index) := by
      simpa using hformulaEntry index hformulaIndex
    have hoffset : index < formulaFinish - (formulaStart + 1) := by omega
    have hvalue := hcross'.entryValue_eq_at_offset
      hoffset hactualEntry' hformulaEntry'
    simpa only [List.getI_eq_getElem actualFormula hactualIndex,
      List.getI_eq_getElem formulaTokens hformulaIndex] using hvalue

theorem compactCrossTableFormulaSetEqSingleton_iff
    {actualTable actualWidth actualTokenCount actualBoundary
      formulaTable formulaWidth formulaTokenCount : Nat}
    {actual : List (List Nat)} {formulaTokens : List Nat}
    (hactual : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout
      actualTable actualWidth actualTokenCount actualBoundary actual)
    (hformulaLength : formulaTokens.length = formulaTokenCount)
    (hformulaEntry : forall index, index < formulaTokens.length ->
      CompactFixedWidthEntry formulaTable formulaWidth
        index (formulaTokens.getI index)) :
    CompactCrossTableFormulaSetEqSingleton
        actualTable actualWidth actualTokenCount actualBoundary actual.length
        formulaTable formulaWidth formulaTokenCount ↔
      actual.toFinset = {formulaTokens} := by
  constructor
  · rintro ⟨hpositive, hrows⟩
    have hformulaOfMem (value : List Nat) (hvalue : value ∈ actual) :
        value = formulaTokens := by
      obtain ⟨index, hindex, hget⟩ := List.mem_iff_getElem.mp hvalue
      rcases hrows index hindex with
        ⟨formulaStart, _hformulaStart,
          formulaFinish, _hformulaFinish,
          hstartEntry, hfinishEntry, hcross⟩
      rcases hactual index hindex with
        ⟨rowStart, _hrowStart, rowFinish, _hrowFinish,
          hrowStartEntry, hrowFinishEntry, hrowLayout⟩
      have hstart : formulaStart = rowStart :=
        (CompactFixedWidthEntry.value_eq_tableValue hstartEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue hrowStartEntry).symm
      have hfinish : formulaFinish = rowFinish :=
        (CompactFixedWidthEntry.value_eq_tableValue hfinishEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue hrowFinishEntry).symm
      subst formulaStart
      subst formulaFinish
      have heq := formula_eq_of_crossTable hcross hrowLayout
        hformulaLength hformulaEntry
      rw [List.getI_eq_getElem actual hindex, hget] at heq
      exact heq
    have htargetMem : formulaTokens ∈ actual := by
      have hzero : 0 < actual.length := hpositive
      have hheadMem : actual.getI 0 ∈ actual := by
        rw [List.getI_eq_getElem actual hzero]
        exact List.getElem_mem hzero
      simpa [hformulaOfMem (actual.getI 0) hheadMem] using hheadMem
    apply Finset.ext
    intro value
    constructor
    · intro hvalue
      have hvalueList : value ∈ actual := by simpa using hvalue
      simp [hformulaOfMem value hvalueList]
    · intro hvalue
      have hvalueEq : value = formulaTokens := by simpa using hvalue
      subst value
      simpa using htargetMem
  · intro hset
    have hpositive : 0 < actual.length := by
      by_contra hnot
      have hempty : actual = [] := List.length_eq_zero_iff.mp (by omega)
      subst actual
      simp at hset
    refine ⟨hpositive, ?_⟩
    intro index hindex
    rcases hactual index hindex with
      ⟨formulaStart, hformulaStart,
        formulaFinish, hformulaFinish,
        hstartEntry, hfinishEntry, hrowLayout⟩
    have hrowMem : actual.getI index ∈ actual := by
      rw [List.getI_eq_getElem actual hindex]
      exact List.getElem_mem hindex
    have hrowEq : actual.getI index = formulaTokens := by
      have : actual.getI index ∈ ({formulaTokens} : Finset (List Nat)) := by
        rw [← hset]
        simpa using hrowMem
      simpa using this
    have hrowLayout' : CompactAdditiveNatListDirectLayout
        actualTable actualWidth actualTokenCount
        formulaStart formulaFinish formulaTokens := by
      simpa only [hrowEq] using hrowLayout
    have hactualFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq hrowLayout'
    have hcross : CompactFixedWidthCrossTableSlicesEq
        actualTable actualWidth actualTokenCount
          (formulaStart + 1) formulaFinish
        formulaTable formulaWidth formulaTokenCount 0 formulaTokenCount := by
      apply CompactFixedWidthCrossTableSlicesEq.of_entry_values
          (values := formulaTokens)
      · omega
      · simpa [hformulaLength]
      · exact hformulaFinish
      · exact Nat.le_refl _
      · intro offset hoffset
        simpa [Nat.add_assoc] using
          (CompactAdditiveNatListDirectLayout.valueEntry
            hrowLayout' offset hoffset)
      · intro offset hoffset
        simpa using hformulaEntry offset hoffset
    exact ⟨formulaStart, hformulaStart,
      formulaFinish, hformulaFinish,
      hstartEntry, hfinishEntry, hcross⟩

#print axioms compactCrossTableFormulaSetEqSingletonDef_spec
#print axioms compactCrossTableFormulaSetEqSingletonDef_sigmaZero
#print axioms compactCrossTableFormulaSetEqSingleton_iff

end FoundationCompactNumericListedDirectCrossTableFormulaSetSingleton
