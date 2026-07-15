import integration.FoundationCompactNumericListedDirectFormulaShiftListRow
import integration.FoundationCompactNumericListedDirectNatListListSameRows
import integration.FoundationCompactNumericListedDirectNatListListRowsRealization
import integration.FoundationCompactNumericListedRuleChecks

/-!
# Exact list-level formula shift rows

Every input formula carries an unconditional total shift trace.  A separate
fixed-width table records each exact-success bit.  The public `Option.foldr`
result is the candidate list only when every bit is one; otherwise it is the
empty default list.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaShiftExactListRows

open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectFormulaTransformTotalOutcomeFormula
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectFormulaShiftListRow
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectNatListListRowsRealization
open FoundationCompactNumericListedDirectNatListListSameRows

def CompactFormulaShiftExactListRows
    (tokenTable width tokenCount
      sourceBoundary formulaCount candidateBoundary successTable
      expectedBoundary expectedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      witnessBound : Nat) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount emptyStart 0 emptyFinish
        emptyBoundary emptyBoundarySize ∧
    (∀ index < formulaCount,
      ∃ sourceStart, sourceStart ≤ witnessBound ∧
      ∃ sourceFinish, sourceFinish ≤ witnessBound ∧
      ∃ sourceInnerCount, sourceInnerCount ≤ witnessBound ∧
      ∃ sourceInnerBoundary, sourceInnerBoundary ≤ witnessBound ∧
      ∃ sourceBoundarySize, sourceBoundarySize ≤ witnessBound ∧
      ∃ candidateStart, candidateStart ≤ witnessBound ∧
      ∃ candidateFinish, candidateFinish ≤ witnessBound ∧
      ∃ candidateInnerCount, candidateInnerCount ≤ witnessBound ∧
      ∃ candidateInnerBoundary, candidateInnerBoundary ≤ witnessBound ∧
      ∃ candidateBoundarySize, candidateBoundarySize ≤ witnessBound ∧
      ∃ stateBoundary, stateBoundary ≤ witnessBound ∧
      ∃ stateCount, stateCount ≤ witnessBound ∧
      ∃ tableWidth, tableWidth ≤ witnessBound ∧
      ∃ valueBound, valueBound ≤ witnessBound ∧
      ∃ successValue, successValue ≤ witnessBound ∧
      ∃ finalStart, finalStart ≤ witnessBound ∧
      ∃ finalFinish, finalFinish ≤ witnessBound ∧
      ∃ finalParserFinish, finalParserFinish ≤ witnessBound ∧
      ∃ finalParserTokensFinish,
        finalParserTokensFinish ≤ witnessBound ∧
      ∃ finalParserTasksFinish,
        finalParserTasksFinish ≤ witnessBound ∧
      ∃ finalParserTokensBoundary,
        finalParserTokensBoundary ≤ witnessBound ∧
      ∃ finalParserTokensCount,
        finalParserTokensCount ≤ witnessBound ∧
      ∃ finalParserTasksBoundary,
        finalParserTasksBoundary ≤ witnessBound ∧
      ∃ finalParserTasksCount,
        finalParserTasksCount ≤ witnessBound ∧
      ∃ finalOutputBoundary, finalOutputBoundary ≤ witnessBound ∧
      ∃ finalOutputCount, finalOutputCount ≤ witnessBound ∧
      ∃ finalParserTokensBoundarySize,
        finalParserTokensBoundarySize ≤ witnessBound ∧
      ∃ finalParserTasksBoundarySize,
        finalParserTasksBoundarySize ≤ witnessBound ∧
      ∃ finalOutputBoundarySize,
        finalOutputBoundarySize ≤ witnessBound ∧
        CompactFormulaShiftListRow
          tokenTable width tokenCount
          sourceBoundary candidateBoundary successTable formulaCount index
          emptyStart emptyFinish emptyBoundary
          sourceStart sourceFinish sourceInnerCount sourceInnerBoundary
            sourceBoundarySize
          candidateStart candidateFinish candidateInnerCount
            candidateInnerBoundary candidateBoundarySize
          stateBoundary stateCount tableWidth valueBound successValue
          (compactFormulaTransformStateRowCoordinatesOf
            finalStart finalFinish finalParserFinish
            finalParserTokensFinish finalParserTasksFinish
            finalParserTokensBoundary finalParserTokensCount
            finalParserTasksBoundary finalParserTasksCount
            finalOutputBoundary finalOutputCount)
          { parserTokensBoundarySize := finalParserTokensBoundarySize
            parserTasksBoundarySize := finalParserTasksBoundarySize
            outputBoundarySize := finalOutputBoundarySize }) ∧
    (((∀ index < formulaCount,
        CompactFixedWidthEntry successTable tokenCount index 1) ∧
      CompactAdditiveNatListListSameRows
        tokenTable width tokenCount
          candidateBoundary formulaCount expectedBoundary expectedCount) ∨
     ((∃ index, index ≤ formulaCount ∧ index < formulaCount ∧
        CompactFixedWidthEntry successTable tokenCount index 0) ∧
      expectedCount = 0))

def compactFormulaShiftExactListRowsDef : 𝚺₀.Semisentence 14 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary formulaCount candidateBoundary successTable
      expectedBoundary expectedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize witnessBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount emptyStart 0 emptyFinish
        emptyBoundary emptyBoundarySize ∧
    (∀ index < formulaCount,
      ∃ sourceStart <⁺ witnessBound,
      ∃ sourceFinish <⁺ witnessBound,
      ∃ sourceInnerCount <⁺ witnessBound,
      ∃ sourceInnerBoundary <⁺ witnessBound,
      ∃ sourceBoundarySize <⁺ witnessBound,
      ∃ candidateStart <⁺ witnessBound,
      ∃ candidateFinish <⁺ witnessBound,
      ∃ candidateInnerCount <⁺ witnessBound,
      ∃ candidateInnerBoundary <⁺ witnessBound,
      ∃ candidateBoundarySize <⁺ witnessBound,
      ∃ stateBoundary <⁺ witnessBound,
      ∃ stateCount <⁺ witnessBound,
      ∃ tableWidth <⁺ witnessBound,
      ∃ valueBound <⁺ witnessBound,
      ∃ successValue <⁺ witnessBound,
      ∃ finalStart <⁺ witnessBound,
      ∃ finalFinish <⁺ witnessBound,
      ∃ finalParserFinish <⁺ witnessBound,
      ∃ finalParserTokensFinish <⁺ witnessBound,
      ∃ finalParserTasksFinish <⁺ witnessBound,
      ∃ finalParserTokensBoundary <⁺ witnessBound,
      ∃ finalParserTokensCount <⁺ witnessBound,
      ∃ finalParserTasksBoundary <⁺ witnessBound,
      ∃ finalParserTasksCount <⁺ witnessBound,
      ∃ finalOutputBoundary <⁺ witnessBound,
      ∃ finalOutputCount <⁺ witnessBound,
      ∃ finalParserTokensBoundarySize <⁺ witnessBound,
      ∃ finalParserTasksBoundarySize <⁺ witnessBound,
      ∃ finalOutputBoundarySize <⁺ witnessBound,
        !(compactFormulaShiftListRowDef)
          tokenTable width tokenCount
          sourceBoundary candidateBoundary successTable formulaCount index
          emptyStart emptyFinish emptyBoundary
          sourceStart sourceFinish sourceInnerCount sourceInnerBoundary
            sourceBoundarySize
          candidateStart candidateFinish candidateInnerCount
            candidateInnerBoundary candidateBoundarySize
          stateBoundary stateCount tableWidth valueBound successValue
          finalStart finalFinish finalParserFinish
          finalParserTokensFinish finalParserTasksFinish
          finalParserTokensBoundary finalParserTokensCount
          finalParserTasksBoundary finalParserTasksCount
          finalOutputBoundary finalOutputCount
          finalParserTokensBoundarySize finalParserTasksBoundarySize
          finalOutputBoundarySize) ∧
    (((∀ index < formulaCount,
        !(compactFixedWidthEntryDef)
          successTable tokenCount index 1) ∧
      !(compactAdditiveNatListListSameRowsDef)
        tokenTable width tokenCount
          candidateBoundary formulaCount expectedBoundary expectedCount) ∨
     ((∃ index <⁺ formulaCount,
        index < formulaCount ∧
        !(compactFixedWidthEntryDef)
          successTable tokenCount index 0) ∧
      expectedCount = 0))”

@[simp] theorem compactFormulaShiftExactListRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary formulaCount candidateBoundary successTable
      expectedBoundary expectedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      witnessBound : Nat) :
    compactFormulaShiftExactListRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, formulaCount, candidateBoundary, successTable,
          expectedBoundary, expectedCount,
          emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
          witnessBound] ↔
      CompactFormulaShiftExactListRows
        tokenTable width tokenCount
        sourceBoundary formulaCount candidateBoundary successTable
        expectedBoundary expectedCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        witnessBound := by
  let env : Fin 14 → Nat :=
    ![tokenTable, width, tokenCount,
      sourceBoundary, formulaCount, candidateBoundary, successTable,
      expectedBoundary, expectedCount,
      emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
      witnessBound]
  change compactFormulaShiftExactListRowsDef.val.Evalb env ↔ _
  have hemptyEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2, #9,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 14),
          #10, #11, #12]) =
        ![tokenTable, width, tokenCount, emptyStart, 0,
          emptyFinish, emptyBoundary, emptyBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsameEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2,
          #5, #4, #7, #8]) =
        ![tokenTable, width, tokenCount,
          candidateBoundary, formulaCount,
          expectedBoundary, expectedCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactFormulaShiftExactListRowsDef,
    CompactFormulaShiftExactListRows, hemptyEnv, hsameEnv, env]

theorem compactFormulaShiftExactListRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaShiftExactListRowsDef.val := by
  simp [compactFormulaShiftExactListRowsDef]

private theorem compactFormulaShiftExactList_eq_some_map_of_all
    (formulas : List (List Nat))
    (hall : ∀ formula ∈ formulas,
      (compactFormulaShiftExact 0 formula).isSome = true) :
    compactFormulaShiftExactList formulas =
      some (formulas.map fun formula =>
        (compactFormulaShiftExact 0 formula).getD []) := by
  induction formulas with
  | nil => simp [compactFormulaShiftExactList]
  | cons formula formulas ih =>
      have hformula := hall formula (by simp)
      have htail : ∀ tailFormula ∈ formulas,
          (compactFormulaShiftExact 0 tailFormula).isSome = true := by
        intro tailFormula htailFormula
        exact hall tailFormula (by simp [htailFormula])
      have hi := ih htail
      change compactShiftedFormulaCons formula
          (compactFormulaShiftExactList formulas) = _
      rw [hi]
      cases hshift : compactFormulaShiftExact 0 formula with
      | none => simp [hshift] at hformula
      | some shifted =>
          simp [compactShiftedFormulaCons, hshift]

private theorem compactFormulaShiftExactList_eq_none_of_failure
    (formulas : List (List Nat))
    (hfailure : ∃ formula ∈ formulas,
      (compactFormulaShiftExact 0 formula).isSome = false) :
    compactFormulaShiftExactList formulas = none := by
  induction formulas with
  | nil => simp at hfailure
  | cons formula formulas ih =>
      rcases hfailure with ⟨failedFormula, hfailedMem, hfailed⟩
      simp only [List.mem_cons] at hfailedMem
      rcases hfailedMem with hhead | htail
      · subst failedFormula
        change compactShiftedFormulaCons formula
          (compactFormulaShiftExactList formulas) = none
        cases hshift : compactFormulaShiftExact 0 formula with
        | none =>
            simp [compactShiftedFormulaCons, hshift]
        | some shifted => simp [hshift] at hfailed
      · have hi := ih ⟨failedFormula, htail, hfailed⟩
        change compactShiftedFormulaCons formula
          (compactFormulaShiftExactList formulas) = none
        rw [hi]
        cases hshift : compactFormulaShiftExact 0 formula <;>
          simp [compactShiftedFormulaCons, hshift]

theorem CompactFormulaShiftExactListRows.sound
    {tokenTable width tokenCount sourceBoundary formulaCount
      candidateBoundary successTable expectedBoundary
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      witnessBound : Nat}
    {source expected : List (List Nat)}
    (hgraph : CompactFormulaShiftExactListRows
      tokenTable width tokenCount
      sourceBoundary formulaCount candidateBoundary successTable
      expectedBoundary expected.length
      emptyStart emptyFinish emptyBoundary emptyBoundarySize witnessBound)
    (hsourceCount : source.length = formulaCount)
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (hexpected : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        expectedBoundary expected) :
    expected = (compactFormulaShiftExactList source).getD [] := by
  rcases hgraph with ⟨hemptyWitness, hrows, hresult⟩
  rcases hemptyWitness.realize with
    ⟨emptyValue, hemptyLength, hemptyLayout, hemptyRows⟩
  have hemptyValue : emptyValue = [] :=
    List.eq_nil_of_length_eq_zero hemptyLength
  subst emptyValue
  have hcandidateWellFormed : CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount candidateBoundary formulaCount := by
    intro index hindex
    rcases hrows index hindex with
      ⟨sourceStart, _hsourceStartBound,
        sourceFinish, _hsourceFinishBound,
        sourceInnerCount, _hsourceInnerCountBound,
        sourceInnerBoundary, _hsourceInnerBoundaryBound,
        sourceBoundarySize, _hsourceBoundarySizeBound,
        candidateStart, _hcandidateStartBound,
        candidateFinish, _hcandidateFinishBound,
        candidateInnerCount, _hcandidateInnerCountBound,
        candidateInnerBoundary, _hcandidateInnerBoundaryBound,
        candidateBoundarySize, _hcandidateBoundarySizeBound,
        stateBoundary, _hstateBoundaryBound,
        stateCount, _hstateCountBound,
        tableWidth, _htableWidthBound,
        valueBound, _hvalueBoundBound,
        successValue, _hsuccessValueBound,
        finalStart, _hfinalStartBound,
        finalFinish, _hfinalFinishBound,
        finalParserFinish, _hfinalParserFinishBound,
        finalParserTokensFinish, _hfinalParserTokensFinishBound,
        finalParserTasksFinish, _hfinalParserTasksFinishBound,
        finalParserTokensBoundary, _hfinalParserTokensBoundaryBound,
        finalParserTokensCount, _hfinalParserTokensCountBound,
        finalParserTasksBoundary, _hfinalParserTasksBoundaryBound,
        finalParserTasksCount, _hfinalParserTasksCountBound,
        finalOutputBoundary, _hfinalOutputBoundaryBound,
        finalOutputCount, _hfinalOutputCountBound,
        finalParserTokensBoundarySize,
          _hfinalParserTokensBoundarySizeBound,
        finalParserTasksBoundarySize,
          _hfinalParserTasksBoundarySizeBound,
        finalOutputBoundarySize, _hfinalOutputBoundarySizeBound,
        hrow⟩
    rcases hrow with
      ⟨_hindex, _hsourceStartEntry, _hsourceFinishEntry,
        _hsourceWitness, hcandidateStartEntry,
        hcandidateFinishEntry, hcandidateWitness,
        _hsuccessEntry, _houtcome⟩
    rcases hcandidateWitness.realize with
      ⟨candidateValue, hcandidateLength,
        hcandidateLayout, _hcandidateRows⟩
    rcases hcandidateWitness.1 with
      ⟨candidateBodyStart, _hcandidateBodyStart,
        hcandidateHeader, hcandidateBoundaryTable⟩
    have hcandidateStartLe : candidateStart ≤ tokenCount :=
      Nat.le_of_lt hcandidateHeader.1.1
    have hcandidateFinishLe : candidateFinish ≤ tokenCount :=
      hcandidateBoundaryTable.2.1
    have hcandidateCountLe : candidateInnerCount ≤ tokenCount := by
      have hcountBound := hcandidateHeader.2
      omega
    refine ⟨candidateStart, hcandidateStartLe,
      candidateFinish, hcandidateFinishLe,
      candidateInnerCount, hcandidateCountLe,
      hcandidateStartEntry, hcandidateFinishEntry, ?_⟩
    simpa only [hcandidateLength] using hcandidateLayout.toSlice
  rcases
      FoundationCompactNumericListedDirectNatListListRowsRealization.CompactAdditiveNatListListRowsWellFormed.realizeRows
        hcandidateWellFormed with
    ⟨candidate, hcandidateLength, hcandidateRows⟩
  have hrowOutcome : ∀ index (hindex : index < source.length),
      ∃ successValue,
        CompactFixedWidthEntry
          successTable tokenCount index successValue ∧
        successValue = compactAdditiveBoolTag
          (compactFormulaShiftExact 0 source[index]).isSome ∧
        candidate[index] =
          (compactFormulaShiftExact 0 source[index]).getD [] := by
    intro index hindex
    have hformulaIndex : index < formulaCount := by
      simpa [← hsourceCount] using hindex
    have hcandidateIndex : index < candidate.length := by
      simpa [hcandidateLength] using hformulaIndex
    rcases hrows index hformulaIndex with
      ⟨sourceStart, _hsourceStartBound,
        sourceFinish, _hsourceFinishBound,
        sourceInnerCount, _hsourceInnerCountBound,
        sourceInnerBoundary, _hsourceInnerBoundaryBound,
        sourceBoundarySize, _hsourceBoundarySizeBound,
        candidateStart, _hcandidateStartBound,
        candidateFinish, _hcandidateFinishBound,
        candidateInnerCount, _hcandidateInnerCountBound,
        candidateInnerBoundary, _hcandidateInnerBoundaryBound,
        candidateBoundarySize, _hcandidateBoundarySizeBound,
        stateBoundary, _hstateBoundaryBound,
        stateCount, _hstateCountBound,
        tableWidth, _htableWidthBound,
        valueBound, _hvalueBoundBound,
        successValue, _hsuccessValueBound,
        finalStart, _hfinalStartBound,
        finalFinish, _hfinalFinishBound,
        finalParserFinish, _hfinalParserFinishBound,
        finalParserTokensFinish, _hfinalParserTokensFinishBound,
        finalParserTasksFinish, _hfinalParserTasksFinishBound,
        finalParserTokensBoundary, _hfinalParserTokensBoundaryBound,
        finalParserTokensCount, _hfinalParserTokensCountBound,
        finalParserTasksBoundary, _hfinalParserTasksBoundaryBound,
        finalParserTasksCount, _hfinalParserTasksCountBound,
        finalOutputBoundary, _hfinalOutputBoundaryBound,
        finalOutputCount, _hfinalOutputCountBound,
        finalParserTokensBoundarySize,
          _hfinalParserTokensBoundarySizeBound,
        finalParserTasksBoundarySize,
          _hfinalParserTasksBoundarySizeBound,
        finalOutputBoundarySize, _hfinalOutputBoundarySizeBound,
        hrow⟩
    rcases hrow with
      ⟨_hindex, hsourceStartEntry, _hsourceFinishEntry,
        hsourceWitness, hcandidateStartEntry,
        _hcandidateFinishEntry, hcandidateWitness,
        hsuccessEntry, houtcome⟩
    rcases hsourceWitness.realize with
      ⟨sourceValue, _hsourceValueLength,
        hsourceValueLayout, hsourceValueRows⟩
    rcases hcandidateWitness.realize with
      ⟨candidateValue, _hcandidateValueLength,
        hcandidateValueLayout, hcandidateValueRows⟩
    rcases hsource index hindex with
      ⟨actualSourceStart, _hactualSourceStart,
        actualSourceFinish, _hactualSourceFinish,
        hactualSourceStartEntry, _hactualSourceFinishEntry,
        hactualSourceLayout⟩
    have hsourceStartEq : sourceStart = actualSourceStart :=
      (CompactFixedWidthEntry.value_eq_tableValue
        hsourceStartEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          hactualSourceStartEntry).symm
    subst actualSourceStart
    have hsourceValueEq : source[index] = sourceValue := by
      have hdet :=
        CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
          hsourceValueLayout hactualSourceLayout
      simpa [List.getI_eq_getElem source hindex] using hdet.1
    rcases hcandidateRows index hcandidateIndex with
      ⟨actualCandidateStart, _hactualCandidateStart,
        actualCandidateFinish, _hactualCandidateFinish,
        hactualCandidateStartEntry, _hactualCandidateFinishEntry,
        hactualCandidateLayout⟩
    have hcandidateStartEq : candidateStart = actualCandidateStart :=
      (CompactFixedWidthEntry.value_eq_tableValue
        hcandidateStartEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          hactualCandidateStartEntry).symm
    subst actualCandidateStart
    have hcandidateValueEq : candidate[index] = candidateValue := by
      have hdet :=
        CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
          hcandidateValueLayout hactualCandidateLayout
      simpa [List.getI_eq_getElem candidate hcandidateIndex] using hdet.1
    have houtcome' := houtcome
    rw [← _hsourceValueLength,
      ← _hcandidateValueLength] at houtcome'
    have houtcomeSound := houtcome'.sound
      hemptyLayout rfl hsourceValueRows hcandidateValueRows hemptyRows
    have hsuccess : successValue = compactAdditiveBoolTag
        (compactFormulaShiftExact 0 sourceValue).isSome := by
      simpa [compactFormulaShiftExact] using houtcomeSound.1
    have hcandidateResult : candidateValue =
        (compactFormulaShiftExact 0 sourceValue).getD [] := by
      simpa [compactFormulaShiftExact] using houtcomeSound.2
    refine ⟨successValue, hsuccessEntry, ?_, ?_⟩
    · simpa only [hsourceValueEq] using hsuccess
    · rw [hcandidateValueEq, hsourceValueEq]
      exact hcandidateResult
  rcases hresult with hsuccessCase | hfailureCase
  · rcases hsuccessCase with ⟨hallOne, hsame⟩
    have hallIsSome : ∀ formula ∈ source,
        (compactFormulaShiftExact 0 formula).isSome = true := by
      intro formula hformula
      rcases List.mem_iff_getElem.mp hformula with
        ⟨index, hindex, hformulaEq⟩
      subst formula
      rcases hrowOutcome index hindex with
        ⟨successValue, hsuccessEntry, hsuccessTag,
          _hcandidateResult⟩
      have honeEntry := hallOne index (by
        simpa [← hsourceCount] using hindex)
      have hsuccessOne : successValue = 1 :=
        (CompactFixedWidthEntry.value_eq_tableValue
          hsuccessEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue honeEntry).symm
      cases hsome : (compactFormulaShiftExact 0 source[index]).isSome with
      | false =>
          simp [compactAdditiveBoolTag, hsome] at hsuccessTag
          omega
      | true => rfl
    have hcandidateMap : candidate = source.map fun formula =>
        (compactFormulaShiftExact 0 formula).getD [] := by
      apply List.ext_getElem
      · simp [hcandidateLength, hsourceCount]
      · intro index hcandidateIndex hmapIndex
        have hsourceIndex : index < source.length := by
          simpa [hcandidateLength, hsourceCount] using hcandidateIndex
        rcases hrowOutcome index hsourceIndex with
          ⟨_successValue, _hsuccessEntry, _hsuccessTag,
            hcandidateResult⟩
        simpa using hcandidateResult
    have hexpectedCandidate : expected = candidate :=
      (compactAdditiveNatListListSameRows_iff_eq
        hcandidateRows hexpected).mp (by
          simpa [hcandidateLength] using hsame)
    have hshifted :=
      compactFormulaShiftExactList_eq_some_map_of_all source hallIsSome
    rw [hexpectedCandidate, hcandidateMap, hshifted]
    rfl
  · rcases hfailureCase with
      ⟨⟨failedIndex, _hfailedIndexLe,
        hfailedIndex, hzeroEntry⟩, hexpectedCount⟩
    have hsourceIndex : failedIndex < source.length := by
      simpa [hsourceCount] using hfailedIndex
    rcases hrowOutcome failedIndex hsourceIndex with
      ⟨successValue, hsuccessEntry, hsuccessTag,
        _hcandidateResult⟩
    have hsuccessZero : successValue = 0 :=
      (CompactFixedWidthEntry.value_eq_tableValue
        hsuccessEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hzeroEntry).symm
    have hfailed :
        (compactFormulaShiftExact 0 source[failedIndex]).isSome = false := by
      cases hsome :
          (compactFormulaShiftExact 0 source[failedIndex]).isSome with
      | false => rfl
      | true =>
          simp [compactAdditiveBoolTag, hsome] at hsuccessTag
          omega
    have hshiftNone := compactFormulaShiftExactList_eq_none_of_failure
      source ⟨source[failedIndex], List.getElem_mem hsourceIndex, hfailed⟩
    have hexpectedEmpty : expected = [] :=
      List.eq_nil_of_length_eq_zero hexpectedCount
    simp [hexpectedEmpty, hshiftNone]

#print axioms compactFormulaShiftExactListRowsDef_spec
#print axioms compactFormulaShiftExactListRowsDef_sigmaZero
#print axioms CompactFormulaShiftExactListRows.sound

end FoundationCompactNumericListedDirectFormulaShiftExactListRows
