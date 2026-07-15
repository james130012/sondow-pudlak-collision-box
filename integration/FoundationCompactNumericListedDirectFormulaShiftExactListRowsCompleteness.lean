import integration.FoundationCompactNumericListedDirectFormulaShiftExactListRows

/-!
# Converse constructor for exact list-level formula shifts

Canonical per-formula traces are assembled into one bounded list graph.  The
common witness bound is the finite supremum of explicit row-coordinate sums;
it is not accepted as an input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaShiftExactListRowsCompleteness

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformTotalOutcomeFormula
open FoundationCompactNumericListedDirectFormulaShiftListRow
open FoundationCompactNumericListedDirectNatListListSameRows
open FoundationCompactNumericListedDirectFormulaShiftExactListRows

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
      | some shifted => simp [compactShiftedFormulaCons, hshift]

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
        | none => simp [compactShiftedFormulaCons, hshift]
        | some shifted => simp [hshift] at hfailed
      · have hi := ih ⟨failedFormula, htail, hfailed⟩
        change compactShiftedFormulaCons formula
            (compactFormulaShiftExactList formulas) = none
        rw [hi]
        cases hshift : compactFormulaShiftExact 0 formula <;>
          simp [compactShiftedFormulaCons, hshift]

structure CompactFormulaShiftExactListRowWitness
    (tokenTable width tokenCount sourceBoundary candidateBoundary
      successTable formulaCount index emptyStart emptyFinish emptyBoundary : Nat)
    where
  sourceStart : Nat
  sourceFinish : Nat
  sourceInnerCount : Nat
  sourceInnerBoundary : Nat
  sourceBoundarySize : Nat
  candidateStart : Nat
  candidateFinish : Nat
  candidateInnerCount : Nat
  candidateInnerBoundary : Nat
  candidateBoundarySize : Nat
  stateBoundary : Nat
  stateCount : Nat
  tableWidth : Nat
  valueBound : Nat
  successValue : Nat
  finalCoordinates : CompactFormulaTransformStateRowCoordinates
  finalSizeWitness : CompactFormulaTransformStateCoreSizeWitness
  coordinateBound : Nat
  coordinateBounds :
    sourceStart ≤ coordinateBound ∧
    sourceFinish ≤ coordinateBound ∧
    sourceInnerCount ≤ coordinateBound ∧
    sourceInnerBoundary ≤ coordinateBound ∧
    sourceBoundarySize ≤ coordinateBound ∧
    candidateStart ≤ coordinateBound ∧
    candidateFinish ≤ coordinateBound ∧
    candidateInnerCount ≤ coordinateBound ∧
    candidateInnerBoundary ≤ coordinateBound ∧
    candidateBoundarySize ≤ coordinateBound ∧
    stateBoundary ≤ coordinateBound ∧
    stateCount ≤ coordinateBound ∧
    tableWidth ≤ coordinateBound ∧
    valueBound ≤ coordinateBound ∧
    successValue ≤ coordinateBound ∧
    finalCoordinates.start ≤ coordinateBound ∧
    finalCoordinates.finish ≤ coordinateBound ∧
    finalCoordinates.parserFinish ≤ coordinateBound ∧
    finalCoordinates.parserTokensFinish ≤ coordinateBound ∧
    finalCoordinates.parserTasksFinish ≤ coordinateBound ∧
    finalCoordinates.parserTokensBoundary ≤ coordinateBound ∧
    finalCoordinates.parserTokensCount ≤ coordinateBound ∧
    finalCoordinates.parserTasksBoundary ≤ coordinateBound ∧
    finalCoordinates.parserTasksCount ≤ coordinateBound ∧
    finalCoordinates.outputBoundary ≤ coordinateBound ∧
    finalCoordinates.outputCount ≤ coordinateBound ∧
    finalSizeWitness.parserTokensBoundarySize ≤ coordinateBound ∧
    finalSizeWitness.parserTasksBoundarySize ≤ coordinateBound ∧
    finalSizeWitness.outputBoundarySize ≤ coordinateBound
  row : CompactFormulaShiftListRow
    tokenTable width tokenCount
    sourceBoundary candidateBoundary successTable formulaCount index
    emptyStart emptyFinish emptyBoundary
    sourceStart sourceFinish sourceInnerCount sourceInnerBoundary
      sourceBoundarySize
    candidateStart candidateFinish candidateInnerCount
      candidateInnerBoundary candidateBoundarySize
    stateBoundary stateCount tableWidth valueBound successValue
    finalCoordinates finalSizeWitness

theorem CompactFormulaShiftExactListRows.of_canonical_rows
    {tokenTable width tokenCount sourceBoundary candidateBoundary
      successTable expectedBoundary emptyStart emptyFinish emptyBoundary
      emptyBoundarySize : Nat}
    {source : List (List Nat)}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (hcandidate : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        candidateBoundary
        (source.map fun formula =>
          (compactFormulaShiftExact 0 formula).getD []))
    (hexpected : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        expectedBoundary ((compactFormulaShiftExactList source).getD []))
    (hemptyWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount emptyStart 0 emptyFinish
        emptyBoundary emptyBoundarySize)
    (hsuccess : ∀ index (_hindex : index < source.length),
      CompactFixedWidthEntry successTable tokenCount index
        (compactAdditiveBoolTag
          (compactFormulaShiftExact 0 (source.getI index)).isSome))
    (htraceRows : ∀ index (_hindex : index < source.length),
      ∃ stateBoundary,
        CompactFormulaTransformStateListRowLayouts
          tokenTable width tokenCount stateBoundary
          (compactFormulaTransformStateTrace (1, [])
            (compactSyntaxRunFuelBound (source.getI index))
            (compactFormulaTransformInitialState 0
              (source.getI index)))) :
    ∃ witnessBound,
      CompactFormulaShiftExactListRows
        tokenTable width tokenCount
        sourceBoundary source.length candidateBoundary successTable
        expectedBoundary ((compactFormulaShiftExactList source).getD []).length
        emptyStart emptyFinish emptyBoundary emptyBoundarySize witnessBound := by
  rcases hemptyWitness.realize with
    ⟨emptyValue, hemptyLength, hemptyLayout, hemptyRows⟩
  have hemptyValue : emptyValue = [] :=
    List.eq_nil_of_length_eq_zero hemptyLength
  subst emptyValue
  have hexists : ∀ index (hindex : index < source.length),
      Nonempty (CompactFormulaShiftExactListRowWitness
        tokenTable width tokenCount sourceBoundary candidateBoundary
        successTable source.length index emptyStart emptyFinish
        emptyBoundary) := by
    intro index hindex
    have hcandidateIndex : index <
        (source.map fun formula =>
          (compactFormulaShiftExact 0 formula).getD []).length := by
      simpa using hindex
    rcases hsource index hindex with
      ⟨sourceStart, _hsourceStart,
        sourceFinish, _hsourceFinish,
        hsourceStartEntry, hsourceFinishEntry, hsourceLayout⟩
    rcases hsourceLayout with
      ⟨sourceInnerBoundary, hsourceStructure,
        hsourceRows, hsourceSize⟩
    rcases hcandidate index hcandidateIndex with
      ⟨candidateStart, _hcandidateStart,
        candidateFinish, _hcandidateFinish,
        hcandidateStartEntry, hcandidateFinishEntry, hcandidateLayout⟩
    rcases hcandidateLayout with
      ⟨candidateInnerBoundary, hcandidateStructure,
        hcandidateRows, hcandidateSize⟩
    rcases htraceRows index hindex with
      ⟨stateBoundary, hstateRows⟩
    have hsourceWitness : CompactAdditiveNatListWitnessRows
        tokenTable width tokenCount sourceStart
          (source.getI index).length sourceFinish
          sourceInnerBoundary (Nat.size sourceInnerBoundary) :=
      ⟨hsourceStructure,
        CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
          hsourceRows,
        rfl, hsourceSize⟩
    have hcandidateWitness : CompactAdditiveNatListWitnessRows
        tokenTable width tokenCount candidateStart
          ((source.map fun formula =>
            (compactFormulaShiftExact 0 formula).getD []).getI index).length
          candidateFinish candidateInnerBoundary
          (Nat.size candidateInnerBoundary) :=
      ⟨hcandidateStructure,
        CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
          hcandidateRows,
        rfl, hcandidateSize⟩
    have hcandidateValue :
        (source.map fun formula =>
          (compactFormulaShiftExact 0 formula).getD []).getI index =
        (compactFormulaShiftExact 0 (source.getI index)).getD [] := by
      rw [List.getI_eq_getElem _ hcandidateIndex]
      rw [List.getI_eq_getElem _ hindex]
      simp
    have hcandidateResult :
        (source.map fun formula =>
          (compactFormulaShiftExact 0 formula).getD []).getI index =
        (compactExactFormulaTransformResult
          (compactFormulaTransformResult
            (1, []) (0, source.getI index))).getD [] := by
      simpa [compactFormulaShiftExact] using hcandidateValue
    rcases CompactFormulaTransformTotalOutcomeRows.of_canonical_trace
        hstateRows hemptyLayout rfl hsourceRows hcandidateRows hemptyRows
        hcandidateResult with
      ⟨tableWidth, finalCoordinates, finalSizeWitness, houtcome⟩
    have houtcome' : CompactFormulaTransformTotalOutcomeRows
        tokenTable width tokenCount stateBoundary
          (compactSyntaxRunFuelBound (source.getI index) + 1) 1
        emptyStart emptyFinish 0
        sourceInnerBoundary (source.getI index).length
        candidateInnerBoundary
          ((source.map fun formula =>
            (compactFormulaShiftExact 0 formula).getD []).getI index).length
        emptyBoundary 0 tableWidth (2 ^ tableWidth)
        (compactAdditiveBoolTag
          (compactFormulaShiftExact 0 (source.getI index)).isSome)
        finalCoordinates finalSizeWitness := by
      simpa [compactFormulaShiftExact] using houtcome
    let coordinateValues : List Nat :=
      [sourceStart, sourceFinish, (source.getI index).length,
        sourceInnerBoundary, Nat.size sourceInnerBoundary,
        candidateStart, candidateFinish,
        ((source.map fun formula =>
          (compactFormulaShiftExact 0 formula).getD []).getI index).length,
        candidateInnerBoundary, Nat.size candidateInnerBoundary,
        stateBoundary, compactSyntaxRunFuelBound (source.getI index) + 1,
        tableWidth, 2 ^ tableWidth,
        compactAdditiveBoolTag
          (compactFormulaShiftExact 0 (source.getI index)).isSome,
        finalCoordinates.start, finalCoordinates.finish,
        finalCoordinates.parserFinish,
        finalCoordinates.parserTokensFinish,
        finalCoordinates.parserTasksFinish,
        finalCoordinates.parserTokensBoundary,
        finalCoordinates.parserTokensCount,
        finalCoordinates.parserTasksBoundary,
        finalCoordinates.parserTasksCount,
        finalCoordinates.outputBoundary, finalCoordinates.outputCount,
        finalSizeWitness.parserTokensBoundarySize,
        finalSizeWitness.parserTasksBoundarySize,
        finalSizeWitness.outputBoundarySize]
    let coordinateBound := coordinateValues.sum
    refine ⟨{
      sourceStart := sourceStart
      sourceFinish := sourceFinish
      sourceInnerCount := (source.getI index).length
      sourceInnerBoundary := sourceInnerBoundary
      sourceBoundarySize := Nat.size sourceInnerBoundary
      candidateStart := candidateStart
      candidateFinish := candidateFinish
      candidateInnerCount :=
        ((source.map fun formula =>
          (compactFormulaShiftExact 0 formula).getD []).getI index).length
      candidateInnerBoundary := candidateInnerBoundary
      candidateBoundarySize := Nat.size candidateInnerBoundary
      stateBoundary := stateBoundary
      stateCount := compactSyntaxRunFuelBound (source.getI index) + 1
      tableWidth := tableWidth
      valueBound := 2 ^ tableWidth
      successValue := compactAdditiveBoolTag
        (compactFormulaShiftExact 0 (source.getI index)).isSome
      finalCoordinates := finalCoordinates
      finalSizeWitness := finalSizeWitness
      coordinateBound := coordinateBound
      coordinateBounds := by
        dsimp only [coordinateBound]
        repeat' apply And.intro
        all_goals
          apply List.le_sum_of_mem
          simp [coordinateValues]
      row := ⟨hindex, hsourceStartEntry, hsourceFinishEntry,
        hsourceWitness, hcandidateStartEntry, hcandidateFinishEntry,
        hcandidateWitness, hsuccess index hindex, houtcome'⟩ }⟩
  let witnesses (index : Fin source.length) :=
    Classical.choice (hexists index.1 index.2)
  let witnessBound := Finset.univ.sup fun index : Fin source.length =>
    (witnesses index).coordinateBound
  have hboundedRows : ∀ index < source.length,
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
          sourceBoundary candidateBoundary successTable source.length index
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
            outputBoundarySize := finalOutputBoundarySize } := by
    intro index hindex
    let boundedIndex : Fin source.length := ⟨index, hindex⟩
    let rowWitness := witnesses boundedIndex
    have hrowBound : rowWitness.coordinateBound ≤ witnessBound := by
      exact Finset.le_sup
        (f := fun i : Fin source.length => (witnesses i).coordinateBound)
        (Finset.mem_univ boundedIndex)
    refine ⟨rowWitness.sourceStart, ?_,
      rowWitness.sourceFinish, ?_,
      rowWitness.sourceInnerCount, ?_,
      rowWitness.sourceInnerBoundary, ?_,
      rowWitness.sourceBoundarySize, ?_,
      rowWitness.candidateStart, ?_,
      rowWitness.candidateFinish, ?_,
      rowWitness.candidateInnerCount, ?_,
      rowWitness.candidateInnerBoundary, ?_,
      rowWitness.candidateBoundarySize, ?_,
      rowWitness.stateBoundary, ?_, rowWitness.stateCount, ?_,
      rowWitness.tableWidth, ?_, rowWitness.valueBound, ?_,
      rowWitness.successValue, ?_,
      rowWitness.finalCoordinates.start, ?_,
      rowWitness.finalCoordinates.finish, ?_,
      rowWitness.finalCoordinates.parserFinish, ?_,
      rowWitness.finalCoordinates.parserTokensFinish, ?_,
      rowWitness.finalCoordinates.parserTasksFinish, ?_,
      rowWitness.finalCoordinates.parserTokensBoundary, ?_,
      rowWitness.finalCoordinates.parserTokensCount, ?_,
      rowWitness.finalCoordinates.parserTasksBoundary, ?_,
      rowWitness.finalCoordinates.parserTasksCount, ?_,
      rowWitness.finalCoordinates.outputBoundary, ?_,
      rowWitness.finalCoordinates.outputCount, ?_,
      rowWitness.finalSizeWitness.parserTokensBoundarySize, ?_,
      rowWitness.finalSizeWitness.parserTasksBoundarySize, ?_,
      rowWitness.finalSizeWitness.outputBoundarySize, ?_, ?_⟩ <;>
      try (have hcoordinates := rowWitness.coordinateBounds; omega)
    simpa [boundedIndex, rowWitness,
      compactFormulaTransformStateRowCoordinatesOf] using rowWitness.row
  refine ⟨witnessBound, hemptyWitness, hboundedRows, ?_⟩
  by_cases hall : ∀ index (hindex : index < source.length),
      (compactFormulaShiftExact 0 (source.getI index)).isSome = true
  · left
    refine ⟨?_, ?_⟩
    · intro index hindex
      simpa [compactAdditiveBoolTag, hall index hindex] using
        hsuccess index hindex
    · have hsame : CompactAdditiveNatListListSameRows
          tokenTable width tokenCount candidateBoundary
          (source.map fun formula =>
            (compactFormulaShiftExact 0 formula).getD []).length
          expectedBoundary
          ((compactFormulaShiftExactList source).getD []).length := by
        apply (compactAdditiveNatListListSameRows_iff_eq
          hcandidate hexpected).mpr
        have hallMem : ∀ formula ∈ source,
            (compactFormulaShiftExact 0 formula).isSome = true := by
          intro formula hformula
          rcases List.mem_iff_getElem.mp hformula with
            ⟨index, hindex, rfl⟩
          simpa [List.getI_eq_getElem source hindex] using hall index hindex
        have hlist := compactFormulaShiftExactList_eq_some_map_of_all
          source hallMem
        simp [hlist]
      simpa using hsame
  · right
    push Not at hall
    rcases hall with ⟨failedIndex, hfailedIndex, hfailed⟩
    have hfailedFalse :
        (compactFormulaShiftExact 0
          (source.getI failedIndex)).isSome = false := by
      cases hvalue :
          (compactFormulaShiftExact 0
            (source.getI failedIndex)).isSome
      · rfl
      · exact (hfailed hvalue).elim
    have hfailedEntry : CompactFixedWidthEntry
        successTable tokenCount failedIndex 0 := by
      simpa [compactAdditiveBoolTag, hfailedFalse] using
        hsuccess failedIndex hfailedIndex
    have hfailedMem : source.getI failedIndex ∈ source := by
      rw [List.getI_eq_getElem source hfailedIndex]
      exact List.getElem_mem hfailedIndex
    have hlistNone := compactFormulaShiftExactList_eq_none_of_failure source
      ⟨source.getI failedIndex, hfailedMem, hfailedFalse⟩
    refine ⟨⟨failedIndex, by omega, hfailedIndex, hfailedEntry⟩, ?_⟩
    simp [hlistNone]

#print axioms CompactFormulaShiftExactListRows.of_canonical_rows

end FoundationCompactNumericListedDirectFormulaShiftExactListRowsCompleteness
