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
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformTotalOutcomeFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
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

def compactFormulaShiftExactListPublicFuelBound
    (tokenCount : Nat) : Nat :=
  16 * (tokenCount + 1) * (tokenCount + 1) + 8

def compactFormulaShiftExactListCoordinateSizeBound
    (width tokenCount : Nat) : Nat :=
  let fuel := compactFormulaShiftExactListPublicFuelBound tokenCount
  compactFormulaTransformAdjacentStepPublicWidth width tokenCount +
    (tokenCount + 1) * tokenCount +
    (fuel + 2) * tokenCount +
    (fuel + 1) +
    compactFormulaTransformCanonicalTableWidthBound
      width tokenCount fuel + 2

def compactFormulaShiftExactListPublicWitnessBound
    (width tokenCount : Nat) : Nat :=
  2 ^ (compactFormulaShiftExactListCoordinateSizeBound width tokenCount + 5)

private theorem list_sum_le_length_mul_of_le
    {values : List Nat} {bound : Nat}
    (hbound : ∀ value ∈ values, value ≤ bound) :
    values.sum ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      have hhead : head ≤ bound := hbound head (by simp)
      have htail : ∀ value ∈ tail, value ≤ bound := by
        intro value hvalue
        exact hbound value (by simp [hvalue])
      simp only [List.sum_cons, List.length_cons]
      calc
        head + tail.sum ≤ bound + tail.length * bound :=
          Nat.add_le_add hhead (ih htail)
        _ = (tail.length + 1) * bound := by ring

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
  coordinateBound_le_public :
    coordinateBound ≤
      compactFormulaShiftExactListPublicWitnessBound width tokenCount
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
              (source.getI index))) ∧
        Nat.size stateBoundary ≤
          ((compactFormulaTransformStateTrace (1, [])
              (compactSyntaxRunFuelBound (source.getI index))
              (compactFormulaTransformInitialState 0
                (source.getI index))).length + 1) * tokenCount) :
    ∃ witnessBound,
      CompactFormulaShiftExactListRows
        tokenTable width tokenCount
        sourceBoundary source.length candidateBoundary successTable
        expectedBoundary ((compactFormulaShiftExactList source).getD []).length
        emptyStart emptyFinish emptyBoundary emptyBoundarySize witnessBound ∧
      Nat.size witnessBound ≤
        compactFormulaShiftExactListCoordinateSizeBound width tokenCount + 6 := by
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
      ⟨stateBoundary, hstateRows, hstateBoundarySizeRaw⟩
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
    rcases
        CompactFormulaTransformTotalOutcomeRows.of_canonical_trace_with_width_bound
        hstateRows hemptyLayout rfl hsourceRows hcandidateRows hemptyRows
        hcandidateResult with
      ⟨tableWidth, finalCoordinates, finalSizeWitness,
        houtcome, htableWidthRaw⟩
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
    have hsourceCount : (source.getI index).length ≤ tokenCount :=
      structuredListLayout_count_le_tokenCount hsourceStructure
    have hcandidateCount :
        ((source.map fun formula =>
          (compactFormulaShiftExact 0 formula).getD []).getI index).length ≤
          tokenCount :=
      structuredListLayout_count_le_tokenCount hcandidateStructure
    have hsourceBoundaryArea : Nat.size sourceInnerBoundary ≤
        (tokenCount + 1) * tokenCount :=
      hsourceSize.trans (listBoundaryArea_le_publicArea hsourceCount)
    have hcandidateBoundaryArea : Nat.size candidateInnerBoundary ≤
        (tokenCount + 1) * tokenCount :=
      hcandidateSize.trans (listBoundaryArea_le_publicArea hcandidateCount)
    have hfuel : compactSyntaxRunFuelBound (source.getI index) ≤
        compactFormulaShiftExactListPublicFuelBound tokenCount := by
      have hlength := Nat.add_le_add_right hsourceCount 1
      have hsquare := Nat.mul_le_mul hlength hlength
      have hscaled := Nat.mul_le_mul_left 16 hsquare
      have htotal := Nat.add_le_add_right hscaled 8
      simpa [compactSyntaxRunFuelBound,
        compactFormulaShiftExactListPublicFuelBound, Nat.mul_assoc] using htotal
    have hstateBoundarySize : Nat.size stateBoundary ≤
        (compactFormulaShiftExactListPublicFuelBound tokenCount + 2) *
          tokenCount := by
      have hraw : Nat.size stateBoundary ≤
          (compactSyntaxRunFuelBound (source.getI index) + 2) *
            tokenCount := by
        simpa using hstateBoundarySizeRaw
      exact hraw.trans (Nat.mul_le_mul_right tokenCount
        (Nat.add_le_add_right hfuel 2))
    have htableWidth : tableWidth ≤
        compactFormulaTransformCanonicalTableWidthBound width tokenCount
          (compactFormulaShiftExactListPublicFuelBound tokenCount) :=
      htableWidthRaw.trans
        (compactFormulaTransformCanonicalTableWidthBound_mono_fuel
          width tokenCount hfuel)
    have hfinalFits :=
      CompactFormulaTransformStateAtRows.coordinateFits houtcome'.2.1
    let coordinateSizeBound :=
      compactFormulaShiftExactListCoordinateSizeBound width tokenCount
    have hpublicWidthLe :
        compactFormulaTransformAdjacentStepPublicWidth width tokenCount ≤
          coordinateSizeBound := by
      simp [coordinateSizeBound,
        compactFormulaShiftExactListCoordinateSizeBound]
      omega
    have hareaLe : (tokenCount + 1) * tokenCount ≤
        coordinateSizeBound := by
      simp [coordinateSizeBound,
        compactFormulaShiftExactListCoordinateSizeBound]
      omega
    have hstateBoundaryLe :
        (compactFormulaShiftExactListPublicFuelBound tokenCount + 2) *
            tokenCount ≤ coordinateSizeBound := by
      simp [coordinateSizeBound,
        compactFormulaShiftExactListCoordinateSizeBound]
      omega
    have hfuelLe :
        compactFormulaShiftExactListPublicFuelBound tokenCount + 1 ≤
          coordinateSizeBound := by
      simp [coordinateSizeBound,
        compactFormulaShiftExactListCoordinateSizeBound]
      omega
    have htableLe :
        compactFormulaTransformCanonicalTableWidthBound width tokenCount
            (compactFormulaShiftExactListPublicFuelBound tokenCount) + 1 ≤
          coordinateSizeBound := by
      simp [coordinateSizeBound,
        compactFormulaShiftExactListCoordinateSizeBound]
      omega
    have honeLe : 1 ≤ coordinateSizeBound := by
      simp [coordinateSizeBound,
        compactFormulaShiftExactListCoordinateSizeBound]
    have hsourceStartSize : Nat.size sourceStart ≤ coordinateSizeBound :=
      (natSize_le_transformStepWidth_of_le_tokenCount _hsourceStart).trans
        hpublicWidthLe
    have hsourceFinishSize : Nat.size sourceFinish ≤ coordinateSizeBound :=
      (natSize_le_transformStepWidth_of_le_tokenCount _hsourceFinish).trans
        hpublicWidthLe
    have hsourceCountSize : Nat.size (source.getI index).length ≤
        coordinateSizeBound :=
      (natSize_le_transformStepWidth_of_le_tokenCount hsourceCount).trans
        hpublicWidthLe
    have hsourceBoundarySize : Nat.size sourceInnerBoundary ≤
        coordinateSizeBound := hsourceBoundaryArea.trans hareaLe
    have hsourceBoundarySizeSize : Nat.size (Nat.size sourceInnerBoundary) ≤
        coordinateSizeBound :=
      (natSize_le_of_le (Nat.le_refl _)).trans
        (hsourceBoundaryArea.trans hareaLe)
    have hcandidateStartSize : Nat.size candidateStart ≤
        coordinateSizeBound :=
      (natSize_le_transformStepWidth_of_le_tokenCount
        _hcandidateStart).trans hpublicWidthLe
    have hcandidateFinishSize : Nat.size candidateFinish ≤
        coordinateSizeBound :=
      (natSize_le_transformStepWidth_of_le_tokenCount
        _hcandidateFinish).trans hpublicWidthLe
    have hcandidateCountSize : Nat.size
        ((source.map fun formula =>
          (compactFormulaShiftExact 0 formula).getD []).getI index).length ≤
          coordinateSizeBound :=
      (natSize_le_transformStepWidth_of_le_tokenCount
        hcandidateCount).trans hpublicWidthLe
    have hcandidateBoundarySize : Nat.size candidateInnerBoundary ≤
        coordinateSizeBound := hcandidateBoundaryArea.trans hareaLe
    have hcandidateBoundarySizeSize :
        Nat.size (Nat.size candidateInnerBoundary) ≤ coordinateSizeBound :=
      (natSize_le_of_le (Nat.le_refl _)).trans
        (hcandidateBoundaryArea.trans hareaLe)
    have hstateBoundarySize' : Nat.size stateBoundary ≤
        coordinateSizeBound := hstateBoundarySize.trans hstateBoundaryLe
    have hstateCountSize : Nat.size
        (compactSyntaxRunFuelBound (source.getI index) + 1) ≤
          coordinateSizeBound :=
      (natSize_le_of_le (Nat.le_refl _)).trans
        ((Nat.add_le_add_right hfuel 1).trans hfuelLe)
    have htableWidthSize : Nat.size tableWidth ≤ coordinateSizeBound :=
      (natSize_le_of_le (Nat.le_refl _)).trans
        (htableWidth.trans (Nat.le_trans (Nat.le_succ _) htableLe))
    have hvalueBoundSize : Nat.size (2 ^ tableWidth) ≤
        coordinateSizeBound := by
      rw [Nat.size_pow]
      exact (Nat.add_le_add_right htableWidth 1).trans htableLe
    have hsuccessValueSize : Nat.size
        (compactAdditiveBoolTag
          (compactFormulaShiftExact 0 (source.getI index)).isSome) ≤
          coordinateSizeBound :=
      (natSize_le_of_le (Nat.le_refl _)).trans
        (houtcome'.2.2.2.1.trans honeLe)
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
    have hcoordinateSizes : ∀ value ∈ coordinateValues,
        Nat.size value ≤ coordinateSizeBound := by
      intro value hvalue
      simp only [coordinateValues, List.mem_cons] at hvalue
      rcases hvalue with
        h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · simpa [h] using hsourceStartSize
      · simpa [h] using hsourceFinishSize
      · simpa [h] using hsourceCountSize
      · simpa [h] using hsourceBoundarySize
      · simpa [h] using hsourceBoundarySizeSize
      · simpa [h] using hcandidateStartSize
      · simpa [h] using hcandidateFinishSize
      · simpa [h] using hcandidateCountSize
      · simpa [h] using hcandidateBoundarySize
      · simpa [h] using hcandidateBoundarySizeSize
      · simpa [h] using hstateBoundarySize'
      · simpa [h] using hstateCountSize
      · simpa [h] using htableWidthSize
      · simpa [h] using hvalueBoundSize
      · simpa [h] using hsuccessValueSize
      · simpa [h] using hfinalFits.start.trans hpublicWidthLe
      · simpa [h] using hfinalFits.finish.trans hpublicWidthLe
      · simpa [h] using hfinalFits.parserFinish.trans hpublicWidthLe
      · simpa [h] using hfinalFits.parserTokensFinish.trans hpublicWidthLe
      · simpa [h] using hfinalFits.parserTasksFinish.trans hpublicWidthLe
      · simpa [h] using hfinalFits.parserTokensBoundary.trans hpublicWidthLe
      · simpa [h] using hfinalFits.parserTokensCount.trans hpublicWidthLe
      · simpa [h] using hfinalFits.parserTasksBoundary.trans hpublicWidthLe
      · simpa [h] using hfinalFits.parserTasksCount.trans hpublicWidthLe
      · simpa [h] using hfinalFits.outputBoundary.trans hpublicWidthLe
      · simpa [h] using hfinalFits.outputCount.trans hpublicWidthLe
      · simpa [h] using
          hfinalFits.parserTokensBoundarySize.trans hpublicWidthLe
      · simpa [h] using
          hfinalFits.parserTasksBoundarySize.trans hpublicWidthLe
      · rcases h with h | h
        · simpa [h] using hfinalFits.outputBoundarySize.trans hpublicWidthLe
        · simp at h
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
      coordinateBound_le_public := by
        dsimp only [coordinateBound]
        unfold compactFormulaShiftExactListPublicWitnessBound
        change coordinateValues.sum ≤ 2 ^ (coordinateSizeBound + 5)
        have hvalues : ∀ value ∈ coordinateValues,
            value ≤ 2 ^ coordinateSizeBound := by
          intro value hvalue
          exact (Nat.size_le.mp (hcoordinateSizes value hvalue)).le
        calc
          coordinateValues.sum ≤
              coordinateValues.length * 2 ^ coordinateSizeBound :=
            list_sum_le_length_mul_of_le hvalues
          _ = 29 * 2 ^ coordinateSizeBound := by
            simp [coordinateValues]
          _ ≤ 32 * 2 ^ coordinateSizeBound := by
            exact Nat.mul_le_mul_right (2 ^ coordinateSizeBound) (by omega)
          _ = 2 ^ (coordinateSizeBound + 5) := by
            rw [pow_add]
            norm_num
            ring
      row := ⟨hindex, hsourceStartEntry, hsourceFinishEntry,
        hsourceWitness, hcandidateStartEntry, hcandidateFinishEntry,
        hcandidateWitness, hsuccess index hindex, houtcome'⟩ }⟩
  let witnesses (index : Fin source.length) :=
    Classical.choice (hexists index.1 index.2)
  let witnessBound :=
    compactFormulaShiftExactListPublicWitnessBound width tokenCount
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
      exact rowWitness.coordinateBound_le_public
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
  refine ⟨witnessBound, ?_, ?_⟩
  · refine ⟨hemptyWitness, hboundedRows, ?_⟩
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
  · dsimp [witnessBound,
      compactFormulaShiftExactListPublicWitnessBound]
    rw [Nat.size_pow]

#print axioms CompactFormulaShiftExactListRows.of_canonical_rows

end FoundationCompactNumericListedDirectFormulaShiftExactListRowsCompleteness
