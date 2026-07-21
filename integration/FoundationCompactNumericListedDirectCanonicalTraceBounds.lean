import integration.FoundationCompactNumericListedDirectVerifierCheckedStepRows
import integration.FoundationCompactNumericListedDirectTraceBounds

/-!
# Quantitative reduction for the canonical accepted trace table

The dynamic table width is exactly the sum of the binary sizes of all 429
coordinates in all canonical rows.  Consequently one uniform row-weight
bound controls the width, the canonical table code, and the binary size of
the exponential value bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCanonicalTraceBounds

open FoundationCompactNumericListedDirectVerifierCheckedStepRows
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedStateBounds
open FoundationCompactNumericListedDirectTraceBounds

def compactNumericVerifierStepFormulaRowBitWeight
    (row : CompactNumericVerifierStepFormulaRow) : Nat :=
  ((compactNumericVerifierStepFormulaRowValues row).map Nat.size).sum

theorem compactNumericVerifierStepFormulaRowBitWeight_le
    (row : CompactNumericVerifierStepFormulaRow)
    (coordinateBound : Nat)
    (hcoordinates : forall coordinate : Fin 429,
      Nat.size (row.environment coordinate) <= coordinateBound) :
    compactNumericVerifierStepFormulaRowBitWeight row <=
      compactNumericVerifierStepWitnessColumnCount * coordinateBound := by
  have hvalues : ∀ value,
      value ∈ compactNumericVerifierStepFormulaRowValues row →
        Nat.size value <= coordinateBound := by
    intro value hvalue
    change value ∈ List.ofFn row.environment at hvalue
    rcases List.mem_ofFn.mp hvalue with ⟨coordinate, rfl⟩
    exact hcoordinates coordinate
  have hsizes : ∀ valueSize,
      valueSize ∈
          (compactNumericVerifierStepFormulaRowValues row).map Nat.size →
        valueSize <= coordinateBound := by
    intro valueSize hvalueSize
    rcases List.mem_map.mp hvalueSize with ⟨value, hvalue, rfl⟩
    exact hvalues value hvalue
  have hsum :
      ((compactNumericVerifierStepFormulaRowValues row).map Nat.size).sum <=
        ((compactNumericVerifierStepFormulaRowValues row).map Nat.size).length *
          coordinateBound := by
    generalize (compactNumericVerifierStepFormulaRowValues row).map Nat.size =
      sizes at hsizes ⊢
    induction sizes with
    | nil => simp
    | cons head tail inductionHypothesis =>
        have hhead : head <= coordinateBound :=
          hsizes head (by simp)
        have htail : ∀ valueSize, valueSize ∈ tail →
            valueSize <= coordinateBound := by
          intro valueSize hvalueSize
          exact hsizes valueSize (by simp [hvalueSize])
        have hinduction := inductionHypothesis htail
        simp only [List.sum_cons, List.length_cons]
        simpa only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul,
          Nat.add_comm] using Nat.add_le_add hhead hinduction
  simpa only [compactNumericVerifierStepFormulaRowBitWeight,
    List.length_map, compactNumericVerifierStepFormulaRowValues_length,
    compactNumericVerifierStepWitnessColumnCount] using hsum

theorem compactNumericVerifierStepFormulaDynamicWidth_eq_rowBitWeight_sum
    (rows : List CompactNumericVerifierStepFormulaRow) :
    compactNumericVerifierStepFormulaDynamicWidth rows =
      (rows.map compactNumericVerifierStepFormulaRowBitWeight).sum := by
  induction rows with
  | nil => simp [compactNumericVerifierStepFormulaDynamicWidth]
  | cons row rows inductionHypothesis =>
      rw [compactNumericVerifierStepFormulaDynamicWidth]
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      rw [← compactNumericVerifierStepFormulaDynamicWidth,
        inductionHypothesis]
      rfl

theorem canonicalVerifierStateAt_weight_le_localRowBound
    (proofTokens certificateTokens : List Nat)
    (fuel stepIndex : Nat)
    (hstepIndex : stepIndex < fuel) :
    compactNumericVerifierStateWeight
        (compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          stepIndex) <=
      compactNumericVerifierLocalRowBound
        proofTokens certificateTokens fuel := by
  let start := compactNumericVerifierInitialState
    proofTokens certificateTokens
  let states := compactNumericVerifierStateTrace fuel start
  have hvalid : CompactNumericVerifierLocalTraceValid fuel start states :=
    compactNumericVerifierStateTrace_localValid fuel start
  have hmember : compactNumericVerifierStateAt start stepIndex ∈ states := by
    apply List.mem_iff_getElem?.mpr
    refine ⟨stepIndex, ?_⟩
    change compactNumericTraceState? states stepIndex =
      some (compactNumericVerifierStateAt start stepIndex)
    simpa only [states, start] using
      compactNumericVerifierStateTrace_getElem?
        fuel stepIndex start (Nat.le_of_lt hstepIndex)
  exact compactNumericVerifierLocalTrace_member_stateWeight_le
    hvalid hmember

theorem canonicalVerifierStateAt_weight_le_localRowBound_of_le
    (proofTokens certificateTokens : List Nat)
    (fuel stepIndex : Nat)
    (hstepIndex : stepIndex <= fuel) :
    compactNumericVerifierStateWeight
        (compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          stepIndex) <=
      compactNumericVerifierLocalRowBound
        proofTokens certificateTokens fuel := by
  let start := compactNumericVerifierInitialState
    proofTokens certificateTokens
  let states := compactNumericVerifierStateTrace fuel start
  have hvalid : CompactNumericVerifierLocalTraceValid fuel start states :=
    compactNumericVerifierStateTrace_localValid fuel start
  have hmember : compactNumericVerifierStateAt start stepIndex ∈ states := by
    apply List.mem_iff_getElem?.mpr
    refine ⟨stepIndex, ?_⟩
    change compactNumericTraceState? states stepIndex =
      some (compactNumericVerifierStateAt start stepIndex)
    simpa only [states, start] using
      compactNumericVerifierStateTrace_getElem?
        fuel stepIndex start hstepIndex
  exact compactNumericVerifierLocalTrace_member_stateWeight_le
    hvalid hmember

theorem canonicalVerifierStateAt_weight_le_publicRowBound
    {proofTokens certificateTokens : List Nat}
    {fuel stepIndex streamWeight : Nat}
    (hproof : compactAdditiveValueWeight proofTokens <= streamWeight)
    (hcertificate :
      compactAdditiveValueWeight certificateTokens <= streamWeight)
    (hfuel : fuel <=
      compactNumericVerifierPublicFuelWeightBound streamWeight)
    (hstepIndex : stepIndex < fuel) :
    compactNumericVerifierStateWeight
        (compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          stepIndex) <=
      compactNumericVerifierPublicRowWeightBound streamWeight := by
  exact (canonicalVerifierStateAt_weight_le_localRowBound
    proofTokens certificateTokens fuel stepIndex hstepIndex).trans
      (compactNumericVerifierLocalRowBound_le_public
        hproof hcertificate hfuel)

theorem canonicalVerifierStateAt_weight_le_publicRowBound_of_le
    {proofTokens certificateTokens : List Nat}
    {fuel stepIndex streamWeight : Nat}
    (hproof : compactAdditiveValueWeight proofTokens <= streamWeight)
    (hcertificate :
      compactAdditiveValueWeight certificateTokens <= streamWeight)
    (hfuel : fuel <=
      compactNumericVerifierPublicFuelWeightBound streamWeight)
    (hstepIndex : stepIndex <= fuel) :
    compactNumericVerifierStateWeight
        (compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          stepIndex) <=
      compactNumericVerifierPublicRowWeightBound streamWeight := by
  exact (canonicalVerifierStateAt_weight_le_localRowBound_of_le
    proofTokens certificateTokens fuel stepIndex hstepIndex).trans
      (compactNumericVerifierLocalRowBound_le_public
        hproof hcertificate hfuel)

theorem compactNumericVerifierStepFormulaDynamicWidth_le_of_rowBitWeight
    {rows : List CompactNumericVerifierStepFormulaRow}
    {rowBound : Nat}
    (hrows : ∀ row, row ∈ rows →
      compactNumericVerifierStepFormulaRowBitWeight row <= rowBound) :
    compactNumericVerifierStepFormulaDynamicWidth rows <=
      rows.length * rowBound := by
  rw [compactNumericVerifierStepFormulaDynamicWidth_eq_rowBitWeight_sum]
  induction rows with
  | nil => simp
  | cons row rows inductionHypothesis =>
      have hrow := hrows row (by simp)
      have htail : ∀ tailRow, tailRow ∈ rows →
          compactNumericVerifierStepFormulaRowBitWeight tailRow <= rowBound := by
        intro tailRow htailRow
        exact hrows tailRow (by simp [htailRow])
      have hinduction := inductionHypothesis htail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      simpa only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul,
        Nat.add_comm] using Nat.add_le_add hrow hinduction

theorem canonicalStepFormulaDynamicWidth_le
    (fuel : Nat) (start : CompactNumericVerifierState)
    (rowBound : Nat)
    (hrows : ∀ row,
      row ∈ compactNumericVerifierCanonicalStepFormulaRows fuel start →
        compactNumericVerifierStepFormulaRowBitWeight row <= rowBound) :
    compactNumericVerifierStepFormulaDynamicWidth
        (compactNumericVerifierCanonicalStepFormulaRows fuel start) <=
      fuel * rowBound := by
  have hbound :=
    compactNumericVerifierStepFormulaDynamicWidth_le_of_rowBitWeight hrows
  simpa only [compactNumericVerifierCanonicalStepFormulaRows_length]
    using hbound

theorem canonicalStepWitnessTableCode_size_le
    (fuel : Nat) (start : CompactNumericVerifierState) :
    let rows := compactNumericVerifierCanonicalStepFormulaRows fuel start
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    Nat.size (compactNumericVerifierStepWitnessTableCode tableWidth rows) <=
      fuel * compactNumericVerifierStepWitnessColumnCount * tableWidth := by
  dsimp only
  simpa only [compactNumericVerifierCanonicalStepFormulaRows_length] using
    compactNumericVerifierStepWitnessTableCode_size_le
      (compactNumericVerifierStepFormulaDynamicWidth
        (compactNumericVerifierCanonicalStepFormulaRows fuel start))
      (compactNumericVerifierCanonicalStepFormulaRows fuel start)

theorem canonicalTraceCoordinates_size_le
    (fuel : Nat) (start : CompactNumericVerifierState)
    (rowBound : Nat)
    (hrows : ∀ row,
      row ∈ compactNumericVerifierCanonicalStepFormulaRows fuel start →
        compactNumericVerifierStepFormulaRowBitWeight row <= rowBound) :
    let rows := compactNumericVerifierCanonicalStepFormulaRows fuel start
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    tableWidth <= fuel * rowBound ∧
      Nat.size table <=
        fuel * compactNumericVerifierStepWitnessColumnCount *
          (fuel * rowBound) ∧
      Nat.size (2 ^ tableWidth) <= fuel * rowBound + 1 := by
  dsimp only
  have hwidth := canonicalStepFormulaDynamicWidth_le
    fuel start rowBound hrows
  have htable := canonicalStepWitnessTableCode_size_le fuel start
  have htableScale :
      fuel * compactNumericVerifierStepWitnessColumnCount *
          compactNumericVerifierStepFormulaDynamicWidth
            (compactNumericVerifierCanonicalStepFormulaRows fuel start) <=
        fuel * compactNumericVerifierStepWitnessColumnCount *
          (fuel * rowBound) := by
    exact Nat.mul_le_mul_left
      (fuel * compactNumericVerifierStepWitnessColumnCount) hwidth
  have hvalue : Nat.size
        (2 ^ compactNumericVerifierStepFormulaDynamicWidth
          (compactNumericVerifierCanonicalStepFormulaRows fuel start)) <=
      fuel * rowBound + 1 := by
    rw [Nat.size_pow]
    omega
  exact ⟨hwidth, htable.trans htableScale, hvalue⟩

#print axioms
  compactNumericVerifierStepFormulaRowBitWeight_le
#print axioms canonicalVerifierStateAt_weight_le_localRowBound
#print axioms canonicalVerifierStateAt_weight_le_localRowBound_of_le
#print axioms canonicalVerifierStateAt_weight_le_publicRowBound
#print axioms canonicalVerifierStateAt_weight_le_publicRowBound_of_le
#print axioms
  compactNumericVerifierStepFormulaDynamicWidth_le_of_rowBitWeight
#print axioms canonicalStepFormulaDynamicWidth_le
#print axioms canonicalStepWitnessTableCode_size_le
#print axioms canonicalTraceCoordinates_size_le

end FoundationCompactNumericListedDirectCanonicalTraceBounds
