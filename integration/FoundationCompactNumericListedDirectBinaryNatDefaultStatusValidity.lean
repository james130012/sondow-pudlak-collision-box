import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidity
import integration.FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy

/-!
# Positive bounded graph for a default binary-Nat status

The total formula-transform endpoint returns the empty output in three cases:
the parser is running, it has failed, or it has completed with a nonempty
suffix.  Recording those cases positively avoids negating a bounded
existential final-state formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096

namespace FoundationCompactNumericListedDirectBinaryNatDefaultStatusValidity

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy

def CompactBinaryNatDefaultStatusValidBounded
    (tokenTable width tokenCount start finish valueBound : Nat) : Prop :=
  CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish ∨
    CompactBinaryNatFailedStatusSlice
      tokenTable width tokenCount start finish ∨
    ∃ outputStart, outputStart ≤ valueBound ∧
    ∃ outputBoundary, outputBoundary ≤ valueBound ∧
    ∃ outputBoundarySize, outputBoundarySize ≤ valueBound ∧
    ∃ outputCount, outputCount ≤ valueBound ∧
      CompactBinaryNatCompletedStatusValidRows
          tokenTable width tokenCount start finish
            (compactBinaryNatStatusValidityWitnessOf
              outputStart outputBoundary outputBoundarySize outputCount) ∧
        0 < outputCount

def compactBinaryNatDefaultStatusValidBoundedDef :
    𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount start finish valueBound.
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount start finish ∨
    !(compactBinaryNatFailedStatusSliceDef)
      tokenTable width tokenCount start finish ∨
    ∃ outputStart <⁺ valueBound,
    ∃ outputBoundary <⁺ valueBound,
    ∃ outputBoundarySize <⁺ valueBound,
    ∃ outputCount <⁺ valueBound,
      ((!(compactBinaryNatCompletedStatusPrefixDef)
          tokenTable width tokenCount start outputStart ∧
        (!(compactAdditiveStructuredListLayoutDef)
            tokenTable width tokenCount outputStart outputCount finish
              outputBoundary ∧
          (!(compactAdditiveUnitBoundaryRowsDef)
              tokenCount outputCount outputBoundary ∧
            (!(compactNatSizeDef) outputBoundarySize outputBoundary ∧
              outputBoundarySize ≤
                (outputCount + 1) * tokenCount)))) ∧
        0 < outputCount)”

@[simp] theorem compactBinaryNatDefaultStatusValidBoundedDef_spec
    (tokenTable width tokenCount start finish valueBound : Nat) :
    compactBinaryNatDefaultStatusValidBoundedDef.val.Evalb
        ![tokenTable, width, tokenCount, start, finish, valueBound] ↔
      CompactBinaryNatDefaultStatusValidBounded
        tokenTable width tokenCount start finish valueBound := by
  have hrunning :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount, start, finish, valueBound]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 6), #1, #2, #3, #4])
          Empty.elim) compactBinaryNatRunningStatusSliceDef.val ↔
        CompactBinaryNatRunningStatusSlice
          tokenTable width tokenCount start finish := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount, start, finish, valueBound]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 6), #1, #2, #3, #4]) =
          ![tokenTable, width, tokenCount, start, finish] := by
      funext index
      fin_cases index <;> rfl
    rw [henv]
    exact compactBinaryNatRunningStatusSliceDef_spec
      tokenTable width tokenCount start finish
  have hfailed :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount, start, finish, valueBound]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 6), #1, #2, #3, #4])
          Empty.elim) compactBinaryNatFailedStatusSliceDef.val ↔
        CompactBinaryNatFailedStatusSlice
          tokenTable width tokenCount start finish := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount, start, finish, valueBound]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 6), #1, #2, #3, #4]) =
          ![tokenTable, width, tokenCount, start, finish] := by
      funext index
      fin_cases index <;> rfl
    rw [henv]
    exact compactBinaryNatFailedStatusSliceDef_spec
      tokenTable width tokenCount start finish
  have hprefix
      (outputCount outputBoundarySize outputBoundary outputStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![outputCount, outputBoundarySize, outputBoundary, outputStart,
                tokenTable, width, tokenCount, start, finish, valueBound]
              Empty.elim ∘
            ![(#4 : Semiterm ℒₒᵣ Empty 10), #5, #6, #7, #3])
          Empty.elim) compactBinaryNatCompletedStatusPrefixDef.val ↔
        CompactBinaryNatCompletedStatusPrefix
          tokenTable width tokenCount start outputStart := by
    have henv :
        (Semiterm.val
            ![outputCount, outputBoundarySize, outputBoundary, outputStart,
              tokenTable, width, tokenCount, start, finish, valueBound]
            Empty.elim ∘
          ![(#4 : Semiterm ℒₒᵣ Empty 10), #5, #6, #7, #3]) =
          ![tokenTable, width, tokenCount, start, outputStart] := by
      funext index
      fin_cases index <;> rfl
    rw [henv]
    exact compactBinaryNatCompletedStatusPrefixDef_spec
      tokenTable width tokenCount start outputStart
  have hlayout
      (outputCount outputBoundarySize outputBoundary outputStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![outputCount, outputBoundarySize, outputBoundary, outputStart,
                tokenTable, width, tokenCount, start, finish, valueBound]
              Empty.elim ∘
            ![(#4 : Semiterm ℒₒᵣ Empty 10), #5, #6, #3, #0, #8, #2])
          Empty.elim) compactAdditiveStructuredListLayoutDef.val ↔
        CompactAdditiveStructuredListLayout tokenTable width tokenCount
          outputStart outputCount finish outputBoundary := by
    have henv :
        (Semiterm.val
            ![outputCount, outputBoundarySize, outputBoundary, outputStart,
              tokenTable, width, tokenCount, start, finish, valueBound]
            Empty.elim ∘
          ![(#4 : Semiterm ℒₒᵣ Empty 10), #5, #6, #3, #0, #8, #2]) =
          ![tokenTable, width, tokenCount, outputStart, outputCount, finish,
            outputBoundary] := by
      funext index
      fin_cases index <;> rfl
    rw [henv]
    exact compactAdditiveStructuredListLayoutDef_spec
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
  simp [compactBinaryNatDefaultStatusValidBoundedDef,
    CompactBinaryNatDefaultStatusValidBounded,
    CompactBinaryNatCompletedStatusValidRows,
    compactBinaryNatStatusValidityWitnessOf, hrunning, hfailed, hprefix,
    hlayout, and_assoc]

theorem compactBinaryNatDefaultStatusValidBoundedDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatDefaultStatusValidBoundedDef.val := by
  simp [compactBinaryNatDefaultStatusValidBoundedDef]

private theorem completed_nonempty_of_rows
    {tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount : Nat}
    {status : Option (Option (List Nat))}
    (hlayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount start finish status)
    (hcompleted : CompactBinaryNatCompletedStatusValidRows
      tokenTable width tokenCount start finish
        (compactBinaryNatStatusValidityWitnessOf outputStart outputBoundary
          outputBoundarySize outputCount))
    (hpositive : 0 < outputCount) :
    status ≠ some (some []) := by
  intro hstatus
  subst status
  simp [CompactBinaryNatCompletedStatusValidRows,
    compactBinaryNatStatusValidityWitnessOf] at hcompleted
  rcases hlayout with
    ⟨actualOuterStart, hactualOuter, actualOutputStart, hactualInner,
      actualBoundary, hactualOutputLayout, hactualRows, _hactualSize⟩
  rcases hcompleted with
    ⟨⟨completedOuterStart, _hcompletedOuterStart, hcompletedOuter,
        hcompletedInner⟩,
      hcompletedOutputLayout, hcompletedUnit, _hsizeEq, _hsizeBound⟩
  have houterStart : actualOuterStart = completedOuterStart := by
    have hactual := hactualOuter.1.2.1
    have hcompleted := hcompletedOuter.2.1
    omega
  subst actualOuterStart
  have houtputStart : actualOutputStart = outputStart := by
    have hactual := hactualInner.1.2.1
    have hcompleted := hcompletedInner.2.1
    omega
  have hactualUnit : CompactAdditiveUnitBoundaryRows tokenCount 0
      actualBoundary :=
    CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
      hactualRows
  have hactualFinish : finish = actualOutputStart + 1 + 0 :=
    CompactAdditiveStructuredListLayout.finish_eq_start_add_count
      hactualOutputLayout hactualUnit
  have hcompletedFinish : finish = outputStart + 1 + outputCount :=
    CompactAdditiveStructuredListLayout.finish_eq_start_add_count
      hcompletedOutputLayout hcompletedUnit
  omega

private theorem completed_nonempty_bounded_of_layout
    {tokenTable width tokenCount start finish tableWidth : Nat}
    {output : List Nat}
    (hlayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount start finish (some (some output)))
    (houtput : output ≠ [])
    (harea : (tokenCount + 1) * tokenCount ≤ tableWidth) :
    CompactBinaryNatDefaultStatusValidBounded tokenTable width tokenCount
      start finish (2 ^ tableWidth) := by
  rcases hlayout with
    ⟨outerPayloadStart, houter, outputStart, hinner, outputBoundary,
      houtputLayout, houtputRows, houtputSize⟩
  let witness := compactBinaryNatStatusValidityWitnessOf outputStart
    outputBoundary (Nat.size outputBoundary) output.length
  have houterCell : CompactAdditiveTokenCell tokenTable width tokenCount
      start 1 outerPayloadStart := by
    simpa [compactAdditiveOptionTag] using houter.1
  have hinnerCell : CompactAdditiveTokenCell tokenTable width tokenCount
      outerPayloadStart 1 outputStart := by
    simpa [compactAdditiveOptionTag] using hinner.1
  have houterPayloadBound : outerPayloadStart ≤ tokenCount :=
    Nat.le_of_lt hinnerCell.1
  have hprefix : CompactBinaryNatCompletedStatusPrefix tokenTable width
      tokenCount start outputStart :=
    ⟨outerPayloadStart, houterPayloadBound, houterCell, hinnerCell⟩
  have hunit : CompactAdditiveUnitBoundaryRows tokenCount output.length
      outputBoundary :=
    CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
      houtputRows
  have hcompleted : CompactBinaryNatCompletedStatusValidRows tokenTable width
      tokenCount start finish witness :=
    ⟨hprefix, houtputLayout, hunit, rfl, houtputSize⟩
  have hwidthPower : tableWidth ≤ 2 ^ tableWidth :=
    Nat.le_of_lt tableWidth.lt_two_pow_self
  have htokenWidth : tokenCount ≤ tableWidth := by
    have htokenArea : tokenCount ≤ (tokenCount + 1) * tokenCount := by
      calc
        tokenCount = 1 * tokenCount := by simp
        _ ≤ (tokenCount + 1) * tokenCount :=
          Nat.mul_le_mul_right tokenCount (by omega)
    exact htokenArea.trans harea
  have hsmall {value : Nat} (hvalue : value ≤ tokenCount) :
      value ≤ 2 ^ tableWidth :=
    (hvalue.trans htokenWidth).trans hwidthPower
  have houtputStart : outputStart ≤ tokenCount := by
    have hinnerLt := hinnerCell.1
    have houtputEq := hinnerCell.2.1
    omega
  have hfinishEq : finish = outputStart + 1 + output.length :=
    CompactAdditiveStructuredListLayout.finish_eq_start_add_count
      houtputLayout hunit
  have hfinishBound : finish ≤ tokenCount := by
    rcases houtputLayout with
      ⟨_bodyStart, _hbodyStart, _hheader, hboundary⟩
    exact hboundary.2.1
  have houtputCount : output.length ≤ tokenCount := by omega
  have houtputArea :
      (output.length + 1) * tokenCount ≤
        (tokenCount + 1) * tokenCount :=
    Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right houtputCount 1)
  have hboundarySize : Nat.size outputBoundary ≤ tableWidth :=
    houtputSize.trans (houtputArea.trans harea)
  have hboundary : outputBoundary ≤ 2 ^ tableWidth :=
    (Nat.size_le.mp hboundarySize).le
  have hsize : Nat.size outputBoundary ≤ 2 ^ tableWidth :=
    hboundarySize.trans hwidthPower
  refine Or.inr (Or.inr ⟨outputStart, hsmall houtputStart,
    outputBoundary, hboundary,
    Nat.size outputBoundary, hsize,
    output.length, hsmall houtputCount, ?_, ?_⟩)
  · simpa only [witness, compactBinaryNatStatusValidityWitnessOf] using
      hcompleted
  · exact List.length_pos_iff.mpr houtput

theorem compactBinaryNatDefaultStatusValidBounded_iff
    {tokenTable width tokenCount start finish tableWidth valueBound : Nat}
    {status : Option (Option (List Nat))}
    (hlayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount start finish status)
    (harea : (tokenCount + 1) * tokenCount ≤ tableWidth)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    CompactBinaryNatDefaultStatusValidBounded tokenTable width tokenCount
        start finish valueBound ↔
      status ≠ some (some []) := by
  subst valueBound
  constructor
  · intro hrows
    rcases hrows with hrunning | hfailed | hcompleted
    · have hstatus :=
        (CompactBinaryNatStreamStatusDirectLayout.running_iff hlayout).mp
          hrunning
      simpa [hstatus]
    · have hstatus :=
        (CompactBinaryNatStreamStatusDirectLayout.failed_iff hlayout).mp
          hfailed
      simpa [hstatus]
    · rcases hcompleted with
        ⟨outputStart, _houtputStart,
          outputBoundary, _houtputBoundary,
          outputBoundarySize, _houtputBoundarySize,
          outputCount, _houtputCount, hcompleted, hpositive⟩
      exact completed_nonempty_of_rows hlayout hcompleted hpositive
  · intro hdefault
    cases status with
    | none =>
        exact Or.inl
          ((CompactBinaryNatStreamStatusDirectLayout.running_iff
            hlayout).mpr rfl)
    | some inner =>
        cases inner with
        | none =>
            exact Or.inr (Or.inl
              ((CompactBinaryNatStreamStatusDirectLayout.failed_iff
                hlayout).mpr rfl))
        | some output =>
            have houtput : output ≠ [] := by
              intro hempty
              subst output
              exact hdefault rfl
            exact completed_nonempty_bounded_of_layout hlayout houtput harea

#print axioms compactBinaryNatDefaultStatusValidBoundedDef_spec
#print axioms compactBinaryNatDefaultStatusValidBoundedDef_sigmaZero
#print axioms compactBinaryNatDefaultStatusValidBounded_iff

end FoundationCompactNumericListedDirectBinaryNatDefaultStatusValidity
