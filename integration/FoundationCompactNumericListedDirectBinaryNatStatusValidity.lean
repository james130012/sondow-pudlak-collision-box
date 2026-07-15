import integration.FoundationCompactNumericListedDirectBinaryNatStatusCases
import integration.FoundationCompactNumericListedDirectAtomicListRowRealization
import integration.FoundationCompactNumericListedDirectNatListBoundaryRigidity

/-!
# Total direct validity for nested natural-list statuses

The parser status is either running, failed, or completed with one natural-list
payload.  This module gives that exhaustive relation a handwritten bounded
formula and proves that every satisfying row realizes an actual nested option.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStatusValidity

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases

structure CompactBinaryNatStatusValidityWitness where
  outputStart : Nat
  outputBoundary : Nat
  outputBoundarySize : Nat
  outputCount : Nat

def compactBinaryNatStatusValidityWitnessOf
    (outputStart outputBoundary outputBoundarySize outputCount : Nat) :
    CompactBinaryNatStatusValidityWitness :=
  { outputStart := outputStart
    outputBoundary := outputBoundary
    outputBoundarySize := outputBoundarySize
    outputCount := outputCount }

def CompactBinaryNatCompletedStatusValidRows
    (tokenTable width tokenCount start finish : Nat)
    (witness : CompactBinaryNatStatusValidityWitness) : Prop :=
  CompactBinaryNatCompletedStatusPrefix
      tokenTable width tokenCount start witness.outputStart ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount witness.outputStart witness.outputCount
        finish witness.outputBoundary ∧
    CompactAdditiveUnitBoundaryRows
      tokenCount witness.outputCount witness.outputBoundary ∧
    witness.outputBoundarySize = Nat.size witness.outputBoundary ∧
    witness.outputBoundarySize ≤
      (witness.outputCount + 1) * tokenCount

def CompactBinaryNatStatusValidRows
    (tokenTable width tokenCount start finish : Nat)
    (witness : CompactBinaryNatStatusValidityWitness) : Prop :=
  CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish ∨
    CompactBinaryNatFailedStatusSlice
      tokenTable width tokenCount start finish ∨
    CompactBinaryNatCompletedStatusValidRows
      tokenTable width tokenCount start finish witness

def CompactBinaryNatStatusValidBounded
    (tokenTable width tokenCount start finish valueBound : Nat) : Prop :=
  ∃ outputStart, outputStart ≤ valueBound ∧
  ∃ outputBoundary, outputBoundary ≤ valueBound ∧
  ∃ outputBoundarySize, outputBoundarySize ≤ valueBound ∧
  ∃ outputCount, outputCount ≤ valueBound ∧
    CompactBinaryNatStatusValidRows tokenTable width tokenCount start finish
      (compactBinaryNatStatusValidityWitnessOf
        outputStart outputBoundary outputBoundarySize outputCount)

def compactBinaryNatStatusValidBoundedDef : 𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount start finish valueBound.
    ∃ outputStart <⁺ valueBound,
    ∃ outputBoundary <⁺ valueBound,
    ∃ outputBoundarySize <⁺ valueBound,
    ∃ outputCount <⁺ valueBound,
      (!(compactBinaryNatRunningStatusSliceDef)
          tokenTable width tokenCount start finish ∨
       !(compactBinaryNatFailedStatusSliceDef)
          tokenTable width tokenCount start finish ∨
       (!(compactBinaryNatCompletedStatusPrefixDef)
          tokenTable width tokenCount start outputStart ∧
        !(compactAdditiveStructuredListLayoutDef)
          tokenTable width tokenCount outputStart outputCount finish
            outputBoundary ∧
        !(compactAdditiveUnitBoundaryRowsDef)
          tokenCount outputCount outputBoundary ∧
        !(compactNatSizeDef) outputBoundarySize outputBoundary ∧
        outputBoundarySize ≤ (outputCount + 1) * tokenCount))”

set_option maxRecDepth 2048 in
@[simp] theorem compactBinaryNatStatusValidBoundedDef_spec
    (tokenTable width tokenCount start finish valueBound : Nat) :
    compactBinaryNatStatusValidBoundedDef.val.Evalb
        ![tokenTable, width, tokenCount, start, finish, valueBound] ↔
      CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount start finish valueBound := by
  have hrunning
      (outputCount outputBoundarySize outputBoundary outputStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![outputCount, outputBoundarySize, outputBoundary, outputStart,
                tokenTable, width, tokenCount, start, finish, valueBound]
              Empty.elim ∘
            ![(#4 : Semiterm ℒₒᵣ Empty 10), #5, #6, #7, #8])
          Empty.elim) compactBinaryNatRunningStatusSliceDef.val ↔
        CompactBinaryNatRunningStatusSlice
          tokenTable width tokenCount start finish := by
    have henv :
        (Semiterm.val
            ![outputCount, outputBoundarySize, outputBoundary, outputStart,
              tokenTable, width, tokenCount, start, finish, valueBound]
            Empty.elim ∘
          ![(#4 : Semiterm ℒₒᵣ Empty 10), #5, #6, #7, #8]) =
          ![tokenTable, width, tokenCount, start, finish] := by
      funext index
      fin_cases index <;> rfl
    rw [henv]
    exact compactBinaryNatRunningStatusSliceDef_spec
      tokenTable width tokenCount start finish
  have hfailed
      (outputCount outputBoundarySize outputBoundary outputStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![outputCount, outputBoundarySize, outputBoundary, outputStart,
                tokenTable, width, tokenCount, start, finish, valueBound]
              Empty.elim ∘
            ![(#4 : Semiterm ℒₒᵣ Empty 10), #5, #6, #7, #8])
          Empty.elim) compactBinaryNatFailedStatusSliceDef.val ↔
        CompactBinaryNatFailedStatusSlice
          tokenTable width tokenCount start finish := by
    have henv :
        (Semiterm.val
            ![outputCount, outputBoundarySize, outputBoundary, outputStart,
              tokenTable, width, tokenCount, start, finish, valueBound]
            Empty.elim ∘
          ![(#4 : Semiterm ℒₒᵣ Empty 10), #5, #6, #7, #8]) =
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
        CompactAdditiveStructuredListLayout
          tokenTable width tokenCount outputStart outputCount finish
            outputBoundary := by
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
  simp [compactBinaryNatStatusValidBoundedDef,
    CompactBinaryNatStatusValidBounded,
    CompactBinaryNatStatusValidRows,
    CompactBinaryNatCompletedStatusValidRows,
    compactBinaryNatStatusValidityWitnessOf, hrunning, hfailed, hprefix,
    hlayout]

theorem compactBinaryNatStatusValidBoundedDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatStatusValidBoundedDef.val := by
  simp [compactBinaryNatStatusValidBoundedDef]

private theorem runningStatusDirectLayout_of_rows
    {tokenTable width tokenCount start finish : Nat}
    (hrows : CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish) :
    CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount start finish none := by
  refine ⟨finish, ?_, trivial⟩
  change CompactAdditiveTokenCell
      tokenTable width tokenCount start 0 finish at hrows
  refine ⟨?_, Or.inl ⟨?_, rfl⟩⟩
  · simpa [compactAdditiveOptionTag] using hrows
  · simp [compactAdditiveOptionTag]

private theorem failedStatusDirectLayout_of_rows
    {tokenTable width tokenCount start finish : Nat}
    (hrows : CompactBinaryNatFailedStatusSlice
      tokenTable width tokenCount start finish) :
    CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount start finish (some none) := by
  rcases hrows with ⟨innerStart, _hinnerStart, houter, hinner⟩
  have hfinishBound : finish ≤ tokenCount := by
    rcases hinner with ⟨hinnerStart, hfinish, _hentry⟩
    omega
  have houterLayout : CompactAdditiveOptionLayout
      tokenTable width tokenCount start 1 innerStart finish := by
    have hinnerLtFinish : innerStart < finish := by
      have hfinish := hinner.2.1
      omega
    exact ⟨houter, Or.inr ⟨rfl, hinnerLtFinish, hfinishBound⟩⟩
  have hinnerLayout : CompactAdditiveOptionLayout
      tokenTable width tokenCount innerStart 0 finish finish := by
    exact ⟨hinner, Or.inl ⟨rfl, rfl⟩⟩
  exact ⟨innerStart, houterLayout, finish, hinnerLayout, trivial⟩

theorem CompactBinaryNatStatusValidRows.realize
    {tokenTable width tokenCount start finish : Nat}
    {witness : CompactBinaryNatStatusValidityWitness}
    (hvalid : CompactBinaryNatStatusValidRows
      tokenTable width tokenCount start finish witness) :
    ∃ status : Option (Option (List Nat)),
      CompactBinaryNatStreamStatusDirectLayout
        tokenTable width tokenCount start finish status := by
  rcases hvalid with hrunning | hfailed | hcompleted
  · exact ⟨none, runningStatusDirectLayout_of_rows hrunning⟩
  · exact ⟨some none, failedStatusDirectLayout_of_rows hfailed⟩
  · rcases hcompleted with
      ⟨hprefix, hlayout, hunit, hsizeEq, hsizeBound⟩
    let output := compactAdditiveNatListRowValues
      tokenTable width tokenCount witness.outputBoundary witness.outputCount
    have hrows : CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
          witness.outputBoundary output := by
      exact CompactAdditiveUnitBoundaryRows.realizedNatRows hunit
    have houtputLength : output.length = witness.outputCount := by
      simp [output]
    rcases hprefix with
      ⟨innerStart, _hinnerStart, houterCell, hinnerCell⟩
    have hfinishEq : finish =
        witness.outputStart + 1 + witness.outputCount :=
      CompactAdditiveStructuredListLayout.finish_eq_start_add_count
        hlayout hunit
    rcases hlayout with ⟨bodyStart, hbodyStart, hheader, hboundary⟩
    have hfinishBound : finish ≤ tokenCount := hboundary.2.1
    have houtputStartFinish : witness.outputStart < finish := by omega
    have hinnerStartOutput : innerStart < witness.outputStart := by
      rcases hinnerCell with ⟨hinnerStart, houtputStart, _hentry⟩
      omega
    have houterLayout : CompactAdditiveOptionLayout
        tokenTable width tokenCount start 1 innerStart finish := by
      exact ⟨houterCell,
        Or.inr ⟨rfl, hinnerStartOutput.trans houtputStartFinish,
          hfinishBound⟩⟩
    have hinnerLayout : CompactAdditiveOptionLayout
        tokenTable width tokenCount innerStart 1 witness.outputStart finish := by
      exact ⟨hinnerCell,
        Or.inr ⟨rfl, houtputStartFinish, hfinishBound⟩⟩
    refine ⟨some (some output), innerStart, houterLayout,
      witness.outputStart, hinnerLayout, witness.outputBoundary, ?_, hrows, ?_⟩
    · simpa only [houtputLength] using
        (show CompactAdditiveStructuredListLayout
          tokenTable width tokenCount witness.outputStart witness.outputCount
            finish witness.outputBoundary from
              ⟨bodyStart, hbodyStart, hheader, hboundary⟩)
    · simpa only [houtputLength, ← hsizeEq] using hsizeBound

theorem CompactBinaryNatStreamStatusDirectLayout.exists_validRows
    {tokenTable width tokenCount start finish : Nat}
    {status : Option (Option (List Nat))}
    (hlayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount start finish status) :
    ∃ witness,
      CompactBinaryNatStatusValidRows
        tokenTable width tokenCount start finish witness := by
  cases status with
  | none =>
      let witness := compactBinaryNatStatusValidityWitnessOf 0 0 0 0
      exact ⟨witness, Or.inl
        ((CompactBinaryNatStreamStatusDirectLayout.running_iff hlayout).mpr rfl)⟩
  | some inner =>
      cases inner with
      | none =>
          let witness := compactBinaryNatStatusValidityWitnessOf 0 0 0 0
          exact ⟨witness, Or.inr (Or.inl
            ((CompactBinaryNatStreamStatusDirectLayout.failed_iff hlayout).mpr
              rfl))⟩
      | some output =>
          rcases hlayout with
            ⟨outerPayloadStart, houter,
              outputStart, hinner, outputBoundary,
              houtputLayout, houtputRows, houtputSize⟩
          let witness := compactBinaryNatStatusValidityWitnessOf
            outputStart outputBoundary (Nat.size outputBoundary) output.length
          have houterCell : CompactAdditiveTokenCell
              tokenTable width tokenCount start 1 outerPayloadStart := by
            simpa [compactAdditiveOptionTag] using houter.1
          have hinnerCell : CompactAdditiveTokenCell
              tokenTable width tokenCount outerPayloadStart 1 outputStart := by
            simpa [compactAdditiveOptionTag] using hinner.1
          have houterPayloadBound : outerPayloadStart ≤ tokenCount := by
            exact Nat.le_of_lt hinnerCell.1
          have hprefix : CompactBinaryNatCompletedStatusPrefix
              tokenTable width tokenCount start outputStart :=
            ⟨outerPayloadStart, houterPayloadBound, houterCell, hinnerCell⟩
          have hunit : CompactAdditiveUnitBoundaryRows
              tokenCount output.length outputBoundary :=
            CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
              houtputRows
          refine ⟨witness, Or.inr (Or.inr ?_)⟩
          exact ⟨hprefix, houtputLayout, hunit, rfl, houtputSize⟩

theorem CompactBinaryNatStatusValidRows.toBounded
    {tokenTable width tokenCount start finish tableWidth : Nat}
    {witness : CompactBinaryNatStatusValidityWitness}
    (hvalid : CompactBinaryNatStatusValidRows
      tokenTable width tokenCount start finish witness)
    (harea : (tokenCount + 1) * tokenCount ≤ tableWidth) :
    CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish (2 ^ tableWidth) := by
  rcases hvalid with hrunning | hfailed | hcompleted
  · exact ⟨0, by simp, 0, by simp, 0, by simp, 0, by simp,
      Or.inl hrunning⟩
  · exact ⟨0, by simp, 0, by simp, 0, by simp, 0, by simp,
      Or.inr (Or.inl hfailed)⟩
  · rcases hcompleted with
      ⟨hprefix, hlayout, hunit, hsizeEq, hsizeBound⟩
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
    have houtputStart : witness.outputStart ≤ tokenCount := by
      rcases hprefix with
        ⟨innerStart, _hinnerStart, _houterCell, hinnerCell⟩
      have hinnerLt := hinnerCell.1
      have houtputEq := hinnerCell.2.1
      omega
    have hfinishEq : finish =
        witness.outputStart + 1 + witness.outputCount :=
      CompactAdditiveStructuredListLayout.finish_eq_start_add_count
        hlayout hunit
    have hfinishBound : finish ≤ tokenCount := by
      rcases hlayout with
        ⟨_bodyStart, _hbodyStart, _hheader, hboundary⟩
      exact hboundary.2.1
    have houtputCount : witness.outputCount ≤ tokenCount := by omega
    have houtputArea :
        (witness.outputCount + 1) * tokenCount ≤
          (tokenCount + 1) * tokenCount :=
      Nat.mul_le_mul_right tokenCount
        (Nat.add_le_add_right houtputCount 1)
    have hboundarySize : Nat.size witness.outputBoundary ≤ tableWidth := by
      rw [← hsizeEq]
      exact hsizeBound.trans (houtputArea.trans harea)
    have hboundary : witness.outputBoundary ≤ 2 ^ tableWidth :=
      (Nat.size_le.mp hboundarySize).le
    have hsize : witness.outputBoundarySize ≤ 2 ^ tableWidth :=
      (hsizeBound.trans (houtputArea.trans harea)).trans hwidthPower
    exact ⟨witness.outputStart, hsmall houtputStart,
      witness.outputBoundary, hboundary,
      witness.outputBoundarySize, hsize,
      witness.outputCount, hsmall houtputCount,
      Or.inr (Or.inr ⟨hprefix, hlayout, hunit, hsizeEq, hsizeBound⟩)⟩

theorem CompactBinaryNatStreamStatusDirectLayout.validBounded
    {tokenTable width tokenCount start finish tableWidth : Nat}
    {status : Option (Option (List Nat))}
    (hlayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount start finish status)
    (harea : (tokenCount + 1) * tokenCount ≤ tableWidth) :
    CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish (2 ^ tableWidth) := by
  rcases CompactBinaryNatStreamStatusDirectLayout.exists_validRows hlayout with
    ⟨witness, hvalid⟩
  exact hvalid.toBounded harea

#print axioms compactBinaryNatStatusValidBoundedDef_spec
#print axioms compactBinaryNatStatusValidBoundedDef_sigmaZero
#print axioms CompactBinaryNatStatusValidRows.realize
#print axioms CompactBinaryNatStreamStatusDirectLayout.exists_validRows
#print axioms CompactBinaryNatStatusValidRows.toBounded
#print axioms CompactBinaryNatStreamStatusDirectLayout.validBounded

end FoundationCompactNumericListedDirectBinaryNatStatusValidity
