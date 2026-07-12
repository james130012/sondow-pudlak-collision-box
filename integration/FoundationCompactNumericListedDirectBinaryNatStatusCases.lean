import integration.FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout

/-!
# Direct arithmetic cases for binary-stream status tags

The nested option status has exactly three tag prefixes: running `0`, failed
`10`, and completed `11`.  Each direct bounded relation is proved equivalent
to its typed status case under the exact status layout.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStatusCases

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout

def CompactBinaryNatRunningStatusSlice
    (tokenTable width tokenCount start finish : Nat) : Prop :=
  CompactAdditiveTokenCell
    tokenTable width tokenCount start 0 finish

def compactBinaryNatRunningStatusSliceDef : 𝚺₀.Semisentence 5 := .mkSigma
  “tokenTable width tokenCount start finish.
    start < tokenCount ∧
    finish = start + 1 ∧
    !(compactFixedWidthEntryDef) tokenTable width start 0”

@[simp] theorem compactBinaryNatRunningStatusSliceDef_spec
    (tokenTable width tokenCount start finish : Nat) :
    compactBinaryNatRunningStatusSliceDef.val.Evalb
        ![tokenTable, width, tokenCount, start, finish] ↔
      CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount start finish := by
  simp [compactBinaryNatRunningStatusSliceDef,
    CompactBinaryNatRunningStatusSlice, CompactAdditiveTokenCell,
    compactFixedWidthEntryDef, CompactFixedWidthEntry,
    arithmeticMem_nat_iff_testBit, foundationNatLE_iff_standard]

theorem compactBinaryNatRunningStatusSliceDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatRunningStatusSliceDef.val := by
  simp [compactBinaryNatRunningStatusSliceDef]

def CompactBinaryNatFailedStatusSlice
    (tokenTable width tokenCount start finish : Nat) : Prop :=
  ∃ innerStart, innerStart ≤ tokenCount ∧
    CompactAdditiveTokenCell
      tokenTable width tokenCount start 1 innerStart ∧
    CompactAdditiveTokenCell
      tokenTable width tokenCount innerStart 0 finish

def compactBinaryNatFailedStatusSliceDef : 𝚺₀.Semisentence 5 := .mkSigma
  “tokenTable width tokenCount start finish.
    ∃ innerStart <⁺ tokenCount,
      start < tokenCount ∧
      innerStart = start + 1 ∧
      !(compactFixedWidthEntryDef) tokenTable width start 1 ∧
      innerStart < tokenCount ∧
      finish = innerStart + 1 ∧
      !(compactFixedWidthEntryDef) tokenTable width innerStart 0”

@[simp] theorem compactBinaryNatFailedStatusSliceDef_spec
    (tokenTable width tokenCount start finish : Nat) :
    compactBinaryNatFailedStatusSliceDef.val.Evalb
        ![tokenTable, width, tokenCount, start, finish] ↔
      CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount start finish := by
  simp [compactBinaryNatFailedStatusSliceDef,
    CompactBinaryNatFailedStatusSlice, CompactAdditiveTokenCell,
    compactFixedWidthEntryDef, CompactFixedWidthEntry,
    arithmeticMem_nat_iff_testBit,
    foundationNatLE_iff_standard]
  aesop

theorem compactBinaryNatFailedStatusSliceDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatFailedStatusSliceDef.val := by
  simp [compactBinaryNatFailedStatusSliceDef]

def CompactBinaryNatCompletedStatusPrefix
    (tokenTable width tokenCount start outputStart : Nat) : Prop :=
  ∃ innerStart, innerStart ≤ tokenCount ∧
    CompactAdditiveTokenCell
      tokenTable width tokenCount start 1 innerStart ∧
    CompactAdditiveTokenCell
      tokenTable width tokenCount innerStart 1 outputStart

def compactBinaryNatCompletedStatusPrefixDef : 𝚺₀.Semisentence 5 := .mkSigma
  “tokenTable width tokenCount start outputStart.
    ∃ innerStart <⁺ tokenCount,
      start < tokenCount ∧
      innerStart = start + 1 ∧
      !(compactFixedWidthEntryDef) tokenTable width start 1 ∧
      innerStart < tokenCount ∧
      outputStart = innerStart + 1 ∧
      !(compactFixedWidthEntryDef) tokenTable width innerStart 1”

@[simp] theorem compactBinaryNatCompletedStatusPrefixDef_spec
    (tokenTable width tokenCount start outputStart : Nat) :
    compactBinaryNatCompletedStatusPrefixDef.val.Evalb
        ![tokenTable, width, tokenCount, start, outputStart] ↔
      CompactBinaryNatCompletedStatusPrefix
        tokenTable width tokenCount start outputStart := by
  simp [compactBinaryNatCompletedStatusPrefixDef,
    CompactBinaryNatCompletedStatusPrefix, CompactAdditiveTokenCell,
    compactFixedWidthEntryDef, CompactFixedWidthEntry,
    arithmeticMem_nat_iff_testBit,
    foundationNatLE_iff_standard]
  aesop

theorem compactBinaryNatCompletedStatusPrefixDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatCompletedStatusPrefixDef.val := by
  simp [compactBinaryNatCompletedStatusPrefixDef]

theorem CompactAdditiveTokenCell.value_eq_of_same_cursor
    {tokenTable width tokenCount cursor
      leftValue leftNext rightValue rightNext : Nat}
    (hleft : CompactAdditiveTokenCell
      tokenTable width tokenCount cursor leftValue leftNext)
    (hright : CompactAdditiveTokenCell
      tokenTable width tokenCount cursor rightValue rightNext) :
    leftValue = rightValue :=
  (CompactAdditiveTokenCell.value_eq_tableValue hleft).trans
    (CompactAdditiveTokenCell.value_eq_tableValue hright).symm

theorem CompactBinaryNatStreamStatusDirectLayout.running_iff
    {tokenTable width tokenCount start finish : Nat}
    {status : Option (Option (List Nat))}
    (hlayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount start finish status) :
    CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount start finish ↔
      status = none := by
  constructor
  · intro hrunning
    cases status with
    | none => rfl
    | some inner =>
        rcases hlayout with
          ⟨outerPayloadStart, houter, _hinner⟩
        have houterCell : CompactAdditiveTokenCell
            tokenTable width tokenCount start 1 outerPayloadStart := by
          simpa [compactAdditiveOptionTag] using houter.1
        have hzeroOne : 0 = 1 :=
          CompactAdditiveTokenCell.value_eq_of_same_cursor
            hrunning houterCell
        omega
  · intro hstatus
    subst status
    rcases hlayout with ⟨outerPayloadStart, houter, _⟩
    have hfinish : finish = outerPayloadStart := by
      rcases houter.2 with hzero | hone
      · exact hzero.2
      · simp [compactAdditiveOptionTag] at hone
    subst outerPayloadStart
    simpa [CompactBinaryNatRunningStatusSlice,
      compactAdditiveOptionTag] using houter.1

theorem CompactBinaryNatStreamStatusDirectLayout.failed_iff
    {tokenTable width tokenCount start finish : Nat}
    {status : Option (Option (List Nat))}
    (hlayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount start finish status) :
    CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount start finish ↔
      status = some none := by
  constructor
  · rintro ⟨innerStart, _hinnerStart, houterDirect, hinnerDirect⟩
    cases status with
    | none =>
        rcases hlayout with ⟨outerPayloadStart, houter, _⟩
        have houterCell : CompactAdditiveTokenCell
            tokenTable width tokenCount start 0 outerPayloadStart := by
          simpa [compactAdditiveOptionTag] using houter.1
        have hzeroOne : 1 = 0 :=
          CompactAdditiveTokenCell.value_eq_of_same_cursor
            houterDirect houterCell
        omega
    | some inner =>
        rcases hlayout with
          ⟨outerPayloadStart, houter,
            innerPayloadStart, hinner, _hpayload⟩
        have hinnerStartEq : innerStart = outerPayloadStart := by
          have hdirectNext := houterDirect.2.1
          have hlayoutNext := houter.1.2.1
          omega
        subst innerStart
        cases inner with
        | none => rfl
        | some output =>
            have hinnerCell : CompactAdditiveTokenCell
                tokenTable width tokenCount outerPayloadStart 1
                  innerPayloadStart := by
              simpa [compactAdditiveOptionTag] using hinner.1
            have hzeroOne : 0 = 1 :=
              CompactAdditiveTokenCell.value_eq_of_same_cursor
                hinnerDirect hinnerCell
            omega
  · intro hstatus
    subst status
    rcases hlayout with
      ⟨outerPayloadStart, houter,
        innerPayloadStart, hinner, _⟩
    have houterCell : CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 outerPayloadStart := by
      simpa [compactAdditiveOptionTag] using houter.1
    have hinnerCell : CompactAdditiveTokenCell
        tokenTable width tokenCount outerPayloadStart 0 finish := by
      have hfinish : finish = innerPayloadStart := by
        rcases hinner.2 with hzero | hone
        · exact hzero.2
        · simp [compactAdditiveOptionTag] at hone
      rw [hfinish]
      simpa [compactAdditiveOptionTag] using hinner.1
    have hbound : outerPayloadStart ≤ tokenCount := by
      have hstart := houterCell.1
      have hnext := houterCell.2.1
      omega
    exact ⟨outerPayloadStart, hbound, houterCell, hinnerCell⟩

theorem CompactBinaryNatStreamStatusDirectLayout.completedPrefix_iff
    {tokenTable width tokenCount start finish outputStart : Nat}
    {status : Option (Option (List Nat))}
    (hlayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount start finish status) :
    CompactBinaryNatCompletedStatusPrefix
        tokenTable width tokenCount start outputStart ↔
      ∃ outputTokens,
        status = some (some outputTokens) ∧ outputStart = start + 2 := by
  constructor
  · rintro ⟨innerStart, _hinnerStart, houterDirect, hinnerDirect⟩
    cases status with
    | none =>
        rcases hlayout with ⟨outerPayloadStart, houter, _⟩
        have houterCell : CompactAdditiveTokenCell
            tokenTable width tokenCount start 0 outerPayloadStart := by
          simpa [compactAdditiveOptionTag] using houter.1
        have hzeroOne : 1 = 0 :=
          CompactAdditiveTokenCell.value_eq_of_same_cursor
            houterDirect houterCell
        omega
    | some inner =>
        rcases hlayout with
          ⟨outerPayloadStart, houter,
            innerPayloadStart, hinner, _hpayload⟩
        have hinnerStartEq : innerStart = outerPayloadStart := by
          have hdirectNext := houterDirect.2.1
          have hlayoutNext := houter.1.2.1
          omega
        subst innerStart
        cases inner with
        | none =>
            have hinnerCell : CompactAdditiveTokenCell
                tokenTable width tokenCount outerPayloadStart 0
                  innerPayloadStart := by
              simpa [compactAdditiveOptionTag] using hinner.1
            have hzeroOne : 1 = 0 :=
              CompactAdditiveTokenCell.value_eq_of_same_cursor
                hinnerDirect hinnerCell
            omega
        | some outputTokens =>
            refine ⟨outputTokens, rfl, ?_⟩
            have houterNext := houterDirect.2.1
            have hinnerNext := hinnerDirect.2.1
            omega
  · rintro ⟨outputTokens, hstatus, houtputStart⟩
    subst status
    rcases hlayout with
      ⟨outerPayloadStart, houter,
        innerPayloadStart, hinner, _hpayload⟩
    have houterCell : CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 outerPayloadStart := by
      simpa [compactAdditiveOptionTag] using houter.1
    have hinnerCell : CompactAdditiveTokenCell
        tokenTable width tokenCount outerPayloadStart 1 outputStart := by
      have hactual : innerPayloadStart = start + 2 := by
        have houterNext := houter.1.2.1
        have hinnerNext := hinner.1.2.1
        omega
      rw [houtputStart, ← hactual]
      simpa [compactAdditiveOptionTag] using hinner.1
    have hbound : outerPayloadStart ≤ tokenCount := by
      have hstart := houterCell.1
      have hnext := houterCell.2.1
      omega
    exact ⟨outerPayloadStart, hbound, houterCell, hinnerCell⟩

#print axioms compactBinaryNatRunningStatusSliceDef_spec
#print axioms compactBinaryNatRunningStatusSliceDef_sigmaZero
#print axioms compactBinaryNatFailedStatusSliceDef_spec
#print axioms compactBinaryNatFailedStatusSliceDef_sigmaZero
#print axioms compactBinaryNatCompletedStatusPrefixDef_spec
#print axioms compactBinaryNatCompletedStatusPrefixDef_sigmaZero
#print axioms CompactAdditiveTokenCell.value_eq_of_same_cursor
#print axioms CompactBinaryNatStreamStatusDirectLayout.running_iff
#print axioms CompactBinaryNatStreamStatusDirectLayout.failed_iff
#print axioms CompactBinaryNatStreamStatusDirectLayout.completedPrefix_iff

end FoundationCompactNumericListedDirectBinaryNatStatusCases
