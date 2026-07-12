import integration.FoundationCompactNumericListedDirectCompletedStatusReverseRows
import integration.FoundationCompactNumericListedDirectNatListSameRows

/-!
# Direct equality of two completed stream statuses

Both status values must have the completed `11` prefix.  Their output lists
are then compared through exact one-token natural-number rows.  Boundary
rigidity prevents either formula-side output table from selecting other rows.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCompletedStatusSameRows

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectNatListSameRows

def CompactBinaryNatCompletedStatusSameRows
    (tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish
      sourceOutputStart sourceOutputBoundary
      targetOutputStart targetOutputBoundary outputCount : Nat) : Prop :=
  CompactBinaryNatCompletedStatusPrefix
      tokenTable width tokenCount sourceStatusStart sourceOutputStart ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount sourceOutputStart outputCount
        sourceStatusFinish sourceOutputBoundary ∧
    CompactBinaryNatCompletedStatusPrefix
      tokenTable width tokenCount targetStatusStart targetOutputStart ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount targetOutputStart outputCount
        targetStatusFinish targetOutputBoundary ∧
    CompactAdditiveNatListSameRows
      tokenTable width tokenCount sourceOutputBoundary outputCount
        targetOutputBoundary outputCount

def CompactBinaryNatCompletedStatusSameRowsWithSize
    (tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) : Prop :=
  CompactBinaryNatCompletedStatusSameRows
      tokenTable width tokenCount
        sourceStatusStart sourceStatusFinish
        targetStatusStart targetStatusFinish
        sourceOutputStart sourceOutputBoundary
        targetOutputStart targetOutputBoundary outputCount ∧
    sourceOutputBoundarySize = Nat.size sourceOutputBoundary ∧
    sourceOutputBoundarySize ≤ (outputCount + 1) * tokenCount ∧
    targetOutputBoundarySize = Nat.size targetOutputBoundary ∧
    targetOutputBoundarySize ≤ (outputCount + 1) * tokenCount

def compactBinaryNatCompletedStatusSameRowsFormulaBundle :
    𝚺₀.Semisentence 5 × 𝚺₀.Semisentence 7 ×
      𝚺₀.Semisentence 5 × 𝚺₀.Semisentence 7 ×
        𝚺₀.Semisentence 7 :=
  (compactBinaryNatCompletedStatusPrefixDef,
    compactAdditiveStructuredListLayoutDef,
    compactBinaryNatCompletedStatusPrefixDef,
    compactAdditiveStructuredListLayoutDef,
    compactAdditiveNatListSameRowsDef)

@[simp] theorem compactBinaryNatCompletedStatusSameRowsFormulaBundle_spec
    (tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish
      sourceOutputStart sourceOutputBoundary
      targetOutputStart targetOutputBoundary outputCount : Nat) :
    (compactBinaryNatCompletedStatusSameRowsFormulaBundle.1.val.Evalb
          ![tokenTable, width, tokenCount,
            sourceStatusStart, sourceOutputStart] ∧
      compactBinaryNatCompletedStatusSameRowsFormulaBundle.2.1.val.Evalb
          ![tokenTable, width, tokenCount, sourceOutputStart, outputCount,
            sourceStatusFinish, sourceOutputBoundary] ∧
      compactBinaryNatCompletedStatusSameRowsFormulaBundle.2.2.1.val.Evalb
          ![tokenTable, width, tokenCount,
            targetStatusStart, targetOutputStart] ∧
      compactBinaryNatCompletedStatusSameRowsFormulaBundle.2.2.2.1.val.Evalb
          ![tokenTable, width, tokenCount, targetOutputStart, outputCount,
            targetStatusFinish, targetOutputBoundary] ∧
      compactBinaryNatCompletedStatusSameRowsFormulaBundle.2.2.2.2.val.Evalb
          ![tokenTable, width, tokenCount,
            sourceOutputBoundary, outputCount,
            targetOutputBoundary, outputCount]) ↔
      CompactBinaryNatCompletedStatusSameRows
        tokenTable width tokenCount
          sourceStatusStart sourceStatusFinish
          targetStatusStart targetStatusFinish
          sourceOutputStart sourceOutputBoundary
          targetOutputStart targetOutputBoundary outputCount := by
  simp [compactBinaryNatCompletedStatusSameRowsFormulaBundle,
    CompactBinaryNatCompletedStatusSameRows]

theorem CompactAdditiveNatListSameRows.sourceUnitBoundaryRows
    {tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat}
    (hsame : CompactAdditiveNatListSameRows
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount) :
    CompactAdditiveUnitBoundaryRows
      tokenCount sourceCount sourceBoundary := by
  intro index hindex
  rcases hsame.2 index hindex with
    ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
      targetLeft, htargetLeft, targetRight, htargetRight,
      hsourceLeftEntry, hsourceRightEntry,
      htargetLeftEntry, htargetRightEntry, hrowEq⟩
  exact ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
    hsourceLeftEntry, hsourceRightEntry, hrowEq.2.1⟩

theorem CompactAdditiveNatListSameRows.targetUnitBoundaryRows
    {tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat}
    (hsame : CompactAdditiveNatListSameRows
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount) :
    CompactAdditiveUnitBoundaryRows
      tokenCount targetCount targetBoundary := by
  intro index hindex
  have hsourceIndex : index < sourceCount := by
    rw [← hsame.1]
    exact hindex
  rcases hsame.2 index hsourceIndex with
    ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
      targetLeft, htargetLeft, targetRight, htargetRight,
      hsourceLeftEntry, hsourceRightEntry,
      htargetLeftEntry, htargetRightEntry, hrowEq⟩
  exact ⟨targetLeft, htargetLeft, targetRight, htargetRight,
    htargetLeftEntry, htargetRightEntry, hrowEq.2.2.2.1⟩

theorem completedStatusSameRows_iff
    {tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish : Nat}
    {sourceStatus targetStatus : Option (Option (List Nat))}
    (hsourceStatus : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount sourceStatusStart sourceStatusFinish
        sourceStatus)
    (htargetStatus : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount targetStatusStart targetStatusFinish
        targetStatus) :
    (∃ sourceOutputStart sourceOutputBoundary
        targetOutputStart targetOutputBoundary outputCount,
        CompactBinaryNatCompletedStatusSameRows
          tokenTable width tokenCount
            sourceStatusStart sourceStatusFinish
            targetStatusStart targetStatusFinish
            sourceOutputStart sourceOutputBoundary
            targetOutputStart targetOutputBoundary outputCount) ↔
      ∃ output,
        sourceStatus = some (some output) ∧
        targetStatus = some (some output) := by
  constructor
  · rintro ⟨sourceOutputStart, sourceOutputBoundary,
      targetOutputStart, targetOutputBoundary, outputCount,
      hsourcePrefix, hsourceFormulaLayout,
      htargetPrefix, htargetFormulaLayout, hsameRows⟩
    rcases
        (CompactBinaryNatStreamStatusDirectLayout.completedPrefix_iff
          hsourceStatus).mp hsourcePrefix with
      ⟨sourceOutput, hsourceStatusEq, hsourceOutputStart⟩
    rcases
        (CompactBinaryNatStreamStatusDirectLayout.completedPrefix_iff
          htargetStatus).mp htargetPrefix with
      ⟨targetOutput, htargetStatusEq, htargetOutputStart⟩
    subst sourceStatus
    subst targetStatus
    rcases hsourceStatus with
      ⟨sourceOuterStart, hsourceOuter,
        sourceActualStart, hsourceInner,
        sourceActualBoundary, hsourceActualLayout,
        hsourceActualRows, _hsourceActualSize⟩
    rcases htargetStatus with
      ⟨targetOuterStart, htargetOuter,
        targetActualStart, htargetInner,
        targetActualBoundary, htargetActualLayout,
        htargetActualRows, _htargetActualSize⟩
    have hsourceActualStart :
        sourceActualStart = sourceStatusStart + 2 := by
      have houterNext := hsourceOuter.1.2.1
      have hinnerNext := hsourceInner.1.2.1
      omega
    have htargetActualStart :
        targetActualStart = targetStatusStart + 2 := by
      have houterNext := htargetOuter.1.2.1
      have hinnerNext := htargetInner.1.2.1
      omega
    have hsourceStart : sourceActualStart = sourceOutputStart := by omega
    have htargetStart : targetActualStart = targetOutputStart := by omega
    have hsourceFormulaUnit : CompactAdditiveUnitBoundaryRows
        tokenCount outputCount sourceOutputBoundary :=
      CompactAdditiveNatListSameRows.sourceUnitBoundaryRows hsameRows
    have htargetFormulaUnit : CompactAdditiveUnitBoundaryRows
        tokenCount outputCount targetOutputBoundary :=
      CompactAdditiveNatListSameRows.targetUnitBoundaryRows hsameRows
    have hsourceActualUnit : CompactAdditiveUnitBoundaryRows
        tokenCount sourceOutput.length sourceActualBoundary :=
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hsourceActualRows
    have htargetActualUnit : CompactAdditiveUnitBoundaryRows
        tokenCount targetOutput.length targetActualBoundary :=
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        htargetActualRows
    have hsourceFormulaFinish :
        sourceStatusFinish = sourceOutputStart + 1 + outputCount :=
      CompactAdditiveStructuredListLayout.finish_eq_start_add_count
        hsourceFormulaLayout hsourceFormulaUnit
    have htargetFormulaFinish :
        targetStatusFinish = targetOutputStart + 1 + outputCount :=
      CompactAdditiveStructuredListLayout.finish_eq_start_add_count
        htargetFormulaLayout htargetFormulaUnit
    have hsourceActualFinish :
        sourceStatusFinish =
          sourceActualStart + 1 + sourceOutput.length :=
      CompactAdditiveStructuredListLayout.finish_eq_start_add_count
        hsourceActualLayout hsourceActualUnit
    have htargetActualFinish :
        targetStatusFinish =
          targetActualStart + 1 + targetOutput.length :=
      CompactAdditiveStructuredListLayout.finish_eq_start_add_count
        htargetActualLayout htargetActualUnit
    have hsourceCount : sourceOutput.length = outputCount := by omega
    have htargetCount : targetOutput.length = outputCount := by omega
    have hsourceFormulaLayout' : CompactAdditiveStructuredListLayout
        tokenTable width tokenCount sourceActualStart sourceOutput.length
          sourceStatusFinish sourceOutputBoundary := by
      rw [hsourceStart, hsourceCount]
      exact hsourceFormulaLayout
    have htargetFormulaLayout' : CompactAdditiveStructuredListLayout
        tokenTable width tokenCount targetActualStart targetOutput.length
          targetStatusFinish targetOutputBoundary := by
      rw [htargetStart, htargetCount]
      exact htargetFormulaLayout
    have hsourceFormulaRows :
        CompactAdditiveStructuredListElementRowLayouts
          CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
            sourceOutputBoundary sourceOutput :=
      CompactAdditiveStructuredListElementRowLayouts.natRows_on_unitBoundary
        hsourceActualLayout hsourceActualRows
          hsourceFormulaLayout' (by simpa [hsourceCount] using
            hsourceFormulaUnit)
    have htargetFormulaRows :
        CompactAdditiveStructuredListElementRowLayouts
          CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
            targetOutputBoundary targetOutput :=
      CompactAdditiveStructuredListElementRowLayouts.natRows_on_unitBoundary
        htargetActualLayout htargetActualRows
          htargetFormulaLayout' (by simpa [htargetCount] using
            htargetFormulaUnit)
    have htypedSameRows : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          sourceOutputBoundary sourceOutput.length
          targetOutputBoundary targetOutput.length := by
      rw [hsourceCount, htargetCount]
      exact hsameRows
    have houtput : targetOutput = sourceOutput :=
      CompactAdditiveNatListSameRows.eq_of_rows
        htypedSameRows hsourceFormulaRows htargetFormulaRows
    exact ⟨sourceOutput, rfl, by simp [houtput]⟩
  · rintro ⟨output, hsourceStatusEq, htargetStatusEq⟩
    subst sourceStatus
    subst targetStatus
    have hsourceStatusCopy := hsourceStatus
    have htargetStatusCopy := htargetStatus
    rcases hsourceStatus with
      ⟨sourceOuterStart, hsourceOuter,
        sourceOutputStart, hsourceInner,
        sourceOutputBoundary, hsourceOutputLayout,
        hsourceOutputRows, _hsourceOutputSize⟩
    rcases htargetStatus with
      ⟨targetOuterStart, htargetOuter,
        targetOutputStart, htargetInner,
        targetOutputBoundary, htargetOutputLayout,
        htargetOutputRows, _htargetOutputSize⟩
    have hsourceOutputStartEq :
        sourceOutputStart = sourceStatusStart + 2 := by
      have houterNext := hsourceOuter.1.2.1
      have hinnerNext := hsourceInner.1.2.1
      omega
    have htargetOutputStartEq :
        targetOutputStart = targetStatusStart + 2 := by
      have houterNext := htargetOuter.1.2.1
      have hinnerNext := htargetInner.1.2.1
      omega
    have hsourcePrefix : CompactBinaryNatCompletedStatusPrefix
        tokenTable width tokenCount sourceStatusStart sourceOutputStart :=
      (CompactBinaryNatStreamStatusDirectLayout.completedPrefix_iff
        hsourceStatusCopy).mpr
          ⟨output, rfl, hsourceOutputStartEq⟩
    have htargetPrefix : CompactBinaryNatCompletedStatusPrefix
        tokenTable width tokenCount targetStatusStart targetOutputStart :=
      (CompactBinaryNatStreamStatusDirectLayout.completedPrefix_iff
        htargetStatusCopy).mpr
          ⟨output, rfl, htargetOutputStartEq⟩
    have hsameRows : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          sourceOutputBoundary output.length
          targetOutputBoundary output.length :=
      CompactAdditiveStructuredListElementRowLayouts.natSameRows
        hsourceOutputRows htargetOutputRows rfl
    exact ⟨sourceOutputStart, sourceOutputBoundary,
      targetOutputStart, targetOutputBoundary, output.length,
      hsourcePrefix, hsourceOutputLayout,
      htargetPrefix, htargetOutputLayout, hsameRows⟩

theorem completedStatusSameRowsWithSize_iff
    {tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish : Nat}
    {sourceStatus targetStatus : Option (Option (List Nat))}
    (hsourceStatus : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount sourceStatusStart sourceStatusFinish
        sourceStatus)
    (htargetStatus : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount targetStatusStart targetStatusFinish
        targetStatus) :
    (∃ sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
        targetOutputStart targetOutputBoundary targetOutputBoundarySize
        outputCount,
        CompactBinaryNatCompletedStatusSameRowsWithSize
          tokenTable width tokenCount
            sourceStatusStart sourceStatusFinish
            targetStatusStart targetStatusFinish
            sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
            targetOutputStart targetOutputBoundary targetOutputBoundarySize
            outputCount) ↔
      ∃ output,
        sourceStatus = some (some output) ∧
        targetStatus = some (some output) := by
  constructor
  · rintro ⟨sourceOutputStart, sourceOutputBoundary,
      sourceOutputBoundarySize, targetOutputStart, targetOutputBoundary,
      targetOutputBoundarySize, outputCount,
      hrelation, _hsourceSizeEq, _hsourceSize,
      _htargetSizeEq, _htargetSize⟩
    exact (completedStatusSameRows_iff
      hsourceStatus htargetStatus).mp
        ⟨sourceOutputStart, sourceOutputBoundary,
          targetOutputStart, targetOutputBoundary, outputCount, hrelation⟩
  · rintro ⟨output, hsourceStatusEq, htargetStatusEq⟩
    subst sourceStatus
    subst targetStatus
    have hsourceStatusCopy := hsourceStatus
    have htargetStatusCopy := htargetStatus
    rcases hsourceStatus with
      ⟨sourceOuterStart, hsourceOuter,
        sourceOutputStart, hsourceInner,
        sourceOutputBoundary, hsourceOutputLayout,
        hsourceOutputRows, hsourceOutputSize⟩
    rcases htargetStatus with
      ⟨targetOuterStart, htargetOuter,
        targetOutputStart, htargetInner,
        targetOutputBoundary, htargetOutputLayout,
        htargetOutputRows, htargetOutputSize⟩
    have hsourceOutputStartEq :
        sourceOutputStart = sourceStatusStart + 2 := by
      have houterNext := hsourceOuter.1.2.1
      have hinnerNext := hsourceInner.1.2.1
      omega
    have htargetOutputStartEq :
        targetOutputStart = targetStatusStart + 2 := by
      have houterNext := htargetOuter.1.2.1
      have hinnerNext := htargetInner.1.2.1
      omega
    have hsourcePrefix : CompactBinaryNatCompletedStatusPrefix
        tokenTable width tokenCount sourceStatusStart sourceOutputStart :=
      (CompactBinaryNatStreamStatusDirectLayout.completedPrefix_iff
        hsourceStatusCopy).mpr
          ⟨output, rfl, hsourceOutputStartEq⟩
    have htargetPrefix : CompactBinaryNatCompletedStatusPrefix
        tokenTable width tokenCount targetStatusStart targetOutputStart :=
      (CompactBinaryNatStreamStatusDirectLayout.completedPrefix_iff
        htargetStatusCopy).mpr
          ⟨output, rfl, htargetOutputStartEq⟩
    have hsameRows : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          sourceOutputBoundary output.length
          targetOutputBoundary output.length :=
      CompactAdditiveStructuredListElementRowLayouts.natSameRows
        hsourceOutputRows htargetOutputRows rfl
    exact ⟨sourceOutputStart, sourceOutputBoundary,
      Nat.size sourceOutputBoundary,
      targetOutputStart, targetOutputBoundary,
      Nat.size targetOutputBoundary, output.length,
      ⟨hsourcePrefix, hsourceOutputLayout,
        htargetPrefix, htargetOutputLayout, hsameRows⟩,
      rfl, by simpa using hsourceOutputSize,
      rfl, by simpa using htargetOutputSize⟩

#print axioms compactBinaryNatCompletedStatusSameRowsFormulaBundle_spec
#print axioms CompactAdditiveNatListSameRows.sourceUnitBoundaryRows
#print axioms CompactAdditiveNatListSameRows.targetUnitBoundaryRows
#print axioms completedStatusSameRows_iff
#print axioms completedStatusSameRowsWithSize_iff

end FoundationCompactNumericListedDirectCompletedStatusSameRows
