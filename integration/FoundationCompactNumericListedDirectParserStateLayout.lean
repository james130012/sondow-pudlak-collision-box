import integration.FoundationCompactNumericListedDirectSyntaxTaskLayout
import integration.FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout

/-!
# Complete direct layout of one compact parser state

A parser state is the product of its remaining natural-number tokens, syntax
task stack, and nested parser status.  The two product splits, both structured
lists, every three-field task row, and the status payload share one exact
interval in the public trace token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserStateLayout

open FoundationCompactAdditiveTokenCodec
open FoundationCompactParserDirectTrace
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectStructuredListCanonical
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayout

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

def CompactUnifiedParserStateDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (state : CompactUnifiedParserState) : Prop :=
  ∃ tokensFinish tasksFinish tokensBoundaryTable tasksBoundaryTable,
    CompactAdditiveProductSplit tokenCount start tokensFinish finish ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start state.1.length tokensFinish
      tokensBoundaryTable ∧
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      tokensBoundaryTable state.1 ∧
    CompactAdditiveProductSplit tokenCount tokensFinish tasksFinish finish ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount tokensFinish state.2.1.length tasksFinish
      tasksBoundaryTable ∧
    CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      tasksBoundaryTable state.2.1 ∧
    CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount tasksFinish finish state.2.2 ∧
    Nat.size tokensBoundaryTable ≤ (state.1.length + 1) * tokenCount ∧
    Nat.size tasksBoundaryTable ≤ (state.2.1.length + 1) * tokenCount

theorem compactUnifiedParserStateDirectLayout_canonical
    (frontTokens : List Nat) (state : CompactUnifiedParserState)
    (backTokens : List Nat) :
    let stateTokens := compactAdditiveEncode state
    let tokens := frontTokens ++ stateTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + stateTokens.length
    CompactUnifiedParserStateDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish state := by
  let suffix := state.1
  let tasks := state.2.1
  let status := state.2.2
  let rest := (tasks, status)
  let stateTokens := compactAdditiveEncode state
  let tokens := frontTokens ++ stateTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := frontTokens.length
  let tokensFinish := start + (compactAdditiveEncode suffix).length
  let tasksFinish := tokensFinish + (compactAdditiveEncode tasks).length
  let finish := start + stateTokens.length
  let afterSuffix := frontTokens ++ compactAdditiveEncode suffix
  let afterTasks := afterSuffix ++ compactAdditiveEncode tasks
  have hrestTokens : compactAdditiveEncode rest =
      compactAdditiveEncode tasks ++ compactAdditiveEncode status := by
    simp [rest]
  have hstateTokens : stateTokens =
      compactAdditiveEncode suffix ++ compactAdditiveEncode tasks ++
        compactAdditiveEncode status := by
    change compactAdditiveEncode state = _
    rw [show state = (suffix, rest) by rfl]
    rw [compactAdditiveEncode_prod, hrestTokens]
    simp [List.append_assoc]
  have hfinish : finish = tasksFinish +
      (compactAdditiveEncode status).length := by
    dsimp only [finish, tasksFinish, tokensFinish]
    rw [hstateTokens]
    simp only [List.length_append]
    omega
  have hcommonTokens : tokens =
      frontTokens ++ compactAdditiveEncode suffix ++
        compactAdditiveEncode tasks ++ compactAdditiveEncode status ++
          backTokens := by
    rw [show tokens = frontTokens ++ stateTokens ++ backTokens by rfl]
    rw [hstateTokens]
    simp [List.append_assoc]
  have hsuffixFull :
      frontTokens ++ compactAdditiveEncode suffix ++
          (compactAdditiveEncode tasks ++
            compactAdditiveEncode status ++ backTokens) = tokens := by
    simpa [List.append_assoc] using hcommonTokens.symm
  have htasksFull :
      afterSuffix ++ compactAdditiveEncode tasks ++
          (compactAdditiveEncode status ++ backTokens) = tokens := by
    simpa [afterSuffix, List.append_assoc] using hcommonTokens.symm
  have hstatusFull :
      afterTasks ++ compactAdditiveEncode status ++ backTokens = tokens := by
    simpa [afterTasks, afterSuffix, List.append_assoc] using
      hcommonTokens.symm
  have houterFull :
      frontTokens ++ compactAdditiveEncode (suffix, rest) ++ backTokens =
        tokens := by
    rw [compactAdditiveEncode_prod, hrestTokens]
    simpa [List.append_assoc] using hcommonTokens.symm
  have hinnerFull :
      afterSuffix ++ compactAdditiveEncode (tasks, status) ++ backTokens =
        tokens := by
    rw [compactAdditiveEncode_prod]
    simpa [afterSuffix, List.append_assoc] using hcommonTokens.symm
  have houterRaw := compactAdditiveProductSplit_canonical
    frontTokens suffix rest backTokens
  have hinnerRaw := compactAdditiveProductSplit_canonical
    afterSuffix tasks status backTokens
  rcases compactAdditiveNatListElementLayouts_canonical
      frontTokens suffix
        (compactAdditiveEncode tasks ++
          compactAdditiveEncode status ++ backTokens) with
    ⟨hsuffixLayout, hsuffixRows, hsuffixSize⟩
  rcases compactAdditiveStructuredListElementLayouts_canonical
      CompactSyntaxTaskDirectLayout
      compactSyntaxTaskDirectLayout_canonical
      afterSuffix tasks (compactAdditiveEncode status ++ backTokens) with
    ⟨htasksLayout, htasksRows, htasksSize⟩
  let tokensBoundaryTable :=
    compactAdditiveStructuredListElementBoundaryTable
      tokens.length (start + 1) suffix
  let tasksBoundaryTable :=
    compactAdditiveStructuredListElementBoundaryTable
      tokens.length (tokensFinish + 1) tasks
  have hstatusRaw := compactBinaryNatStreamStatusDirectLayout_canonical
    afterTasks status backTokens
  dsimp only at houterRaw hinnerRaw hstatusRaw
  rw [houterFull] at houterRaw
  rw [hinnerFull] at hinnerRaw
  rw [hsuffixFull] at hsuffixLayout hsuffixRows hsuffixSize
  rw [htasksFull] at htasksLayout htasksRows htasksSize
  rw [hstatusFull] at hstatusRaw
  have hafterSuffix : afterSuffix.length = tokensFinish := by
    dsimp only [afterSuffix, tokensFinish, start]
    simp only [List.length_append]
  have hafterTasks : afterTasks.length = tasksFinish := by
    dsimp only [afterTasks, afterSuffix, tasksFinish, tokensFinish, start]
    simp only [List.length_append]
  have hsuffixLayout' : CompactAdditiveStructuredListLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start suffix.length tokensFinish
      tokensBoundaryTable := by
    have hstart : frontTokens.length = start := rfl
    simpa only [width, hstart, hafterSuffix] using hsuffixLayout
  have htasksLayout' : CompactAdditiveStructuredListLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length tokensFinish tasks.length tasksFinish
      tasksBoundaryTable := by
    simpa only [width, hafterSuffix, hafterTasks] using htasksLayout
  have hsuffixRows' : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length tokensBoundaryTable suffix := by
    simpa only [width, tokensBoundaryTable, start] using hsuffixRows
  have htasksRows' : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length tasksBoundaryTable tasks := by
    simpa only [width, hafterSuffix, tasksBoundaryTable,
      tokensFinish] using htasksRows
  have hstatus' : CompactBinaryNatStreamStatusDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length tasksFinish finish status := by
    have hstatusFinish : tasksFinish +
        (compactAdditiveEncode status).length = finish := hfinish.symm
    simpa only [width, hafterTasks, hstatusFinish] using hstatusRaw
  have houterFinish : start + (compactAdditiveEncode suffix).length +
      (compactAdditiveEncode rest).length = finish := by
    rw [hrestTokens]
    dsimp only [finish]
    rw [hstateTokens]
    simp only [List.length_append]
    omega
  have houter : CompactAdditiveProductSplit
      tokens.length start tokensFinish finish := by
    simpa only [start, tokensFinish, houterFinish] using houterRaw
  have hinnerFinish : tokensFinish +
      (compactAdditiveEncode tasks).length +
        (compactAdditiveEncode status).length = finish := hfinish.symm
  have hinner : CompactAdditiveProductSplit
      tokens.length tokensFinish tasksFinish finish := by
    simpa only [hafterSuffix, hafterTasks, hinnerFinish] using hinnerRaw
  have hsuffixSize' : Nat.size tokensBoundaryTable ≤
      (suffix.length + 1) * tokens.length := hsuffixSize
  have htasksSize' : Nat.size tasksBoundaryTable ≤
      (tasks.length + 1) * tokens.length := by
    simpa only [tasksBoundaryTable, hafterSuffix,
      tokensFinish] using htasksSize
  exact ⟨tokensFinish, tasksFinish, tokensBoundaryTable,
    tasksBoundaryTable, houter, hsuffixLayout', hsuffixRows', hinner,
    htasksLayout', htasksRows', hstatus', hsuffixSize', htasksSize'⟩

#print axioms compactUnifiedParserStateDirectLayout_canonical

end FoundationCompactNumericListedDirectParserStateLayout
