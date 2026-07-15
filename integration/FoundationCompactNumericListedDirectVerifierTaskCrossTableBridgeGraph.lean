import integration.FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality
import integration.FoundationCompactNumericListedDirectVerifierTaskLayout

/-!
# Cross-table bridge for complete verifier tasks

The proof table and verifier-state table are independent fixed-width tables.
This graph identifies a complete verifier task by its tag and five direct
field slices.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTaskCrossTableBridgeGraph

open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality

def CompactNumericVerifierTaskCrossTableBridgeGraph
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish sourceTag
      sourceGammaFinish sourceFirstFinish sourceSecondFinish sourceWitnessFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish targetTag
      targetGammaFinish targetFirstFinish targetSecondFinish targetWitnessFinish :
      Nat) : Prop :=
  sourceTag = targetTag ∧
    CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount (sourceStart + 1) sourceGammaFinish
      targetTable targetWidth targetTokenCount (targetStart + 1) targetGammaFinish ∧
    CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceGammaFinish sourceFirstFinish
      targetTable targetWidth targetTokenCount targetGammaFinish targetFirstFinish ∧
    CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceFirstFinish sourceSecondFinish
      targetTable targetWidth targetTokenCount targetFirstFinish targetSecondFinish ∧
    CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceSecondFinish sourceWitnessFinish
      targetTable targetWidth targetTokenCount targetSecondFinish targetWitnessFinish ∧
    CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceWitnessFinish sourceFinish
      targetTable targetWidth targetTokenCount targetWitnessFinish targetFinish

def compactNumericVerifierTaskCrossTableBridgeGraphDef :
    𝚺₀.Semisentence 20 := .mkSigma
  “sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish sourceTag
      sourceGammaFinish sourceFirstFinish sourceSecondFinish sourceWitnessFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish targetTag
      targetGammaFinish targetFirstFinish targetSecondFinish targetWitnessFinish.
    sourceTag = targetTag ∧
    !(compactFixedWidthCrossTableSlicesEqDef)
      sourceTable sourceWidth sourceTokenCount (sourceStart + 1) sourceGammaFinish
      targetTable targetWidth targetTokenCount (targetStart + 1) targetGammaFinish ∧
    !(compactFixedWidthCrossTableSlicesEqDef)
      sourceTable sourceWidth sourceTokenCount sourceGammaFinish sourceFirstFinish
      targetTable targetWidth targetTokenCount targetGammaFinish targetFirstFinish ∧
    !(compactFixedWidthCrossTableSlicesEqDef)
      sourceTable sourceWidth sourceTokenCount sourceFirstFinish sourceSecondFinish
      targetTable targetWidth targetTokenCount targetFirstFinish targetSecondFinish ∧
    !(compactFixedWidthCrossTableSlicesEqDef)
      sourceTable sourceWidth sourceTokenCount sourceSecondFinish sourceWitnessFinish
      targetTable targetWidth targetTokenCount targetSecondFinish targetWitnessFinish ∧
    !(compactFixedWidthCrossTableSlicesEqDef)
      sourceTable sourceWidth sourceTokenCount sourceWitnessFinish sourceFinish
      targetTable targetWidth targetTokenCount targetWitnessFinish targetFinish”

def compactNumericVerifierTaskCrossTableBridgeGraphEnvironment
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish sourceTag
      sourceGammaFinish sourceFirstFinish sourceSecondFinish sourceWitnessFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish targetTag
      targetGammaFinish targetFirstFinish targetSecondFinish targetWitnessFinish :
      Nat) : Fin 20 → Nat :=
  ![sourceTable, sourceWidth, sourceTokenCount, sourceStart, sourceFinish,
    sourceTag, sourceGammaFinish, sourceFirstFinish, sourceSecondFinish,
    sourceWitnessFinish, targetTable, targetWidth, targetTokenCount,
    targetStart, targetFinish, targetTag, targetGammaFinish,
    targetFirstFinish, targetSecondFinish, targetWitnessFinish]

@[simp] theorem compactNumericVerifierTaskCrossTableBridgeGraphDef_spec
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish sourceTag
      sourceGammaFinish sourceFirstFinish sourceSecondFinish sourceWitnessFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish targetTag
      targetGammaFinish targetFirstFinish targetSecondFinish targetWitnessFinish :
      Nat) :
    compactNumericVerifierTaskCrossTableBridgeGraphDef.val.Evalb
        (compactNumericVerifierTaskCrossTableBridgeGraphEnvironment
          sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish sourceTag
          sourceGammaFinish sourceFirstFinish sourceSecondFinish sourceWitnessFinish
          targetTable targetWidth targetTokenCount targetStart targetFinish targetTag
          targetGammaFinish targetFirstFinish targetSecondFinish targetWitnessFinish) ↔
      CompactNumericVerifierTaskCrossTableBridgeGraph
        sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish sourceTag
        sourceGammaFinish sourceFirstFinish sourceSecondFinish sourceWitnessFinish
        targetTable targetWidth targetTokenCount targetStart targetFinish targetTag
        targetGammaFinish targetFirstFinish targetSecondFinish targetWitnessFinish := by
  let env := compactNumericVerifierTaskCrossTableBridgeGraphEnvironment
    sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish sourceTag
    sourceGammaFinish sourceFirstFinish sourceSecondFinish sourceWitnessFinish
    targetTable targetWidth targetTokenCount targetStart targetFinish targetTag
    targetGammaFinish targetFirstFinish targetSecondFinish targetWitnessFinish
  change compactNumericVerifierTaskCrossTableBridgeGraphDef.val.Evalb env ↔ _
  have hgammaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2,
          Semiterm.Operator.Add.add.operator
            ![(#3 : Semiterm ℒₒᵣ Empty 20),
              Semiterm.numeral (L := ℒₒᵣ) 1],
          #6, #10, #11, #12,
          Semiterm.Operator.Add.add.operator
            ![(#13 : Semiterm ℒₒᵣ Empty 20),
              Semiterm.numeral (L := ℒₒᵣ) 1],
          #16]) =
        ![sourceTable, sourceWidth, sourceTokenCount, sourceStart + 1,
          sourceGammaFinish, targetTable, targetWidth, targetTokenCount,
          targetStart + 1, targetGammaFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hfirstEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2, #6, #7,
          #10, #11, #12, #16, #17]) =
        ![sourceTable, sourceWidth, sourceTokenCount, sourceGammaFinish,
          sourceFirstFinish, targetTable, targetWidth, targetTokenCount,
          targetGammaFinish, targetFirstFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsecondEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2, #7, #8,
          #10, #11, #12, #17, #18]) =
        ![sourceTable, sourceWidth, sourceTokenCount, sourceFirstFinish,
          sourceSecondFinish, targetTable, targetWidth, targetTokenCount,
          targetFirstFinish, targetSecondFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hwitnessEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2, #8, #9,
          #10, #11, #12, #18, #19]) =
        ![sourceTable, sourceWidth, sourceTokenCount, sourceSecondFinish,
          sourceWitnessFinish, targetTable, targetWidth, targetTokenCount,
          targetSecondFinish, targetWitnessFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsuffixEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2, #9, #4,
          #10, #11, #12, #19, #14]) =
        ![sourceTable, sourceWidth, sourceTokenCount, sourceWitnessFinish,
          sourceFinish, targetTable, targetWidth, targetTokenCount,
          targetWitnessFinish, targetFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsourceTag : env 5 = sourceTag := rfl
  have htargetTag : env 15 = targetTag := rfl
  simp [compactNumericVerifierTaskCrossTableBridgeGraphDef,
    CompactNumericVerifierTaskCrossTableBridgeGraph,
    hgammaEnv, hfirstEnv, hsecondEnv, hwitnessEnv, hsuffixEnv,
    hsourceTag, htargetTag, env]

theorem compactNumericVerifierTaskCrossTableBridgeGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierTaskCrossTableBridgeGraphDef.val := by
  simp [compactNumericVerifierTaskCrossTableBridgeGraphDef]

theorem CompactNumericVerifierTaskCrossTableBridgeGraph.sound
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      sourceGammaFinish sourceFirstFinish sourceSecondFinish sourceWitnessFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish
      targetGammaFinish targetFirstFinish targetSecondFinish targetWitnessFinish :
      Nat}
    {sourceTask targetTask : CompactNumericVerifierTask}
    (hgraph : CompactNumericVerifierTaskCrossTableBridgeGraph
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish sourceTask.1
      sourceGammaFinish sourceFirstFinish sourceSecondFinish sourceWitnessFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish targetTask.1
      targetGammaFinish targetFirstFinish targetSecondFinish targetWitnessFinish)
    (_hsource : CompactNumericVerifierTaskDirectLayout
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish sourceTask)
    (_htarget : CompactNumericVerifierTaskDirectLayout
      targetTable targetWidth targetTokenCount targetStart targetFinish targetTask) :
    CompactAdditiveNatListListDirectLayout
      sourceTable sourceWidth sourceTokenCount
        (sourceStart + 1) sourceGammaFinish sourceTask.2.1 →
    CompactAdditiveNatListListDirectLayout
      targetTable targetWidth targetTokenCount
        (targetStart + 1) targetGammaFinish targetTask.2.1 →
    CompactAdditiveNatListDirectLayout
      sourceTable sourceWidth sourceTokenCount
        sourceGammaFinish sourceFirstFinish sourceTask.2.2.1 →
    CompactAdditiveNatListDirectLayout
      targetTable targetWidth targetTokenCount
        targetGammaFinish targetFirstFinish targetTask.2.2.1 →
    CompactAdditiveNatListDirectLayout
      sourceTable sourceWidth sourceTokenCount
        sourceFirstFinish sourceSecondFinish sourceTask.2.2.2.1 →
    CompactAdditiveNatListDirectLayout
      targetTable targetWidth targetTokenCount
        targetFirstFinish targetSecondFinish targetTask.2.2.2.1 →
    CompactAdditiveNatListDirectLayout
      sourceTable sourceWidth sourceTokenCount
        sourceSecondFinish sourceWitnessFinish sourceTask.2.2.2.2.1 →
    CompactAdditiveNatListDirectLayout
      targetTable targetWidth targetTokenCount
        targetSecondFinish targetWitnessFinish targetTask.2.2.2.2.1 →
    CompactAdditiveNatListDirectLayout
      sourceTable sourceWidth sourceTokenCount
        sourceWitnessFinish sourceFinish sourceTask.2.2.2.2.2 →
    CompactAdditiveNatListDirectLayout
      targetTable targetWidth targetTokenCount
        targetWitnessFinish targetFinish targetTask.2.2.2.2.2 →
    targetTask = sourceTask := by
  intro hsourceGamma htargetGamma hsourceFirst htargetFirst hsourceSecond
    htargetSecond hsourceWitness htargetWitness hsourceSuffix htargetSuffix
  have hgamma : targetTask.2.1 = sourceTask.2.1 :=
    CompactFixedWidthCrossTableSlicesEq.natListListValues_eq
      hgraph.2.1 hsourceGamma htargetGamma
  have hfirst : targetTask.2.2.1 = sourceTask.2.2.1 :=
    CompactFixedWidthCrossTableSlicesEq.natListValues_eq
      hgraph.2.2.1 hsourceFirst htargetFirst
  have hsecond : targetTask.2.2.2.1 = sourceTask.2.2.2.1 :=
    CompactFixedWidthCrossTableSlicesEq.natListValues_eq
      hgraph.2.2.2.1 hsourceSecond htargetSecond
  have hwitness : targetTask.2.2.2.2.1 = sourceTask.2.2.2.2.1 :=
    CompactFixedWidthCrossTableSlicesEq.natListValues_eq
      hgraph.2.2.2.2.1 hsourceWitness htargetWitness
  have hsuffix : targetTask.2.2.2.2.2 = sourceTask.2.2.2.2.2 :=
    CompactFixedWidthCrossTableSlicesEq.natListValues_eq
      hgraph.2.2.2.2.2 hsourceSuffix htargetSuffix
  apply Prod.ext
  · exact hgraph.1.symm
  · apply Prod.ext
    · exact hgamma
    · apply Prod.ext
      · exact hfirst
      · apply Prod.ext
        · exact hsecond
        · apply Prod.ext <;> assumption

theorem CompactNumericVerifierTaskCrossTableBridgeGraph.of_layouts
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat}
    {task : CompactNumericVerifierTask}
    (hsource : CompactNumericVerifierTaskDirectLayout
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish task)
    (htarget : CompactNumericVerifierTaskDirectLayout
      targetTable targetWidth targetTokenCount targetStart targetFinish task) :
    ∃ sourceGammaFinish sourceFirstFinish sourceSecondFinish sourceWitnessFinish
        targetGammaFinish targetFirstFinish targetSecondFinish targetWitnessFinish,
      CompactNumericVerifierTaskCrossTableBridgeGraph
        sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish task.1
        sourceGammaFinish sourceFirstFinish sourceSecondFinish sourceWitnessFinish
        targetTable targetWidth targetTokenCount targetStart targetFinish task.1
        targetGammaFinish targetFirstFinish targetSecondFinish targetWitnessFinish := by
  rcases hsource with ⟨sourceFieldsStart, hsourceTag, hsourceFields⟩
  rcases htarget with ⟨targetFieldsStart, htargetTag, htargetFields⟩
  rcases hsourceTag with ⟨_hsourceStart, hsourceFieldsStart, _hsourceTag⟩
  rcases htargetTag with ⟨_htargetStart, htargetFieldsStart, _htargetTag⟩
  subst sourceFieldsStart
  subst targetFieldsStart
  rcases hsourceFields with
    ⟨sourceGammaFinish, sourceFirstFinish, sourceSecondFinish,
      sourceWitnessFinish, hsourceGamma, hsourceFirst, hsourceSecond,
      hsourceWitness, hsourceSuffix⟩
  rcases htargetFields with
    ⟨targetGammaFinish, targetFirstFinish, targetSecondFinish,
      targetWitnessFinish, htargetGamma, htargetFirst, htargetSecond,
      htargetWitness, htargetSuffix⟩
  refine ⟨sourceGammaFinish, sourceFirstFinish, sourceSecondFinish,
    sourceWitnessFinish, targetGammaFinish, targetFirstFinish,
    targetSecondFinish, targetWitnessFinish, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact CompactFixedWidthCrossTableSlicesEq.of_natListListLayouts
      hsourceGamma htargetGamma
  · exact CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
      hsourceFirst htargetFirst
  · exact CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
      hsourceSecond htargetSecond
  · exact CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
      hsourceWitness htargetWitness
  · exact CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
      hsourceSuffix htargetSuffix

#print axioms compactNumericVerifierTaskCrossTableBridgeGraphDef_spec
#print axioms compactNumericVerifierTaskCrossTableBridgeGraphDef_sigmaZero
#print axioms CompactNumericVerifierTaskCrossTableBridgeGraph.sound
#print axioms CompactNumericVerifierTaskCrossTableBridgeGraph.of_layouts

end FoundationCompactNumericListedDirectVerifierTaskCrossTableBridgeGraph
