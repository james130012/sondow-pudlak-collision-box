import integration.FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
import integration.FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStatePublicBounds

/-!
# Public 429-coordinate bound for a failed verifier parse step

The failed parser branch now constructs the actual 429-column formula witness.
The two canonical state cores, the task head, and all twenty-two parser
coordinates share one explicit budget.  Every parse-success-only coordinate is
the fixed unused value, so no argument-sensitive environment constant remains
in the stated bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseFailureStepPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierParseStateCompleteness
open FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateGraph
open FoundationCompactNumericListedDirectVerifierParsePayloadFailureSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStatePublicBounds
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds

def compactNumericVerifierParseFailureStepCommonCoordinateSizeBound
    (stateWidth stateTokenCount proofWeight certificateWeight : Nat) : Nat :=
  let stateBound :=
    compactNumericVerifierStateCoreCoordinateSizeBound
      stateWidth stateTokenCount
  let parserBound :=
    compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  parserBound + compactNumericVerifierStepUnusedEnvironmentConstant

def compactNumericVerifierParseFailureStepCoordinateSizeBound
    (stateWidth stateTokenCount proofWeight certificateWeight : Nat) : Nat :=
  let stateBound :=
    compactNumericVerifierStateCoreCoordinateSizeBound
      stateWidth stateTokenCount
  let commonBound :=
    compactNumericVerifierParseFailureStepCommonCoordinateSizeBound
      stateWidth stateTokenCount proofWeight certificateWeight
  stateBound + 384 * commonBound

/- Every concrete failed parse step has an actual 429-column formula witness
whose coordinates are bounded only by the canonical state header and the two
parser-input weights. -/
set_option maxHeartbeats 2400000 in
set_option maxRecDepth 65536 in
theorem exists_compactNumericVerifierParseFailureStepFormulaWitness_with_publicBounds
    {stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {currentTask : CompactNumericVerifierTask}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    (hcurrent : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount currentStart currentFinish
      (((proofTokens, certificateTokens),
        (currentTask :: restTasks, values)), none))
    (hnext : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextFinish
      (((proofTokens, certificateTokens), (restTasks, values)), some false))
    (hparse : compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = none)
    (hcurrentTaskTag : currentTask.1 = 10)
    (hstateTable :
      Nat.size stateTable <=
        compactNumericVerifierStateCoreCoordinateSizeBound
          stateWidth stateTokenCount) :
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    exists witness : CompactNumericVerifierStepFormulaWitness
        stateTable stateWidth stateTokenCount
        currentStart currentFinish nextStart nextFinish,
      forall coordinate : Fin 429,
        Nat.size (witness.environment coordinate) <=
          compactNumericVerifierParseFailureStepCoordinateSizeBound
            stateWidth stateTokenCount proofWeight certificateWeight := by
  let stateBound :=
    compactNumericVerifierStateCoreCoordinateSizeBound
      stateWidth stateTokenCount
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  let parserBound :=
    compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  let commonBound :=
    compactNumericVerifierParseFailureStepCommonCoordinateSizeBound
      stateWidth stateTokenCount proofWeight certificateWeight
  let finalBound :=
    compactNumericVerifierParseFailureStepCoordinateSizeBound
      stateWidth stateTokenCount proofWeight certificateWeight
  have hstateWidth : Nat.size stateWidth <= stateBound := by
    exact (natSize_le_of_le (Nat.le_refl stateWidth)).trans
      (width_le_stateCoreCoordinateSizeBound stateWidth stateTokenCount)
  have hstateTokenCount : Nat.size stateTokenCount <= stateBound := by
    exact (natSize_le_of_le (Nat.le_refl stateTokenCount)).trans
      (tokenCount_le_stateCoreCoordinateSizeBound stateWidth stateTokenCount)
  rcases
      exists_compactNumericVerifierParseFailureSeparatedTablesStateGraph_of_layouts_with_publicBounds
        hcurrent hnext hparse hcurrentTaskTag
        hstateTable hstateWidth hstateTokenCount with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness,
      proofTable, proofWidth, proofTokenCount,
      proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      hcurrentStartEq, hcurrentFinishEq, hnextStartEq, hnextFinishEq,
      hcurrentPackage, hnextPackage, hfailure,
      hparserBounds, _hparseEnvironmentBounds⟩
  let arguments : CompactNumericVerifierStepArguments :=
    { compactNumericVerifierStepUnusedArguments with
      taskCoordinates := taskCoordinates
      taskSizeWitness := taskSizeWitness
      proofTable := proofTable
      proofWidth := proofWidth
      proofTokenCount := proofTokenCount
      proofInputStart := proofInputStart
      proofInputFinish := proofInputFinish
      rootStart := rootStart
      rootFinish := rootFinish
      proofTag := proofTag
      proofEndpointBound := proofEndpointBound
      certificateTable := certificateTable
      certificateWidth := certificateWidth
      certificateTokenCount := certificateTokenCount
      certificateInputStart := certificateInputStart
      certificateInputFinish := certificateInputFinish
      axiomStart := axiomStart
      axiomFinish := axiomFinish
      formulaStart := formulaStart
      formulaFinish := formulaFinish
      suffixStart := suffixStart
      suffixFinish := suffixFinish
      certificateTag := certificateTag
      certificateEndpointBound := certificateEndpointBound }
  have hgraph : arguments.Graph
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness := by
    dsimp only [CompactNumericVerifierStepArguments.Graph, arguments]
    exact Or.inr (Or.inr (Or.inl (Or.inl hfailure)))
  have hstateBound_le_parserBound : stateBound <= parserBound := by
    dsimp [parserBound,
      compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound]
    omega
  have hparserBound_le_commonBound : parserBound <= commonBound := by
    dsimp [commonBound,
      compactNumericVerifierParseFailureStepCommonCoordinateSizeBound,
      parserBound, stateBound]
    omega
  have hstateBound_le_commonBound : stateBound <= commonBound :=
    hstateBound_le_parserBound.trans hparserBound_le_commonBound
  have hvalueBound :
      Nat.size currentSizeWitness.taskValueBound <= commonBound := by
    exact
      (CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
        hcurrentPackage).taskValueBound.trans hstateBound_le_commonBound
  have hnonTask :
      forall coordinate : Fin 22,
        Nat.size
          (compactNumericVerifierStepFailureNonTaskEnvironment
            arguments coordinate) <= commonBound := by
    have hparserBoundsAligned :
        CompactNumericParsePayloadFailureSeparatedTablesParserCoordinateBounds
          proofTable proofWidth proofTokenCount
          proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          parserBound := by
      simpa only [parserBound, stateBound, proofWeight, certificateWeight] using
        hparserBounds
    rcases hparserBoundsAligned with
      ⟨hproofTable, hproofWidth, hproofTokenCount,
        hproofInputStart, hproofInputFinish,
        hrootStart, hrootFinish, hproofTag, hproofEndpointBound,
        hcertificateTable, hcertificateWidth, hcertificateTokenCount,
        hcertificateInputStart, hcertificateInputFinish,
        haxiomStart, haxiomFinish, hformulaStart, hformulaFinish,
        hsuffixStart, hsuffixFinish, hcertificateTag,
        hcertificateEndpointBound⟩
    intro coordinate
    fin_cases coordinate <;>
      simp [compactNumericVerifierStepFailureNonTaskEnvironment,
        arguments] <;>
      omega
  have hfailureEnvironment :
      forall coordinate : Fin 36,
        Nat.size
          (compactNumericVerifierStepFailureTailEnvironment
            arguments coordinate) <= commonBound := by
    exact compactNumericVerifierStepFailureTailEnvironment_size_le
      arguments hfailure.2.2.1 hvalueBound hnonTask
  have htailEq :
      compactNumericVerifierStepTailEnvironment arguments =
        compactNumericVerifierStepTailEnvironment
          compactNumericVerifierStepUnusedArguments := by
    rfl
  have htailEnvironment :
      forall coordinate : Fin 348,
        Nat.size
          (compactNumericVerifierStepTailEnvironment
            arguments coordinate) <= commonBound := by
    intro coordinate
    rw [htailEq]
    have hcoordinate :=
      natSize_coordinate_le_finSum
        (compactNumericVerifierStepTailEnvironment
          compactNumericVerifierStepUnusedArguments)
        coordinate
    have hsum :
        (∑ index,
            Nat.size
              (compactNumericVerifierStepTailEnvironment
                compactNumericVerifierStepUnusedArguments index)) <=
          compactNumericVerifierStepUnusedEnvironmentConstant := by
      unfold compactNumericVerifierStepUnusedEnvironmentConstant
      unfold compactNumericVerifierStepArgumentsEnvironmentConstant
      omega
    have hunused_le_commonBound :
        compactNumericVerifierStepUnusedEnvironmentConstant <= commonBound := by
      dsimp [commonBound,
        compactNumericVerifierParseFailureStepCommonCoordinateSizeBound,
        parserBound, stateBound]
      omega
    exact hcoordinate.trans (hsum.trans hunused_le_commonBound)
  have henvironmentConstant :
      compactNumericVerifierStepArgumentsEnvironmentConstant arguments <=
        384 * commonBound := by
    exact compactNumericVerifierStepArgumentsEnvironmentConstant_le
      arguments commonBound hfailureEnvironment htailEnvironment
  rcases
      exists_compactNumericVerifierStepFormulaWitness_with_sizeBound
        arguments hstateTable hcurrentPackage hnextPackage hgraph with
    ⟨witness, hwitness⟩
  refine ⟨witness, ?_⟩
  intro coordinate
  have hbound :
      compactNumericVerifierStepArgumentsCoordinateSizeBound
          arguments stateWidth stateTokenCount <=
        compactNumericVerifierParseFailureStepCoordinateSizeBound
          stateWidth stateTokenCount proofWeight certificateWeight := by
    unfold compactNumericVerifierStepArgumentsCoordinateSizeBound
    unfold compactNumericVerifierParseFailureStepCoordinateSizeBound
    exact Nat.add_le_add_left henvironmentConstant stateBound
  exact (hwitness coordinate).trans hbound

#print axioms
  exists_compactNumericVerifierParseFailureStepFormulaWitness_with_publicBounds

end FoundationCompactNumericListedDirectVerifierParseFailureStepPublicBounds
