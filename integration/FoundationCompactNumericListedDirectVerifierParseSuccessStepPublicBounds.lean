import integration.FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
import integration.FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierLeafOutputPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafPublicBounds

/-!
# Explicit public coordinate bound for successful parse steps

The 384 non-state coordinates are split into their actual parser, parsed-root,
leaf-output, closed-rule, PA, and non-leaf schedule blocks.  Once each block is
bounded by one public budget `B`, the complete 429-column witness is bounded by
the explicit expression `stateBound + 384 * B`.  No witness-dependent finite
sum remains in the public statement.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectInductionPAAxiomRuleCheck
open FoundationCompactNumericListedDirectGuardedInductionSentenceRoute
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness
open FoundationCompactNumericListedDirectVerifierParseStateCompleteness
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateCoordinates
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds

def compactNumericVerifierParseSuccessStepCoordinateSizeBound
    (stateWidth stateTokenCount blockBound : Nat) : Nat :=
  compactNumericVerifierStateCoreCoordinateSizeBound
      stateWidth stateTokenCount +
    384 * blockBound

theorem blockBound_le_compactNumericVerifierParseSuccessStepCoordinateSizeBound
    (stateWidth stateTokenCount blockBound : Nat) :
    blockBound <= compactNumericVerifierParseSuccessStepCoordinateSizeBound
      stateWidth stateTokenCount blockBound := by
  unfold compactNumericVerifierParseSuccessStepCoordinateSizeBound
  omega

structure CompactNumericVerifierParseSuccessArgumentBlockBounds
    (arguments : CompactNumericVerifierStepArguments) (bound : Nat) : Prop where
  parser :
    CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
      arguments.proofTable arguments.proofWidth arguments.proofTokenCount
      arguments.proofInputStart arguments.proofInputFinish
      arguments.rootStart arguments.rootFinish arguments.proofTag
      arguments.proofEndpointBound
      arguments.certificateTable arguments.certificateWidth
      arguments.certificateTokenCount arguments.certificateInputStart
      arguments.certificateInputFinish
      arguments.axiomStart arguments.axiomFinish
      arguments.formulaStart arguments.formulaFinish
      arguments.suffixStart arguments.suffixFinish
      arguments.certificateTag arguments.certificateEndpointBound bound
  parsedRoot : CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
    arguments.rootGammaFinish arguments.rootGammaCount
    arguments.rootGammaBoundary arguments.firstFinish arguments.firstCount
    arguments.secondFinish arguments.secondCount arguments.witnessFinish
    arguments.witnessCount arguments.suffixCount
    arguments.rootGammaBoundarySize bound
  leafOutput : forall coordinate : Fin 8,
    Nat.size
      (compactNumericVerifierParseLeafOutputEnvironment
        arguments.targetStart arguments.targetFinish
        arguments.targetGammaFinish arguments.targetGammaCount
        arguments.targetGammaBoundary arguments.targetBool
        arguments.targetGammaBoundarySize arguments.resultBool coordinate) <= bound
  closedExtra : forall coordinate : Fin 28,
    Nat.size
      (compactNumericVerifierParseClosedExtraEnvironment
        arguments.ruleTable arguments.ruleWidth arguments.ruleTokenCount
        arguments.ruleProofTag arguments.ruleCertificateTag
        arguments.ruleGammaStart arguments.ruleGammaFinish
        arguments.ruleGammaBoundary arguments.ruleGammaCount
        arguments.ruleGammaBoundarySize arguments.ruleFormulaStart
        arguments.ruleFormulaFinish arguments.ruleFormulaBoundary
        arguments.ruleFormulaCount arguments.ruleFormulaBoundarySize
        arguments.ruleNegatedStart arguments.ruleNegatedFinish
        arguments.ruleNegatedBoundary arguments.ruleNegatedCount
        arguments.ruleNegatedBoundarySize arguments.ruleStateBoundary
        arguments.ruleStateCount arguments.ruleEmptyStart
        arguments.ruleEmptyFinish arguments.ruleEmptyBoundary
        arguments.ruleEmptyBoundarySize arguments.ruleTableWidth
        arguments.ruleValueBound coordinate) <= bound
  pa : forall coordinate : Fin 259,
    Nat.size
      (compactNumericVerifierPAAxiomJointLeafRowsEnvironment
        arguments.paCoordinates coordinate) <= bound
  nonLeaf : forall coordinate : Fin 42,
    Nat.size
      (compactNumericVerifierParseNonLeafEnvironment
        arguments.firstParseCoordinates arguments.secondParseCoordinates
        arguments.combineCoordinates arguments.firstParseSize
        arguments.secondParseSize arguments.combineSize coordinate) <= bound

/-- The four parser coordinates that control actual finite iterations in a
successful parse row.  Packed parser tables and endpoint bounds are omitted:
they are existential values whose binary sizes, rather than numeric values,
control the bounded formula compiler. -/
structure CompactNumericVerifierParseSuccessParserControlBounds
    (environment : Fin 429 -> Nat) (bound : Nat) : Prop where
  proofWidth_le : environment 60 <= bound
  proofTokenCount_le : environment 61 <= bound
  certificateWidth_le : environment 69 <= bound
  certificateTokenCount_le : environment 70 <= bound

theorem CompactNumericVerifierParseSuccessParserControlBounds.mono
    {environment : Fin 429 -> Nat} {left right : Nat}
    (hbounds : CompactNumericVerifierParseSuccessParserControlBounds
      environment left)
    (hle : left <= right) :
    CompactNumericVerifierParseSuccessParserControlBounds environment right :=
  { proofWidth_le := hbounds.proofWidth_le.trans hle
    proofTokenCount_le := hbounds.proofTokenCount_le.trans hle
    certificateWidth_le := hbounds.certificateWidth_le.trans hle
    certificateTokenCount_le := hbounds.certificateTokenCount_le.trans hle }

set_option maxRecDepth 65536 in
theorem compactNumericVerifierParseSuccessParserControlBounds_of_blocks
    {arguments : CompactNumericVerifierStepArguments} {bound : Nat}
    (hbounds : CompactNumericVerifierParseSuccessArgumentBlockBounds
      arguments bound)
    (stateTable stateWidth stateTokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness) :
    CompactNumericVerifierParseSuccessParserControlBounds
      (arguments.environment stateTable stateWidth stateTokenCount
        currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness)
      bound := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change arguments.proofWidth <= bound
    exact hbounds.parser.proofWidth_value
  · change arguments.proofTokenCount <= bound
    exact hbounds.parser.proofTokenCount_value
  · change arguments.certificateWidth <= bound
    exact hbounds.parser.certificateWidth_value
  · change arguments.certificateTokenCount <= bound
    exact hbounds.parser.certificateTokenCount_value

theorem compactNumericVerifierStepFailureNonTaskEnvironment_size_le_of_parser
    {arguments : CompactNumericVerifierStepArguments} {bound : Nat}
    (hparser :
      CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
        arguments.proofTable arguments.proofWidth arguments.proofTokenCount
        arguments.proofInputStart arguments.proofInputFinish
        arguments.rootStart arguments.rootFinish arguments.proofTag
        arguments.proofEndpointBound
        arguments.certificateTable arguments.certificateWidth
        arguments.certificateTokenCount arguments.certificateInputStart
        arguments.certificateInputFinish
        arguments.axiomStart arguments.axiomFinish
        arguments.formulaStart arguments.formulaFinish
        arguments.suffixStart arguments.suffixFinish
        arguments.certificateTag arguments.certificateEndpointBound bound)
    (coordinate : Fin 22) :
    Nat.size
        (compactNumericVerifierStepFailureNonTaskEnvironment
          arguments coordinate) <= bound := by
  rcases hparser with
    ⟨hproofTable, _hproofWidthValue, hproofWidth,
      _hproofTokenCountValue, hproofTokenCount,
      hproofInputStart, hproofInputFinish, hrootStart, hrootFinish,
      hproofTag, hproofEndpointBound,
      hcertificateTable, _hcertificateWidthValue, hcertificateWidth,
      _hcertificateTokenCountValue, hcertificateTokenCount,
      hcertificateInputStart, hcertificateInputFinish,
      haxiomStart, haxiomFinish, hformulaStart, hformulaFinish,
      hsuffixStart, hsuffixFinish, hcertificateTag,
      hcertificateEndpointBound⟩
  fin_cases coordinate <;>
    simp [compactNumericVerifierStepFailureNonTaskEnvironment] <;>
    assumption

theorem compactNumericVerifierParseSuccessParsedEnvironment_size_le
    {arguments : CompactNumericVerifierStepArguments} {bound : Nat}
    (hbounds : CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
      arguments.rootGammaFinish arguments.rootGammaCount
      arguments.rootGammaBoundary arguments.firstFinish arguments.firstCount
      arguments.secondFinish arguments.secondCount arguments.witnessFinish
      arguments.witnessCount arguments.suffixCount
      arguments.rootGammaBoundarySize bound)
    (coordinate : Fin 11) :
    Nat.size
        (compactNumericVerifierParseSuccessParsedEnvironment
          arguments.rootGammaFinish arguments.rootGammaCount
          arguments.rootGammaBoundary arguments.firstFinish arguments.firstCount
          arguments.secondFinish arguments.secondCount arguments.witnessFinish
          arguments.witnessCount arguments.suffixCount
          arguments.rootGammaBoundarySize coordinate) <= bound := by
  rcases hbounds with
    ⟨hgammaFinish, hgammaCount, hgammaBoundary,
      hfirstFinish, hfirstCount, hsecondFinish, hsecondCount,
      hwitnessFinish, hwitnessCount, hsuffixCount,
      hgammaBoundarySize⟩
  fin_cases coordinate <;>
    simp [compactNumericVerifierParseSuccessParsedEnvironment] <;>
    assumption

theorem compactNumericVerifierUnusedLeafOutputEnvironment_size_le
    (bound : Nat) (coordinate : Fin 8) :
    Nat.size
        (compactNumericVerifierParseLeafOutputEnvironment
          0 0 0 0 0 0 0 0 coordinate) <= bound := by
  fin_cases coordinate <;>
    simp [compactNumericVerifierParseLeafOutputEnvironment]

theorem compactNumericVerifierUnusedClosedExtraEnvironment_size_le
    (bound : Nat) (coordinate : Fin 28) :
    Nat.size
        (compactNumericVerifierParseClosedExtraEnvironment
          0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
          coordinate) <= bound := by
  fin_cases coordinate <;>
    simp [compactNumericVerifierParseClosedExtraEnvironment]

theorem compactNumericVerifierUnusedTaskScheduleEnvironment_size_le
    (bound : Nat) (coordinate : Fin 14) :
    Nat.size
        (compactNumericVerifierTaskScheduleEnvironment
          compactNumericVerifierParseUnusedTaskCoordinates
          compactNumericVerifierParseUnusedTaskSize coordinate) <= bound := by
  fin_cases coordinate <;>
    simp [compactNumericVerifierTaskScheduleEnvironment,
      compactNumericVerifierParseUnusedTaskCoordinates,
      compactNumericVerifierParseUnusedTaskSize]

theorem compactNumericVerifierUnusedNonLeafEnvironment_size_le
    (bound : Nat) (coordinate : Fin 42) :
    Nat.size
        (compactNumericVerifierParseNonLeafEnvironment
          compactNumericVerifierParseUnusedTaskCoordinates
          compactNumericVerifierParseUnusedTaskCoordinates
          compactNumericVerifierParseUnusedTaskCoordinates
          compactNumericVerifierParseUnusedTaskSize
          compactNumericVerifierParseUnusedTaskSize
          compactNumericVerifierParseUnusedTaskSize coordinate) <= bound := by
  unfold compactNumericVerifierParseNonLeafEnvironment
  apply natSize_vecAppend_le rfl
  · exact compactNumericVerifierUnusedTaskScheduleEnvironment_size_le bound
  · apply natSize_vecAppend_le rfl
    · exact compactNumericVerifierUnusedTaskScheduleEnvironment_size_le bound
    · exact compactNumericVerifierUnusedTaskScheduleEnvironment_size_le bound

theorem compactNumericVerifierStepTailEnvironment_size_le_of_blocks
    {arguments : CompactNumericVerifierStepArguments} {bound : Nat}
    (hbounds : CompactNumericVerifierParseSuccessArgumentBlockBounds
      arguments bound)
    (coordinate : Fin 348) :
    Nat.size (compactNumericVerifierStepTailEnvironment arguments coordinate) <=
      bound := by
  unfold compactNumericVerifierStepTailEnvironment
  apply natSize_vecAppend_le rfl
  · exact compactNumericVerifierParseSuccessParsedEnvironment_size_le
      hbounds.parsedRoot
  · apply natSize_vecAppend_le rfl
    · exact hbounds.leafOutput
    · apply natSize_vecAppend_le rfl
      · exact hbounds.closedExtra
      · apply natSize_vecAppend_le rfl
        · exact hbounds.pa
        · exact hbounds.nonLeaf

theorem compactNumericVerifierStepArgumentsEnvironmentConstant_le_of_blocks
    {arguments : CompactNumericVerifierStepArguments}
    {tokenTable width tokenCount taskBoundary valueBound bound : Nat}
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
      arguments.taskCoordinates arguments.taskSizeWitness)
    (hvalueBound : Nat.size valueBound <= bound)
    (hbounds : CompactNumericVerifierParseSuccessArgumentBlockBounds
      arguments bound) :
    compactNumericVerifierStepArgumentsEnvironmentConstant arguments <=
      384 * bound := by
  apply compactNumericVerifierStepArgumentsEnvironmentConstant_le arguments bound
  · apply compactNumericVerifierStepFailureTailEnvironment_size_le
      arguments hhead hvalueBound
    exact compactNumericVerifierStepFailureNonTaskEnvironment_size_le_of_parser
      hbounds.parser
  · exact compactNumericVerifierStepTailEnvironment_size_le_of_blocks hbounds

theorem exists_compactNumericVerifierParseSuccessStepFormulaWitness_with_publicSizeBound
    (arguments : CompactNumericVerifierStepArguments)
    {stateTable stateWidth stateTokenCount taskBoundary valueBound blockBound
      currentStart currentFinish nextStart nextFinish : Nat}
    {currentState nextState : CompactNumericVerifierState}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    (htable : Nat.size stateTable <=
      compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount)
    (hcurrentPackage : CompactNumericVerifierStateCanonicalCorePackage
      stateTable stateWidth stateTokenCount currentStart currentFinish
      currentState currentCoordinates currentSizeWitness)
    (hnextPackage : CompactNumericVerifierStateCanonicalCorePackage
      stateTable stateWidth stateTokenCount nextStart nextFinish
      nextState nextCoordinates nextSizeWitness)
    (hgraph : arguments.Graph
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness)
    (hhead : CompactNumericVerifierTaskBoundedHead
      stateTable stateWidth stateTokenCount taskBoundary valueBound
      arguments.taskCoordinates arguments.taskSizeWitness)
    (hvalueBound : Nat.size valueBound <= blockBound)
    (hblocks : CompactNumericVerifierParseSuccessArgumentBlockBounds
      arguments blockBound) :
    exists witness : CompactNumericVerifierStepFormulaWitness
        stateTable stateWidth stateTokenCount
        currentStart currentFinish nextStart nextFinish,
      (forall coordinate : Fin 429,
          Nat.size (witness.environment coordinate) <=
            compactNumericVerifierParseSuccessStepCoordinateSizeBound
              stateWidth stateTokenCount blockBound) /\
        CompactNumericVerifierParseSuccessParserControlBounds
          witness.environment blockBound := by
  have hconstant :
      compactNumericVerifierStepArgumentsEnvironmentConstant arguments <=
        384 * blockBound :=
    compactNumericVerifierStepArgumentsEnvironmentConstant_le_of_blocks
      hhead hvalueBound hblocks
  let witness := arguments.toFormulaWitness
    hcurrentPackage.1 hcurrentPackage.2.1
    hnextPackage.1 hnextPackage.2.1 hgraph
  refine ⟨witness, ?_, ?_⟩
  · intro coordinate
    change Nat.size (arguments.environment
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness coordinate) <=
        compactNumericVerifierParseSuccessStepCoordinateSizeBound
          stateWidth stateTokenCount blockBound
    have hcoordinate := compactNumericVerifierStepEnvironment_size_le
      arguments htable
        (CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
          hcurrentPackage)
        (CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
          hnextPackage)
        coordinate
    exact hcoordinate.trans (by
      unfold compactNumericVerifierStepArgumentsCoordinateSizeBound
      unfold compactNumericVerifierParseSuccessStepCoordinateSizeBound
      omega)
  · change CompactNumericVerifierParseSuccessParserControlBounds
      (arguments.environment stateTable stateWidth stateTokenCount
        currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness)
      blockBound
    exact compactNumericVerifierParseSuccessParserControlBounds_of_blocks
      hblocks stateTable stateWidth stateTokenCount currentCoordinates
        nextCoordinates currentSizeWitness nextSizeWitness

#print axioms
  compactNumericVerifierStepArgumentsEnvironmentConstant_le_of_blocks
#print axioms
  blockBound_le_compactNumericVerifierParseSuccessStepCoordinateSizeBound
#print axioms
  compactNumericVerifierParseSuccessParserControlBounds_of_blocks
#print axioms
  exists_compactNumericVerifierParseSuccessStepFormulaWitness_with_publicSizeBound

end FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
