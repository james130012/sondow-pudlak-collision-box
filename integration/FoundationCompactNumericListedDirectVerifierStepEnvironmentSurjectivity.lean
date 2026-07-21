import integration.FoundationCompactNumericListedDirectVerifierStepCompleteness

/-!
# Surjectivity of the verifier-step formula environment

Every assignment of the 429 formula columns can be read back into the complete
parameter package used by `compactNumericVerifierParseStateGraphEnvironment`.
Consequently, forward exactness applies to an arbitrary satisfying assignment,
not only to assignments already presented in constructor form.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStepEnvironmentSurjectivity

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepExactness
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectSuccIndBaseNegationRoute
open FoundationCompactNumericListedDirectSuccIndStepAssemblyRoute
open FoundationCompactNumericListedDirectSuccIndSentenceRoute
open FoundationCompactNumericListedDirectFormulaFvSupTotalEndpoint
open FoundationCompactNumericListedDirectFixedAllClosureTotalEndpoint
open FoundationCompactNumericListedDirectGuardedInductionSentenceRoute
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness
open FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpoint
open FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness

private def compactNatListRowSlotFromEnvironment
    {n : Nat} (env : Fin n -> Nat) (offset : Nat)
    (h : offset + 5 <= n) : CompactNatListRowSlot where
  start := env ⟨offset, by omega⟩
  finish := env ⟨offset + 1, by omega⟩
  boundary := env ⟨offset + 2, by omega⟩
  count := env ⟨offset + 3, by omega⟩
  boundarySize := env ⟨offset + 4, by omega⟩

private def compactFormulaTransformTraceSlotFromEnvironment
    {n : Nat} (env : Fin n -> Nat) (offset : Nat)
    (h : offset + 4 <= n) : CompactFormulaTransformTraceSlot where
  stateBoundary := env ⟨offset, by omega⟩
  stateCount := env ⟨offset + 1, by omega⟩
  tableWidth := env ⟨offset + 2, by omega⟩
  valueBound := env ⟨offset + 3, by omega⟩

private def compactNumericVerifierStateRowCoordinatesFromEnvironment
    (env : Fin 429 -> Nat) (offset : Nat)
    (h : offset + 15 <= 429) : CompactNumericVerifierStateRowCoordinates where
  start := env ⟨offset, by omega⟩
  finish := env ⟨offset + 1, by omega⟩
  proofFinish := env ⟨offset + 2, by omega⟩
  proofCount := env ⟨offset + 3, by omega⟩
  certificateFinish := env ⟨offset + 4, by omega⟩
  certificateCount := env ⟨offset + 5, by omega⟩
  tasksFinish := env ⟨offset + 6, by omega⟩
  taskCount := env ⟨offset + 7, by omega⟩
  taskBoundary := env ⟨offset + 8, by omega⟩
  valuesFinish := env ⟨offset + 9, by omega⟩
  valueCount := env ⟨offset + 10, by omega⟩
  valueBoundary := env ⟨offset + 11, by omega⟩
  statusTag := env ⟨offset + 12, by omega⟩
  statusPayloadStart := env ⟨offset + 13, by omega⟩
  statusBool := env ⟨offset + 14, by omega⟩

private def compactNumericVerifierStateSizeWitnessFromEnvironment
    (env : Fin 429 -> Nat) (offset : Nat)
    (h : offset + 6 <= 429) : CompactNumericVerifierStateSizeWitness where
  taskBoundarySize := env ⟨offset, by omega⟩
  valueBoundarySize := env ⟨offset + 1, by omega⟩
  taskTableWidth := env ⟨offset + 2, by omega⟩
  taskValueBound := env ⟨offset + 3, by omega⟩
  valueTableWidth := env ⟨offset + 4, by omega⟩
  valueValueBound := env ⟨offset + 5, by omega⟩

private def compactNumericVerifierTaskRowCoordinatesFromEnvironment
    (env : Fin 429 -> Nat) (offset : Nat)
    (h : offset + 13 <= 429) : CompactNumericVerifierTaskRowCoordinates where
  start := env ⟨offset, by omega⟩
  finish := env ⟨offset + 1, by omega⟩
  tag := env ⟨offset + 2, by omega⟩
  gammaFinish := env ⟨offset + 3, by omega⟩
  gammaCount := env ⟨offset + 4, by omega⟩
  gammaBoundary := env ⟨offset + 5, by omega⟩
  firstFinish := env ⟨offset + 6, by omega⟩
  firstCount := env ⟨offset + 7, by omega⟩
  secondFinish := env ⟨offset + 8, by omega⟩
  secondCount := env ⟨offset + 9, by omega⟩
  witnessFinish := env ⟨offset + 10, by omega⟩
  witnessCount := env ⟨offset + 11, by omega⟩
  suffixCount := env ⟨offset + 12, by omega⟩

private def compactNumericVerifierTaskSizeWitnessFromEnvironment
    (env : Fin 429 -> Nat) (offset : Nat)
    (h : offset < 429) : CompactNumericVerifierTaskSizeWitness where
  gammaBoundarySize := env ⟨offset, h⟩

def compactNumericVerifierPAAxiomJointLeafCoordinatesFromEnvironment
    (env : Fin 259 -> Nat) :
    CompactNumericVerifierPAAxiomJointLeafCoordinates where
  endpointTable := env 184
  endpointWidth := env 185
  endpointTokenCount := env 186
  ruleTable := env 0
  ruleWidth := env 1
  ruleTokenCount := env 2
  inputStart := env 187
  inputFinish := env 188
  endpointAxiomStart := env 189
  endpointAxiomFinish := env 190
  formulaStart := env 191
  formulaFinish := env 192
  suffixStart := env 193
  suffixFinish := env 194
  proofTag := env 195
  certificateTag := env 196
  gammaStart := env 197
  gammaFinish := env 198
  gammaBoundary := env 177
  gammaCount := env 178
  gammaBoundarySize := env 199
  candidate :=
    { start := env 182
      finish := env 183
      boundary := env 200
      count := env 201
      boundarySize := env 202 }
  ruleAxiom :=
    { start := env 203
      finish := env 204
      boundary := env 180
      count := env 181
      boundarySize := env 205 }
  resultBool := env 179
  depth := env 148
  fixedEndpoint :=
    { inputBoundary := env 206
      inputCount := env 207
      inputBoundarySize := env 208
      tailStart := env 209
      tailFinish := env 210
      tailBoundary := env 211
      tailCount := env 212
      tailBoundarySize := env 213
      axiomBoundary := env 214
      axiomCount := env 215
      axiomBoundarySize := env 216
      suffixBoundary := env 217
      suffixCount := env 218
      suffixBoundarySize := env 219
      paTag := env 220 }
  symbolEndpoint :=
    { inputBoundary := env 221
      inputCount := env 222
      inputBoundarySize := env 223
      tailStart := env 224
      tailFinish := env 225
      tailBoundary := env 226
      tailCount := env 227
      tailBoundarySize := env 228
      axiomBoundary := env 229
      axiomCount := env 230
      axiomBoundarySize := env 231
      suffixBoundary := env 232
      suffixCount := env 233
      suffixBoundarySize := env 234
      paTag := env 235
      arity := env 236
      symbolCode := env 237 }
  inductionEndpoint :=
    { inputBoundary := env 238
      inputCount := env 239
      inputBoundarySize := env 240
      tailStart := env 241
      tailFinish := env 242
      tailBoundary := env 243
      tailCount := env 244
      tailBoundarySize := env 245
      axiomBoundary := env 246
      axiomCount := env 247
      axiomBoundarySize := env 248
      parser :=
        { inputBoundary := env 249
          inputCount := env 250
          inputBoundarySize := env 251
          expectedBoundary := env 252
          expectedCount := env 253
          expectedBoundarySize := env 254
          stateBoundary := env 255
          stateCount := env 256
          tableWidth := env 257
          valueBound := env 258 } }
  body := compactNatListRowSlotFromEnvironment env 3 (by omega)
  zeroWitness := compactNatListRowSlotFromEnvironment env 8 (by omega)
  openZeroWitness := compactNatListRowSlotFromEnvironment env 13 (by omega)
  openSuccessorWitness :=
    compactNatListRowSlotFromEnvironment env 18 (by omega)
  captureOne := compactNatListRowSlotFromEnvironment env 23 (by omega)
  empty := compactNatListRowSlotFromEnvironment env 28 (by omega)
  base := compactNatListRowSlotFromEnvironment env 33 (by omega)
  negatedBase := compactNatListRowSlotFromEnvironment env 38 (by omega)
  stepZero := compactNatListRowSlotFromEnvironment env 43 (by omega)
  stepSuccessor := compactNatListRowSlotFromEnvironment env 48 (by omega)
  negatedStepZero := compactNatListRowSlotFromEnvironment env 53 (by omega)
  stepDisjunction := compactNatListRowSlotFromEnvironment env 58 (by omega)
  quantifiedStep := compactNatListRowSlotFromEnvironment env 63 (by omega)
  negatedQuantifiedStep :=
    compactNatListRowSlotFromEnvironment env 68 (by omega)
  quantifiedFinal := compactNatListRowSlotFromEnvironment env 73 (by omega)
  innerDisjunction := compactNatListRowSlotFromEnvironment env 78 (by omega)
  sentence := compactNatListRowSlotFromEnvironment env 83 (by omega)
  fvarList := compactNatListRowSlotFromEnvironment env 149 (by omega)
  depthCapture := compactNatListRowSlotFromEnvironment env 154 (by omega)
  fixed := compactNatListRowSlotFromEnvironment env 159 (by omega)
  generated := compactNatListRowSlotFromEnvironment env 164 (by omega)
  route :=
    { sentence :=
        { base :=
            { baseTrace :=
                compactFormulaTransformTraceSlotFromEnvironment env 88
                  (by omega)
              negationTrace :=
                compactFormulaTransformTraceSlotFromEnvironment env 92
                  (by omega) }
          openZero :=
            { shifted :=
                compactNatListRowSlotFromEnvironment env 96 (by omega)
              substituted :=
                compactNatListRowSlotFromEnvironment env 101 (by omega)
              shiftTrace :=
                compactFormulaTransformTraceSlotFromEnvironment env 106
                  (by omega)
              substitutionTrace :=
                compactFormulaTransformTraceSlotFromEnvironment env 110
                  (by omega)
              fixitrTrace :=
                compactFormulaTransformTraceSlotFromEnvironment env 114
                  (by omega) }
          openSuccessor :=
            { shifted :=
                compactNatListRowSlotFromEnvironment env 118 (by omega)
              substituted :=
                compactNatListRowSlotFromEnvironment env 123 (by omega)
              shiftTrace :=
                compactFormulaTransformTraceSlotFromEnvironment env 128
                  (by omega)
              substitutionTrace :=
                compactFormulaTransformTraceSlotFromEnvironment env 132
                  (by omega)
              fixitrTrace :=
                compactFormulaTransformTraceSlotFromEnvironment env 136
                  (by omega) }
          step :=
            { negatedStepZeroTrace :=
                compactFormulaTransformTraceSlotFromEnvironment env 140
                  (by omega)
              negatedQuantifiedStepTrace :=
                compactFormulaTransformTraceSlotFromEnvironment env 144
                  (by omega) } }
      fvSup :=
        { trace :=
            compactFormulaTransformTraceSlotFromEnvironment env 169 (by omega) }
      closure :=
        { trace :=
            compactFormulaTransformTraceSlotFromEnvironment env 173 (by omega) } }

set_option maxRecDepth 65536 in
theorem compactNumericVerifierPAAxiomJointLeafRowsEnvironment_fromEnvironment
    (env : Fin 259 -> Nat) :
    compactNumericVerifierPAAxiomJointLeafRowsEnvironment
        (compactNumericVerifierPAAxiomJointLeafCoordinatesFromEnvironment env) =
      env := by
  funext coordinate
  fin_cases coordinate <;> rfl

private def compactNumericVerifierPAAxiomJointLeafBlock
    (env : Fin 429 -> Nat) : Fin 259 -> Nat :=
  fun coordinate => env ⟨128 + coordinate, by omega⟩

structure CompactNumericVerifierParseStateGraphParameters where
  stateTable : Nat
  stateWidth : Nat
  stateTokenCount : Nat
  currentCoordinates : CompactNumericVerifierStateRowCoordinates
  nextCoordinates : CompactNumericVerifierStateRowCoordinates
  currentSizeWitness : CompactNumericVerifierStateSizeWitness
  nextSizeWitness : CompactNumericVerifierStateSizeWitness
  arguments : CompactNumericVerifierStepArguments

def CompactNumericVerifierParseStateGraphParameters.environment
    (parameters : CompactNumericVerifierParseStateGraphParameters) :
    Fin 429 -> Nat :=
  parameters.arguments.environment
    parameters.stateTable parameters.stateWidth parameters.stateTokenCount
    parameters.currentCoordinates parameters.nextCoordinates
    parameters.currentSizeWitness parameters.nextSizeWitness

def compactNumericVerifierParseStateGraphParametersFromEnvironment
    (env : Fin 429 -> Nat) : CompactNumericVerifierParseStateGraphParameters where
  stateTable := env 0
  stateWidth := env 1
  stateTokenCount := env 2
  currentCoordinates :=
    compactNumericVerifierStateRowCoordinatesFromEnvironment env 3 (by omega)
  nextCoordinates :=
    compactNumericVerifierStateRowCoordinatesFromEnvironment env 24 (by omega)
  currentSizeWitness :=
    compactNumericVerifierStateSizeWitnessFromEnvironment env 18 (by omega)
  nextSizeWitness :=
    compactNumericVerifierStateSizeWitnessFromEnvironment env 39 (by omega)
  arguments :=
    { taskCoordinates :=
        compactNumericVerifierTaskRowCoordinatesFromEnvironment env 45 (by omega)
      taskSizeWitness :=
        compactNumericVerifierTaskSizeWitnessFromEnvironment env 58 (by omega)
      proofTable := env 59
      proofWidth := env 60
      proofTokenCount := env 61
      proofInputStart := env 62
      proofInputFinish := env 63
      rootStart := env 64
      rootFinish := env 65
      proofTag := env 66
      proofEndpointBound := env 67
      certificateTable := env 68
      certificateWidth := env 69
      certificateTokenCount := env 70
      certificateInputStart := env 71
      certificateInputFinish := env 72
      axiomStart := env 73
      axiomFinish := env 74
      formulaStart := env 75
      formulaFinish := env 76
      suffixStart := env 77
      suffixFinish := env 78
      certificateTag := env 79
      certificateEndpointBound := env 80
      rootGammaFinish := env 81
      rootGammaCount := env 82
      rootGammaBoundary := env 83
      firstFinish := env 84
      firstCount := env 85
      secondFinish := env 86
      secondCount := env 87
      witnessFinish := env 88
      witnessCount := env 89
      suffixCount := env 90
      rootGammaBoundarySize := env 91
      targetStart := env 92
      targetFinish := env 93
      targetGammaFinish := env 94
      targetGammaCount := env 95
      targetGammaBoundary := env 96
      targetBool := env 97
      targetGammaBoundarySize := env 98
      resultBool := env 99
      ruleTable := env 100
      ruleWidth := env 101
      ruleTokenCount := env 102
      ruleProofTag := env 103
      ruleCertificateTag := env 104
      ruleGammaStart := env 105
      ruleGammaFinish := env 106
      ruleGammaBoundary := env 107
      ruleGammaCount := env 108
      ruleGammaBoundarySize := env 109
      ruleFormulaStart := env 110
      ruleFormulaFinish := env 111
      ruleFormulaBoundary := env 112
      ruleFormulaCount := env 113
      ruleFormulaBoundarySize := env 114
      ruleNegatedStart := env 115
      ruleNegatedFinish := env 116
      ruleNegatedBoundary := env 117
      ruleNegatedCount := env 118
      ruleNegatedBoundarySize := env 119
      ruleStateBoundary := env 120
      ruleStateCount := env 121
      ruleEmptyStart := env 122
      ruleEmptyFinish := env 123
      ruleEmptyBoundary := env 124
      ruleEmptyBoundarySize := env 125
      ruleTableWidth := env 126
      ruleValueBound := env 127
      paCoordinates :=
        compactNumericVerifierPAAxiomJointLeafCoordinatesFromEnvironment
          (compactNumericVerifierPAAxiomJointLeafBlock env)
      firstParseCoordinates :=
        compactNumericVerifierTaskRowCoordinatesFromEnvironment env 387
          (by omega)
      secondParseCoordinates :=
        compactNumericVerifierTaskRowCoordinatesFromEnvironment env 401
          (by omega)
      combineCoordinates :=
        compactNumericVerifierTaskRowCoordinatesFromEnvironment env 415
          (by omega)
      firstParseSize :=
        compactNumericVerifierTaskSizeWitnessFromEnvironment env 400 (by omega)
      secondParseSize :=
        compactNumericVerifierTaskSizeWitnessFromEnvironment env 414 (by omega)
      combineSize :=
        compactNumericVerifierTaskSizeWitnessFromEnvironment env 428 (by omega) }

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
theorem compactNumericVerifierParseStateGraphEnvironment_fromEnvironment
    (env : Fin 429 -> Nat) :
    (compactNumericVerifierParseStateGraphParametersFromEnvironment env).environment =
      env := by
  funext coordinate
  fin_cases coordinate <;> rfl

theorem compactNumericVerifierParseStateGraphEnvironment_surjective
    (env : Fin 429 -> Nat) :
    exists parameters : CompactNumericVerifierParseStateGraphParameters,
      parameters.environment = env := by
  exact ⟨compactNumericVerifierParseStateGraphParametersFromEnvironment env,
    compactNumericVerifierParseStateGraphEnvironment_fromEnvironment env⟩

theorem CompactNumericVerifierStepArguments.Graph.currentCore
    {arguments : CompactNumericVerifierStepArguments}
    {stateTable stateWidth stateTokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    (hgraph : arguments.Graph
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness) :
    CompactNumericVerifierStateCoreGraph
      stateTable stateWidth stateTokenCount
      currentCoordinates currentSizeWitness := by
  unfold CompactNumericVerifierStepArguments.Graph at hgraph
  rcases hgraph with hhalted | hfinish | hparse | hcombine
  · exact hhalted.1
  · exact hfinish.1
  · rcases hparse with hfailure | hsuccess
    · exact hfailure.1
    · exact hsuccess.1
  · exact hcombine.1

theorem CompactNumericVerifierStepArguments.Graph.nextCore
    {arguments : CompactNumericVerifierStepArguments}
    {stateTable stateWidth stateTokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    (hgraph : arguments.Graph
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness) :
    CompactNumericVerifierStateCoreGraph
      stateTable stateWidth stateTokenCount
      nextCoordinates nextSizeWitness := by
  unfold CompactNumericVerifierStepArguments.Graph at hgraph
  rcases hgraph with hhalted | hfinish | hparse | hcombine
  · exact hhalted.2.1
  · exact hfinish.2.1
  · rcases hparse with hfailure | hsuccess
    · exact hfailure.2.1
    · exact hsuccess.2.1
  · exact hcombine.2.1

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
theorem compactNumericVerifierStepGraphDef_evalb_graph
    (env : Fin 429 -> Nat)
    (henv : compactNumericVerifierStepGraphDef.val.Evalb env) :
    let parameters :=
      compactNumericVerifierParseStateGraphParametersFromEnvironment env
    parameters.arguments.Graph
      parameters.stateTable parameters.stateWidth parameters.stateTokenCount
      parameters.currentCoordinates parameters.nextCoordinates
      parameters.currentSizeWitness parameters.nextSizeWitness := by
  dsimp only
  let parameters :=
    compactNumericVerifierParseStateGraphParametersFromEnvironment env
  have hparameters :
      compactNumericVerifierStepGraphDef.val.Evalb parameters.environment := by
    rw [compactNumericVerifierParseStateGraphEnvironment_fromEnvironment]
    exact henv
  exact
    (compactNumericVerifierStepGraphDef_spec
      parameters.stateTable parameters.stateWidth parameters.stateTokenCount
      parameters.currentCoordinates parameters.nextCoordinates
      parameters.currentSizeWitness parameters.nextSizeWitness
      parameters.arguments.taskCoordinates
      parameters.arguments.taskSizeWitness
      parameters.arguments.proofTable parameters.arguments.proofWidth
      parameters.arguments.proofTokenCount
      parameters.arguments.proofInputStart
      parameters.arguments.proofInputFinish
      parameters.arguments.rootStart parameters.arguments.rootFinish
      parameters.arguments.proofTag parameters.arguments.proofEndpointBound
      parameters.arguments.certificateTable
      parameters.arguments.certificateWidth
      parameters.arguments.certificateTokenCount
      parameters.arguments.certificateInputStart
      parameters.arguments.certificateInputFinish
      parameters.arguments.axiomStart parameters.arguments.axiomFinish
      parameters.arguments.formulaStart parameters.arguments.formulaFinish
      parameters.arguments.suffixStart parameters.arguments.suffixFinish
      parameters.arguments.certificateTag
      parameters.arguments.certificateEndpointBound
      parameters.arguments.rootGammaFinish
      parameters.arguments.rootGammaCount
      parameters.arguments.rootGammaBoundary parameters.arguments.firstFinish
      parameters.arguments.firstCount parameters.arguments.secondFinish
      parameters.arguments.secondCount parameters.arguments.witnessFinish
      parameters.arguments.witnessCount parameters.arguments.suffixCount
      parameters.arguments.rootGammaBoundarySize
      parameters.arguments.targetStart parameters.arguments.targetFinish
      parameters.arguments.targetGammaFinish
      parameters.arguments.targetGammaCount
      parameters.arguments.targetGammaBoundary parameters.arguments.targetBool
      parameters.arguments.targetGammaBoundarySize
      parameters.arguments.resultBool parameters.arguments.ruleTable
      parameters.arguments.ruleWidth parameters.arguments.ruleTokenCount
      parameters.arguments.ruleProofTag
      parameters.arguments.ruleCertificateTag
      parameters.arguments.ruleGammaStart parameters.arguments.ruleGammaFinish
      parameters.arguments.ruleGammaBoundary
      parameters.arguments.ruleGammaCount
      parameters.arguments.ruleGammaBoundarySize
      parameters.arguments.ruleFormulaStart
      parameters.arguments.ruleFormulaFinish
      parameters.arguments.ruleFormulaBoundary
      parameters.arguments.ruleFormulaCount
      parameters.arguments.ruleFormulaBoundarySize
      parameters.arguments.ruleNegatedStart
      parameters.arguments.ruleNegatedFinish
      parameters.arguments.ruleNegatedBoundary
      parameters.arguments.ruleNegatedCount
      parameters.arguments.ruleNegatedBoundarySize
      parameters.arguments.ruleStateBoundary parameters.arguments.ruleStateCount
      parameters.arguments.ruleEmptyStart parameters.arguments.ruleEmptyFinish
      parameters.arguments.ruleEmptyBoundary
      parameters.arguments.ruleEmptyBoundarySize
      parameters.arguments.ruleTableWidth parameters.arguments.ruleValueBound
      parameters.arguments.paCoordinates
      parameters.arguments.firstParseCoordinates
      parameters.arguments.secondParseCoordinates
      parameters.arguments.combineCoordinates
      parameters.arguments.firstParseSize parameters.arguments.secondParseSize
      parameters.arguments.combineSize).mp hparameters

def compactNumericVerifierStepCurrentCoordinates
    (env : Fin 429 -> Nat) : CompactNumericVerifierStateRowCoordinates :=
  (compactNumericVerifierParseStateGraphParametersFromEnvironment env).currentCoordinates

def compactNumericVerifierStepNextCoordinates
    (env : Fin 429 -> Nat) : CompactNumericVerifierStateRowCoordinates :=
  (compactNumericVerifierParseStateGraphParametersFromEnvironment env).nextCoordinates

def compactNumericVerifierStepCurrentSizeWitness
    (env : Fin 429 -> Nat) : CompactNumericVerifierStateSizeWitness :=
  (compactNumericVerifierParseStateGraphParametersFromEnvironment env).currentSizeWitness

def compactNumericVerifierStepNextSizeWitness
    (env : Fin 429 -> Nat) : CompactNumericVerifierStateSizeWitness :=
  (compactNumericVerifierParseStateGraphParametersFromEnvironment env).nextSizeWitness

theorem compactNumericVerifierStepGraphDef_evalb_currentCore
    (env : Fin 429 -> Nat)
    (henv : compactNumericVerifierStepGraphDef.val.Evalb env) :
    CompactNumericVerifierStateCoreGraph
      (env 0) (env 1) (env 2)
      (compactNumericVerifierStepCurrentCoordinates env)
      (compactNumericVerifierStepCurrentSizeWitness env) := by
  have hgraph := compactNumericVerifierStepGraphDef_evalb_graph env henv
  have hcore :=
    CompactNumericVerifierStepArguments.Graph.currentCore hgraph
  simpa [compactNumericVerifierStepCurrentCoordinates,
    compactNumericVerifierStepCurrentSizeWitness,
    compactNumericVerifierParseStateGraphParametersFromEnvironment] using hcore

theorem compactNumericVerifierStepGraphDef_evalb_nextCore
    (env : Fin 429 -> Nat)
    (henv : compactNumericVerifierStepGraphDef.val.Evalb env) :
    CompactNumericVerifierStateCoreGraph
      (env 0) (env 1) (env 2)
      (compactNumericVerifierStepNextCoordinates env)
      (compactNumericVerifierStepNextSizeWitness env) := by
  have hgraph := compactNumericVerifierStepGraphDef_evalb_graph env henv
  have hcore :=
    CompactNumericVerifierStepArguments.Graph.nextCore hgraph
  simpa [compactNumericVerifierStepNextCoordinates,
    compactNumericVerifierStepNextSizeWitness,
    compactNumericVerifierParseStateGraphParametersFromEnvironment] using hcore

@[simp] theorem compactNumericVerifierStepCurrentCoordinates_fields
    (env : Fin 429 -> Nat) :
    let coordinates := compactNumericVerifierStepCurrentCoordinates env
    coordinates.start = env 3 ∧ coordinates.finish = env 4 ∧
    coordinates.proofFinish = env 5 ∧ coordinates.proofCount = env 6 ∧
    coordinates.certificateFinish = env 7 ∧
    coordinates.certificateCount = env 8 ∧
    coordinates.tasksFinish = env 9 ∧ coordinates.taskCount = env 10 ∧
    coordinates.taskBoundary = env 11 ∧
    coordinates.valuesFinish = env 12 ∧ coordinates.valueCount = env 13 ∧
    coordinates.valueBoundary = env 14 ∧ coordinates.statusTag = env 15 ∧
    coordinates.statusPayloadStart = env 16 ∧ coordinates.statusBool = env 17 := by
  simp [compactNumericVerifierStepCurrentCoordinates,
    compactNumericVerifierParseStateGraphParametersFromEnvironment,
    compactNumericVerifierStateRowCoordinatesFromEnvironment]

@[simp] theorem compactNumericVerifierStepNextCoordinates_fields
    (env : Fin 429 -> Nat) :
    let coordinates := compactNumericVerifierStepNextCoordinates env
    coordinates.start = env 24 ∧ coordinates.finish = env 25 ∧
    coordinates.proofFinish = env 26 ∧ coordinates.proofCount = env 27 ∧
    coordinates.certificateFinish = env 28 ∧
    coordinates.certificateCount = env 29 ∧
    coordinates.tasksFinish = env 30 ∧ coordinates.taskCount = env 31 ∧
    coordinates.taskBoundary = env 32 ∧
    coordinates.valuesFinish = env 33 ∧ coordinates.valueCount = env 34 ∧
    coordinates.valueBoundary = env 35 ∧ coordinates.statusTag = env 36 ∧
    coordinates.statusPayloadStart = env 37 ∧ coordinates.statusBool = env 38 := by
  simp [compactNumericVerifierStepNextCoordinates,
    compactNumericVerifierParseStateGraphParametersFromEnvironment,
    compactNumericVerifierStateRowCoordinatesFromEnvironment]

@[simp] theorem compactNumericVerifierStepCurrentSizeWitness_fields
    (env : Fin 429 -> Nat) :
    let witness := compactNumericVerifierStepCurrentSizeWitness env
    witness.taskBoundarySize = env 18 ∧ witness.valueBoundarySize = env 19 ∧
    witness.taskTableWidth = env 20 ∧ witness.taskValueBound = env 21 ∧
    witness.valueTableWidth = env 22 ∧ witness.valueValueBound = env 23 := by
  simp [compactNumericVerifierStepCurrentSizeWitness,
    compactNumericVerifierParseStateGraphParametersFromEnvironment,
    compactNumericVerifierStateSizeWitnessFromEnvironment]

@[simp] theorem compactNumericVerifierStepNextSizeWitness_fields
    (env : Fin 429 -> Nat) :
    let witness := compactNumericVerifierStepNextSizeWitness env
    witness.taskBoundarySize = env 39 ∧ witness.valueBoundarySize = env 40 ∧
    witness.taskTableWidth = env 41 ∧ witness.taskValueBound = env 42 ∧
    witness.valueTableWidth = env 43 ∧ witness.valueValueBound = env 44 := by
  simp [compactNumericVerifierStepNextSizeWitness,
    compactNumericVerifierParseStateGraphParametersFromEnvironment,
    compactNumericVerifierStateSizeWitnessFromEnvironment]

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
theorem compactNumericVerifierStepGraphDef_evalb_realizeExactStep
    (env : Fin 429 -> Nat)
    (henv : compactNumericVerifierStepGraphDef.val.Evalb env) :
    exists currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
          (env 0) (env 1) (env 2) (env 3) (env 4) currentState /\
        CompactNumericVerifierStateDirectLayout
          (env 0) (env 1) (env 2) (env 24) (env 25) nextState /\
        nextState = compactNumericVerifierStep currentState := by
  let parameters :=
    compactNumericVerifierParseStateGraphParametersFromEnvironment env
  have hparameters :
      compactNumericVerifierStepGraphDef.val.Evalb parameters.environment := by
    rw [compactNumericVerifierParseStateGraphEnvironment_fromEnvironment]
    exact henv
  have hgraph : parameters.arguments.Graph
      parameters.stateTable parameters.stateWidth parameters.stateTokenCount
      parameters.currentCoordinates parameters.nextCoordinates
      parameters.currentSizeWitness parameters.nextSizeWitness :=
    (compactNumericVerifierStepGraphDef_spec
      parameters.stateTable parameters.stateWidth parameters.stateTokenCount
      parameters.currentCoordinates parameters.nextCoordinates
      parameters.currentSizeWitness parameters.nextSizeWitness
      parameters.arguments.taskCoordinates
      parameters.arguments.taskSizeWitness
      parameters.arguments.proofTable parameters.arguments.proofWidth
      parameters.arguments.proofTokenCount
      parameters.arguments.proofInputStart
      parameters.arguments.proofInputFinish
      parameters.arguments.rootStart parameters.arguments.rootFinish
      parameters.arguments.proofTag parameters.arguments.proofEndpointBound
      parameters.arguments.certificateTable
      parameters.arguments.certificateWidth
      parameters.arguments.certificateTokenCount
      parameters.arguments.certificateInputStart
      parameters.arguments.certificateInputFinish
      parameters.arguments.axiomStart parameters.arguments.axiomFinish
      parameters.arguments.formulaStart parameters.arguments.formulaFinish
      parameters.arguments.suffixStart parameters.arguments.suffixFinish
      parameters.arguments.certificateTag
      parameters.arguments.certificateEndpointBound
      parameters.arguments.rootGammaFinish
      parameters.arguments.rootGammaCount
      parameters.arguments.rootGammaBoundary parameters.arguments.firstFinish
      parameters.arguments.firstCount parameters.arguments.secondFinish
      parameters.arguments.secondCount parameters.arguments.witnessFinish
      parameters.arguments.witnessCount parameters.arguments.suffixCount
      parameters.arguments.rootGammaBoundarySize
      parameters.arguments.targetStart parameters.arguments.targetFinish
      parameters.arguments.targetGammaFinish
      parameters.arguments.targetGammaCount
      parameters.arguments.targetGammaBoundary parameters.arguments.targetBool
      parameters.arguments.targetGammaBoundarySize
      parameters.arguments.resultBool parameters.arguments.ruleTable
      parameters.arguments.ruleWidth parameters.arguments.ruleTokenCount
      parameters.arguments.ruleProofTag
      parameters.arguments.ruleCertificateTag
      parameters.arguments.ruleGammaStart parameters.arguments.ruleGammaFinish
      parameters.arguments.ruleGammaBoundary
      parameters.arguments.ruleGammaCount
      parameters.arguments.ruleGammaBoundarySize
      parameters.arguments.ruleFormulaStart
      parameters.arguments.ruleFormulaFinish
      parameters.arguments.ruleFormulaBoundary
      parameters.arguments.ruleFormulaCount
      parameters.arguments.ruleFormulaBoundarySize
      parameters.arguments.ruleNegatedStart
      parameters.arguments.ruleNegatedFinish
      parameters.arguments.ruleNegatedBoundary
      parameters.arguments.ruleNegatedCount
      parameters.arguments.ruleNegatedBoundarySize
      parameters.arguments.ruleStateBoundary parameters.arguments.ruleStateCount
      parameters.arguments.ruleEmptyStart parameters.arguments.ruleEmptyFinish
      parameters.arguments.ruleEmptyBoundary
      parameters.arguments.ruleEmptyBoundarySize
      parameters.arguments.ruleTableWidth parameters.arguments.ruleValueBound
      parameters.arguments.paCoordinates
      parameters.arguments.firstParseCoordinates
      parameters.arguments.secondParseCoordinates
      parameters.arguments.combineCoordinates
      parameters.arguments.firstParseSize parameters.arguments.secondParseSize
      parameters.arguments.combineSize).mp hparameters
  rcases CompactNumericVerifierStepGraph.realizeExactStep hgraph with
    ⟨currentState, nextState, hcurrent, hnext, hstep⟩
  exact ⟨currentState, nextState, hcurrent, hnext, hstep⟩

#print axioms compactNumericVerifierPAAxiomJointLeafRowsEnvironment_fromEnvironment
#print axioms compactNumericVerifierParseStateGraphEnvironment_fromEnvironment
#print axioms compactNumericVerifierParseStateGraphEnvironment_surjective
#print axioms CompactNumericVerifierStepArguments.Graph.currentCore
#print axioms CompactNumericVerifierStepArguments.Graph.nextCore
#print axioms compactNumericVerifierStepGraphDef_evalb_graph
#print axioms compactNumericVerifierStepGraphDef_evalb_currentCore
#print axioms compactNumericVerifierStepGraphDef_evalb_nextCore
#print axioms compactNumericVerifierStepGraphDef_evalb_realizeExactStep

end FoundationCompactNumericListedDirectVerifierStepEnvironmentSurjectivity
