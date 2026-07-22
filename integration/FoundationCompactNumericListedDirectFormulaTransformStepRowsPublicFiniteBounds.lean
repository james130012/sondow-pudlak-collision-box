import integration.FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicBounds

/-!
# Public-finite structural resources for one formula-transform step

The semantic branch is still recovered from the checked graph, but every
branch is charged to one of six graph-independent candidates. Their finite sum
is therefore a common public envelope for the complete step certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserDonePublicBounds
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxInvalidFormula
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsPublicBounds

structure CompactFormulaTransformStepRowsPublicFiniteBranchPayloads where
  quietDonePayload : Nat
  quietEmptyPayload : Nat
  quietRepeatPayload : Nat
  quietInvalidPayload : Nat
  termPayload : Nat
  formulaPayload : Nat

noncomputable def compactFormulaTransformStepRowsPublicFiniteBranchPayloads
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    CompactFormulaTransformStepRowsPublicFiniteBranchPayloads := by
  let doneFormula := compactUnifiedParserDoneClosedFormula tokenTable width
    tokenCount current.parser next.parser stepWitness.done
  let emptyFormula := compactUnifiedParserEmptyClosedFormula tokenTable width
    tokenCount current.parser next.parser stepWitness.empty
  let repeatFormula := compactUnifiedParserSyntaxRepeatClosedFormula tokenTable
    width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.slot1 stepWitness.repeat
  let invalidFormula := compactUnifiedParserSyntaxInvalidClosedFormula
    tokenTable width tokenCount current.parser next.parser stepWitness.invalid
  let quietParserFormula := doneFormula ⋎
    (emptyFormula ⋎ (repeatFormula ⋎ invalidFormula))
  let sameFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable width
    tokenCount current.outputBoundary current.outputCount next.outputBoundary
    next.outputCount
  let quietFormula := quietParserFormula ⋏ sameFormula
  let termParserFormula := compactUnifiedParserSyntaxTermClosedFormula tokenTable
    width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.term
  let termOutputFormula := compactFormulaTransformTermOutputRowsClosedFormula
    tokenTable width tokenCount current next mode stepWitness.slot0
    stepWitness.term.tag stepWitness.term.argument consumedCount witnessStart
    witnessFinish witnessCount
  let termFormula := termParserFormula ⋏ termOutputFormula
  let formulaParserFormula := compactUnifiedParserSyntaxFormulaClosedFormula
    tokenTable width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.formula
  let formulaOutputFormula :=
    compactFormulaTransformFormulaOutputRowsClosedFormula tokenTable width
      tokenCount current next mode stepWitness.formula.tag consumedCount
      mappedHead
  let formulaFormula := formulaParserFormula ⋏ formulaOutputFormula
  let sameResource := compactAdditiveNatListSameRowsPublicFinitePayloadEnvelope
    tokenTable width tokenCount current.outputBoundary current.outputCount
    next.outputBoundary next.outputCount
  let doneParserResource := fourWayPath0PayloadEnvelope doneFormula emptyFormula
    repeatFormula invalidFormula
    (compactUnifiedParserDonePublicFinitePayloadEnvelope tokenTable width
      tokenCount current.parser next.parser stepWitness.done)
  let emptyParserResource := fourWayPath1PayloadEnvelope doneFormula emptyFormula
    repeatFormula invalidFormula
    (compactUnifiedParserEmptyPublicFinitePayloadEnvelope tokenTable width
      tokenCount current.parser next.parser stepWitness.empty)
  let repeatParserResource := fourWayPath2PayloadEnvelope doneFormula emptyFormula
    repeatFormula invalidFormula
    (compactUnifiedParserSyntaxRepeatPublicFinitePayloadEnvelope tokenTable width
      tokenCount current.parser next.parser stepWitness.slot0 stepWitness.slot1
      stepWitness.repeat)
  let invalidParserResource := fourWayPath3PayloadEnvelope doneFormula emptyFormula
    repeatFormula invalidFormula
    (compactUnifiedParserSyntaxInvalidPublicFinitePayloadEnvelope tokenTable width
      tokenCount current.parser next.parser stepWitness.invalid)
  let quietDoneResource := transparentHybridConjunctionPayloadEnvelope
    stepRowsZeroValuation quietParserFormula sameFormula doneParserResource
    sameResource
  let quietEmptyResource := transparentHybridConjunctionPayloadEnvelope
    stepRowsZeroValuation quietParserFormula sameFormula emptyParserResource
    sameResource
  let quietRepeatResource := transparentHybridConjunctionPayloadEnvelope
    stepRowsZeroValuation quietParserFormula sameFormula repeatParserResource
    sameResource
  let quietInvalidResource := transparentHybridConjunctionPayloadEnvelope
    stepRowsZeroValuation quietParserFormula sameFormula invalidParserResource
    sameResource
  let termResource := transparentHybridConjunctionPayloadEnvelope
    stepRowsZeroValuation termParserFormula termOutputFormula
    (compactUnifiedParserSyntaxTermPublicFinitePayloadEnvelope tokenTable width
      tokenCount current.parser next.parser stepWitness.slot0 stepWitness.term)
    (compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope tokenTable
      width tokenCount current next mode stepWitness.slot0 stepWitness.term.tag
      stepWitness.term.argument consumedCount witnessStart witnessFinish
      witnessCount)
  let formulaResource := transparentHybridConjunctionPayloadEnvelope
    stepRowsZeroValuation formulaParserFormula formulaOutputFormula
    (compactUnifiedParserSyntaxFormulaPublicFinitePayloadEnvelope tokenTable width
      tokenCount current.parser next.parser stepWitness.slot0 stepWitness.formula)
    (compactFormulaTransformFormulaOutputRowsPublicFinitePayloadEnvelope tokenTable
      width tokenCount current next mode stepWitness.formula.tag consumedCount
      mappedHead)
  exact {
    quietDonePayload := threeWayPath0PayloadEnvelope quietFormula termFormula
      formulaFormula quietDoneResource
    quietEmptyPayload := threeWayPath0PayloadEnvelope quietFormula termFormula
      formulaFormula quietEmptyResource
    quietRepeatPayload := threeWayPath0PayloadEnvelope quietFormula termFormula
      formulaFormula quietRepeatResource
    quietInvalidPayload := threeWayPath0PayloadEnvelope quietFormula termFormula
      formulaFormula quietInvalidResource
    termPayload := threeWayPath1PayloadEnvelope quietFormula termFormula
      formulaFormula termResource
    formulaPayload := threeWayPath2PayloadEnvelope quietFormula termFormula
      formulaFormula formulaResource }

noncomputable def compactFormulaTransformStepRowsPublicFinitePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) : Nat :=
  let resources := compactFormulaTransformStepRowsPublicFiniteBranchPayloads
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount
  resources.quietDonePayload + resources.quietEmptyPayload +
    resources.quietRepeatPayload + resources.quietInvalidPayload +
    resources.termPayload + resources.formulaPayload

theorem compactFormulaTransformStepRowsBranchPayloadEnvelopeFromData_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (data : CompactFormulaTransformStepRowsCheckedBranchData tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount) :
    compactFormulaTransformStepRowsBranchPayloadEnvelopeFromData tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount data <=
      compactFormulaTransformStepRowsPublicFinitePayloadEnvelope tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount := by
  let resources := compactFormulaTransformStepRowsPublicFiniteBranchPayloads
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount
  cases data with
  | quietDone hparser hrows =>
      change resources.quietDonePayload <=
        resources.quietDonePayload + resources.quietEmptyPayload +
          resources.quietRepeatPayload + resources.quietInvalidPayload +
          resources.termPayload + resources.formulaPayload
      omega
  | quietEmpty hparser hrows =>
      change resources.quietEmptyPayload <=
        resources.quietDonePayload + resources.quietEmptyPayload +
          resources.quietRepeatPayload + resources.quietInvalidPayload +
          resources.termPayload + resources.formulaPayload
      omega
  | quietRepeat hparser hrows =>
      change resources.quietRepeatPayload <=
        resources.quietDonePayload + resources.quietEmptyPayload +
          resources.quietRepeatPayload + resources.quietInvalidPayload +
          resources.termPayload + resources.formulaPayload
      omega
  | quietInvalid hparser hrows =>
      change resources.quietInvalidPayload <=
        resources.quietDonePayload + resources.quietEmptyPayload +
          resources.quietRepeatPayload + resources.quietInvalidPayload +
          resources.termPayload + resources.formulaPayload
      omega
  | term hparser hrows =>
      change resources.termPayload <=
        resources.quietDonePayload + resources.quietEmptyPayload +
          resources.quietRepeatPayload + resources.quietInvalidPayload +
          resources.termPayload + resources.formulaPayload
      omega
  | formula hparser hrows =>
      change resources.formulaPayload <=
        resources.quietDonePayload + resources.quietEmptyPayload +
          resources.quietRepeatPayload + resources.quietInvalidPayload +
          resources.termPayload + resources.formulaPayload
      omega

theorem compactFormulaTransformStepRowsGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformStepRows tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount) :
    compactFormulaTransformStepRowsGraphPayloadEnvelope tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount hgraph <=
      compactFormulaTransformStepRowsPublicFinitePayloadEnvelope tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount := by
  unfold compactFormulaTransformStepRowsGraphPayloadEnvelope
  exact
    compactFormulaTransformStepRowsBranchPayloadEnvelopeFromData_le_publicFinite
      tokenTable width tokenCount current next mode stepWitness consumedCount
      mappedHead witnessStart witnessFinish witnessCount
      (compactFormulaTransformStepRowsCheckedBranchDataOfGraph tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount hgraph)

theorem
    compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformStepRows tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next mode stepWitness consumedCount
          mappedHead witnessStart witnessFinish witnessCount hgraph) <=
      compactFormulaTransformStepRowsPublicFinitePayloadEnvelope tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount := by
  exact
    (compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode stepWitness consumedCount
      mappedHead witnessStart witnessFinish witnessCount hgraph).trans
    (compactFormulaTransformStepRowsGraphPayloadEnvelope_le_publicFinite tokenTable
      width tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount hgraph)

#print axioms
  compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicBounds
