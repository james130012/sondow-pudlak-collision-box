import integration.FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
import integration.FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportRows
import integration.FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportExactness

/-!
# Successful parsed-leaf transport

This is the same-object conjunction of successful parse-payload realization and
the resulting verifier-leaf transport.  The common state, proof, certificate,
root, and suffix coordinates occur once.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportGraph

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportRows
open FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportExactness

def CompactNumericVerifierLeafParseSuccessTransportGraph
    (stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat) : Prop :=
  CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize ∧
    CompactNumericVerifierLeafParseSeparatedTablesTransportRows
      stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount rootStart rootGammaFinish
      witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool

def compactNumericVerifierLeafParseSuccessTransportGraphDef :
    𝚺₀.Semisentence 68 := .mkSigma
  “stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool.
    !(compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef)
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize ∧
    !(compactNumericVerifierLeafParseSeparatedTablesTransportRowsDef)
      stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount rootStart rootGammaFinish
      witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool”

def compactNumericVerifierLeafParseSuccessTransportGraphEnvironment
    (stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat) : Fin 68 → Nat :=
  ![stateTable, stateWidth, stateTokenCount,
    stateProofStart, stateProofFinish, stateCertificateStart, stateCertificateFinish,
    proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
    rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    rootGammaBoundarySize,
    sourceTaskBoundary, sourceTaskCount, targetTaskBoundary, targetTaskCount,
    sourceValueBoundary, sourceValueCount, targetValueBoundary, targetValueCount,
    currentTaskTableWidth, currentTaskValueBound,
    currentValueTableWidth, currentValueValueBound,
    nextTaskTableWidth, nextTaskValueBound,
    nextValueTableWidth, nextValueValueBound,
    nextStart, nextProofFinish, nextCertificateFinish, nextStatusTag,
    targetStart, targetFinish, targetGammaFinish, targetGammaCount,
    targetGammaBoundary, targetBool, targetGammaBoundarySize, resultBool]

set_option maxRecDepth 32768 in
@[simp] theorem compactNumericVerifierLeafParseSuccessTransportGraphDef_spec
    (stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat) :
    compactNumericVerifierLeafParseSuccessTransportGraphDef.val.Evalb
        (compactNumericVerifierLeafParseSuccessTransportGraphEnvironment
          stateTable stateWidth stateTokenCount
          stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
          secondFinish secondCount witnessFinish witnessCount suffixCount
          rootGammaBoundarySize
          sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
          sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
          currentTaskTableWidth currentTaskValueBound
          currentValueTableWidth currentValueValueBound
          nextTaskTableWidth nextTaskValueBound
          nextValueTableWidth nextValueValueBound
          nextStart nextProofFinish nextCertificateFinish nextStatusTag
          targetStart targetFinish targetGammaFinish targetGammaCount
          targetGammaBoundary targetBool targetGammaBoundarySize resultBool) ↔
      CompactNumericVerifierLeafParseSuccessTransportGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize
        sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
        sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize resultBool := by
  let env := compactNumericVerifierLeafParseSuccessTransportGraphEnvironment
    stateTable stateWidth stateTokenCount
    stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
    proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
    rootStart rootFinish proofTag proofEndpointBound
    certificateTable certificateWidth certificateTokenCount
    certificateInputStart certificateInputFinish
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag certificateEndpointBound
    rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
    secondFinish secondCount witnessFinish witnessCount suffixCount
    rootGammaBoundarySize
    sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
    sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
    currentTaskTableWidth currentTaskValueBound
    currentValueTableWidth currentValueValueBound
    nextTaskTableWidth nextTaskValueBound
    nextValueTableWidth nextValueValueBound
    nextStart nextProofFinish nextCertificateFinish nextStatusTag
    targetStart targetFinish targetGammaFinish targetGammaCount
    targetGammaBoundary targetBool targetGammaBoundarySize resultBool
  change compactNumericVerifierLeafParseSuccessTransportGraphDef.val.Evalb env ↔ _
  have hsuccessEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2, #3, #4, #5, #6,
          #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23, #24, #25, #26, #27, #28, #29,
          #30, #31, #32, #33, #34, #35, #36, #37, #38, #39]) =
        ![stateTable, stateWidth, stateTokenCount,
          stateProofStart, stateProofFinish, stateCertificateStart, stateCertificateFinish,
          proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
          rootStart, rootFinish, proofTag, proofEndpointBound,
          certificateTable, certificateWidth, certificateTokenCount,
          certificateInputStart, certificateInputFinish,
          axiomStart, axiomFinish, formulaStart, formulaFinish,
          suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
          rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
          secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
          rootGammaBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htransportEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2,
          #40, #41, #42, #43, #44, #45, #46, #47,
          #48, #49, #50, #51, #52, #53, #54, #55,
          #56, #57, #58, #59, #7, #8, #9, #12, #29, #36, #13,
          #16, #17, #18, #25, #26, #60, #61, #62, #63,
          #64, #65, #66, #67]) =
        ![stateTable, stateWidth, stateTokenCount,
          sourceTaskBoundary, sourceTaskCount, targetTaskBoundary, targetTaskCount,
          sourceValueBoundary, sourceValueCount, targetValueBoundary, targetValueCount,
          currentTaskTableWidth, currentTaskValueBound,
          currentValueTableWidth, currentValueValueBound,
          nextTaskTableWidth, nextTaskValueBound,
          nextValueTableWidth, nextValueValueBound,
          nextStart, nextProofFinish, nextCertificateFinish, nextStatusTag,
          proofTable, proofWidth, proofTokenCount, rootStart, rootGammaFinish,
          witnessFinish, rootFinish,
          certificateTable, certificateWidth, certificateTokenCount, suffixStart, suffixFinish,
          targetStart, targetFinish, targetGammaFinish, targetGammaCount,
          targetGammaBoundary, targetBool, targetGammaBoundarySize, resultBool] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsuccess :=
    compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef_spec
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
      stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
  simp only [compactNumericParsePayloadSuccessExposedSeparatedTablesGraphEnvironment]
    at hsuccess
  have htransport :=
    compactNumericVerifierLeafParseSeparatedTablesTransportRowsDef_spec
      stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount rootStart rootGammaFinish
      witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount
      suffixStart suffixFinish
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool
  simp only [compactNumericVerifierLeafParseSeparatedTablesTransportRowsEnvironment]
    at htransport
  simp only [compactNumericVerifierLeafParseSuccessTransportGraphDef,
    CompactNumericVerifierLeafParseSuccessTransportGraph]
  apply and_congr
  · refine (Semiformula.eval_substs (b := env) (f := Empty.elim)
      ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2, #3, #4, #5, #6,
        #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
        #19, #20, #21, #22, #23, #24, #25, #26, #27, #28, #29,
        #30, #31, #32, #33, #34, #35, #36, #37, #38, #39]
      compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef.val).trans ?_
    rw [hsuccessEnv]
    exact hsuccess
  · refine (Semiformula.eval_substs (b := env) (f := Empty.elim)
      ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2,
        #40, #41, #42, #43, #44, #45, #46, #47,
        #48, #49, #50, #51, #52, #53, #54, #55,
        #56, #57, #58, #59, #7, #8, #9, #12, #29, #36, #13,
        #16, #17, #18, #25, #26, #60, #61, #62, #63,
        #64, #65, #66, #67]
      compactNumericVerifierLeafParseSeparatedTablesTransportRowsDef.val).trans ?_
    rw [htransportEnv]
    exact htransport

theorem compactNumericVerifierLeafParseSuccessTransportGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierLeafParseSuccessTransportGraphDef.val := by
  simp [compactNumericVerifierLeafParseSuccessTransportGraphDef]

theorem CompactNumericVerifierLeafParseSuccessTransportGraph.sound
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      sourceTaskBoundary targetTaskBoundary sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize : Nat}
    {proofTokens certificateTokens proofSuffix certificateSuffix nextProof nextCertificate : List Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    {rootGamma : List (List Nat)} {result : Bool}
    (hgraph : CompactNumericVerifierLeafParseSuccessTransportGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      sourceTaskBoundary sourceTasks.length targetTaskBoundary targetTasks.length
      sourceValueBoundary sourceValues.length targetValueBoundary targetValues.length
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize
      (compactAdditiveBoolTag result))
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hproofSuffix : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount witnessFinish rootFinish proofSuffix)
    (hcertificateSuffix : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish certificateSuffix)
    (hrootGamma : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount (rootStart + 1) rootGammaFinish rootGamma)
    (hnextProof : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextProofFinish nextProof)
    (hnextCertificate : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount nextProofFinish nextCertificateFinish nextCertificate)
    (hsourceTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout
        stateTable stateWidth stateTokenCount sourceTaskBoundary sourceTasks)
    (htargetTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout
        stateTable stateWidth stateTokenCount targetTaskBoundary targetTasks)
    (hsourceValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount sourceValueBoundary sourceValues)
    (htargetValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount targetValueBoundary targetValues) :
    (∃ parsed, compactNumericParsePayload
      ((proofTokens, certificateTokens), (sourceTasks.drop 1, sourceValues)) =
        some parsed) ∧
      nextProof = proofSuffix ∧
      nextCertificate = certificateSuffix ∧
      targetTasks = sourceTasks.drop 1 ∧
      targetValues = (rootGamma, result) :: sourceValues ∧
      nextTaskTableWidth = currentTaskTableWidth ∧
      nextTaskValueBound = currentTaskValueBound ∧
      nextValueTableWidth = currentValueTableWidth ∧
      nextValueValueBound = currentValueValueBound ∧
      nextStatusTag = 0 := by
  refine ⟨hgraph.1.sound hproofLayout hcertificateLayout, ?_⟩
  exact
    FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportExactness.CompactNumericVerifierLeafParseSeparatedTablesTransportRows.sound
      hgraph.2 hproofSuffix hcertificateSuffix hrootGamma hnextProof
      hnextCertificate hsourceTaskRows htargetTaskRows hsourceValueRows
      htargetValueRows

theorem exists_compactNumericVerifierLeafParseSuccessTransportGraph_of_success_and_transition
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      sourceTaskBoundary targetTaskBoundary sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag : Nat}
    {proofTokens certificateTokens proofSuffix certificateSuffix nextProof nextCertificate : List Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    {proofNode : CompactNumericVerifierTask}
    {certificateNode : Nat × (List Nat × List Nat)}
    {rootGamma : List (List Nat)} {result : Bool}
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens = some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser certificateTokens =
      some certificateNode)
    (htransition : compactNumericNodeTransition proofNode certificateNode
      (sourceTasks.drop 1) sourceValues =
        some ((nextProof, nextCertificate), (targetTasks, targetValues)))
    (hrootGammaValue : rootGamma = proofNode.2.1)
    (hproofSuffixValue : proofSuffix = proofNode.2.2.2.2.2)
    (hcertificateSuffixValue : certificateSuffix = certificateNode.2.2)
    (hnextProof : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextProofFinish nextProof)
    (hnextCertificate : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount nextProofFinish nextCertificateFinish nextCertificate)
    (hsourceTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout
        stateTable stateWidth stateTokenCount sourceTaskBoundary sourceTasks)
    (htargetTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout
        stateTable stateWidth stateTokenCount targetTaskBoundary targetTasks)
    (hsourceValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount sourceValueBoundary sourceValues)
    (htargetValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount targetValueBoundary targetValues)
    (hsourceTaskGraph : CompactNumericVerifierTaskListRowsGraph
      stateTable stateWidth stateTokenCount sourceTaskBoundary
        sourceTasks.length currentTaskTableWidth currentTaskValueBound)
    (htargetTaskGraph : CompactNumericVerifierTaskListRowsGraph
      stateTable stateWidth stateTokenCount targetTaskBoundary
        targetTasks.length currentTaskTableWidth currentTaskValueBound)
    (hsourceValueGraph : CompactNumericChildResultListRowsGraph
      stateTable stateWidth stateTokenCount sourceValueBoundary
        sourceValues.length currentValueTableWidth currentValueValueBound)
    (htargetValueGraph : CompactNumericChildResultListRowsGraph
      stateTable stateWidth stateTokenCount targetValueBoundary
        targetValues.length currentValueTableWidth currentValueValueBound)
    (hsourceTaskNonempty : 1 ≤ sourceTasks.length)
    (htasks : targetTasks = sourceTasks.drop 1)
    (hvalues : targetValues = (rootGamma, result) :: sourceValues)
    (hnextProofValue : nextProof = proofSuffix)
    (hnextCertificateValue : nextCertificate = certificateSuffix)
    (htaskTableWidth : nextTaskTableWidth = currentTaskTableWidth)
    (htaskValueBound : nextTaskValueBound = currentTaskValueBound)
    (hvalueTableWidth : nextValueTableWidth = currentValueTableWidth)
    (hvalueValueBound : nextValueValueBound = currentValueValueBound)
    (hnextStatus : nextStatusTag = 0) :
    ∃ proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
      ∃ rootStart rootFinish proofTag proofEndpointBound,
      ∃ certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish,
      ∃ axiomStart axiomFinish formulaStart formulaFinish,
      ∃ suffixStart suffixFinish certificateTag certificateEndpointBound,
      ∃ rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount rootGammaBoundarySize,
      ∃ targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize,
      CompactNumericVerifierLeafParseSuccessTransportGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize
        sourceTaskBoundary sourceTasks.length targetTaskBoundary targetTasks.length
        sourceValueBoundary sourceValues.length targetValueBoundary targetValues.length
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize
        (compactAdditiveBoolTag result) := by
  have hparse : ∃ parsed, compactNumericParsePayload
      ((proofTokens, certificateTokens), (sourceTasks.drop 1, sourceValues)) =
        some parsed := by
    refine ⟨((nextProof, nextCertificate), (targetTasks, targetValues)), ?_⟩
    apply (compactNumericParsePayload_eq_some_iff
      ((proofTokens, certificateTokens), (sourceTasks.drop 1, sourceValues)) _).2
    exact ⟨proofNode, certificateNode, hproofParser, hcertificateParser, htransition⟩
  rcases exists_compactNumericParsePayloadSuccessExposedSeparatedTablesGraph_of_exists_some
      hproofLayout hcertificateLayout hparse with
    ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      rootGammaBoundarySize, hsuccess⟩
  have hproofCross := hsuccess.1.1
  have hcertificateCross := hsuccess.1.2.1
  have hproofRoot := hsuccess.1.2.2.1
  have hcertificateRoot := hsuccess.1.2.2.2.1
  rcases hproofRoot.sound with
    ⟨parsedProofTokens, parsedProofNode, hparsedProofLayout,
      hparsedProofNodeLayout, hparsedProof, hparsedProofTag⟩
  have hproofTokensEq : parsedProofTokens = proofTokens :=
    hproofCross.natListValues_eq hproofLayout hparsedProofLayout
  subst parsedProofTokens
  have hproofNodeEq : parsedProofNode = proofNode :=
    Option.some.inj (hparsedProof.symm.trans hproofParser)
  subst parsedProofNode
  have hcoreSaved := hsuccess.2
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hcoreSaved with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag, hrootGammaRows,
      _hrootGammaLength, hfirst, _hfirstLength, hsecond, _hsecondLength,
      hwitness, _hwitnessLength, hsuffix, _hsuffixLength⟩
  have hrealizedRootEq : realizedRoot = proofNode :=
    FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hcoreSaved hparsedProofNodeLayout hrealizedRoot
  subst realizedRoot
  rcases hcoreSaved with
    ⟨htag, hrootGammaLayout, hrootGammaRows', hrootGammaSizeEq,
      hrootGammaSize, _hfirstSlice, _hsecondSlice, _hwitnessSlice,
      _hsuffixSlice⟩
  have hrootGammaLength : proofNode.2.1.length = rootGammaCount := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using
      _hrootGammaLength
  have hrootGammaStructure :
      CompactAdditiveStructuredListLayout proofTable proofWidth proofTokenCount
        (rootStart + 1) proofNode.2.1.length rootGammaFinish
        rootGammaBoundary := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf, hrootGammaLength] using
      hrootGammaLayout
  have hrootGammaSizeEq' :
      rootGammaBoundarySize = Nat.size rootGammaBoundary := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using
      hrootGammaSizeEq
  have hrootGammaSize' :
      rootGammaBoundarySize ≤ (rootGammaCount + 1) * proofTokenCount := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hrootGammaSize
  have hrootGammaSizeBound : Nat.size rootGammaBoundary ≤
      (proofNode.2.1.length + 1) * proofTokenCount := by
    rw [hrootGammaLength, ← hrootGammaSizeEq']
    exact hrootGammaSize'
  have hrootGammaLayoutNode : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount (rootStart + 1) rootGammaFinish
        proofNode.2.1 :=
    ⟨rootGammaBoundary, hrootGammaStructure, hrootGammaRows,
      hrootGammaSizeBound⟩
  have hrootGammaLayoutActual : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount (rootStart + 1) rootGammaFinish rootGamma := by
    simpa [hrootGammaValue] using hrootGammaLayoutNode
  have hproofSuffixLayout : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount witnessFinish rootFinish proofSuffix := by
    simpa [hproofSuffixValue, compactNumericVerifierTaskRowCoordinatesOf] using
      hsuffix
  have hcertificateSuffixLayout : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        suffixStart suffixFinish certificateSuffix := by
    rcases hcertificateRoot.sound with
      ⟨parsedCertificateTokens, parsedSuffix, hparsedCertificateLayout,
        hparsedSuffixLayout, hparsedCertificate⟩ |
      ⟨parsedCertificateTokens, _parsedAxiomTokens, parsedSuffix,
        hparsedCertificateLayout, _hparsedAxiomLayout, hparsedSuffixLayout,
        hparsedCertificate⟩
    · have hcertificateTokensEq : parsedCertificateTokens = certificateTokens :=
        hcertificateCross.natListValues_eq hcertificateLayout hparsedCertificateLayout
      subst parsedCertificateTokens
      have hcertificateNodeEq :
          (certificateTag, ([], parsedSuffix)) = certificateNode :=
        Option.some.inj (hparsedCertificate.symm.trans hcertificateParser)
      have hsuffixEq : parsedSuffix = certificateNode.2.2 := by
        simpa using congrArg (fun node => node.2.2) hcertificateNodeEq
      simpa [hcertificateSuffixValue, hsuffixEq] using hparsedSuffixLayout
    · have hcertificateTokensEq : parsedCertificateTokens = certificateTokens :=
        hcertificateCross.natListValues_eq hcertificateLayout hparsedCertificateLayout
      subst parsedCertificateTokens
      have hcertificateNodeEq :
          (certificateTag, (_parsedAxiomTokens, parsedSuffix)) = certificateNode :=
        Option.some.inj (hparsedCertificate.symm.trans hcertificateParser)
      have hsuffixEq : parsedSuffix = certificateNode.2.2 := by
        simpa using congrArg (fun node => node.2.2) hcertificateNodeEq
      simpa [hcertificateSuffixValue, hsuffixEq] using hparsedSuffixLayout
  rcases exists_compactNumericVerifierLeafParseSeparatedTablesTransportRows_of_rows
      hproofSuffixLayout hcertificateSuffixLayout hrootGammaLayoutActual
      hnextProof hnextCertificate
      hsourceTaskRows htargetTaskRows hsourceValueRows htargetValueRows
      hsourceTaskGraph htargetTaskGraph hsourceValueGraph htargetValueGraph
      hnextProofValue hnextCertificateValue
      htaskTableWidth htaskValueBound hvalueTableWidth hvalueValueBound
      hsourceTaskNonempty htasks hvalues hnextStatus with
    ⟨targetStart, targetFinish, targetGammaFinish, targetGammaCount,
      targetGammaBoundary, targetBool, targetGammaBoundarySize, htransport⟩
  exact ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
    rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    rootGammaBoundarySize,
    targetStart, targetFinish, targetGammaFinish, targetGammaCount,
    targetGammaBoundary, targetBool, targetGammaBoundarySize, hsuccess, htransport⟩

#print axioms compactNumericVerifierLeafParseSuccessTransportGraphDef_spec
#print axioms compactNumericVerifierLeafParseSuccessTransportGraphDef_sigmaZero
#print axioms CompactNumericVerifierLeafParseSuccessTransportGraph.sound
#print axioms
  exists_compactNumericVerifierLeafParseSuccessTransportGraph_of_success_and_transition

end FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportGraph
