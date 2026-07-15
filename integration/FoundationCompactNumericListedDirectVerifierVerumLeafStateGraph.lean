import integration.FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportGraph
import integration.FoundationCompactNumericListedDirectVerifierVerumLeafParsedRuleGraph

/-!
# Same-object parsed verum leaf state graph

The successful parsed-leaf transport and the verum row share the one exposed
proof-root table.  In particular, `rootGammaBoundary` is not duplicated.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierVerumLeafStateGraph

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportGraph
open FoundationCompactNumericListedDirectVerifierVerumLeafRuleRows
open FoundationCompactNumericListedDirectVerifierVerumLeafRuleRowsCompleteness

def CompactNumericVerifierVerumLeafStateGraph
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
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool ∧
    CompactNumericVerifierVerumLeafRuleRows
      proofTable proofWidth proofTokenCount proofTag certificateTag
      rootGammaBoundary rootGammaCount resultBool

def compactNumericVerifierVerumLeafStateGraphDef :
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
    !(compactNumericVerifierLeafParseSuccessTransportGraphDef)
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
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool ∧
    !(compactNumericVerifierVerumLeafRuleRowsDef)
      proofTable proofWidth proofTokenCount proofTag certificateTag
      rootGammaBoundary rootGammaCount resultBool”

def compactNumericVerifierVerumLeafStateGraphEnvironment
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
  compactNumericVerifierLeafParseSuccessTransportGraphEnvironment
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

set_option maxRecDepth 32768 in
@[simp] theorem compactNumericVerifierVerumLeafStateGraphDef_spec
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
    compactNumericVerifierVerumLeafStateGraphDef.val.Evalb
        (compactNumericVerifierVerumLeafStateGraphEnvironment
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
      CompactNumericVerifierVerumLeafStateGraph
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
  let env := compactNumericVerifierVerumLeafStateGraphEnvironment
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
  change compactNumericVerifierVerumLeafStateGraphDef.val.Evalb env ↔ _
  have htransportEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2, #3, #4, #5, #6,
          #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23, #24, #25, #26, #27, #28, #29,
          #30, #31, #32, #33, #34, #35, #36, #37, #38, #39, #40,
          #41, #42, #43, #44, #45, #46, #47, #48, #49, #50, #51,
          #52, #53, #54, #55, #56, #57, #58, #59, #60, #61, #62,
          #63, #64, #65, #66, #67]) =
        compactNumericVerifierLeafParseSuccessTransportGraphEnvironment
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
    funext coordinate
    fin_cases coordinate <;> rfl
  have htransport := compactNumericVerifierLeafParseSuccessTransportGraphDef_spec
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
  have hverumEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#7 : Semiterm ℒₒᵣ Empty 68), #8, #9, #14, #27, #31, #30, #67]) =
        ![proofTable, proofWidth, proofTokenCount, proofTag, certificateTag,
          rootGammaBoundary, rootGammaCount, resultBool] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hverum := compactNumericVerifierVerumLeafRuleRowsDef_spec
    proofTable proofWidth proofTokenCount proofTag certificateTag
    rootGammaBoundary rootGammaCount resultBool
  simp only [compactNumericVerifierVerumLeafStateGraphDef,
    CompactNumericVerifierVerumLeafStateGraph]
  apply and_congr
  · refine (Semiformula.eval_substs (b := env) (f := Empty.elim)
      ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2, #3, #4, #5, #6,
        #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
        #19, #20, #21, #22, #23, #24, #25, #26, #27, #28, #29,
        #30, #31, #32, #33, #34, #35, #36, #37, #38, #39, #40,
        #41, #42, #43, #44, #45, #46, #47, #48, #49, #50, #51,
        #52, #53, #54, #55, #56, #57, #58, #59, #60, #61, #62,
        #63, #64, #65, #66, #67]
      compactNumericVerifierLeafParseSuccessTransportGraphDef.val).trans ?_
    rw [htransportEnv]
    exact htransport
  · refine (Semiformula.eval_substs (b := env) (f := Empty.elim)
      ![(#7 : Semiterm ℒₒᵣ Empty 68), #8, #9, #14, #27, #31, #30,
        #67]
      compactNumericVerifierVerumLeafRuleRowsDef.val).trans ?_
    rw [hverumEnv]
    exact hverum

theorem compactNumericVerifierVerumLeafStateGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierVerumLeafStateGraphDef.val := by
  simp [compactNumericVerifierVerumLeafStateGraphDef]

theorem CompactNumericVerifierVerumLeafStateGraph.sound
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
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat}
    {proofTokens certificateTokens proofSuffix certificateSuffix nextProof nextCertificate : List Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    {rootGamma : List (List Nat)}
    (hgraph : CompactNumericVerifierVerumLeafStateGraph
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
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool)
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
    resultBool = compactAdditiveBoolTag (compactVerumRuleCheck rootGamma) ∧
    proofTag = 2 ∧
    certificateTag = 0 ∧
    (∃ parsed, compactNumericParsePayload
      ((proofTokens, certificateTokens), (sourceTasks.drop 1, sourceValues)) =
        some parsed) ∧
      nextProof = proofSuffix ∧
      nextCertificate = certificateSuffix ∧
      targetTasks = sourceTasks.drop 1 ∧
      targetValues = (rootGamma, compactVerumRuleCheck rootGamma) :: sourceValues ∧
      nextTaskTableWidth = currentTaskTableWidth ∧
      nextTaskValueBound = currentTaskValueBound ∧
      nextValueTableWidth = currentValueTableWidth ∧
      nextValueValueBound = currentValueValueBound ∧
      nextStatusTag = 0 := by
  have hcore := hgraph.1.1.2
  rcases CompactNumericVerifierVerumLeafRuleRows.sound hcore hgraph.2 with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag, _hcertificateTag, hresult⟩
  rcases CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
      hcore with
    ⟨fieldRoot, hfieldRoot, _hfieldTag, _hfieldGammaRows,
      _hfieldGammaLength, hfieldFirst, _hfieldFirstLength,
      hfieldSecond, _hfieldSecondLength, hfieldWitness,
      _hfieldWitnessLength, hfieldSuffix, _hfieldSuffixLength⟩
  have hfieldRootEq : fieldRoot = realizedRoot :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hcore hrealizedRoot hfieldRoot
  subst fieldRoot
  rcases hcore with
    ⟨htag, hgammaLayout, hgammaRows, hgammaSizeEq, hgammaSize,
      hfirst, hsecond, hwitness, hsuffix⟩
  let actualRoot : CompactNumericVerifierTask :=
    (proofTag, (rootGamma, (realizedRoot.2.2.1,
      (realizedRoot.2.2.2.1,
        (realizedRoot.2.2.2.2.1, realizedRoot.2.2.2.2.2)))))
  have hactualFields : CompactNumericNodeFieldsDirectLayout
      proofTable proofWidth proofTokenCount (rootStart + 1) rootFinish actualRoot.2 := by
    refine ⟨rootGammaFinish, firstFinish, secondFinish, witnessFinish, ?_,
      ?_, ?_, ?_, ?_⟩
    · simpa [actualRoot] using hrootGamma
    · simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using hfieldFirst
    · simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using hfieldSecond
    · simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using hfieldWitness
    · simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using hfieldSuffix
  have hactualRoot : CompactNumericVerifierTaskDirectLayout
      proofTable proofWidth proofTokenCount rootStart rootFinish actualRoot :=
    ⟨rootStart + 1, by
      simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using htag,
      hactualFields⟩
  have hrootEq : realizedRoot = actualRoot :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      (show CompactNumericVerifierTaskCoreGraph proofTable proofWidth proofTokenCount
        (compactNumericVerifierTaskRowCoordinatesOf
          rootStart rootFinish proofTag rootGammaFinish rootGammaCount rootGammaBoundary
          firstFinish firstCount secondFinish secondCount witnessFinish witnessCount suffixCount)
        { gammaBoundarySize := rootGammaBoundarySize } from
        ⟨htag, hgammaLayout, hgammaRows, hgammaSizeEq, hgammaSize,
          hfirst, hsecond, hwitness, hsuffix⟩)
      hactualRoot hrealizedRoot
  have hrootGammaEq : realizedRoot.2.1 = rootGamma := by
    simpa [actualRoot] using congrArg (fun task => task.2.1) hrootEq
  have hresult' : resultBool = compactAdditiveBoolTag
      (compactVerumRuleCheck rootGamma) := by
    simpa [hrootGammaEq] using hresult
  refine ⟨hresult', hgraph.2.1, hgraph.2.2.1, ?_⟩
  have htransport : CompactNumericVerifierLeafParseSuccessTransportGraph
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
      (compactAdditiveBoolTag (compactVerumRuleCheck rootGamma)) := by
    simpa [hresult'] using hgraph.1
  exact CompactNumericVerifierLeafParseSuccessTransportGraph.sound htransport
    hproofLayout hcertificateLayout hproofSuffix hcertificateSuffix hrootGamma
    hnextProof hnextCertificate hsourceTaskRows htargetTaskRows hsourceValueRows
    htargetValueRows

theorem exists_compactNumericVerifierVerumLeafStateGraph_of_success_and_transition
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      sourceTaskBoundary targetTaskBoundary sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag : Nat}
    {proofTokens certificateTokens nextProof nextCertificate : List Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    {proofNode : CompactNumericVerifierTask}
    {certificateNode : Nat × (List Nat × List Nat)}
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens = some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser certificateTokens =
      some certificateNode)
    (hproofTag : proofNode.1 = 2)
    (htransition : compactNumericNodeTransition proofNode certificateNode
      (sourceTasks.drop 1) sourceValues =
        some ((nextProof, nextCertificate), (targetTasks, targetValues)))
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
      CompactNumericVerifierVerumLeafStateGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount rootGammaBoundarySize
        sourceTaskBoundary sourceTasks.length targetTaskBoundary targetTasks.length
        sourceValueBoundary sourceValues.length targetValueBoundary targetValues.length
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize
        (compactAdditiveBoolTag (compactVerumRuleCheck proofNode.2.1)) := by
  have houtputCase :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode (sourceTasks.drop 1) sourceValues
      ((nextProof, nextCertificate), (targetTasks, targetValues))).1 htransition
  have hverumOutput :
      certificateNode.1 = 0 ∧
      ((proofNode.2.2.2.2.2, certificateNode.2.2),
        (sourceTasks.drop 1,
          (proofNode.2.1, compactVerumRuleCheck proofNode.2.1) ::
            sourceValues)) =
        ((nextProof, nextCertificate), (targetTasks, targetValues)) := by
    simpa [CompactNumericNodeTransitionOutputCase, hproofTag,
      compactNumericNodeFieldsSuffix] using houtputCase
  rcases hverumOutput with ⟨_hcertificateNodeTag, houtput⟩
  have hnextProofValue : nextProof = proofNode.2.2.2.2.2 := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.1.1)
      houtput
    simpa using h.symm
  have hnextCertificateValue : nextCertificate = certificateNode.2.2 := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.1.2)
      houtput
    simpa using h.symm
  have htasks : targetTasks = sourceTasks.drop 1 := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.2.1)
      houtput
    simpa using h.symm
  have hvalues : targetValues =
      (proofNode.2.1, compactVerumRuleCheck proofNode.2.1) :: sourceValues := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.2.2)
      houtput
    simpa using h.symm
  rcases exists_compactNumericVerifierLeafParseSuccessTransportGraph_of_success_and_transition
      hproofLayout hcertificateLayout hproofParser hcertificateParser htransition
      rfl rfl rfl hnextProof hnextCertificate hsourceTaskRows htargetTaskRows
      hsourceValueRows htargetValueRows hsourceTaskGraph htargetTaskGraph
      hsourceValueGraph htargetValueGraph hsourceTaskNonempty htasks hvalues
      hnextProofValue hnextCertificateValue htaskTableWidth htaskValueBound
      hvalueTableWidth hvalueValueBound hnextStatus with
    ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      rootGammaBoundarySize,
      targetStart, targetFinish, targetGammaFinish, targetGammaCount,
      targetGammaBoundary, targetBool, targetGammaBoundarySize, htransport⟩
  have hsuccess := htransport.1
  rcases hsuccess.1.2.2.1.sound with
    ⟨decodedProofTokens, decodedRoot, hdecodedProofLayout, hdecodedRootLayout,
      hdecodedProof, hdecodedTag⟩
  have hdecodedProofTokensEq : decodedProofTokens = proofTokens :=
    hsuccess.1.1.natListValues_eq hproofLayout hdecodedProofLayout
  subst decodedProofTokens
  have hdecodedRootEq : decodedRoot = proofNode :=
    Option.some.inj (hdecodedProof.symm.trans hproofParser)
  subst decodedRoot
  have hproofTagCoord : proofTag = 2 := hdecodedTag.symm.trans hproofTag
  have htagMatch := hsuccess.1.2.2.2.2
  have hcertificateTagCoord : certificateTag = 0 := by
    rw [hproofTagCoord] at htagMatch
    simpa [CompactNumericNodeTransitionTagMatch] using htagMatch
  rcases CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
      hsuccess.2 with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag, hgammaRows, hgammaLength,
      _hfirstLayout, _hfirstLength, _hsecondLayout, _hsecondLength,
      _hwitnessLayout, _hwitnessLength, _hsuffixLayout, _hsuffixLength⟩
  have hrealizedRootEq : realizedRoot = proofNode :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hsuccess.2 hdecodedRootLayout hrealizedRoot
  subst realizedRoot
  have hverum : CompactNumericVerifierVerumLeafRuleRows
      proofTable proofWidth proofTokenCount proofTag certificateTag
      rootGammaBoundary rootGammaCount
      (compactAdditiveBoolTag (compactVerumRuleCheck proofNode.2.1)) := by
    have hraw := CompactNumericVerifierVerumLeafRuleRows.of_gammaRows hgammaRows
    simpa only [hproofTagCoord, hcertificateTagCoord, hgammaLength,
      compactNumericVerifierTaskRowCoordinatesOf] using hraw
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
    targetGammaBoundary, targetBool, targetGammaBoundarySize, htransport, hverum⟩

#print axioms compactNumericVerifierVerumLeafStateGraphDef_spec
#print axioms compactNumericVerifierVerumLeafStateGraphDef_sigmaZero
#print axioms CompactNumericVerifierVerumLeafStateGraph.sound
#print axioms exists_compactNumericVerifierVerumLeafStateGraph_of_success_and_transition

end FoundationCompactNumericListedDirectVerifierVerumLeafStateGraph
