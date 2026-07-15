import integration.FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportGraph
import integration.FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness
import integration.FoundationCompactNumericListedDirectVerifierPAAxiomLeafCrossTableBridgeGraph
import integration.FoundationCompactNumericListedDirectVerifierPAAxiomLeafParsedSemantics

/-!
# Complete PA-axiom leaf state graph

The first 68 coordinates are the successful parser/transport graph.  The
remaining 259 coordinates are the complete canonical PA-axiom endpoint and
rule table.  Three cross-table slice equalities identify the parser context,
candidate, and certificate axiom with their rule-table counterparts.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraph

open FoundationCompactSyntaxTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
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
open FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafCrossTableBridgeGraph
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafParsedSemantics
open FoundationCompactNumericListedDirectInductionPAAxiomRuleCheck
open FoundationCompactNumericListedDirectGuardedInductionSentenceRoute
open FoundationCompactPAAxiomCertificate

def CompactNumericVerifierPAAxiomLeafStateGraph
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
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat)
    (c : CompactNumericVerifierPAAxiomJointLeafCoordinates) : Prop :=
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
    CompactNumericVerifierPAAxiomJointLeafRows c ∧
    CompactNumericVerifierPAAxiomLeafCrossTableBridgeGraph
      proofTable proofWidth proofTokenCount (rootStart + 1) rootGammaFinish
      rootGammaFinish firstFinish
      certificateTable certificateWidth certificateTokenCount
      axiomStart axiomFinish
      c.ruleTable c.ruleWidth c.ruleTokenCount c.gammaStart c.gammaFinish
      c.candidate.start c.candidate.finish
      c.ruleAxiom.start c.ruleAxiom.finish ∧
    proofTag = c.proofTag ∧ certificateTag = c.certificateTag ∧
      resultBool = c.resultBool

def compactNumericVerifierPAAxiomLeafStateGraphDef :
    𝚺₀.Semisentence 327 := .mkSigma
  ((compactNumericVerifierLeafParseSuccessTransportGraphDef.val ⇜
      (fun index : Fin 68 =>
        (#(Fin.castLE (show 68 ≤ 327 by omega) index) :
          Semiterm ℒₒᵣ Empty 327))) ⋏
    (compactNumericVerifierPAAxiomJointLeafRowsDef.val ⇜
      (fun index : Fin 259 =>
        (#(Fin.natAdd 68 index) : Semiterm ℒₒᵣ Empty 327))) ⋏
    (compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphDef.val ⇜
      ![(#7 : Semiterm ℒₒᵣ Empty 327), #8, #9, ‘(#12 + 1)’, #29, #29,
        #32, #16, #17, #18, #21, #22,
        #68, #69, #70, #265, #266, #250, #251, #271, #272]) ⋏
    “(#14 = #263)” ⋏ “(#27 = #264)” ⋏ “(#67 = #247)”) (by simp)

def compactNumericVerifierPAAxiomLeafStateGraphEnvironment
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
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat)
    (c : CompactNumericVerifierPAAxiomJointLeafCoordinates) : Fin 327 → Nat :=
  Matrix.vecAppend rfl
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
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool)
    (compactNumericVerifierPAAxiomJointLeafRowsEnvironment c)

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 32768 in
@[simp] theorem compactNumericVerifierPAAxiomLeafStateGraphDef_spec
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
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat)
    (c : CompactNumericVerifierPAAxiomJointLeafCoordinates) :
    compactNumericVerifierPAAxiomLeafStateGraphDef.val.Evalb
        (compactNumericVerifierPAAxiomLeafStateGraphEnvironment
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
          targetGammaBoundary targetBool targetGammaBoundarySize resultBool c) ↔
      CompactNumericVerifierPAAxiomLeafStateGraph
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
        targetGammaBoundary targetBool targetGammaBoundarySize resultBool c := by
  let transportEnv :=
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
  let jointEnv := compactNumericVerifierPAAxiomJointLeafRowsEnvironment c
  let env := Matrix.vecAppend rfl transportEnv jointEnv
  have htransportEnv :
      (Semiterm.val env Empty.elim ∘
        (fun index : Fin 68 =>
          (#(Fin.castLE (show 68 ≤ 327 by omega) index) :
            Semiterm ℒₒᵣ Empty 327))) = transportEnv := by
    funext coordinate
    simp [env, Matrix.vecAppend_eq_ite]
  have hjointEnv :
      (Semiterm.val env Empty.elim ∘
        (fun index : Fin 259 =>
          (#(Fin.natAdd 68 index) : Semiterm ℒₒᵣ Empty 327))) = jointEnv := by
    funext coordinate
    simp [env, Matrix.vecAppend_eq_ite]
  have htransportAt (index : Fin 68) :
      env (Fin.castLE (show 68 ≤ 327 by omega) index) = transportEnv index := by
    simpa [Function.comp_apply] using congrFun htransportEnv index
  have hjointAt (index : Fin 259) :
      env (Fin.natAdd 68 index) = jointEnv index := by
    simpa [Function.comp_apply] using congrFun hjointEnv index
  have henv7 : env 7 = proofTable := by
    simpa [transportEnv,
      compactNumericVerifierLeafParseSuccessTransportGraphEnvironment] using
      htransportAt (7 : Fin 68)
  have henv8 : env 8 = proofWidth := by
    simpa [transportEnv,
      compactNumericVerifierLeafParseSuccessTransportGraphEnvironment] using
      htransportAt (8 : Fin 68)
  have henv9 : env 9 = proofTokenCount := by
    simpa [transportEnv,
      compactNumericVerifierLeafParseSuccessTransportGraphEnvironment] using
      htransportAt (9 : Fin 68)
  have henv12 : env 12 = rootStart := by
    simpa [transportEnv,
      compactNumericVerifierLeafParseSuccessTransportGraphEnvironment] using
      htransportAt (12 : Fin 68)
  have henv14 : env 14 = proofTag := by
    simpa [transportEnv,
      compactNumericVerifierLeafParseSuccessTransportGraphEnvironment] using
      htransportAt (14 : Fin 68)
  have henv16 : env 16 = certificateTable := by
    simpa [transportEnv,
      compactNumericVerifierLeafParseSuccessTransportGraphEnvironment] using
      htransportAt (16 : Fin 68)
  have henv17 : env 17 = certificateWidth := by
    simpa [transportEnv,
      compactNumericVerifierLeafParseSuccessTransportGraphEnvironment] using
      htransportAt (17 : Fin 68)
  have henv18 : env 18 = certificateTokenCount := by
    simpa [transportEnv,
      compactNumericVerifierLeafParseSuccessTransportGraphEnvironment] using
      htransportAt (18 : Fin 68)
  have henv21 : env 21 = axiomStart := by
    simpa [transportEnv,
      compactNumericVerifierLeafParseSuccessTransportGraphEnvironment] using
      htransportAt (21 : Fin 68)
  have henv22 : env 22 = axiomFinish := by
    simpa [transportEnv,
      compactNumericVerifierLeafParseSuccessTransportGraphEnvironment] using
      htransportAt (22 : Fin 68)
  have henv27 : env 27 = certificateTag := by
    simpa [transportEnv,
      compactNumericVerifierLeafParseSuccessTransportGraphEnvironment] using
      htransportAt (27 : Fin 68)
  have henv29 : env 29 = rootGammaFinish := by
    simpa [transportEnv,
      compactNumericVerifierLeafParseSuccessTransportGraphEnvironment] using
      htransportAt (29 : Fin 68)
  have henv32 : env 32 = firstFinish := by
    simpa [transportEnv,
      compactNumericVerifierLeafParseSuccessTransportGraphEnvironment] using
      htransportAt (32 : Fin 68)
  have henv67 : env 67 = resultBool := by
    simpa [transportEnv,
      compactNumericVerifierLeafParseSuccessTransportGraphEnvironment] using
      htransportAt (67 : Fin 68)
  have hjoint0 : jointEnv 0 = c.ruleTable := by
    simp [jointEnv, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      compactGuardedInductionSentenceRouteEnvironment,
      Matrix.vecAppend_eq_ite]
  have hjoint1 : jointEnv 1 = c.ruleWidth := by
    simp [jointEnv, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      compactGuardedInductionSentenceRouteEnvironment,
      Matrix.vecAppend_eq_ite]
  have hjoint2 : jointEnv 2 = c.ruleTokenCount := by
    simp [jointEnv, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      compactGuardedInductionSentenceRouteEnvironment,
      Matrix.vecAppend_eq_ite]
  have hjoint179 : jointEnv 179 = c.resultBool := by
    simp [jointEnv, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      Matrix.vecAppend_eq_ite]
  have hjoint182 : jointEnv 182 = c.candidate.start := by
    simp [jointEnv, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      Matrix.vecAppend_eq_ite]
  have hjoint183 : jointEnv 183 = c.candidate.finish := by
    simp [jointEnv, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      Matrix.vecAppend_eq_ite]
  have hjoint195 : jointEnv 195 = c.proofTag := by rfl
  have hjoint196 : jointEnv 196 = c.certificateTag := by rfl
  have hjoint197 : jointEnv 197 = c.gammaStart := by rfl
  have hjoint198 : jointEnv 198 = c.gammaFinish := by rfl
  have hjoint203 : jointEnv 203 = c.ruleAxiom.start := by rfl
  have hjoint204 : jointEnv 204 = c.ruleAxiom.finish := by rfl
  have henv68 : env 68 = c.ruleTable := by
    simpa [hjoint0] using hjointAt (0 : Fin 259)
  have henv69 : env 69 = c.ruleWidth := by
    simpa [hjoint1] using hjointAt (1 : Fin 259)
  have henv70 : env 70 = c.ruleTokenCount := by
    simpa [hjoint2] using hjointAt (2 : Fin 259)
  have henv247 : env 247 = c.resultBool := by
    simpa [hjoint179] using hjointAt (179 : Fin 259)
  have henv250 : env 250 = c.candidate.start := by
    simpa [hjoint182] using hjointAt (182 : Fin 259)
  have henv251 : env 251 = c.candidate.finish := by
    simpa [hjoint183] using hjointAt (183 : Fin 259)
  have henv263 : env 263 = c.proofTag := by
    simpa [hjoint195] using hjointAt (195 : Fin 259)
  have henv264 : env 264 = c.certificateTag := by
    simpa [hjoint196] using hjointAt (196 : Fin 259)
  have henv265 : env 265 = c.gammaStart := by
    simpa [hjoint197] using hjointAt (197 : Fin 259)
  have henv266 : env 266 = c.gammaFinish := by
    simpa [hjoint198] using hjointAt (198 : Fin 259)
  have henv271 : env 271 = c.ruleAxiom.start := by
    simpa [hjoint203] using hjointAt (203 : Fin 259)
  have henv272 : env 272 = c.ruleAxiom.finish := by
    simpa [hjoint204] using hjointAt (204 : Fin 259)
  have hbridgeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#7 : Semiterm ℒₒᵣ Empty 327), #8, #9, ‘(#12 + 1)’, #29,
          #29, #32, #16, #17, #18, #21, #22,
          #68, #69, #70, #265, #266, #250, #251, #271, #272]) =
        compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphEnvironment
          proofTable proofWidth proofTokenCount (rootStart + 1) rootGammaFinish
          rootGammaFinish firstFinish
          certificateTable certificateWidth certificateTokenCount
          axiomStart axiomFinish
          c.ruleTable c.ruleWidth c.ruleTokenCount c.gammaStart c.gammaFinish
          c.candidate.start c.candidate.finish
          c.ruleAxiom.start c.ruleAxiom.finish := by
    funext coordinate
    fin_cases coordinate <;>
      simp [Function.comp_apply,
        compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphEnvironment,
        henv7, henv8, henv9, henv12, henv16, henv17, henv18,
        henv21, henv22, henv29, henv32, henv68, henv69, henv70,
        henv250, henv251, henv265, henv266, henv271, henv272]
  have htransportSpec :=
    compactNumericVerifierLeafParseSuccessTransportGraphDef_spec
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
  change (Semiformula.Eval transportEnv Empty.elim)
      compactNumericVerifierLeafParseSuccessTransportGraphDef.val ↔ _ at htransportSpec
  have hjointSpec := compactNumericVerifierPAAxiomJointLeafRowsDef_spec c
  change (Semiformula.Eval jointEnv Empty.elim)
      compactNumericVerifierPAAxiomJointLeafRowsDef.val ↔ _ at hjointSpec
  change compactNumericVerifierPAAxiomLeafStateGraphDef.val.Evalb env ↔ _
  simp [compactNumericVerifierPAAxiomLeafStateGraphDef,
    CompactNumericVerifierPAAxiomLeafStateGraph,
    Semiformula.eval_substs, htransportEnv, hjointEnv, hbridgeEnv,
    htransportSpec, hjointSpec,
    henv14, henv27, henv67, henv247, henv263, henv264]

theorem compactNumericVerifierPAAxiomLeafStateGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierPAAxiomLeafStateGraphDef.val := by
  simp [compactNumericVerifierPAAxiomLeafStateGraphDef]

theorem CompactNumericVerifierPAAxiomLeafStateGraph.sound
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
    {c : CompactNumericVerifierPAAxiomJointLeafCoordinates}
    {proofTokens certificateTokens proofSuffix certificateSuffix
      nextProof nextCertificate actualCandidate actualAxiomTokens : List Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    {actualGamma : List (List Nat)}
    (hgraph : CompactNumericVerifierPAAxiomLeafStateGraph
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
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool c)
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hproofSuffix : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount witnessFinish rootFinish proofSuffix)
    (hcertificateSuffix : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        suffixStart suffixFinish certificateSuffix)
    (hactualGamma : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) rootGammaFinish actualGamma)
    (hactualCandidate : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount
        rootGammaFinish firstFinish actualCandidate)
    (hactualAxiom : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        axiomStart axiomFinish actualAxiomTokens)
    (hnextProof : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextProofFinish nextProof)
    (hnextCertificate : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        nextProofFinish nextCertificateFinish nextCertificate)
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
    ∃ candidate : LO.FirstOrder.ArithmeticSentence,
    ∃ certificate : PAAxiomCertificate,
      actualCandidate = compactSentenceTokens candidate ∧
      actualAxiomTokens = compactPAAxiomCertificateTokens certificate ∧
      proofTag = 1 ∧ certificateTag = 1 ∧
      resultBool = compactAdditiveBoolTag
        (compactAxmRuleCheck (actualGamma, (actualCandidate, actualAxiomTokens))) ∧
      (∃ parsed, compactNumericParsePayload
        ((proofTokens, certificateTokens), (sourceTasks.drop 1, sourceValues)) =
          some parsed) ∧
      nextProof = proofSuffix ∧ nextCertificate = certificateSuffix ∧
      targetTasks = sourceTasks.drop 1 ∧
      targetValues =
        (actualGamma,
          compactAxmRuleCheck (actualGamma, (actualCandidate, actualAxiomTokens))) ::
            sourceValues ∧
      nextTaskTableWidth = currentTaskTableWidth ∧
      nextTaskValueBound = currentTaskValueBound ∧
      nextValueTableWidth = currentValueTableWidth ∧
      nextValueValueBound = currentValueValueBound ∧ nextStatusTag = 0 := by
  have htransport := hgraph.1
  have hrows := hgraph.2.1
  have hbridge := hgraph.2.2.1
  have hproofBinding := hgraph.2.2.2.1
  have hcertificateBinding := hgraph.2.2.2.2.1
  have hresultBinding := hgraph.2.2.2.2.2
  have hcProofTag : c.proofTag = 1 := hrows.2.2.2.2.1
  have hproofTagOne : proofTag = 1 := hproofBinding.trans hcProofTag
  rcases
      CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph.realize_pa_leaf_fields
        htransport.1 hproofTagOne with
    ⟨_proofInput, _root, parsedCandidate, parsedCertificate,
      _certificateInput, parsedAxiomTokens, _parsedCertificateSuffix,
      _hproofInput, _hroot, _hproofParser, _hrootTag,
      _hparsedGamma, hparsedCandidate, _hrootCandidate,
      _hcertificateInput, hparsedAxiom, _hparsedCertificateSuffix,
      _hcertificateParser, hparsedAxiomTokens, hcertificateTagOne⟩
  have hactualCandidateTyped :
      actualCandidate = compactSentenceTokens parsedCandidate :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hactualCandidate hparsedCandidate).1.symm
  have hactualAxiomTyped :
      actualAxiomTokens = compactPAAxiomCertificateTokens parsedCertificate := by
    have hactualParsed : actualAxiomTokens = parsedAxiomTokens :=
      (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
        hactualAxiom hparsedAxiom).1.symm
    exact hactualParsed.trans hparsedAxiomTokens
  rcases CompactNumericVerifierPAAxiomJointLeafRows.sound hrows with
    ⟨ruleGamma, ruleCandidate, ruleCertificate, _endpointInput,
      _endpointSuffix, _hgammaCount, _hcandidateCount, _haxiomCount,
      hruleGamma, _hruleGammaRows, hruleCandidate, hruleAxiom,
      _hendpointAxiom, _hendpointInput, _hendpointSuffix,
      _hendpointParser, hruleResult⟩
  rcases CompactNumericVerifierPAAxiomLeafCrossTableBridgeGraph.sound
      hbridge hactualGamma hruleGamma hactualCandidate hruleCandidate
        hactualAxiom hruleAxiom with
    ⟨hruleGammaEq, hruleCandidateEq, hruleAxiomEq⟩
  have hresult : resultBool = compactAdditiveBoolTag
      (compactAxmRuleCheck
        (actualGamma, (actualCandidate, actualAxiomTokens))) := by
    calc
      resultBool = c.resultBool := hresultBinding
      _ = compactAdditiveBoolTag
          (compactAxmRuleCheck
            (ruleGamma,
              (ruleCandidate, compactPAAxiomCertificateTokens ruleCertificate))) :=
        hruleResult
      _ = compactAdditiveBoolTag
          (compactAxmRuleCheck
            (actualGamma, (actualCandidate, actualAxiomTokens))) := by
        rw [hruleGammaEq, hruleCandidateEq, hruleAxiomEq]
  have htransportResult : CompactNumericVerifierLeafParseSuccessTransportGraph
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
      (compactAdditiveBoolTag
        (compactAxmRuleCheck
          (actualGamma, (actualCandidate, actualAxiomTokens)))) := by
    rw [← hresult]
    exact htransport
  have htransportSound :=
    CompactNumericVerifierLeafParseSuccessTransportGraph.sound
      htransportResult hproofLayout hcertificateLayout hproofSuffix
      hcertificateSuffix hactualGamma hnextProof hnextCertificate
      hsourceTaskRows htargetTaskRows hsourceValueRows htargetValueRows
  exact ⟨parsedCandidate, parsedCertificate, hactualCandidateTyped,
    hactualAxiomTyped, hproofTagOne, hcertificateTagOne, hresult,
    htransportSound⟩

theorem exists_compactNumericVerifierPAAxiomLeafStateGraph_of_success_and_transition
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
    {certificateNode : CompactNumericCertificateNode}
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens = some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser certificateTokens =
      some certificateNode)
    (hproofTag : proofNode.1 = 1)
    (htransition : compactNumericNodeTransition proofNode certificateNode
      (sourceTasks.drop 1) sourceValues =
        some ((nextProof, nextCertificate), (targetTasks, targetValues)))
    (hnextProof : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextProofFinish nextProof)
    (hnextCertificate : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        nextProofFinish nextCertificateFinish nextCertificate)
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
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize,
    ∃ targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize,
    ∃ c : CompactNumericVerifierPAAxiomJointLeafCoordinates,
      CompactNumericVerifierPAAxiomLeafStateGraph
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
        (compactAdditiveBoolTag
          (compactAxmRuleCheck
            (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1)))) c := by
  have houtputCase :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode (sourceTasks.drop 1) sourceValues
      ((nextProof, nextCertificate), (targetTasks, targetValues))).1 htransition
  have hpaOutput :
      certificateNode.1 = 1 ∧
      ((proofNode.2.2.2.2.2, certificateNode.2.2),
        (sourceTasks.drop 1,
          (proofNode.2.1,
            compactAxmRuleCheck
              (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1))) ::
              sourceValues)) =
        ((nextProof, nextCertificate), (targetTasks, targetValues)) := by
    simpa [CompactNumericNodeTransitionOutputCase, hproofTag,
      compactNumericNodeFieldsSuffix] using houtputCase
  rcases hpaOutput with ⟨_hcertificateNodeTag, houtput⟩
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
      (proofNode.2.1,
        compactAxmRuleCheck
          (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1))) ::
        sourceValues := by
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
    ⟨decodedProofTokens, decodedRoot, hdecodedProofLayout,
      _hdecodedRootLayout, hdecodedProof, hdecodedTag⟩
  have hdecodedProofTokensEq : decodedProofTokens = proofTokens :=
    hsuccess.1.1.natListValues_eq hproofLayout hdecodedProofLayout
  subst decodedProofTokens
  have hdecodedRootEq : decodedRoot = proofNode :=
    Option.some.inj (hdecodedProof.symm.trans hproofParser)
  subst decodedRoot
  have hproofTagCoordinate : proofTag = 1 := hdecodedTag.symm.trans hproofTag
  rcases
      CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph.realize_pa_leaf_fields
        hsuccess hproofTagCoordinate with
    ⟨parsedProofInput, parsedRoot, candidate, certificate,
      parsedCertificateInput, axiomTokens, parsedCertificateSuffix,
      hparsedProofInput, _hparsedRoot, hparsedProofParser, _hparsedRootTag,
      hparsedGamma, hparsedCandidate, hparsedRootCandidate,
      hparsedCertificateInput, hparsedAxiom, _hparsedCertificateSuffix,
      hparsedCertificateParser, hparsedAxiomTokens, hcertificateTagCoordinate⟩
  have hparsedProofInputEq : parsedProofInput = proofTokens :=
    hsuccess.1.1.natListValues_eq hproofLayout hparsedProofInput
  subst parsedProofInput
  have hparsedRootEq : parsedRoot = proofNode :=
    Option.some.inj (hparsedProofParser.symm.trans hproofParser)
  subst parsedRoot
  have hparsedCertificateInputEq : parsedCertificateInput = certificateTokens :=
    hsuccess.1.2.1.natListValues_eq hcertificateLayout hparsedCertificateInput
  subst parsedCertificateInput
  have hcertificateNodeEq :
      (1, (axiomTokens, parsedCertificateSuffix)) = certificateNode :=
    Option.some.inj (hparsedCertificateParser.symm.trans hcertificateParser)
  have hcertificateAxiom : axiomTokens = certificateNode.2.1 := by
    simpa using congrArg (fun node : CompactNumericCertificateNode => node.2.1)
      hcertificateNodeEq
  have hcertificateAxiomTyped :
      certificateNode.2.1 = compactPAAxiomCertificateTokens certificate :=
    hcertificateAxiom.symm.trans hparsedAxiomTokens
  rcases CompactNumericVerifierPAAxiomJointLeafRows.exists_canonical
      proofNode.2.1 candidate certificate with ⟨c, hcanonical⟩
  have hparsedAxiomTyped : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
      axiomStart axiomFinish (compactPAAxiomCertificateTokens certificate) := by
    simpa [hparsedAxiomTokens] using hparsedAxiom
  have hbridge := CompactNumericVerifierPAAxiomLeafCrossTableBridgeGraph.of_layouts
    hparsedGamma hcanonical.2.2.1 hparsedCandidate hcanonical.2.2.2.1
    hparsedAxiomTyped hcanonical.2.2.2.2.1
  have hcProofTag : c.proofTag = 1 := hcanonical.1.2.2.2.2.1
  have hcCertificateTag : c.certificateTag = 1 := by
    rcases hcanonical.1.2.2.2.2.2 with hfixedOrSymbol | hinduction
    · rcases hfixedOrSymbol with hfixed | hsymbol
      · exact hfixed.1.2.2.2.2.1
      · exact hsymbol.1.2.2.2.2.1
    · exact hinduction.1.2.2.2.1
  have hproofBinding : proofTag = c.proofTag :=
    hproofTagCoordinate.trans hcProofTag.symm
  have hcertificateBinding : certificateTag = c.certificateTag :=
    hcertificateTagCoordinate.trans hcCertificateTag.symm
  have hresultBinding :
      compactAdditiveBoolTag
          (compactAxmRuleCheck
            (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1))) =
        c.resultBool := by
    symm
    simpa [hparsedRootCandidate, hcertificateAxiomTyped] using hcanonical.2.1
  have hfull : CompactNumericVerifierPAAxiomLeafStateGraph
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
      (compactAdditiveBoolTag
        (compactAxmRuleCheck
          (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1)))) c :=
    ⟨htransport, hcanonical.1, hbridge, hproofBinding,
      hcertificateBinding, hresultBinding⟩
  exact ⟨proofTable, proofWidth, proofTokenCount, proofInputStart,
    proofInputFinish, rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    rootGammaBoundarySize,
    targetStart, targetFinish, targetGammaFinish, targetGammaCount,
    targetGammaBoundary, targetBool, targetGammaBoundarySize, c, hfull⟩

#print axioms compactNumericVerifierPAAxiomLeafStateGraphDef_spec
#print axioms compactNumericVerifierPAAxiomLeafStateGraphDef_sigmaZero
#print axioms CompactNumericVerifierPAAxiomLeafStateGraph.sound
#print axioms
  exists_compactNumericVerifierPAAxiomLeafStateGraph_of_success_and_transition

end FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraph
