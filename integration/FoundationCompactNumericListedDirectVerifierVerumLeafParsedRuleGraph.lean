import integration.FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
import integration.FoundationCompactNumericListedDirectVerifierVerumLeafRuleRowsCompleteness

/-!
# Parsed verum leaf on the exposed proof-root table

The successful proof-root graph already exposes the exact `Gamma` boundary.
The verum rule therefore runs on that same table and needs no auxiliary copy.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierVerumLeafParsedRuleGraph

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierVerumLeafRuleRows
open FoundationCompactNumericListedDirectVerifierVerumLeafRuleRowsCompleteness

def CompactNumericVerifierVerumLeafParsedRuleGraph
    (stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize resultBool : Nat) : Prop :=
  CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize ∧
    CompactNumericVerifierVerumLeafRuleRows
      proofTable proofWidth proofTokenCount proofTag certificateTag
      gammaBoundary gammaCount resultBool

def compactNumericVerifierVerumLeafParsedRuleGraphDef :
    𝚺₀.Semisentence 41 := .mkSigma
  “stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize resultBool.
    !(compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef)
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize ∧
    !(compactNumericVerifierVerumLeafRuleRowsDef)
      proofTable proofWidth proofTokenCount proofTag certificateTag
      gammaBoundary gammaCount resultBool”

def compactNumericVerifierVerumLeafParsedRuleGraphEnvironment
    (stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize resultBool : Nat) : Fin 41 → Nat :=
  ![stateTable, stateWidth, stateTokenCount,
    stateProofStart, stateProofFinish,
    stateCertificateStart, stateCertificateFinish,
    proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
    rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    gammaBoundarySize, resultBool]

set_option maxRecDepth 32768 in
@[simp] theorem compactNumericVerifierVerumLeafParsedRuleGraphDef_spec
    (stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize resultBool : Nat) :
    compactNumericVerifierVerumLeafParsedRuleGraphDef.val.Evalb
        (compactNumericVerifierVerumLeafParsedRuleGraphEnvironment
          stateTable stateWidth stateTokenCount
          stateProofStart stateProofFinish
          stateCertificateStart stateCertificateFinish
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          gammaFinish gammaCount gammaBoundary firstFinish firstCount
          secondFinish secondCount witnessFinish witnessCount suffixCount
          gammaBoundarySize resultBool) ↔
      CompactNumericVerifierVerumLeafParsedRuleGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        gammaFinish gammaCount gammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        gammaBoundarySize resultBool := by
  let env := compactNumericVerifierVerumLeafParsedRuleGraphEnvironment
    stateTable stateWidth stateTokenCount
    stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
    proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
    rootStart rootFinish proofTag proofEndpointBound
    certificateTable certificateWidth certificateTokenCount
    certificateInputStart certificateInputFinish
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag certificateEndpointBound
    gammaFinish gammaCount gammaBoundary firstFinish firstCount
    secondFinish secondCount witnessFinish witnessCount suffixCount
    gammaBoundarySize resultBool
  change compactNumericVerifierVerumLeafParsedRuleGraphDef.val.Evalb env ↔ _
  have hsuccessEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 41), #1, #2, #3, #4, #5, #6,
          #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23, #24, #25, #26, #27, #28, #29,
          #30, #31, #32, #33, #34, #35, #36, #37, #38, #39]) =
        ![stateTable, stateWidth, stateTokenCount,
          stateProofStart, stateProofFinish,
          stateCertificateStart, stateCertificateFinish,
          proofTable, proofWidth, proofTokenCount, proofInputStart,
          proofInputFinish, rootStart, rootFinish, proofTag, proofEndpointBound,
          certificateTable, certificateWidth, certificateTokenCount,
          certificateInputStart, certificateInputFinish,
          axiomStart, axiomFinish, formulaStart, formulaFinish,
          suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
          gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
          secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
          gammaBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hverumEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#7 : Semiterm ℒₒᵣ Empty 41), #8, #9, #14, #27, #31, #30,
          #40]) =
        ![proofTable, proofWidth, proofTokenCount, proofTag, certificateTag,
          gammaBoundary, gammaCount, resultBool] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsuccess :=
    compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef_spec
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize
  simp only [compactNumericParsePayloadSuccessExposedSeparatedTablesGraphEnvironment]
    at hsuccess
  have hverum := compactNumericVerifierVerumLeafRuleRowsDef_spec
    proofTable proofWidth proofTokenCount proofTag certificateTag
    gammaBoundary gammaCount resultBool
  simp only [compactNumericVerifierVerumLeafParsedRuleGraphDef,
    CompactNumericVerifierVerumLeafParsedRuleGraph]
  apply and_congr
  · refine (Semiformula.eval_substs (b := env) (f := Empty.elim)
      ![(#0 : Semiterm ℒₒᵣ Empty 41), #1, #2, #3, #4, #5, #6,
        #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
        #19, #20, #21, #22, #23, #24, #25, #26, #27, #28, #29,
        #30, #31, #32, #33, #34, #35, #36, #37, #38, #39]
      compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef.val).trans ?_
    rw [hsuccessEnv]
    exact hsuccess
  · refine (Semiformula.eval_substs (b := env) (f := Empty.elim)
      ![(#7 : Semiterm ℒₒᵣ Empty 41), #8, #9, #14, #27, #31, #30,
        #40]
      compactNumericVerifierVerumLeafRuleRowsDef.val).trans ?_
    rw [hverumEnv]
    exact hverum

theorem compactNumericVerifierVerumLeafParsedRuleGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierVerumLeafParsedRuleGraphDef.val := by
  simp [compactNumericVerifierVerumLeafParsedRuleGraphDef]

theorem CompactNumericVerifierVerumLeafParsedRuleGraph.sound
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize resultBool : Nat}
    {proofTokens certificateTokens : List Nat}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    (hgraph : CompactNumericVerifierVerumLeafParsedRuleGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize resultBool)
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens) :
    (∃ parsed, compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = some parsed) ∧
    ∃ root : CompactNumericVerifierTask,
      CompactNumericVerifierTaskDirectLayout
        proofTable proofWidth proofTokenCount rootStart rootFinish root ∧
      root.1 = 2 ∧ certificateTag = 0 ∧
      resultBool = compactAdditiveBoolTag
        (compactVerumRuleCheck root.2.1) := by
  refine ⟨hgraph.1.sound hproofLayout hcertificateLayout, ?_⟩
  have hleaf := CompactNumericVerifierVerumLeafRuleRows.sound
    (coordinates := compactNumericVerifierTaskRowCoordinatesOf
      rootStart rootFinish proofTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount witnessFinish
      witnessCount suffixCount)
    (sizeWitness := { gammaBoundarySize := gammaBoundarySize })
    hgraph.1.2 hgraph.2
  simpa [compactNumericVerifierTaskRowCoordinatesOf] using hleaf

theorem exists_compactNumericVerifierVerumLeafParsedRuleGraph_of_parsers
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {root : CompactNumericVerifierTask}
    {certificateNode : CompactNumericCertificateNode}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens = some root)
    (hcertificateParser :
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode)
    (hrootTag : root.1 = 2)
    (hcertificateTag : certificateNode.1 = 0) :
    ∃ proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
    ∃ rootStart rootFinish proofTag proofEndpointBound,
    ∃ certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish certificateTag certificateEndpointBound,
    ∃ gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize,
      CompactNumericVerifierVerumLeafParsedRuleGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        gammaFinish gammaCount gammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        gammaBoundarySize
        (compactAdditiveBoolTag (compactVerumRuleCheck root.2.1)) := by
  have htagMatch : CompactNumericNodeTransitionTagMatch
      root.1 certificateNode.1 := by
    rw [hrootTag, hcertificateTag]
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  rcases (compactNumericNodeTransition_exists_iff_tagMatch
      root certificateNode restTasks values).2 htagMatch with
    ⟨parsed, htransition⟩
  have hparse : compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = some parsed :=
    (compactNumericParsePayload_eq_some_iff _ _).2
      ⟨root, certificateNode, hproofParser, hcertificateParser, htransition⟩
  rcases
      exists_compactNumericParsePayloadSuccessExposedSeparatedTablesGraph_of_exists_some
        hproofLayout hcertificateLayout ⟨parsed, hparse⟩ with
    ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      gammaBoundarySize, hsuccess⟩
  rcases hsuccess.1.2.2.1.sound with
    ⟨decodedInput, decodedRoot, hdecodedInput, hdecodedRoot,
      hdecodedParser, hdecodedTag⟩
  have hdecodedInputEq : decodedInput = proofTokens :=
    hsuccess.1.1.natListValues_eq hproofLayout hdecodedInput
  subst decodedInput
  have hdecodedRootEq : decodedRoot = root :=
    Option.some.inj (hdecodedParser.symm.trans hproofParser)
  subst decodedRoot
  have hproofTag : proofTag = 2 := hdecodedTag.symm.trans hrootTag
  have hcoordTagMatch := hsuccess.1.2.2.2.2
  have hcertificateTagCoord : certificateTag = 0 := by
    rw [hproofTag] at hcoordTagMatch
    simpa [CompactNumericNodeTransitionTagMatch] using hcoordTagMatch
  rcases CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
      hsuccess.2 with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag,
      hgammaRows, hgammaLength,
      _hfirstLayout, _hfirstLength,
      _hsecondLayout, _hsecondLength,
      _hwitnessLayout, _hwitnessLength,
      _hsuffixLayout, _hsuffixLength⟩
  have hrealizedEq : realizedRoot = root :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hsuccess.2 hdecodedRoot hrealizedRoot
  subst realizedRoot
  have hverum : CompactNumericVerifierVerumLeafRuleRows
      proofTable proofWidth proofTokenCount proofTag certificateTag
      gammaBoundary gammaCount
      (compactAdditiveBoolTag (compactVerumRuleCheck root.2.1)) := by
    have hraw := CompactNumericVerifierVerumLeafRuleRows.of_gammaRows hgammaRows
    simpa only [hproofTag, hcertificateTagCoord, hgammaLength,
      compactNumericVerifierTaskRowCoordinatesOf] using hraw
  exact ⟨proofTable, proofWidth, proofTokenCount, proofInputStart,
    proofInputFinish, rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    gammaBoundarySize, hsuccess, hverum⟩

#print axioms compactNumericVerifierVerumLeafParsedRuleGraphDef_spec
#print axioms compactNumericVerifierVerumLeafParsedRuleGraphDef_sigmaZero
#print axioms CompactNumericVerifierVerumLeafParsedRuleGraph.sound
#print axioms exists_compactNumericVerifierVerumLeafParsedRuleGraph_of_parsers

end FoundationCompactNumericListedDirectVerifierVerumLeafParsedRuleGraph
