import integration.FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesFormula
import integration.FoundationCompactNumericListedDirectVerifierTaskFieldRealization

/-!
# Parse-payload success with public proof-root task fields

This extends the separated-table parse-payload success graph with the public
verifier-task coordinates realized by a successful proof root.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesFormula

def CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph
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
      gammaBoundarySize : Nat) : Prop :=
  CompactNumericParsePayloadSuccessSeparatedTablesGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound ∧
    CompactNumericVerifierTaskCoreGraph proofTable proofWidth proofTokenCount
      (compactNumericVerifierTaskRowCoordinatesOf
        rootStart rootFinish proofTag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount witnessFinish
        witnessCount suffixCount)
      { gammaBoundarySize := gammaBoundarySize }

def compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef :
    𝚺₀.Semisentence 40 := .mkSigma
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
      gammaBoundarySize.
    !(compactNumericParsePayloadSuccessSeparatedTablesGraphDef)
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound ∧
    !(compactNumericVerifierTaskCoreGraphDef)
      proofTable proofWidth proofTokenCount rootStart rootFinish proofTag
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize”

def compactNumericParsePayloadSuccessExposedSeparatedTablesGraphEnvironment
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
      gammaBoundarySize : Nat) : Fin 40 → Nat :=
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
    gammaBoundarySize]

@[simp] theorem compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef_spec
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
      gammaBoundarySize : Nat) :
    compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef.val.Evalb
        (compactNumericParsePayloadSuccessExposedSeparatedTablesGraphEnvironment
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
          gammaBoundarySize) ↔
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
        gammaBoundarySize := by
  let env := compactNumericParsePayloadSuccessExposedSeparatedTablesGraphEnvironment
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
  change compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef.val.Evalb env ↔ _
  have hsuccessEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2, #3, #4, #5, #6,
          #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23, #24, #25, #26, #27, #28]) =
        ![stateTable, stateWidth, stateTokenCount,
          stateProofStart, stateProofFinish,
          stateCertificateStart, stateCertificateFinish,
          proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
          rootStart, rootFinish, proofTag, proofEndpointBound,
          certificateTable, certificateWidth, certificateTokenCount,
          certificateInputStart, certificateInputFinish,
          axiomStart, axiomFinish, formulaStart, formulaFinish,
          suffixStart, suffixFinish, certificateTag, certificateEndpointBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcoreEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#7 : Semiterm ℒₒᵣ Empty 40), #8, #9, #12, #13, #14,
          #29, #30, #31, #32, #33, #34, #35, #36, #37, #38, #39]) =
        ![proofTable, proofWidth, proofTokenCount, rootStart, rootFinish,
          proofTag, gammaFinish, gammaCount, gammaBoundary, firstFinish,
          firstCount, secondFinish, secondCount, witnessFinish, witnessCount,
          suffixCount, gammaBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcore :
      (Semiformula.Eval
          ![proofTable, proofWidth, proofTokenCount, rootStart, rootFinish,
            proofTag, gammaFinish, gammaCount, gammaBoundary, firstFinish,
            firstCount, secondFinish, secondCount, witnessFinish, witnessCount,
            suffixCount, gammaBoundarySize]
          Empty.elim) compactNumericVerifierTaskCoreGraphDef.val ↔
      CompactNumericVerifierTaskCoreGraph proofTable proofWidth proofTokenCount
        (compactNumericVerifierTaskRowCoordinatesOf
          rootStart rootFinish proofTag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount witnessFinish
          witnessCount suffixCount)
        { gammaBoundarySize := gammaBoundarySize } := by
    simpa [compactNumericVerifierTaskCoreFormulaEnvironment] using
      (compactNumericVerifierTaskCoreGraphDef_spec
        proofTable proofWidth proofTokenCount rootStart rootFinish proofTag
        gammaFinish gammaCount gammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        gammaBoundarySize)
  have hsuccess :
      (Semiformula.Eval
          ![stateTable, stateWidth, stateTokenCount,
            stateProofStart, stateProofFinish,
            stateCertificateStart, stateCertificateFinish,
            proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
            rootStart, rootFinish, proofTag, proofEndpointBound,
            certificateTable, certificateWidth, certificateTokenCount,
            certificateInputStart, certificateInputFinish,
            axiomStart, axiomFinish, formulaStart, formulaFinish,
            suffixStart, suffixFinish, certificateTag, certificateEndpointBound]
          Empty.elim) compactNumericParsePayloadSuccessSeparatedTablesGraphDef.val ↔
      CompactNumericParsePayloadSuccessSeparatedTablesGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound := by
    simpa [compactNumericParsePayloadSuccessSeparatedTablesGraphEnvironment] using
      (compactNumericParsePayloadSuccessSeparatedTablesGraphDef_spec
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound)
  simp [compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef,
    CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph,
    compactNumericVerifierTaskRowCoordinatesOf, hsuccessEnv, hcoreEnv, hcore,
    hsuccess]

theorem compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef.val := by
  simp [compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef]

theorem CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph.to_successSeparatedTablesGraph
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
      gammaBoundarySize : Nat}
    (hgraph : CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph
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
      gammaBoundarySize) :
    CompactNumericParsePayloadSuccessSeparatedTablesGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound := hgraph.1

theorem CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph.sound
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
      gammaBoundarySize : Nat}
    {proofTokens certificateTokens : List Nat}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    (hgraph : CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph
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
      gammaBoundarySize)
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens) :
    ∃ parsed, compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = some parsed :=
  hgraph.1.sound hproofLayout hcertificateLayout

theorem CompactNumericParsePayloadSuccessSeparatedTablesGraph.exists_exposed
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat}
    (hgraph : CompactNumericParsePayloadSuccessSeparatedTablesGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound) :
    ∃ gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize,
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
        gammaBoundarySize := by
  rcases hgraph.2.2.1.sound with
    ⟨_input, root, _hinput, hroot, _hparser, hrootTag⟩
  rcases CompactNumericVerifierTaskDirectLayout.toCoreGraph hroot with
    ⟨coordinates, sizeWitness, hstart, hfinish, htag, hcore⟩
  rcases coordinates with
    ⟨start, finish, tag, gammaFinish, gammaCount, gammaBoundary,
      firstFinish, firstCount, secondFinish, secondCount, witnessFinish,
      witnessCount, suffixCount⟩
  rcases sizeWitness with ⟨gammaBoundarySize⟩
  change start = rootStart at hstart
  change finish = rootFinish at hfinish
  change tag = root.1 at htag
  subst start
  subst finish
  have htag' : tag = proofTag := htag.trans hrootTag
  rw [htag'] at hcore
  exact ⟨gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    gammaBoundarySize, hgraph, hcore⟩

theorem exists_compactNumericParsePayloadSuccessExposedSeparatedTablesGraph_of_exists_some
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hparse : ∃ parsed, compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = some parsed) :
    ∃ proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
    ∃ rootStart rootFinish proofTag proofEndpointBound,
    ∃ certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish certificateTag certificateEndpointBound,
    ∃ gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize,
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
        gammaBoundarySize := by
  rcases exists_compactNumericParsePayloadSuccessSeparatedTablesGraph_of_exists_some
      hproofLayout hcertificateLayout hparse with
    ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      hgraph⟩
  rcases
      FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula.CompactNumericParsePayloadSuccessSeparatedTablesGraph.exists_exposed
        hgraph with
    ⟨gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      gammaBoundarySize, hexposed⟩
  exact ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
    rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    gammaBoundarySize, hexposed⟩

#print axioms compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef_spec
#print axioms compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef_sigmaZero
#print axioms CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph.to_successSeparatedTablesGraph
#print axioms CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph.sound
#print axioms CompactNumericParsePayloadSuccessSeparatedTablesGraph.exists_exposed
#print axioms exists_compactNumericParsePayloadSuccessExposedSeparatedTablesGraph_of_exists_some

end FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
