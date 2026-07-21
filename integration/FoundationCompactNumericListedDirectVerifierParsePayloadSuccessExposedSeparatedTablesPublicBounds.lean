import integration.FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
import integration.FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesPublicBounds

/-!
# Public bounds for all exposed successful-parse coordinates

The successful parser graph first exposes twenty-nine state and parser
coordinates.  Its proof-root task contributes eleven more coordinates.  The
proof-root constructor already gives a numeric token-count bound; this file
uses that fact to control the task boundary table without an exponential
conversion from bit length.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula

def compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound
    (stateBound proofWeight certificateWeight : Nat) : Nat :=
  let baseBound :=
    compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  baseBound + (baseBound + 1) * baseBound + 2

structure CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
    (gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize bound : Nat) : Prop where
  gammaFinish : Nat.size gammaFinish <= bound
  gammaCount : Nat.size gammaCount <= bound
  gammaBoundary : Nat.size gammaBoundary <= bound
  firstFinish : Nat.size firstFinish <= bound
  firstCount : Nat.size firstCount <= bound
  secondFinish : Nat.size secondFinish <= bound
  secondCount : Nat.size secondCount <= bound
  witnessFinish : Nat.size witnessFinish <= bound
  witnessCount : Nat.size witnessCount <= bound
  suffixCount : Nat.size suffixCount <= bound
  gammaBoundarySize : Nat.size gammaBoundarySize <= bound

private theorem nat_size_le_self_exposed (value : Nat) :
    Nat.size value <= value := by
  rw [Nat.size_le]
  exact value.lt_two_pow_self

theorem
    CompactNumericParsePayloadSuccessSeparatedTablesStateCoordinateBounds.mono
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish left right : Nat}
    (hbounds :
      CompactNumericParsePayloadSuccessSeparatedTablesStateCoordinateBounds
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish left)
    (hle : left <= right) :
    CompactNumericParsePayloadSuccessSeparatedTablesStateCoordinateBounds
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish right :=
  { stateTable := hbounds.stateTable.trans hle
    stateWidth := hbounds.stateWidth.trans hle
    stateTokenCount := hbounds.stateTokenCount.trans hle
    stateProofStart := hbounds.stateProofStart.trans hle
    stateProofFinish := hbounds.stateProofFinish.trans hle
    stateCertificateStart := hbounds.stateCertificateStart.trans hle
    stateCertificateFinish := hbounds.stateCertificateFinish.trans hle }

theorem
    CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds.mono
    {proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      left right : Nat}
    (hbounds :
      CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound left)
    (hle : left <= right) :
    CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound right :=
  { proofTable := hbounds.proofTable.trans hle
    proofWidth_value := hbounds.proofWidth_value.trans hle
    proofWidth := hbounds.proofWidth.trans hle
    proofTokenCount_value := hbounds.proofTokenCount_value.trans hle
    proofTokenCount := hbounds.proofTokenCount.trans hle
    proofInputStart := hbounds.proofInputStart.trans hle
    proofInputFinish := hbounds.proofInputFinish.trans hle
    rootStart := hbounds.rootStart.trans hle
    rootFinish := hbounds.rootFinish.trans hle
    proofTag := hbounds.proofTag.trans hle
    proofEndpointBound := hbounds.proofEndpointBound.trans hle
    certificateTable := hbounds.certificateTable.trans hle
    certificateWidth_value := hbounds.certificateWidth_value.trans hle
    certificateWidth := hbounds.certificateWidth.trans hle
    certificateTokenCount_value :=
      hbounds.certificateTokenCount_value.trans hle
    certificateTokenCount := hbounds.certificateTokenCount.trans hle
    certificateInputStart := hbounds.certificateInputStart.trans hle
    certificateInputFinish := hbounds.certificateInputFinish.trans hle
    axiomStart := hbounds.axiomStart.trans hle
    axiomFinish := hbounds.axiomFinish.trans hle
    formulaStart := hbounds.formulaStart.trans hle
    formulaFinish := hbounds.formulaFinish.trans hle
    suffixStart := hbounds.suffixStart.trans hle
    suffixFinish := hbounds.suffixFinish.trans hle
    certificateTag := hbounds.certificateTag.trans hle
    certificateEndpointBound := hbounds.certificateEndpointBound.trans hle }

theorem compactNumericParsePayloadSuccessExposedSeparatedTablesGraphEnvironment_size_le
    {stateTable stateWidth stateTokenCount
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
      gammaBoundarySize bound : Nat}
    (hstate :
      CompactNumericParsePayloadSuccessSeparatedTablesStateCoordinateBounds
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish bound)
    (hparser :
      CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound bound)
    (htask : CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize bound)
    (coordinate : Fin 40) :
    Nat.size
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
          gammaBoundarySize coordinate) <= bound := by
  rcases hstate with
    ⟨hstateTable, hstateWidth, hstateTokenCount,
      hstateProofStart, hstateProofFinish,
      hstateCertificateStart, hstateCertificateFinish⟩
  rcases hparser with
    ⟨hproofTable, hproofWidth, _hproofTokenCountValue, hproofTokenCount,
      hproofInputStart, hproofInputFinish,
      hrootStart, hrootFinish, hproofTag, hproofEndpointBound,
      hcertificateTable, hcertificateWidth, hcertificateTokenCount,
      hcertificateInputStart, hcertificateInputFinish,
      haxiomStart, haxiomFinish, hformulaStart, hformulaFinish,
      hsuffixStart, hsuffixFinish, hcertificateTag,
      hcertificateEndpointBound⟩
  rcases htask with
    ⟨hgammaFinish, hgammaCount, hgammaBoundary,
      hfirstFinish, hfirstCount, hsecondFinish, hsecondCount,
      hwitnessFinish, hwitnessCount, hsuffixCount,
      hgammaBoundarySize⟩
  fin_cases coordinate <;>
    simp [compactNumericParsePayloadSuccessExposedSeparatedTablesGraphEnvironment] <;>
    assumption

set_option maxHeartbeats 2400000 in
theorem
    exists_compactNumericParsePayloadSuccessExposedSeparatedTablesGraph_of_exists_some_with_publicBounds
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish stateBound : Nat}
    {proofTokens certificateTokens : List Nat}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hstateBounds :
      CompactNumericParsePayloadSuccessSeparatedTablesStateCoordinateBounds
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish stateBound)
    (hparse : exists parsed, compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = some parsed) :
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let publicBound :=
      compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    exists proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
    exists rootStart rootFinish proofTag proofEndpointBound,
    exists certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish,
    exists axiomStart axiomFinish formulaStart formulaFinish,
    exists suffixStart suffixFinish certificateTag certificateEndpointBound,
    exists gammaFinish gammaCount gammaBoundary firstFinish firstCount
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
        gammaBoundarySize /\
      CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        publicBound /\
      CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
        gammaFinish gammaCount gammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        gammaBoundarySize publicBound /\
      forall coordinate : Fin 40,
        Nat.size
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
            gammaBoundarySize coordinate) <= publicBound := by
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  let baseBound :=
    compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  let publicBound :=
    compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  have hbaseToPublic : baseBound <= publicBound := by
    dsimp only [baseBound, publicBound,
      compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound]
    omega
  have hstateToBase : stateBound <= baseBound := by
    dsimp only [baseBound,
      compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound]
    omega
  rcases
      exists_compactNumericParsePayloadSuccessSeparatedTablesGraph_of_exists_some_with_publicBounds
        hproofLayout hcertificateLayout hstateBounds hparse with
    ⟨proofTable, proofWidth, proofTokenCount,
      proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      hbaseGraph, hparserBase, _hbaseEnvironment⟩
  rcases
      FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula.CompactNumericParsePayloadSuccessSeparatedTablesGraph.exists_exposed
        hbaseGraph with
    ⟨gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      gammaBoundarySize, hexposed⟩
  have hcoreBounds := hexposed.2.bounds
  have hgammaCountSucc : gammaCount + 1 <= baseBound + 1 := by
    exact Nat.add_le_add_right
      (hcoreBounds.gammaCount_le.trans hparserBase.proofTokenCount_value) 1
  have htaskProduct :
      (gammaCount + 1) * proofTokenCount <=
        (baseBound + 1) * baseBound :=
    Nat.mul_le_mul hgammaCountSucc hparserBase.proofTokenCount_value
  have htaskProductPublic :
      (gammaCount + 1) * proofTokenCount <= publicBound := by
    apply htaskProduct.trans
    dsimp only [publicBound,
      compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound,
      baseBound]
    omega
  have hproofTokenCountPublic : proofTokenCount <= publicBound :=
    hparserBase.proofTokenCount_value.trans hbaseToPublic
  have size_of_le_proofTokenCount {value : Nat}
      (hvalue : value <= proofTokenCount) : Nat.size value <= publicBound :=
    (nat_size_le_self_exposed value).trans
      (hvalue.trans hproofTokenCountPublic)
  have htaskBounds :
      CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
        gammaFinish gammaCount gammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        gammaBoundarySize publicBound :=
    { gammaFinish := size_of_le_proofTokenCount hcoreBounds.gammaFinish_le
      gammaCount := size_of_le_proofTokenCount hcoreBounds.gammaCount_le
      gammaBoundary :=
        hcoreBounds.gammaBoundary_size_le.trans htaskProductPublic
      firstFinish := size_of_le_proofTokenCount hcoreBounds.firstFinish_le
      firstCount := size_of_le_proofTokenCount hcoreBounds.firstCount_le
      secondFinish := size_of_le_proofTokenCount hcoreBounds.secondFinish_le
      secondCount := size_of_le_proofTokenCount hcoreBounds.secondCount_le
      witnessFinish := size_of_le_proofTokenCount hcoreBounds.witnessFinish_le
      witnessCount := size_of_le_proofTokenCount hcoreBounds.witnessCount_le
      suffixCount := size_of_le_proofTokenCount hcoreBounds.suffixCount_le
      gammaBoundarySize :=
        (nat_size_le_self_exposed gammaBoundarySize).trans
          (hcoreBounds.gammaBoundarySize_le.trans htaskProductPublic) }
  have hstatePublic :=
    FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds.CompactNumericParsePayloadSuccessSeparatedTablesStateCoordinateBounds.mono
      hstateBounds (hstateToBase.trans hbaseToPublic)
  have hparserPublic :=
    FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds.CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds.mono
      hparserBase hbaseToPublic
  refine ⟨proofTable, proofWidth, proofTokenCount,
    proofInputStart, proofInputFinish,
    rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    gammaBoundarySize, hexposed, hparserPublic, htaskBounds, ?_⟩
  exact
    compactNumericParsePayloadSuccessExposedSeparatedTablesGraphEnvironment_size_le
      hstatePublic hparserPublic htaskBounds

#print axioms
  compactNumericParsePayloadSuccessExposedSeparatedTablesGraphEnvironment_size_le
#print axioms
  exists_compactNumericParsePayloadSuccessExposedSeparatedTablesGraph_of_exists_some_with_publicBounds

end FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds
