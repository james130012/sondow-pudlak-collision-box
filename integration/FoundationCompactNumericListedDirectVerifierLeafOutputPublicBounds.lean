import integration.FoundationCompactNumericListedDirectVerifierParseStateFormula

/-!
# Public bounds for the parsed-leaf output row

The successful leaf transport exposes eight output coordinates.  Seven are
bounded directly by the target state's child-result value bound; the eighth is
the same Boolean result.  Thus this block needs no additional size oracle.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierLeafOutputPublicBounds

open FoundationCompactNumericListedDirectChildResultBoundedRowExposedFormula
open FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportRows
open FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportGraph
open FoundationCompactNumericListedDirectVerifierParseStateFormula

structure CompactNumericVerifierLeafOutputCoordinateBounds
    (targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool
      bound : Nat) : Prop where
  targetStart : Nat.size targetStart <= bound
  targetFinish : Nat.size targetFinish <= bound
  targetGammaFinish : Nat.size targetGammaFinish <= bound
  targetGammaCount : Nat.size targetGammaCount <= bound
  targetGammaBoundary : Nat.size targetGammaBoundary <= bound
  targetBool : Nat.size targetBool <= bound
  targetGammaBoundarySize : Nat.size targetGammaBoundarySize <= bound
  resultBool : Nat.size resultBool <= bound

theorem
    CompactNumericVerifierLeafParseSuccessTransportGraph.leafOutputCoordinateBounds
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
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool
      bound : Nat}
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
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool)
    (hvalueBound : Nat.size nextValueValueBound <= bound) :
    CompactNumericVerifierLeafOutputCoordinateBounds
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool bound := by
  rcases hgraph.2.2.2.1 with
    ⟨hstart, hfinish, hgammaFinish, hgammaCount, hgammaBoundary,
      hbool, hgammaBoundarySize, _hstartEntry, _hfinishEntry, _hcore⟩
  have hsize {value : Nat} (hvalue : value <= nextValueValueBound) :
      Nat.size value <= bound :=
    (Nat.size_le_size hvalue).trans hvalueBound
  have hresult : targetBool = resultBool := hgraph.2.2.2.2.2.1
  exact
    { targetStart := hsize hstart
      targetFinish := hsize hfinish
      targetGammaFinish := hsize hgammaFinish
      targetGammaCount := hsize hgammaCount
      targetGammaBoundary := hsize hgammaBoundary
      targetBool := hsize hbool
      targetGammaBoundarySize := hsize hgammaBoundarySize
      resultBool := by simpa [hresult] using hsize hbool }

theorem compactNumericVerifierParseLeafOutputEnvironment_size_le
    {targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool
      bound : Nat}
    (hbounds : CompactNumericVerifierLeafOutputCoordinateBounds
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool bound)
    (coordinate : Fin 8) :
    Nat.size
        (compactNumericVerifierParseLeafOutputEnvironment
          targetStart targetFinish targetGammaFinish targetGammaCount
          targetGammaBoundary targetBool targetGammaBoundarySize resultBool
          coordinate) <= bound := by
  rcases hbounds with
    ⟨hstart, hfinish, hgammaFinish, hgammaCount, hgammaBoundary,
      hbool, hgammaBoundarySize, hresult⟩
  fin_cases coordinate <;>
    simp [compactNumericVerifierParseLeafOutputEnvironment] <;>
    assumption

#print axioms
  CompactNumericVerifierLeafParseSuccessTransportGraph.leafOutputCoordinateBounds
#print axioms compactNumericVerifierParseLeafOutputEnvironment_size_le

end FoundationCompactNumericListedDirectVerifierLeafOutputPublicBounds
