import integration.FoundationCompactNumericListedDirectVerifierParseStateFormula

/-!
# Public bounds for successful non-leaf schedules

Each scheduled task is exposed through `CompactNumericVerifierTaskBoundedAt`.
Its fourteen coordinates are therefore bounded by the current state's public
task value bound.  The one-parse branch additionally requires its deliberately
unused middle schedule to be supplied with a pointwise bound; the canonical
parse-step constructor supplies the all-zero schedule there.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafPublicBounds

open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedAtFormula
open FoundationCompactNumericListedDirectVerifierParseScheduleRows
open FoundationCompactNumericListedDirectVerifierOneParseSuccessNonLeafStateGraph
open FoundationCompactNumericListedDirectVerifierTwoParseSuccessNonLeafStateGraph
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateCoordinates

theorem compactNumericVerifierTaskScheduleEnvironment_size_le_of_boundedAt
    {tokenTable width tokenCount taskBoundary valueBound rowIndex bound : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hat : CompactNumericVerifierTaskBoundedAt
      tokenTable width tokenCount taskBoundary valueBound rowIndex
      coordinates sizeWitness)
    (hvalueBound : Nat.size valueBound <= bound)
    (coordinate : Fin 14) :
    Nat.size
        (compactNumericVerifierTaskScheduleEnvironment
          coordinates sizeWitness coordinate) <= bound := by
  rcases hat with
    ⟨hstart, hfinish, htag, hgammaFinish, hgammaCount, hgammaBoundary,
      hfirstFinish, hfirstCount, hsecondFinish, hsecondCount,
      hwitnessFinish, hwitnessCount, hsuffixCount, hgammaBoundarySize,
      _hstartEntry, _hfinishEntry, _hcore⟩
  have hsize {value : Nat} (hvalue : value <= valueBound) :
      Nat.size value <= bound :=
    (Nat.size_le_size hvalue).trans hvalueBound
  fin_cases coordinate <;>
    simp [compactNumericVerifierTaskScheduleEnvironment] <;>
    apply hsize <;>
    assumption

private theorem natSize_vecAppend_le
    {leftLength rightLength totalLength bound : Nat}
    (length_eq : totalLength = leftLength + rightLength)
    (left : Fin leftLength -> Nat) (right : Fin rightLength -> Nat)
    (hleft : forall coordinate, Nat.size (left coordinate) <= bound)
    (hright : forall coordinate, Nat.size (right coordinate) <= bound)
    (coordinate : Fin totalLength) :
    Nat.size (Matrix.vecAppend length_eq left right coordinate) <= bound := by
  rw [Matrix.vecAppend_eq_ite]
  dsimp only
  split_ifs with hcoordinate
  · exact hleft ⟨coordinate, hcoordinate⟩
  · exact hright ⟨coordinate - leftLength, by omega⟩

variable
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
    gammaBoundarySize
    sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
    sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
    currentTaskTableWidth currentTaskValueBound
    currentValueTableWidth currentValueValueBound
    nextTaskTableWidth nextTaskValueBound
    nextValueTableWidth nextValueValueBound
    nextStart nextProofFinish nextCertificateFinish nextStatusTag bound : Nat}
  {firstParseCoordinates secondParseCoordinates combineCoordinates :
    CompactNumericVerifierTaskRowCoordinates}
  {firstParseSize secondParseSize combineSize :
    CompactNumericVerifierTaskSizeWitness}

theorem compactNumericVerifierParseNonLeafEnvironment_size_le_of_two
    (hgraph : CompactNumericVerifierTwoParseSuccessNonLeafStateGraph
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
      gammaBoundarySize
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      firstParseCoordinates secondParseCoordinates combineCoordinates
      firstParseSize secondParseSize combineSize)
    (hvalueBound : Nat.size currentTaskValueBound <= bound)
    (coordinate : Fin 42) :
    Nat.size
        (compactNumericVerifierParseNonLeafEnvironment
          firstParseCoordinates secondParseCoordinates combineCoordinates
          firstParseSize secondParseSize combineSize coordinate) <= bound := by
  rcases hgraph.2.2.1 with
    ⟨_tag, _replace, hfirst, _firstShape, hsecond, _secondShape,
      hcombine, _root⟩
  unfold compactNumericVerifierParseNonLeafEnvironment
  apply natSize_vecAppend_le rfl
  · exact compactNumericVerifierTaskScheduleEnvironment_size_le_of_boundedAt
      hfirst hvalueBound
  · apply natSize_vecAppend_le rfl
    · exact compactNumericVerifierTaskScheduleEnvironment_size_le_of_boundedAt
        hsecond hvalueBound
    · exact compactNumericVerifierTaskScheduleEnvironment_size_le_of_boundedAt
        hcombine hvalueBound

theorem compactNumericVerifierParseNonLeafEnvironment_size_le_of_one
    (hgraph : CompactNumericVerifierOneParseSuccessNonLeafStateGraph
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
      gammaBoundarySize
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      firstParseCoordinates combineCoordinates firstParseSize combineSize)
    (hvalueBound : Nat.size currentTaskValueBound <= bound)
    (hsecond : forall coordinate : Fin 14,
      Nat.size
        (compactNumericVerifierTaskScheduleEnvironment
          secondParseCoordinates secondParseSize coordinate) <= bound)
    (coordinate : Fin 42) :
    Nat.size
        (compactNumericVerifierParseNonLeafEnvironment
          firstParseCoordinates secondParseCoordinates combineCoordinates
          firstParseSize secondParseSize combineSize coordinate) <= bound := by
  rcases hgraph.2.2.1 with
    ⟨_tag, _replace, hfirst, _firstShape, hcombine, _root⟩
  unfold compactNumericVerifierParseNonLeafEnvironment
  apply natSize_vecAppend_le rfl
  · exact compactNumericVerifierTaskScheduleEnvironment_size_le_of_boundedAt
      hfirst hvalueBound
  · apply natSize_vecAppend_le rfl
    · exact hsecond
    · exact compactNumericVerifierTaskScheduleEnvironment_size_le_of_boundedAt
        hcombine hvalueBound

#print axioms
  compactNumericVerifierTaskScheduleEnvironment_size_le_of_boundedAt
#print axioms compactNumericVerifierParseNonLeafEnvironment_size_le_of_two
#print axioms compactNumericVerifierParseNonLeafEnvironment_size_le_of_one

end FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafPublicBounds
