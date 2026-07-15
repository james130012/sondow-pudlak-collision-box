import integration.FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula

/-!
# Shared coordinates for successful non-leaf parse states

The first forty coordinates are the exposed separated-table parser graph.
The remaining twenty public coordinates describe the source/target task and
value tables together with the next running payload.  Each scheduled task row
is appended as fourteen coordinates: thirteen row coordinates and one size
witness.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateCoordinates

open FoundationCompactNumericListedDirectVerifierTaskFormula

def compactNumericVerifierParseSuccessNonLeafBaseEnvironment
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
      gammaBoundarySize
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag : Nat) :
    Fin 60 -> Nat :=
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
    gammaBoundarySize,
    sourceTaskBoundary, sourceTaskCount, targetTaskBoundary, targetTaskCount,
    sourceValueBoundary, sourceValueCount, targetValueBoundary, targetValueCount,
    currentTaskTableWidth, currentTaskValueBound,
    currentValueTableWidth, currentValueValueBound,
    nextTaskTableWidth, nextTaskValueBound,
    nextValueTableWidth, nextValueValueBound,
    nextStart, nextProofFinish, nextCertificateFinish, nextStatusTag]

def compactNumericVerifierTaskScheduleEnvironment
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) : Fin 14 -> Nat :=
  ![coordinates.start, coordinates.finish, coordinates.tag,
    coordinates.gammaFinish, coordinates.gammaCount,
    coordinates.gammaBoundary, coordinates.firstFinish,
    coordinates.firstCount, coordinates.secondFinish,
    coordinates.secondCount, coordinates.witnessFinish,
    coordinates.witnessCount, coordinates.suffixCount,
    sizeWitness.gammaBoundarySize]

end FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateCoordinates
