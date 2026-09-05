import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointDirectSyntax
import integration.FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedProof
import integration.FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectCompilerBounds
import integration.FoundationCompactNumericListedDirectFixedClosedToEmptyResourceBound

/-! # The three witness-row leaves and trace leaf of the sequent endpoint -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 240000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointWitnessTraceLeaves

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointDirectSyntax
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedProof
open FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectCompilerBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectFixedClosedToEmptyResourceBound
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

structure CompactSequentFormulaEndpointWitnessTraceLeaves
    (tokenTable width tokenCount inputStart inputFinish finalStart finalFinish
      numericBound bitBound : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) where
  inputRows : FixedResourceEmptyContextProof
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      inputStart coordinates.inputCount inputFinish coordinates.inputBoundary
      coordinates.inputBoundarySize)
    (compactNatListWitnessRowsFullyFixedPayloadPolynomial numericBound bitBound)
  firstRows : FixedResourceEmptyContextProof
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      coordinates.firstStart coordinates.firstCount coordinates.firstFinish
      coordinates.firstBoundary coordinates.firstBoundarySize)
    (compactNatListWitnessRowsFullyFixedPayloadPolynomial numericBound bitBound)
  finalRows : FixedResourceEmptyContextProof
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      finalStart coordinates.finalCount finalFinish coordinates.finalBoundary
      coordinates.finalBoundarySize)
    (compactNatListWitnessRowsFullyFixedPayloadPolynomial numericBound bitBound)
  trace : FixedResourceEmptyContextProof
    (compactSequentFormulaTraceBoundedDirectClosedFormula tokenTable width
      tokenCount coordinates.suffixBoundary coordinates.suffixCount
      coordinates.valueBoundary coordinates.valueCount
      coordinates.traceTableWidth coordinates.traceValueBound)
    (compactSequentFormulaTraceBoundedDirectPayloadEnvelope tokenTable width
      tokenCount coordinates.suffixBoundary coordinates.suffixCount
      coordinates.valueBoundary coordinates.valueCount
      coordinates.traceTableWidth coordinates.traceValueBound)

noncomputable def compactSequentFormulaEndpointWitnessTraceLeavesOfGraph
    (tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
      finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates)
    (numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hinputCount : coordinates.inputCount <= numericBound)
    (hfirstCount : coordinates.firstCount <= numericBound)
    (hfinalCount : coordinates.finalCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hinputBoundarySize : Nat.size coordinates.inputBoundary <= bitBound)
    (hfirstBoundarySize : Nat.size coordinates.firstBoundary <= bitBound)
    (hfinalBoundarySize : Nat.size coordinates.finalBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hgraph : CompactSequentFormulaEndpointGraph tokenTable width tokenCount
      inputStart inputFinish valueStart valueFinish finalStart finalFinish
      coordinates) :
    CompactSequentFormulaEndpointWitnessTraceLeaves tokenTable width tokenCount
      inputStart inputFinish finalStart finalFinish numericBound bitBound
      coordinates := by
  rcases hgraph with
    ⟨hinput, hfirst, hfinal, htrace, _, _, _, _, _, _, _, _⟩
  let inputBound := compactNatListWitnessRowsFullyFixedBound tokenTable width
    tokenCount inputStart coordinates.inputCount inputFinish
    coordinates.inputBoundary coordinates.inputBoundarySize numericBound
    bitBound hinput hwidth htokenCount hinputCount htokenTableSize
    hinputBoundarySize hnumericSize
  let firstBound := compactNatListWitnessRowsFullyFixedBound tokenTable width
    tokenCount coordinates.firstStart coordinates.firstCount
    coordinates.firstFinish coordinates.firstBoundary
    coordinates.firstBoundarySize numericBound bitBound hfirst hwidth
    htokenCount hfirstCount htokenTableSize hfirstBoundarySize hnumericSize
  let finalBound := compactNatListWitnessRowsFullyFixedBound tokenTable width
    tokenCount finalStart coordinates.finalCount finalFinish
    coordinates.finalBoundary coordinates.finalBoundarySize numericBound
    bitBound hfinal hwidth htokenCount hfinalCount htokenTableSize
    hfinalBoundarySize hnumericSize
  let traceProof := compileCompactSequentFormulaTraceBoundedDirectClosed
    tokenTable width tokenCount coordinates.suffixBoundary
    coordinates.suffixCount coordinates.valueBoundary coordinates.valueCount
    coordinates.traceTableWidth coordinates.traceValueBound htrace
  exact
    { inputRows :=
        fixedResourceEmptyContextProofOfClosedDirectFormulaBound inputBound
      firstRows :=
        fixedResourceEmptyContextProofOfClosedDirectFormulaBound firstBound
      finalRows :=
        fixedResourceEmptyContextProofOfClosedDirectFormulaBound finalBound
      trace :=
        { proof := traceProof
          payloadLength_le :=
            compileCompactSequentFormulaTraceBoundedDirectClosed_payloadLength_le
              tokenTable width tokenCount coordinates.suffixBoundary
              coordinates.suffixCount coordinates.valueBoundary
              coordinates.valueCount coordinates.traceTableWidth
              coordinates.traceValueBound htrace } }

#print axioms compactSequentFormulaEndpointWitnessTraceLeavesOfGraph

end FoundationCompactNumericListedDirectSequentFormulaEndpointWitnessTraceLeaves
