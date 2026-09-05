import integration.FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietRepeatFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietInvalidFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds

/-! # One fully fixed resource for all six formula-transform step branches -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectFormulaTransformStepRowsAllBranchesFullyFixedBounds

open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
open FoundationCompactNumericListedDirectParserSyntaxInvalidFormula
open FoundationCompactNumericListedDirectParserDoneFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietDoneFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietEmptyFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietRepeatFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietInvalidFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStepRowsHeavyBranchesFullyFixedBounds

private abbrev allBranchesZeroValuation : Nat -> Nat :=
  compactFormulaTransformStepRowsZeroValuation

def compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
    (currentOutputCount tokenCount numericBound bitBound : Nat) : Nat :=
  stepRowsQuietDoneFixedPayloadPolynomial numericBound bitBound +
    stepRowsQuietEmptyFixedPayloadPolynomial numericBound bitBound +
    stepRowsQuietRepeatFixedPayloadPolynomial tokenCount numericBound bitBound +
    stepRowsQuietInvalidFixedPayloadPolynomial tokenCount numericBound bitBound +
    stepRowsTermBranchFixedPayloadPolynomial tokenCount numericBound bitBound +
    stepRowsFormulaBranchFixedPayloadPolynomial currentOutputCount tokenCount
      numericBound bitBound

noncomputable def compactFormulaTransformStepRowsFullyFixedBoundFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      numericBound bitBound : Nat)
    (data : CompactFormulaTransformStepRowsCheckedBranchData tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount)
    (hstepEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate) <= bitBound)
    (htermEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode stepWitness.slot0 stepWitness.term.tag
          stepWitness.term.argument consumedCount witnessStart witnessFinish
          witnessCount coordinate) <= bitBound)
    (hformulaEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode stepWitness.formula.tag consumedCount
          mappedHead coordinate) <= bitBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentOutputCount : current.outputCount <= numericBound)
    (hnextOutputCount : next.outputCount <= numericBound)
    (hwitnessCount : witnessCount <= numericBound)
    (hcurrentParserValue :
      CompactUnifiedParserStateCoordinateValueBound current.parser numericBound)
    (hnextParserValue :
      CompactUnifiedParserStateCoordinateValueBound next.parser numericBound)
    (hwitnessValue :
      CompactUnifiedParserSyntaxStepWitnessCoordinateValueBound stepWitness
        numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentParserSize :
      CompactUnifiedParserStateCoordinateSizeBound current.parser bitBound)
    (hnextParserSize :
      CompactUnifiedParserStateCoordinateSizeBound next.parser bitBound)
    (hwitnessSize :
      CompactUnifiedParserSyntaxStepWitnessCoordinateSizeBound stepWitness
        bitBound)
    (hcurrentOutputBoundarySize :
      Nat.size current.outputBoundary <= bitBound)
    (hnextOutputBoundarySize :
      Nat.size next.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound allBranchesZeroValuation
      (compactFormulaTransformStepRowsExplicitFormula tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount)
      (compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
        current.outputCount tokenCount numericBound bitBound) := by
  have hdoneWitnessSize :=
    compactUnifiedParserSyntaxStepDoneWitness_size_le stepWitness bitBound
      hwitnessSize
  have htermWitnessSize :=
    compactUnifiedParserSyntaxStepTermWitness_size_le stepWitness bitBound
      hwitnessSize
  have hrepeatWitnessSize :=
    compactUnifiedParserSyntaxStepRepeatWitness_size_le stepWitness bitBound
      hwitnessSize
  have hrepeatEnvironmentSize :=
    compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf_size_le tokenTable
      width tokenCount current.parser next.parser stepWitness.slot0
      stepWitness.slot1 stepWitness.repeat bitBound htokenTableSize hwidthSize
      htokenCountSize hcurrentParserSize hnextParserSize
      (by
        simpa [compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          hwitnessSize (0 : Fin 7))
      (by
        simpa [compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          hwitnessSize (1 : Fin 7))
      hrepeatWitnessSize
  cases data with
  | quietDone hparser hrows =>
      let proof :=
        compileCompactFormulaTransformStepRowsQuietDoneFullyFixedContext
          tokenTable width tokenCount current next mode stepWitness consumedCount
          mappedHead witnessStart witnessFinish witnessCount numericBound
          bitBound hparser hrows htokenCount
          (by
            simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.done,
              compactUnifiedParserDoneWitnessCoordinatesOf,
              compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
              hwitnessValue (6 : Fin 7))
          (by
            simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.done,
              compactUnifiedParserDoneWitnessCoordinatesOf,
              compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
                hwitnessSize (1 : Fin 7))
          (by
            simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.done,
              compactUnifiedParserDoneWitnessCoordinatesOf,
              compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
                hwitnessSize (4 : Fin 7))
          hnumericSize
      have hproof :=
        compileCompactFormulaTransformStepRowsQuietDoneFullyFixedContext_payloadLength_le
          tokenTable width tokenCount current next mode stepWitness consumedCount
          mappedHead witnessStart witnessFinish witnessCount numericBound
          bitBound hparser hrows hstepEnvironmentSize hwidth htokenCount
          (by
            simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.done,
              compactUnifiedParserDoneWitnessCoordinatesOf,
              compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
              hwitnessValue (6 : Fin 7))
          hcurrentOutputCount hcurrentParserValue hnextParserValue
          htokenTableSize hcurrentParserSize hnextParserSize hdoneWitnessSize
          hcurrentOutputBoundarySize hnextOutputBoundarySize hnumericSize
          hbitPositive
      exact ⟨proof, hproof.trans (by
        unfold compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
        omega)⟩
  | quietEmpty hparser hrows =>
      let proof :=
        compileCompactFormulaTransformStepRowsQuietEmptyFullyFixedContext
          tokenTable width tokenCount current next mode stepWitness consumedCount
          mappedHead witnessStart witnessFinish witnessCount numericBound
          bitBound hparser hrows htokenCount
          (by
            simpa [compactUnifiedParserStateCoordinateValues] using
              hcurrentParserValue (5 : Fin 8))
          (by
            simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.empty,
              compactUnifiedParserEmptyWitnessCoordinatesOf,
              compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
                hwitnessSize (1 : Fin 7))
          hnumericSize
      have hproof :=
        compileCompactFormulaTransformStepRowsQuietEmptyFullyFixedContext_payloadLength_le
          tokenTable width tokenCount current next mode stepWitness consumedCount
          mappedHead witnessStart witnessFinish witnessCount numericBound
          bitBound hparser hrows hstepEnvironmentSize hwidth htokenCount
          hcurrentOutputCount hcurrentParserValue hnextParserValue
          htokenTableSize hcurrentParserSize hnextParserSize
          (by
            simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.empty,
              compactUnifiedParserEmptyWitnessCoordinatesOf,
              compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
                hwitnessSize (1 : Fin 7))
          hcurrentOutputBoundarySize hnextOutputBoundarySize hnumericSize
          hbitPositive
      exact ⟨proof, hproof.trans (by
        unfold compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
        omega)⟩
  | quietRepeat hparser hrows =>
      let certificate :=
        compactFormulaTransformStepRowsQuietRepeatFullyFixedCertificate
          tokenTable width tokenCount current next mode stepWitness consumedCount
          mappedHead witnessStart witnessFinish witnessCount hparser hrows
      have hcertificate :=
        compactFormulaTransformStepRowsQuietRepeatFullyFixedCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next mode stepWitness consumedCount
          mappedHead witnessStart witnessFinish witnessCount numericBound
          bitBound hparser hrows hstepEnvironmentSize hrepeatEnvironmentSize
          hwidth htokenCount
          (by
            simpa [compactUnifiedParserStateCoordinateValues] using
              hcurrentParserValue (3 : Fin 8))
          (by
            simpa [compactUnifiedParserStateCoordinateValues] using
              hnextParserValue (3 : Fin 8))
          (by
            simpa [compactUnifiedParserStateCoordinateValues] using
              hcurrentParserValue (5 : Fin 8))
          (by
            simpa [compactUnifiedParserStateCoordinateValues] using
              hcurrentParserValue (7 : Fin 8))
          (by
            simpa [compactUnifiedParserStateCoordinateValues] using
              hnextParserValue (7 : Fin 8))
          (by
            simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.repeat,
              compactSyntaxRepeatTaskWitnessCoordinatesOf,
              compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
                hwitnessValue (3 : Fin 7))
          hcurrentOutputCount htokenTableSize hwidthSize htokenCountSize
          (by
            simpa [compactUnifiedParserStateCoordinateValues] using
              hcurrentParserSize (3 : Fin 8))
          (by
            simpa [compactUnifiedParserStateCoordinateValues] using
              hcurrentParserSize (1 : Fin 8))
          (by
            simpa [compactUnifiedParserStateCoordinateValues] using
              hnextParserSize (3 : Fin 8))
          (by
            simpa [compactUnifiedParserStateCoordinateValues] using
              hnextParserSize (1 : Fin 8))
          (by
            simpa [compactUnifiedParserStateCoordinateValues] using
              hcurrentParserSize (4 : Fin 8))
          (by
            simpa [compactUnifiedParserStateCoordinateValues] using
              hnextParserSize (4 : Fin 8))
          (by
            simpa [compactUnifiedParserStateCoordinateValues] using
              hcurrentParserSize (6 : Fin 8))
          (by
            simpa [compactUnifiedParserStateCoordinateValues] using
              hnextParserSize (6 : Fin 8))
          (by
            simpa [compactUnifiedParserStateCoordinateValues] using
              hnextParserSize (7 : Fin 8))
          (by
            simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.repeat,
              compactSyntaxRepeatTaskWitnessCoordinatesOf,
              compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
                hwitnessSize (2 : Fin 7))
          (by
            simpa [compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
              hwitnessSize (0 : Fin 7))
          (by
            simpa [compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
              hwitnessSize (1 : Fin 7))
          (by
            simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.repeat,
              compactSyntaxRepeatTaskWitnessCoordinatesOf,
              compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
                hwitnessSize (5 : Fin 7))
          hcurrentOutputBoundarySize hnextOutputBoundarySize hnumericSize
      have hcompile :=
        compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate
      exact ⟨certificate.compile, (hcompile.trans hcertificate).trans (by
        unfold compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
        omega)⟩
  | quietInvalid hparser hrows =>
      let certificate :=
        compactFormulaTransformStepRowsQuietInvalidFullyFixedCertificate
          tokenTable width tokenCount current next mode stepWitness consumedCount
          mappedHead witnessStart witnessFinish witnessCount hparser hrows
      have hcertificate :=
        compactFormulaTransformStepRowsQuietInvalidFullyFixedCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next mode stepWitness consumedCount
          mappedHead witnessStart witnessFinish witnessCount numericBound
          bitBound hparser hrows hstepEnvironmentSize hwidth hwidthBit
          htokenCount hcurrentOutputCount hcurrentParserValue hnextParserValue
          htokenTableSize hcurrentParserSize hnextParserSize
          (by
            simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.invalid,
              compactSyntaxInvalidTaskWitnessCoordinatesOf,
              compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
                hwitnessSize (0 : Fin 7))
          hcurrentOutputBoundarySize hnextOutputBoundarySize hnumericSize
          hbitPositive
      have hcompile :=
        compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate
      exact ⟨certificate.compile, (hcompile.trans hcertificate).trans (by
        unfold compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
        omega)⟩
  | term hparser hrows =>
      let certificate := compactFormulaTransformStepRowsTermFullyFixedCertificate
        tokenTable width tokenCount current next mode stepWitness consumedCount
        mappedHead witnessStart witnessFinish witnessCount hparser hrows
      have hcertificate :=
        compactFormulaTransformStepRowsTermFullyFixedCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next mode stepWitness consumedCount
          mappedHead witnessStart witnessFinish witnessCount numericBound
          bitBound hparser hrows hstepEnvironmentSize htermEnvironmentSize
          hwidth htokenCount hcurrentOutputCount hnextOutputCount hwitnessCount
          hcurrentParserValue hnextParserValue htokenTableSize hwidthSize
          htokenCountSize hcurrentParserSize hnextParserSize
          (by
            simpa [compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
              hwitnessSize (0 : Fin 7))
          htermWitnessSize hnumericSize hbitPositive
      have hcompile :=
        compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate
      exact ⟨certificate.compile, (hcompile.trans hcertificate).trans (by
        unfold compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
        omega)⟩
  | formula hparser hrows =>
      let certificate :=
        compactFormulaTransformStepRowsFormulaFullyFixedCertificate tokenTable
          width tokenCount current next mode stepWitness consumedCount mappedHead
          witnessStart witnessFinish witnessCount hparser hrows
      have hcertificate :=
        compactFormulaTransformStepRowsFormulaFullyFixedCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next mode stepWitness consumedCount
          mappedHead witnessStart witnessFinish witnessCount numericBound
          bitBound hparser hrows hstepEnvironmentSize hformulaEnvironmentSize
          hwidth htokenCount hcurrentOutputCount hcurrentParserValue
          hnextParserValue htokenTableSize hcurrentParserSize hnextParserSize
          (by
            simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.formula,
              compactSyntaxFormulaTaskWitnessCoordinatesOf,
              compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
                hwitnessSize (1 : Fin 7))
          (by
            simpa [compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
              hwitnessSize (0 : Fin 7))
          (by
            simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.formula,
              compactSyntaxFormulaTaskWitnessCoordinatesOf,
              compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
                hwitnessSize (5 : Fin 7))
          (by
            simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.formula,
              compactSyntaxFormulaTaskWitnessCoordinatesOf,
              compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
                hwitnessSize (6 : Fin 7))
          (by
            simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.formula,
              compactSyntaxFormulaTaskWitnessCoordinatesOf,
              compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
                hwitnessSize (4 : Fin 7))
          hnumericSize hbitPositive
      have hcompile :=
        compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate
      exact ⟨certificate.compile, (hcompile.trans hcertificate).trans (by
        unfold compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
        omega)⟩

noncomputable def compactFormulaTransformStepRowsFullyFixedBoundOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      numericBound bitBound : Nat)
    (hgraph : CompactFormulaTransformStepRows tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount)
    (hstepEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate) <= bitBound)
    (htermEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode stepWitness.slot0 stepWitness.term.tag
          stepWitness.term.argument consumedCount witnessStart witnessFinish
          witnessCount coordinate) <= bitBound)
    (hformulaEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode stepWitness.formula.tag consumedCount
          mappedHead coordinate) <= bitBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentOutputCount : current.outputCount <= numericBound)
    (hnextOutputCount : next.outputCount <= numericBound)
    (hwitnessCount : witnessCount <= numericBound)
    (hcurrentParserValue :
      CompactUnifiedParserStateCoordinateValueBound current.parser numericBound)
    (hnextParserValue :
      CompactUnifiedParserStateCoordinateValueBound next.parser numericBound)
    (hwitnessValue :
      CompactUnifiedParserSyntaxStepWitnessCoordinateValueBound stepWitness
        numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentParserSize :
      CompactUnifiedParserStateCoordinateSizeBound current.parser bitBound)
    (hnextParserSize :
      CompactUnifiedParserStateCoordinateSizeBound next.parser bitBound)
    (hwitnessSize :
      CompactUnifiedParserSyntaxStepWitnessCoordinateSizeBound stepWitness
        bitBound)
    (hcurrentOutputBoundarySize :
      Nat.size current.outputBoundary <= bitBound)
    (hnextOutputBoundarySize :
      Nat.size next.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound allBranchesZeroValuation
      (compactFormulaTransformStepRowsExplicitFormula tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount)
      (compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
        current.outputCount tokenCount numericBound bitBound) :=
  compactFormulaTransformStepRowsFullyFixedBoundFromData tokenTable width
    tokenCount current next mode stepWitness consumedCount mappedHead
    witnessStart witnessFinish witnessCount numericBound bitBound
    (compactFormulaTransformStepRowsCheckedBranchDataOfGraph tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount hgraph)
    hstepEnvironmentSize htermEnvironmentSize hformulaEnvironmentSize hwidth
    hwidthBit htokenCount hcurrentOutputCount hnextOutputCount hwitnessCount
    hcurrentParserValue hnextParserValue hwitnessValue htokenTableSize
    hwidthSize htokenCountSize hcurrentParserSize hnextParserSize hwitnessSize
    hcurrentOutputBoundarySize hnextOutputBoundarySize hnumericSize hbitPositive

#print axioms compactFormulaTransformStepRowsFullyFixedBoundFromData
#print axioms compactFormulaTransformStepRowsFullyFixedBoundOfGraph

end FoundationCompactNumericListedDirectFormulaTransformStepRowsAllBranchesFullyFixedBounds
