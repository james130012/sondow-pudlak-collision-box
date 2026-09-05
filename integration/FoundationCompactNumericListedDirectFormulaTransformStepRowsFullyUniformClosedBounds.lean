import integration.FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicUniformBounds
import integration.FoundationCompactPAClosedDirectContextTransport
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

/-! # Externally uniform closed bounds for one formula-transform step -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectFormulaTransformStepRowsFullyUniformClosedBounds

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAClosedDirectContextTransport
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStepRowsFormulaFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStepRowsAllBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicUniformBounds

noncomputable def compactFormulaTransformStepRowsFullyUniformClosedBoundAtValuation
    (valuation : Nat -> Nat)
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
    (hnextOutputBoundarySize : Nat.size next.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound valuation
      (compactFormulaTransformStepRowsClosedFormula tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount)
      (compactFormulaTransformStepRowsFullyUniformPayloadPolynomial tokenCount
        numericBound bitBound) := by
  let explicitBound := compactFormulaTransformStepRowsFullyFixedBoundOfGraph
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount numericBound bitBound
    hgraph hstepEnvironmentSize htermEnvironmentSize hformulaEnvironmentSize
    hwidth hwidthBit htokenCount hcurrentOutputCount hnextOutputCount
    hwitnessCount hcurrentParserValue hnextParserValue hwitnessValue
    htokenTableSize hwidthSize htokenCountSize hcurrentParserSize
    hnextParserSize hwitnessSize hcurrentOutputBoundarySize
    hnextOutputBoundarySize hnumericSize hbitPositive
  have halignment :
      compactFormulaTransformStepRowsExplicitFormula tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount =
        compactFormulaTransformStepRowsClosedFormula tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount :=
    (compactFormulaTransformStepRowsClosedFormula_alignment tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount).symm
  let closedAtZero := castValuationContextProof halignment explicitBound.proof
  have hclosed := compactFormulaTransformStepRowsClosedFormula_closed
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount
  let proof := transportClosedDirectProofAtValuation
    (target := valuation) closedAtZero hclosed
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = closedAtZero.payloadLength by
    exact transportClosedDirectProofAtValuation_payloadLength_eq
      (target := valuation) closedAtZero hclosed]
  rw [show closedAtZero.payloadLength = explicitBound.proof.payloadLength by
    exact castValuationContextProof_payloadLength_eq halignment
      explicitBound.proof]
  exact explicitBound.payloadLength_le.trans_eq
    (compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial_eq_uniform
      current.outputCount tokenCount numericBound bitBound)

noncomputable def
    compactFormulaTransformStepRowsFullyUniformClosedBoundAtValuationOfValueBounds
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      numericBound bitBound : Nat)
    (hgraph : CompactFormulaTransformStepRows tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentParserValue : CompactUnifiedParserStateCoordinateValueBound
      current.parser numericBound)
    (hcurrentFinish : current.finish <= numericBound)
    (hcurrentOutputBoundarySize : Nat.size current.outputBoundary <= bitBound)
    (hcurrentOutputCount : current.outputCount <= numericBound)
    (hnextParserValue : CompactUnifiedParserStateCoordinateValueBound
      next.parser numericBound)
    (hnextFinish : next.finish <= numericBound)
    (hnextOutputBoundarySize : Nat.size next.outputBoundary <= bitBound)
    (hnextOutputCount : next.outputCount <= numericBound)
    (hmode : mode <= numericBound)
    (hwitnessValue : CompactUnifiedParserSyntaxStepWitnessCoordinateValueBound
      stepWitness numericBound)
    (hconsumedCount : consumedCount <= numericBound)
    (hmappedHead : mappedHead <= numericBound)
    (hwitnessStart : witnessStart <= numericBound)
    (hwitnessFinish : witnessFinish <= numericBound)
    (hwitnessCount : witnessCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound valuation
      (compactFormulaTransformStepRowsClosedFormula tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount)
      (compactFormulaTransformStepRowsFullyUniformPayloadPolynomial tokenCount
        numericBound bitBound) := by
  have hsizeOfNumeric {value : Nat} (hvalue : value <= numericBound) :
      Nat.size value <= bitBound :=
    (Nat.size_le_size hvalue).trans hnumericSize
  have hcurrentParserSize : CompactUnifiedParserStateCoordinateSizeBound
      current.parser bitBound := fun coordinate =>
    hsizeOfNumeric (hcurrentParserValue coordinate)
  have hnextParserSize : CompactUnifiedParserStateCoordinateSizeBound
      next.parser bitBound := fun coordinate =>
    hsizeOfNumeric (hnextParserValue coordinate)
  have hwitnessSize : CompactUnifiedParserSyntaxStepWitnessCoordinateSizeBound
      stepWitness bitBound := fun coordinate =>
    hsizeOfNumeric (hwitnessValue coordinate)
  have hstepEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate) <= bitBound := by
    intro coordinate
    fin_cases coordinate
    · exact htokenTableSize
    · exact hsizeOfNumeric hwidth
    · exact hsizeOfNumeric htokenCount
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hcurrentParserSize (0 : Fin 8)
    · exact hsizeOfNumeric hcurrentFinish
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hcurrentParserSize (1 : Fin 8)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hcurrentParserSize (2 : Fin 8)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hcurrentParserSize (3 : Fin 8)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hcurrentParserSize (4 : Fin 8)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hcurrentParserSize (5 : Fin 8)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hcurrentParserSize (6 : Fin 8)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hcurrentParserSize (7 : Fin 8)
    · exact hcurrentOutputBoundarySize
    · exact hsizeOfNumeric hcurrentOutputCount
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hnextParserSize (0 : Fin 8)
    · exact hsizeOfNumeric hnextFinish
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hnextParserSize (1 : Fin 8)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hnextParserSize (2 : Fin 8)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hnextParserSize (3 : Fin 8)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hnextParserSize (4 : Fin 8)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hnextParserSize (5 : Fin 8)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hnextParserSize (6 : Fin 8)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        CompactFormulaTransformStateRowCoordinates.parser,
        compactUnifiedParserStateCoordinateValues] using
        hnextParserSize (7 : Fin 8)
    · exact hnextOutputBoundarySize
    · exact hsizeOfNumeric hnextOutputCount
    · simpa [compactFormulaTransformStepRowsEnvironment] using
        hsizeOfNumeric hmode
    · simpa [compactFormulaTransformStepRowsEnvironment,
        compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
        hwitnessSize (0 : Fin 7)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
        hwitnessSize (1 : Fin 7)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
        hwitnessSize (2 : Fin 7)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
        hwitnessSize (3 : Fin 7)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
        hwitnessSize (4 : Fin 7)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
        hwitnessSize (5 : Fin 7)
    · simpa [compactFormulaTransformStepRowsEnvironment,
        compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
        hwitnessSize (6 : Fin 7)
    · exact hsizeOfNumeric hconsumedCount
    · exact hsizeOfNumeric hmappedHead
    · simpa [compactFormulaTransformStepRowsEnvironment] using
        hsizeOfNumeric hwitnessStart
    · simpa [compactFormulaTransformStepRowsEnvironment] using
        hsizeOfNumeric hwitnessFinish
    · simpa [compactFormulaTransformStepRowsEnvironment] using
        hsizeOfNumeric hwitnessCount
  let termStepCoordinate : Fin 33 -> Fin 38 :=
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
      17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 30, 31, 33, 35, 36, 37]
  have htermEnvironmentAlignment (coordinate : Fin 33) :
      compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode stepWitness.slot0 stepWitness.term.tag
          stepWitness.term.argument consumedCount witnessStart witnessFinish
          witnessCount coordinate =
        compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount (termStepCoordinate coordinate) := by
    fin_cases coordinate <;> rfl
  have htermEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode stepWitness.slot0 stepWitness.term.tag
          stepWitness.term.argument consumedCount witnessStart witnessFinish
          witnessCount coordinate) <= bitBound := by
    intro coordinate
    rw [htermEnvironmentAlignment coordinate]
    exact hstepEnvironmentSize (termStepCoordinate coordinate)
  let formulaStepCoordinate : Fin 29 -> Fin 38 :=
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
      17, 18, 19, 20, 21, 22, 23, 24, 25, 30, 33, 34]
  have hformulaEnvironmentAlignment (coordinate : Fin 29) :
      compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode stepWitness.formula.tag consumedCount
          mappedHead coordinate =
        compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount (formulaStepCoordinate coordinate) := by
    fin_cases coordinate <;> rfl
  have hformulaEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode stepWitness.formula.tag consumedCount
          mappedHead coordinate) <= bitBound := by
    intro coordinate
    rw [hformulaEnvironmentAlignment coordinate]
    exact hstepEnvironmentSize (formulaStepCoordinate coordinate)
  exact compactFormulaTransformStepRowsFullyUniformClosedBoundAtValuation
    valuation tokenTable width tokenCount current next mode stepWitness
    consumedCount mappedHead witnessStart witnessFinish witnessCount
    numericBound bitBound hgraph hstepEnvironmentSize htermEnvironmentSize
    hformulaEnvironmentSize hwidth hwidthBit htokenCount hcurrentOutputCount
    hnextOutputCount hwitnessCount hcurrentParserValue hnextParserValue
    hwitnessValue htokenTableSize (hsizeOfNumeric hwidth)
    (hsizeOfNumeric htokenCount) hcurrentParserSize hnextParserSize hwitnessSize
    hcurrentOutputBoundarySize hnextOutputBoundarySize hnumericSize hbitPositive

theorem
    compactFormulaTransformStepRowsFullyUniformClosedBoundAtValuation_payloadLength_le
    (valuation : Nat -> Nat)
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
    (hnextOutputBoundarySize : Nat.size next.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compactFormulaTransformStepRowsFullyUniformClosedBoundAtValuation
      valuation tokenTable width tokenCount current next mode stepWitness
      consumedCount mappedHead witnessStart witnessFinish witnessCount
      numericBound bitBound hgraph hstepEnvironmentSize htermEnvironmentSize
      hformulaEnvironmentSize hwidth hwidthBit htokenCount hcurrentOutputCount
      hnextOutputCount hwitnessCount hcurrentParserValue hnextParserValue
      hwitnessValue htokenTableSize hwidthSize htokenCountSize
      hcurrentParserSize hnextParserSize hwitnessSize
      hcurrentOutputBoundarySize hnextOutputBoundarySize hnumericSize
      hbitPositive).proof.payloadLength <=
      compactFormulaTransformStepRowsFullyUniformPayloadPolynomial tokenCount
        numericBound bitBound :=
  (compactFormulaTransformStepRowsFullyUniformClosedBoundAtValuation
    valuation tokenTable width tokenCount current next mode stepWitness
    consumedCount mappedHead witnessStart witnessFinish witnessCount
    numericBound bitBound hgraph hstepEnvironmentSize htermEnvironmentSize
    hformulaEnvironmentSize hwidth hwidthBit htokenCount hcurrentOutputCount
    hnextOutputCount hwitnessCount hcurrentParserValue hnextParserValue
    hwitnessValue htokenTableSize hwidthSize htokenCountSize
    hcurrentParserSize hnextParserSize hwitnessSize
    hcurrentOutputBoundarySize hnextOutputBoundarySize hnumericSize
    hbitPositive).payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformStepRowsFullyUniformClosedBounds
