import integration.FoundationCompactNumericListedDirectFormulaTransformStepRowsAllBranchesFullyFixedBounds

/-! # Bound-free public endpoint for one formula-transform step -/

open LO FirstOrder LO.FirstOrder.Arithmetic
open scoped BigOperators

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicFullyFixedBounds

open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStepRowsAllBranchesFullyFixedBounds

private abbrev publicZeroValuation : Nat -> Nat :=
  compactFormulaTransformStepRowsZeroValuation

def compactFormulaTransformStepRowsPublicNumericBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    Nat :=
  1 + ∑ coordinate : Fin 38,
    compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount coordinate

def compactFormulaTransformStepRowsPublicBitBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    Nat :=
  let numericBound := compactFormulaTransformStepRowsPublicNumericBound
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount
  numericBound + Nat.size numericBound + 1

def compactFormulaTransformStepRowsPublicFullyFixedPayloadPolynomial
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    Nat :=
  let numericBound := compactFormulaTransformStepRowsPublicNumericBound
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount
  let bitBound := compactFormulaTransformStepRowsPublicBitBound tokenTable width
    tokenCount current next mode stepWitness consumedCount mappedHead
    witnessStart witnessFinish witnessCount
  compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
    current.outputCount tokenCount numericBound bitBound

private def termOutputCoordinateInStep : Fin 33 -> Fin 38 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 30, 31, 33, 35, 36, 37]

private def formulaOutputCoordinateInStep : Fin 29 -> Fin 38 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 24, 25, 30, 33, 34]

private def currentParserCoordinateInStep : Fin 8 -> Fin 38 :=
  ![3, 5, 6, 7, 8, 9, 10, 11]

private def nextParserCoordinateInStep : Fin 8 -> Fin 38 :=
  ![14, 16, 17, 18, 19, 20, 21, 22]

private def stepWitnessCoordinateInStep : Fin 7 -> Fin 38 :=
  ![26, 27, 28, 29, 30, 31, 32]

private theorem termOutputEnvironment_step_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (coordinate : Fin 33) :
    compactFormulaTransformTermOutputRowsEnvironment tokenTable width
        tokenCount current next mode stepWitness.slot0 stepWitness.term.tag
        stepWitness.term.argument consumedCount witnessStart witnessFinish
        witnessCount coordinate =
      compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount (termOutputCoordinateInStep coordinate) := by
  fin_cases coordinate <;> rfl

private theorem formulaOutputEnvironment_step_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (coordinate : Fin 29) :
    compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
        tokenCount current next mode stepWitness.formula.tag consumedCount
        mappedHead coordinate =
      compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount
        (formulaOutputCoordinateInStep coordinate) := by
  fin_cases coordinate <;> rfl

private theorem currentParserEnvironment_step_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (coordinate : Fin 8) :
    compactUnifiedParserStateCoordinateValues current.parser coordinate =
      compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount
        (currentParserCoordinateInStep coordinate) := by
  fin_cases coordinate <;> rfl

private theorem nextParserEnvironment_step_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (coordinate : Fin 8) :
    compactUnifiedParserStateCoordinateValues next.parser coordinate =
      compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount
        (nextParserCoordinateInStep coordinate) := by
  fin_cases coordinate <;> rfl

private theorem stepWitnessEnvironment_step_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (coordinate : Fin 7) :
    compactUnifiedParserSyntaxStepWitnessCoordinateValues stepWitness
        coordinate =
      compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount
        (stepWitnessCoordinateInStep coordinate) := by
  fin_cases coordinate <;> rfl

theorem compactFormulaTransformStepRowsEnvironment_le_publicNumericBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    forall coordinate,
      compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate <=
        compactFormulaTransformStepRowsPublicNumericBound tokenTable width
          tokenCount current next mode stepWitness consumedCount mappedHead
          witnessStart witnessFinish witnessCount := by
  intro coordinate
  have hsum :
      compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate <=
        ∑ index : Fin 38,
          compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
            current next mode stepWitness consumedCount mappedHead witnessStart
            witnessFinish witnessCount index := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ coordinate)
  unfold compactFormulaTransformStepRowsPublicNumericBound
  omega

theorem compactFormulaTransformTermOutputRowsEnvironment_le_publicNumericBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    forall coordinate,
      compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode stepWitness.slot0 stepWitness.term.tag
          stepWitness.term.argument consumedCount witnessStart witnessFinish
          witnessCount coordinate <=
        compactFormulaTransformStepRowsPublicNumericBound tokenTable width
          tokenCount current next mode stepWitness consumedCount mappedHead
          witnessStart witnessFinish witnessCount := by
  intro coordinate
  rw [termOutputEnvironment_step_alignment]
  exact compactFormulaTransformStepRowsEnvironment_le_publicNumericBound
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount
    (termOutputCoordinateInStep coordinate)

theorem compactFormulaTransformFormulaOutputRowsEnvironment_le_publicNumericBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    forall coordinate,
      compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode stepWitness.formula.tag consumedCount
          mappedHead coordinate <=
        compactFormulaTransformStepRowsPublicNumericBound tokenTable width
          tokenCount current next mode stepWitness consumedCount mappedHead
          witnessStart witnessFinish witnessCount := by
  intro coordinate
  rw [formulaOutputEnvironment_step_alignment]
  exact compactFormulaTransformStepRowsEnvironment_le_publicNumericBound
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount
    (formulaOutputCoordinateInStep coordinate)

theorem compactFormulaTransformCurrentParser_le_publicNumericBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    CompactUnifiedParserStateCoordinateValueBound current.parser
      (compactFormulaTransformStepRowsPublicNumericBound tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount) := by
  intro coordinate
  rw [currentParserEnvironment_step_alignment]
  exact compactFormulaTransformStepRowsEnvironment_le_publicNumericBound
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount
    (currentParserCoordinateInStep coordinate)

theorem compactFormulaTransformNextParser_le_publicNumericBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    CompactUnifiedParserStateCoordinateValueBound next.parser
      (compactFormulaTransformStepRowsPublicNumericBound tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount) := by
  intro coordinate
  rw [nextParserEnvironment_step_alignment]
  exact compactFormulaTransformStepRowsEnvironment_le_publicNumericBound
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount
    (nextParserCoordinateInStep coordinate)

theorem compactFormulaTransformStepWitness_le_publicNumericBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    CompactUnifiedParserSyntaxStepWitnessCoordinateValueBound stepWitness
      (compactFormulaTransformStepRowsPublicNumericBound tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount) := by
  intro coordinate
  rw [stepWitnessEnvironment_step_alignment]
  exact compactFormulaTransformStepRowsEnvironment_le_publicNumericBound
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount
    (stepWitnessCoordinateInStep coordinate)

theorem compactFormulaTransformStepRowsPublicNumericBound_le_bitBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    compactFormulaTransformStepRowsPublicNumericBound tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount <=
      compactFormulaTransformStepRowsPublicBitBound tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount := by
  simp only [compactFormulaTransformStepRowsPublicBitBound]
  omega

theorem compactFormulaTransformStepRowsPublicNumericSize_le_bitBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    Nat.size
        (compactFormulaTransformStepRowsPublicNumericBound tokenTable width
          tokenCount current next mode stepWitness consumedCount mappedHead
          witnessStart witnessFinish witnessCount) <=
      compactFormulaTransformStepRowsPublicBitBound tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount := by
  simp only [compactFormulaTransformStepRowsPublicBitBound]
  omega

theorem compactFormulaTransformStepRowsPublicBitBound_positive
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    1 <= compactFormulaTransformStepRowsPublicBitBound tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount := by
  simp [compactFormulaTransformStepRowsPublicBitBound]

noncomputable def compactFormulaTransformStepRowsPublicFullyFixedBoundOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformStepRows tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount) :
    ExplicitDirectFormulaBound publicZeroValuation
      (compactFormulaTransformStepRowsExplicitFormula tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount)
      (compactFormulaTransformStepRowsPublicFullyFixedPayloadPolynomial
        tokenTable width tokenCount current next mode stepWitness consumedCount
        mappedHead witnessStart witnessFinish witnessCount) := by
  let numericBound := compactFormulaTransformStepRowsPublicNumericBound
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount
  let bitBound := compactFormulaTransformStepRowsPublicBitBound tokenTable width
    tokenCount current next mode stepWitness consumedCount mappedHead
    witnessStart witnessFinish witnessCount
  have hstepValue :=
    compactFormulaTransformStepRowsEnvironment_le_publicNumericBound tokenTable
      width tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount
  have htermValue :=
    compactFormulaTransformTermOutputRowsEnvironment_le_publicNumericBound
      tokenTable width tokenCount current next mode stepWitness consumedCount
      mappedHead witnessStart witnessFinish witnessCount
  have hformulaValue :=
    compactFormulaTransformFormulaOutputRowsEnvironment_le_publicNumericBound
      tokenTable width tokenCount current next mode stepWitness consumedCount
      mappedHead witnessStart witnessFinish witnessCount
  have hcurrentValue :=
    compactFormulaTransformCurrentParser_le_publicNumericBound tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount
  have hnextValue :=
    compactFormulaTransformNextParser_le_publicNumericBound tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount
  have hwitnessValue :=
    compactFormulaTransformStepWitness_le_publicNumericBound tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount
  have hnumericSize :=
    compactFormulaTransformStepRowsPublicNumericSize_le_bitBound tokenTable
      width tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount
  have hnumericBit :=
    compactFormulaTransformStepRowsPublicNumericBound_le_bitBound tokenTable
      width tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount
  have hstepSize : forall coordinate,
      Nat.size
        (compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate) <= bitBound := fun coordinate =>
    (Nat.size_le_size (hstepValue coordinate)).trans hnumericSize
  have htermSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode stepWitness.slot0 stepWitness.term.tag
          stepWitness.term.argument consumedCount witnessStart witnessFinish
          witnessCount coordinate) <= bitBound := fun coordinate =>
    (Nat.size_le_size (htermValue coordinate)).trans hnumericSize
  have hformulaSize : forall coordinate,
      Nat.size
        (compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode stepWitness.formula.tag consumedCount
          mappedHead coordinate) <= bitBound := fun coordinate =>
    (Nat.size_le_size (hformulaValue coordinate)).trans hnumericSize
  have hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current.parser bitBound :=
    fun coordinate =>
      (Nat.size_le_size (hcurrentValue coordinate)).trans hnumericSize
  have hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next.parser bitBound :=
    fun coordinate =>
      (Nat.size_le_size (hnextValue coordinate)).trans hnumericSize
  have hwitnessSize :
      CompactUnifiedParserSyntaxStepWitnessCoordinateSizeBound stepWitness
        bitBound := fun coordinate =>
    (Nat.size_le_size (hwitnessValue coordinate)).trans hnumericSize
  have hbound := compactFormulaTransformStepRowsFullyFixedBoundOfGraph
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount numericBound bitBound
    hgraph hstepSize htermSize hformulaSize
    (by
      simpa [compactFormulaTransformStepRowsEnvironment] using
        hstepValue (1 : Fin 38))
    (by
      have hwidth : width <= numericBound := by
        simpa [compactFormulaTransformStepRowsEnvironment] using
          hstepValue (1 : Fin 38)
      exact hwidth.trans hnumericBit)
    (by
      simpa [compactFormulaTransformStepRowsEnvironment] using
        hstepValue (2 : Fin 38))
    (by
      simpa [compactFormulaTransformStepRowsEnvironment] using
        hstepValue (13 : Fin 38))
    (by
      simpa [compactFormulaTransformStepRowsEnvironment] using
        hstepValue (24 : Fin 38))
    (by
      simpa [compactFormulaTransformStepRowsEnvironment] using
        hstepValue (37 : Fin 38))
    hcurrentValue hnextValue hwitnessValue
    ((Nat.size_le_size (by
      simpa [compactFormulaTransformStepRowsEnvironment] using
        hstepValue (0 : Fin 38))).trans hnumericSize)
    ((Nat.size_le_size (by
      simpa [compactFormulaTransformStepRowsEnvironment] using
        hstepValue (1 : Fin 38))).trans hnumericSize)
    ((Nat.size_le_size (by
      simpa [compactFormulaTransformStepRowsEnvironment] using
        hstepValue (2 : Fin 38))).trans hnumericSize)
    hcurrentSize hnextSize hwitnessSize
    ((Nat.size_le_size (by
      simpa [compactFormulaTransformStepRowsEnvironment] using
        hstepValue (12 : Fin 38))).trans hnumericSize)
    ((Nat.size_le_size (by
      simpa [compactFormulaTransformStepRowsEnvironment] using
        hstepValue (23 : Fin 38))).trans hnumericSize)
    hnumericSize
    (compactFormulaTransformStepRowsPublicBitBound_positive tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount)
  simpa [compactFormulaTransformStepRowsPublicFullyFixedPayloadPolynomial,
    numericBound, bitBound] using hbound

#print axioms compactFormulaTransformStepRowsPublicFullyFixedBoundOfGraph

end FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicFullyFixedBounds
