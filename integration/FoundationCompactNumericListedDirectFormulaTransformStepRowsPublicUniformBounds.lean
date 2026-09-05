import integration.FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicFullyFixedBounds

/-! # Uniform public bounds for one formula-transform step -/

open LO FirstOrder LO.FirstOrder.Arithmetic
open scoped BigOperators

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicUniformBounds

open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStepRowsAllBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietDoneFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietEmptyFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietRepeatFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietInvalidFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStepRowsHeavyBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAllBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsMappedRowsFullyFixedBounds
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixFullyFixedBounds

def compactFormulaTransformStepRowsUniformNumericBound
    (numericBound : Nat) : Nat :=
  1 + 38 * numericBound

def compactFormulaTransformStepRowsUniformBitBound
    (numericBound : Nat) : Nat :=
  let uniformNumericBound :=
    compactFormulaTransformStepRowsUniformNumericBound numericBound
  uniformNumericBound + Nat.size uniformNumericBound + 1

def compactFormulaTransformStepRowsCoordinateSumPayloadPolynomial
    (numericBound : Nat) : Nat :=
  compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
    numericBound numericBound
    (compactFormulaTransformStepRowsUniformNumericBound numericBound)
    (compactFormulaTransformStepRowsUniformBitBound numericBound)

private theorem one_add_sum_fin38_le
    (values : Fin 38 -> Nat) (numericBound : Nat)
    (hvalues : forall coordinate, values coordinate <= numericBound) :
    1 + ∑ coordinate : Fin 38, values coordinate <=
      1 + 38 * numericBound := by
  calc
    1 + ∑ coordinate : Fin 38, values coordinate <=
        1 + ∑ _coordinate : Fin 38, numericBound := by
      apply Nat.add_le_add_left
      exact Finset.sum_le_sum (fun coordinate _ => hvalues coordinate)
    _ = 1 + 38 * numericBound := by simp

theorem compactFormulaTransformStepRowsPublicNumericBound_le_uniform
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      numericBound : Nat)
    (henvironment : forall coordinate,
      compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount coordinate <= numericBound) :
    compactFormulaTransformStepRowsPublicNumericBound tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount <=
      compactFormulaTransformStepRowsUniformNumericBound numericBound := by
  have hsum := one_add_sum_fin38_le
    (compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount)
    numericBound henvironment
  simpa only [compactFormulaTransformStepRowsPublicNumericBound,
    compactFormulaTransformStepRowsUniformNumericBound] using hsum

theorem compactFormulaTransformStepRowsPublicBitBound_le_uniform
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      numericBound : Nat)
    (henvironment : forall coordinate,
      compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount coordinate <= numericBound) :
    compactFormulaTransformStepRowsPublicBitBound tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount <=
      compactFormulaTransformStepRowsUniformBitBound numericBound := by
  let localNumericBound := compactFormulaTransformStepRowsPublicNumericBound
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount
  let uniformNumericBound :=
    compactFormulaTransformStepRowsUniformNumericBound numericBound
  have hnumeric : localNumericBound <= uniformNumericBound :=
    compactFormulaTransformStepRowsPublicNumericBound_le_uniform tokenTable
      width tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount numericBound henvironment
  have hsize : Nat.size localNumericBound <= Nat.size uniformNumericBound :=
    Nat.size_le_size hnumeric
  change localNumericBound + Nat.size localNumericBound + 1 <=
    uniformNumericBound + Nat.size uniformNumericBound + 1
  omega

theorem outputRowsMappedSelectedFixedPayloadPolynomial_count_independent
    (leftCount rightCount numericBound bitBound : Nat) :
    outputRowsMappedSelectedFixedPayloadPolynomial leftCount numericBound
        bitBound =
      outputRowsMappedSelectedFixedPayloadPolynomial rightCount numericBound
        bitBound := by
  unfold outputRowsMappedSelectedFixedPayloadPolynomial
    outputRowsMappedCaseFixedPayloadPolynomial
    outputRowsMappedTailFixedPayloadPolynomial
    appendMappedSourcePrefixFullyFixedPayloadPolynomial
  rfl

theorem outputRowsAllBranchesFullyFixedPayloadPolynomial_count_independent
    (leftCount rightCount numericBound bitBound : Nat) :
    outputRowsAllBranchesFullyFixedPayloadPolynomial leftCount numericBound
        bitBound =
      outputRowsAllBranchesFullyFixedPayloadPolynomial rightCount numericBound
        bitBound := by
  unfold outputRowsAllBranchesFullyFixedPayloadPolynomial
  rw [outputRowsMappedSelectedFixedPayloadPolynomial_count_independent
    leftCount rightCount numericBound bitBound]

def compactFormulaTransformStepRowsFullyUniformPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
    0 tokenCount numericBound bitBound

theorem
    compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial_eq_uniform
    (currentOutputCount tokenCount numericBound bitBound : Nat) :
    compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
        currentOutputCount tokenCount numericBound bitBound =
      compactFormulaTransformStepRowsFullyUniformPayloadPolynomial tokenCount
        numericBound bitBound := by
  change
    compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
        currentOutputCount tokenCount numericBound bitBound =
      compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
        0 tokenCount numericBound bitBound
  unfold compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial
    stepRowsFormulaBranchFixedPayloadPolynomial
  rw [outputRowsAllBranchesFullyFixedPayloadPolynomial_count_independent
    currentOutputCount 0 numericBound bitBound]

#print axioms compactFormulaTransformStepRowsPublicNumericBound_le_uniform
#print axioms compactFormulaTransformStepRowsPublicBitBound_le_uniform
#print axioms
  outputRowsAllBranchesFullyFixedPayloadPolynomial_count_independent
#print axioms
  compactFormulaTransformStepRowsAllBranchesFullyFixedPayloadPolynomial_eq_uniform

end FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicUniformBounds
