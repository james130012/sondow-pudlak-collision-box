import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPreparedTerminal
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity31

/-! # Thirty-one-layer direct bounded-witness compilation -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectCompilation

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity31
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectData
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectTerminal
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPreparedTerminal

def compactFormulaTransformInitialFinalBoundedDirectSourceFormula
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    ValuationFormula :=
  explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 31
    (compactFormulaTransformInitialFinalBoundedDirectRawTerminal tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity)

noncomputable def
    compactFormulaTransformInitialFinalBoundedDirectStructuralPayloadEnvelope
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    Nat :=
  let body :=
    compactFormulaTransformInitialFinalBoundedDirectRawTerminal tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity
  let terminalResource :=
    compactFormulaTransformInitialFinalBoundedDirectTerminalPayloadEnvelope
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound
  explicitBoundedWitnessDirectPublicPayloadEnvelope 31 0 valueBound
    (binaryFormulaCode body).length terminalResource

structure FormulaTransformInitialFinalBoundedDirectCompilation
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    where
  direct : ExplicitBoundedWitnessDirectCompilation
    compactFormulaTransformInitialFinalBoundedDirectZeroValuation
  formula_eq : direct.formula =
    compactFormulaTransformInitialFinalBoundedDirectSourceFormula tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound
  resource_eq : direct.payloadResource =
    compactFormulaTransformInitialFinalBoundedDirectStructuralPayloadEnvelope
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound

noncomputable def formulaTransformInitialFinalBoundedDirectCompilationOfBounded
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    (hbounded : CompactFormulaTransformInitialFinalBounded tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound) :
    FormulaTransformInitialFinalBoundedDirectCompilation tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound := by
  let data := formulaTransformInitialFinalBoundedDirectDataOfBounded tokenTable
    width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
    expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
    expectedSuffixCount binderArity valueBound hbounded
  let body :=
    compactFormulaTransformInitialFinalBoundedDirectRawTerminal tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity
  let values :=
    compactFormulaTransformInitialFinalBoundedDirectWitnessValues data.witness
  let terminalBound :=
    formulaTransformInitialFinalBoundedDirectPreparedTerminalBoundOfData
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound data
  let terminalResource :=
    compactFormulaTransformInitialFinalBoundedDirectTerminalPayloadEnvelope
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound
  have hcontext :=
    compactFormulaTransformInitialFinalBoundedDirectRawContextCode_le_zero
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
  let direct := compileExplicitBoundedWitnessDirectPublicWithResource
    0 valueBound (binaryFormulaCode body).length body values
      data.directWitnessValues_le (by rfl) hcontext terminalResource
      terminalBound.proof terminalBound.payloadLength_le
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity31
      0 valueBound (binaryFormulaCode body).length body values
      data.directWitnessValues_le (by rfl) hcontext terminalResource
      terminalBound.proof terminalBound.payloadLength_le
  refine { direct := direct, formula_eq := ?_, resource_eq := ?_ }
  · simpa only [
      compactFormulaTransformInitialFinalBoundedDirectSourceFormula,
      direct, body] using hcoordinates.1
  · simpa only [
      compactFormulaTransformInitialFinalBoundedDirectStructuralPayloadEnvelope,
      direct, body, terminalResource] using hcoordinates.2

#print axioms
  formulaTransformInitialFinalBoundedDirectCompilationOfBounded

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectCompilation
