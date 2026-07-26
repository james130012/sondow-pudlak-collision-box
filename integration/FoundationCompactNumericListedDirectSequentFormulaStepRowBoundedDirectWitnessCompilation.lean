import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectWitnessCompilationCore

/-! # Public compilation of the eighteen bounded sequent-step witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectWitnessCompilation

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerOpaqueArity18
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectTerminalBound
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectWitnessCompilationCore

noncomputable def
    compactSequentFormulaStepRowBoundedDirectWitnessPayloadEnvelope
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 18 0 valueBound
    (binaryFormulaCode
      (compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowIndex)).length
    (compactSequentFormulaStepDirectPublicPayloadEnvelope tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      data.row)

noncomputable def
    compactSequentFormulaStepRowBoundedExplicitWitnessDirectBoundOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    ExplicitDirectFormulaBound
      compactSequentFormulaStepRowBoundedDirectZeroValuation
      (explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm valueBound) 18
        (compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount
          rowIndex))
      (compactSequentFormulaStepRowBoundedDirectWitnessPayloadEnvelope
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex valueBound data) := by
  let certified :=
    compactSequentFormulaStepRowBoundedDirectWitnessCompilationOfData
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound data
  let sourceFormula :=
    explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 18
      (compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex)
  let proof :=
    castDirectCompilationProof certified.compilation sourceFormula
      certified.formula_eq
  refine ⟨proof, ?_⟩
  apply
    castDirectCompilationProof_payloadLength_le certified.compilation
      sourceFormula certified.formula_eq
  simpa only [
    compactSequentFormulaStepRowBoundedDirectWitnessPayloadEnvelope] using
      certified.resource_eq

#print axioms
  compactSequentFormulaStepRowBoundedExplicitWitnessDirectBoundOfData

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectWitnessCompilation
