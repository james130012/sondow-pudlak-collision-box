import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport

/-! # Public direct syntax for the thirty-one endpoint witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalExplicitHybridCertificate

def compactFormulaTransformInitialFinalBoundedDirectPublicTerms
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat) :
    Fin 13 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    shortBinaryNumeralTerm stateCount,
    shortBinaryNumeralTerm fuel,
    shortBinaryNumeralTerm inputBoundary,
    shortBinaryNumeralTerm inputCount,
    shortBinaryNumeralTerm expectedOutputBoundary,
    shortBinaryNumeralTerm expectedOutputCount,
    shortBinaryNumeralTerm expectedSuffixBoundary,
    shortBinaryNumeralTerm expectedSuffixCount,
    shortBinaryNumeralTerm binderArity]

def compactFormulaTransformInitialFinalBoundedDirectInitialWitnessValues
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    Fin 14 -> Nat :=
  ![witness.initialCoordinates.start,
    witness.initialCoordinates.finish,
    witness.initialCoordinates.parserFinish,
    witness.initialCoordinates.parserTokensFinish,
    witness.initialCoordinates.parserTasksFinish,
    witness.initialCoordinates.parserTokensBoundary,
    witness.initialCoordinates.parserTokensCount,
    witness.initialCoordinates.parserTasksBoundary,
    witness.initialCoordinates.parserTasksCount,
    witness.initialCoordinates.outputBoundary,
    witness.initialCoordinates.outputCount,
    witness.initialSizeWitness.parserTokensBoundarySize,
    witness.initialSizeWitness.parserTasksBoundarySize,
    witness.initialSizeWitness.outputBoundarySize]

def compactFormulaTransformInitialFinalBoundedDirectFinalWitnessValues
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    Fin 17 -> Nat :=
  ![witness.finalCoordinates.start,
    witness.finalCoordinates.finish,
    witness.finalCoordinates.parserFinish,
    witness.finalCoordinates.parserTokensFinish,
    witness.finalCoordinates.parserTasksFinish,
    witness.finalCoordinates.parserTokensBoundary,
    witness.finalCoordinates.parserTokensCount,
    witness.finalCoordinates.parserTasksBoundary,
    witness.finalCoordinates.parserTasksCount,
    witness.finalCoordinates.outputBoundary,
    witness.finalCoordinates.outputCount,
    witness.finalSizeWitness.parserTokensBoundarySize,
    witness.finalSizeWitness.parserTasksBoundarySize,
    witness.finalSizeWitness.outputBoundarySize,
    witness.finalParserOutputStart,
    witness.finalParserOutputBoundary,
    witness.finalParserOutputBoundarySize]

def compactFormulaTransformInitialFinalBoundedDirectClosedWitnessValues
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    Fin 31 -> Nat :=
  Matrix.vecAppend rfl
    (compactFormulaTransformInitialFinalBoundedDirectInitialWitnessValues
      witness)
    (compactFormulaTransformInitialFinalBoundedDirectFinalWitnessValues
      witness)

def compactFormulaTransformInitialFinalBoundedDirectReverseIndex
    (coordinate : Fin 31) : Fin 31 :=
  ⟨30 - coordinate, by omega⟩

def compactFormulaTransformInitialFinalBoundedDirectWitnessValues
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    Fin 31 -> Nat :=
  fun coordinate =>
    compactFormulaTransformInitialFinalBoundedDirectClosedWitnessValues witness
      (compactFormulaTransformInitialFinalBoundedDirectReverseIndex coordinate)

def compactFormulaTransformInitialFinalBoundedDirectRawPublicTerms
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat) :
    Fin 13 -> ArithmeticSemiterm Nat 31 :=
  fun coordinate => sourceSubstitutionLift 31
    (compactFormulaTransformInitialFinalBoundedDirectPublicTerms tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity coordinate)

def compactFormulaTransformInitialFinalBoundedDirectRawWitnessTerms :
    Fin 31 -> ArithmeticSemiterm Nat 31 :=
  fun coordinate =>
    #(compactFormulaTransformInitialFinalBoundedDirectReverseIndex coordinate)

def compactFormulaTransformInitialFinalBoundedDirectRawTerms
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat) :
    Fin 44 -> ArithmeticSemiterm Nat 31 :=
  Matrix.vecAppend rfl
    (compactFormulaTransformInitialFinalBoundedDirectRawPublicTerms tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity)
    compactFormulaTransformInitialFinalBoundedDirectRawWitnessTerms

def compactFormulaTransformInitialFinalBoundedDirectRawTerminal
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat) :
    ArithmeticSemiformula Nat 31 :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformInitialFinalRowsDef.val) ⇜
    compactFormulaTransformInitialFinalBoundedDirectRawTerms tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity

def compactFormulaTransformInitialFinalBoundedDirectClosedWitnessTerms
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    Fin 31 -> ValuationTerm :=
  fun coordinate => shortBinaryNumeralTerm
    (compactFormulaTransformInitialFinalBoundedDirectClosedWitnessValues
      witness coordinate)

def compactFormulaTransformInitialFinalBoundedDirectClosedTerms
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    Fin 44 -> ValuationTerm :=
  Matrix.vecAppend rfl
    (compactFormulaTransformInitialFinalBoundedDirectPublicTerms tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity)
    (compactFormulaTransformInitialFinalBoundedDirectClosedWitnessTerms witness)

theorem compactFormulaTransformInitialFinalRowsClosedFormula_eq_directTerms
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    compactFormulaTransformInitialFinalRowsClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity witness =
      (Rewriting.emb (ξ := Nat)
          compactFormulaTransformInitialFinalRowsDef.val) ⇜
        compactFormulaTransformInitialFinalBoundedDirectClosedTerms tokenTable
          width tokenCount stateBoundary stateCount fuel inputBoundary
          inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity witness := by
  unfold compactFormulaTransformInitialFinalRowsClosedFormula
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [compactFormulaTransformInitialFinalBoundedDirectClosedTerms,
      compactFormulaTransformInitialFinalBoundedDirectPublicTerms,
      compactFormulaTransformInitialFinalBoundedDirectClosedWitnessTerms,
      compactFormulaTransformInitialFinalBoundedDirectClosedWitnessValues,
      compactFormulaTransformInitialFinalBoundedDirectInitialWitnessValues,
      compactFormulaTransformInitialFinalBoundedDirectFinalWitnessValues,
      Matrix.vecAppend_eq_ite]

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax
