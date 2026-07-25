import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase

/-!
# Public direct syntax for the bounded parser endpoints

This light module exposes a reducible copy of the original twenty-three-value
terminal and its witness vector.  Both are aligned to the already audited
source formula; the historical large syntax module remains unchanged.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase

def compactParserInitialFinalBoundedDirectPublicTerms
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat) :
    Fin 13 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    shortBinaryNumeralTerm stateCount,
    shortBinaryNumeralTerm fuel,
    shortBinaryNumeralTerm inputBoundary,
    shortBinaryNumeralTerm inputCount,
    shortBinaryNumeralTerm expectedBoundary,
    shortBinaryNumeralTerm expectedCount,
    shortBinaryNumeralTerm taskKind,
    shortBinaryNumeralTerm taskBinderArity,
    shortBinaryNumeralTerm taskRepeatCount]

def compactParserInitialFinalBoundedDirectRawPublicTerms
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat) :
    Fin 13 -> ArithmeticSemiterm Nat 23 :=
  fun coordinate => sourceSubstitutionLift 23
    (compactParserInitialFinalBoundedDirectPublicTerms tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      coordinate)

def compactParserInitialFinalBoundedDirectReverseIndex
    (coordinate : Fin 23) : Fin 23 :=
  ⟨22 - coordinate, by omega⟩

def compactParserInitialFinalBoundedDirectRawWitnessTerms :
    Fin 23 -> ArithmeticSemiterm Nat 23 :=
  fun coordinate =>
    #(compactParserInitialFinalBoundedDirectReverseIndex coordinate)

def compactParserInitialFinalBoundedDirectWitnessValues
    (witness : CompactParserInitialFinalWitnessCoordinates) : Fin 23 -> Nat :=
  ![witness.outputBoundarySize,
    witness.outputBoundary,
    witness.outputStart,
    witness.finalSizeWitness.tasksBoundarySize,
    witness.finalSizeWitness.tokensBoundarySize,
    witness.finalCoordinates.tasksCount,
    witness.finalCoordinates.tasksBoundary,
    witness.finalCoordinates.tokensCount,
    witness.finalCoordinates.tokensBoundary,
    witness.finalCoordinates.tasksFinish,
    witness.finalCoordinates.tokensFinish,
    witness.finalCoordinates.finish,
    witness.finalCoordinates.start,
    witness.initialSizeWitness.tasksBoundarySize,
    witness.initialSizeWitness.tokensBoundarySize,
    witness.initialCoordinates.tasksCount,
    witness.initialCoordinates.tasksBoundary,
    witness.initialCoordinates.tokensCount,
    witness.initialCoordinates.tokensBoundary,
    witness.initialCoordinates.tasksFinish,
    witness.initialCoordinates.tokensFinish,
    witness.initialCoordinates.finish,
    witness.initialCoordinates.start]

def compactParserInitialFinalBoundedDirectClosedWitnessTerms
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    Fin 23 -> ValuationTerm :=
  fun coordinate => shortBinaryNumeralTerm
    (compactParserInitialFinalBoundedDirectWitnessValues witness
      (compactParserInitialFinalBoundedDirectReverseIndex coordinate))

def compactParserInitialFinalBoundedDirectClosedTerms
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    Fin 36 -> ValuationTerm :=
  Matrix.vecAppend rfl
    (compactParserInitialFinalBoundedDirectPublicTerms tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount)
    (compactParserInitialFinalBoundedDirectClosedWitnessTerms witness)

def compactParserInitialFinalBoundedDirectRawTerms
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat) :
    Fin 36 -> ArithmeticSemiterm Nat 23 :=
  Matrix.vecAppend rfl
    (compactParserInitialFinalBoundedDirectRawPublicTerms tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount)
    compactParserInitialFinalBoundedDirectRawWitnessTerms

@[irreducible] def compactParserInitialFinalBoundedDirectRawTerminal
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat) :
    ArithmeticSemiformula Nat 23 :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserInitialFinalRowsDef.val) ⇜
    compactParserInitialFinalBoundedDirectRawTerms tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount

end FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
