import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle

/-! # Exact composite-fuel syntax for the combined parser endpoints -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle

def compactUnifiedParserInitialFinalRowsExactFuelTerms
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    Fin 36 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      compactParserSyntaxExactFuelTerm inputCount,
      shortBinaryNumeralTerm inputBoundary,
      shortBinaryNumeralTerm inputCount,
      shortBinaryNumeralTerm expectedBoundary,
      shortBinaryNumeralTerm expectedCount,
      shortBinaryNumeralTerm taskKind,
      shortBinaryNumeralTerm taskBinderArity,
      shortBinaryNumeralTerm taskRepeatCount,
      shortBinaryNumeralTerm witness.initialCoordinates.start,
      shortBinaryNumeralTerm witness.initialCoordinates.finish,
      shortBinaryNumeralTerm witness.initialCoordinates.tokensFinish,
      shortBinaryNumeralTerm witness.initialCoordinates.tasksFinish,
      shortBinaryNumeralTerm witness.initialCoordinates.tokensBoundary,
      shortBinaryNumeralTerm witness.initialCoordinates.tokensCount,
      shortBinaryNumeralTerm witness.initialCoordinates.tasksBoundary,
      shortBinaryNumeralTerm witness.initialCoordinates.tasksCount,
      shortBinaryNumeralTerm witness.initialSizeWitness.tokensBoundarySize,
      shortBinaryNumeralTerm witness.initialSizeWitness.tasksBoundarySize,
      shortBinaryNumeralTerm witness.finalCoordinates.start,
      shortBinaryNumeralTerm witness.finalCoordinates.finish,
      shortBinaryNumeralTerm witness.finalCoordinates.tokensFinish,
      shortBinaryNumeralTerm witness.finalCoordinates.tasksFinish,
      shortBinaryNumeralTerm witness.finalCoordinates.tokensBoundary,
      shortBinaryNumeralTerm witness.finalCoordinates.tokensCount,
      shortBinaryNumeralTerm witness.finalCoordinates.tasksBoundary,
      shortBinaryNumeralTerm witness.finalCoordinates.tasksCount,
      shortBinaryNumeralTerm witness.finalSizeWitness.tokensBoundarySize,
      shortBinaryNumeralTerm witness.finalSizeWitness.tasksBoundarySize,
      shortBinaryNumeralTerm witness.outputStart,
      shortBinaryNumeralTerm witness.outputBoundary,
      shortBinaryNumeralTerm witness.outputBoundarySize]

def compactUnifiedParserInitialFinalRowsExactFuelClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserInitialFinalRowsDef.val) ⇜
    compactUnifiedParserInitialFinalRowsExactFuelTerms tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      witness

def compactUnifiedParserInitialFinalRowsExactFuelExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    ValuationFormula :=
  compactParserInitialFinalExactFuelCountFormula stateCount inputCount ⋏
    (compactUnifiedParserStateAtRowsClosedFormula tokenTable width tokenCount
        stateBoundary stateCount 0 witness.initialCoordinates
        witness.initialSizeWitness ⋏
      (compactUnifiedParserInitialStateRowsClosedFormula tokenTable width
          tokenCount witness.initialCoordinates inputBoundary inputCount
          taskKind taskBinderArity taskRepeatCount ⋏
        (compactParserInitialFinalExactFuelFinalAtFormula tokenTable width
            tokenCount stateBoundary stateCount inputCount
            witness.finalCoordinates witness.finalSizeWitness ⋏
      compactUnifiedParserFinalStateRowsClosedFormula tokenTable width
            tokenCount witness.finalCoordinates expectedBoundary expectedCount
            witness.outputStart witness.outputBoundary
            witness.outputBoundarySize)))

end FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax
