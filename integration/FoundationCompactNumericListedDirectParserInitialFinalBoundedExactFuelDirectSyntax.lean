import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFullyFixedDirectBound
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceSyntax

/-!
# Exact-fuel direct syntax for the bounded parser endpoints

The public fuel coordinate is the composite parser-fuel term.  The same
twenty-three witness coordinates and the audited source quantifier stack are
reused unchanged.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceSyntax
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax

def compactParserInitialFinalBoundedExactFuelDirectPublicTerms
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat) :
    Fin 13 -> ValuationTerm :=
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
    shortBinaryNumeralTerm taskRepeatCount]

def compactParserInitialFinalBoundedExactFuelDirectRawPublicTerms
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat) :
    Fin 13 -> ArithmeticSemiterm Nat 23 :=
  fun coordinate => sourceSubstitutionLift 23
    (compactParserInitialFinalBoundedExactFuelDirectPublicTerms tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      coordinate)

def compactParserInitialFinalBoundedExactFuelDirectClosedTerms
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    Fin 36 -> ValuationTerm :=
  Matrix.vecAppend rfl
    (compactParserInitialFinalBoundedExactFuelDirectPublicTerms tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount)
    (compactParserInitialFinalBoundedDirectClosedWitnessTerms witness)

def compactParserInitialFinalBoundedExactFuelDirectRawTerms
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat) :
    Fin 36 -> ArithmeticSemiterm Nat 23 :=
  Matrix.vecAppend rfl
    (compactParserInitialFinalBoundedExactFuelDirectRawPublicTerms tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount)
    compactParserInitialFinalBoundedDirectRawWitnessTerms

def compactParserInitialFinalBoundedExactFuelDirectRawTerminal
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat) :
    ArithmeticSemiformula Nat 23 :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserInitialFinalRowsDef.val) ⇜
    compactParserInitialFinalBoundedExactFuelDirectRawTerms tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount

def compactParserInitialFinalBoundedExactFuelDirectSourceTerms
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound : Nat) :
    Fin 14 -> ValuationTerm :=
  Matrix.vecAppend rfl
    (compactParserInitialFinalBoundedExactFuelDirectPublicTerms tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount)
    ![shortBinaryNumeralTerm valueBound]

def compactParserInitialFinalBoundedExactFuelDirectClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound : Nat) :
    ValuationFormula :=
  Rew.subst
    (compactParserInitialFinalBoundedExactFuelDirectSourceTerms tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      valueBound) ▹
    compactParserInitialFinalBoundedDirectSourceRawBody

end FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax
