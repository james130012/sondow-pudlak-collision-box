import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax

/-!
# Public-source syntax for the twenty-three bounded endpoint witnesses

The source formula has fourteen public coordinates.  Thirteen are passed to
the endpoint terminal; coordinate thirteen is the common witness bound.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax

def compactParserInitialFinalBoundedDirectSourcePublicTerms :
    Fin 13 -> ArithmeticSemiterm Nat 37 :=
  fun coordinate =>
    #(⟨23 + coordinate, by omega⟩ : Fin 37)

def compactParserInitialFinalBoundedDirectSourceWitnessTerms :
    Fin 23 -> ArithmeticSemiterm Nat 37 :=
  fun coordinate =>
    #(⟨(compactParserInitialFinalBoundedDirectReverseIndex coordinate).val,
      by omega⟩ : Fin 37)

def compactParserInitialFinalBoundedDirectSourceRawTerms :
    Fin 36 -> ArithmeticSemiterm Nat 37 :=
  Matrix.vecAppend rfl
    compactParserInitialFinalBoundedDirectSourcePublicTerms
    compactParserInitialFinalBoundedDirectSourceWitnessTerms

def compactParserInitialFinalBoundedDirectSourceRawTerminal :
    ArithmeticSemiformula Nat 37 :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserInitialFinalRowsDef.val) ⇜
    compactParserInitialFinalBoundedDirectSourceRawTerms

def compactParserInitialFinalBoundedDirectSourceRawBody :
    ArithmeticSemiformula Nat 14 :=
  sourceBoundedWitnessFormula
    (#13 : ArithmeticSemiterm Nat 14) 23
    compactParserInitialFinalBoundedDirectSourceRawTerminal

def compactParserInitialFinalBoundedDirectSourceTerms
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) :
    Fin 14 -> ValuationTerm :=
  Matrix.vecAppend rfl
    (compactParserInitialFinalBoundedDirectPublicTerms tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount)
    ![shortBinaryNumeralTerm valueBound]

def compactParserInitialFinalBoundedDirectClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) :
    ValuationFormula :=
  Rew.subst
    (compactParserInitialFinalBoundedDirectSourceTerms tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      valueBound) ▹
    compactParserInitialFinalBoundedDirectSourceRawBody

end FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceSyntax
