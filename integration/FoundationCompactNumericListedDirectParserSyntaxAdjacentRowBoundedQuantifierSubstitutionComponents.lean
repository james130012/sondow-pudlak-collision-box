import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntaxBase

/-! # Three components of the adjacent-row terminal substitution -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSubstitutionComponents

open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

def compactParserSyntaxAdjacentRowSourceRowFormula :
    ArithmeticSemiformula Nat 34 :=
  (Rewriting.emb (ξ := Nat)
      compactParserSyntaxAdjacentStepRowDef.val) ⇜
    ![(#27 : ArithmeticSemiterm Nat 34), #28, #29, #30, #31, #32,
      #26, #25, #24, #23, #22, #21, #20, #19, #18, #17, #16, #15,
      #14, #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1,
      #0]

def compactParserSyntaxAdjacentRowSourceCurrentStatusFormula :
    ArithmeticSemiformula Nat 34 :=
  (Rewriting.emb (ξ := Nat)
      compactBinaryNatStatusValidBoundedDef.val) ⇜
    ![(#27 : ArithmeticSemiterm Nat 34), #28, #29, #23, #25, #33]

def compactParserSyntaxAdjacentRowSourceNextStatusFormula :
    ArithmeticSemiformula Nat 34 :=
  (Rewriting.emb (ξ := Nat)
      compactBinaryNatStatusValidBoundedDef.val) ⇜
    ![(#27 : ArithmeticSemiterm Nat 34), #28, #29, #13, #15, #33]

def compactParserSyntaxAdjacentRowRawRowFormula
    (tokenTable width tokenCount stateBoundary stateCount index : Nat) :
    ArithmeticSemiformula Nat 27 :=
  (Rewriting.emb (ξ := Nat)
      compactParserSyntaxAdjacentStepRowDef.val) ⇜
    ![sourceSubstitutionLift 27 (shortBinaryNumeralTerm tokenTable),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm width),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm tokenCount),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm stateBoundary),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm stateCount),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm index),
      (#26 : ArithmeticSemiterm Nat 27), #25, #24, #23, #22, #21, #20,
      #19, #18, #17, #16, #15, #14, #13, #12, #11, #10, #9, #8, #7,
      #6, #5, #4, #3, #2, #1, #0]

def compactParserSyntaxAdjacentRowRawCurrentStatusFormula
    (tokenTable width tokenCount valueBound : Nat) :
    ArithmeticSemiformula Nat 27 :=
  (Rewriting.emb (ξ := Nat)
      compactBinaryNatStatusValidBoundedDef.val) ⇜
    ![sourceSubstitutionLift 27 (shortBinaryNumeralTerm tokenTable),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm width),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm tokenCount),
      (#23 : ArithmeticSemiterm Nat 27), #25,
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm valueBound)]

def compactParserSyntaxAdjacentRowRawNextStatusFormula
    (tokenTable width tokenCount valueBound : Nat) :
    ArithmeticSemiformula Nat 27 :=
  (Rewriting.emb (ξ := Nat)
      compactBinaryNatStatusValidBoundedDef.val) ⇜
    ![sourceSubstitutionLift 27 (shortBinaryNumeralTerm tokenTable),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm width),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm tokenCount),
      (#13 : ArithmeticSemiterm Nat 27), #15,
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm valueBound)]

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSubstitutionComponents
