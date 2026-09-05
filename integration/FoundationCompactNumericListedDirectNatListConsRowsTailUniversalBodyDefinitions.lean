import integration.FoundationCompactNumericListedDirectNatListConsRowsTailSourceTerminalSyntaxUniformBound

/-! # Four intermediate formulas closing the cons-tail witnesses -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyDefinitions

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate

def natListConsRowsTailBodyAfter04
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 4 :=
  (compactAdditiveNatListConsRowsTailTerminal tokenTable width tokenCount
    sourceBoundary targetBoundary).bexsLTSucc
      (closedShift 4 (shortBinaryNumeralTerm tokenCount))

def natListConsRowsTailBodyAfter03
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 3 :=
  (natListConsRowsTailBodyAfter04 tokenTable width tokenCount sourceBoundary
    targetBoundary).bexsLTSucc
      (closedShift 3 (shortBinaryNumeralTerm tokenCount))

def natListConsRowsTailBodyAfter02
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 2 :=
  (natListConsRowsTailBodyAfter03 tokenTable width tokenCount sourceBoundary
    targetBoundary).bexsLTSucc
      (closedShift 2 (shortBinaryNumeralTerm tokenCount))

def natListConsRowsTailBodyAfter01
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (natListConsRowsTailBodyAfter02 tokenTable width tokenCount sourceBoundary
    targetBoundary).bexsLTSucc
      (closedShift 1 (shortBinaryNumeralTerm tokenCount))

theorem compactAdditiveNatListConsRowsTailBody_eq_after01
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary =
      natListConsRowsTailBodyAfter01 tokenTable width tokenCount sourceBoundary
        targetBoundary := by
  rfl

#print axioms compactAdditiveNatListConsRowsTailBody_eq_after01

end FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyDefinitions
