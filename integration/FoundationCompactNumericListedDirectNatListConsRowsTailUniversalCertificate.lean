import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBranchTreeFixedBound
import integration.FoundationCompactPAContextualTermBoundedUniversalCompiler

/-! # Exact bounded-universal certificate for all cons-tail rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 140000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchTreeUniformBound

abbrev natListConsRowsTailUniversalZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

def natListConsRowsTailUniversalBody
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 1 :=
  compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
    sourceBoundary targetBoundary

def natListConsRowsTailUniversalBoundTerm (sourceCount : Nat) :
    ValuationTerm :=
  shortBinaryNumeralTerm sourceCount

theorem natListConsRowsTailUniversalBoundValue_eq (sourceCount : Nat) :
    termValue natListConsRowsTailUniversalZeroValuation
        (natListConsRowsTailUniversalBoundTerm sourceCount) =
      sourceCount := by
  rw [natListConsRowsTailUniversalBoundTerm,
    termValue_shortBinaryNumeralTerm]

noncomputable def
    compactAdditiveNatListConsRowsTailUniversalBranchesAtBoundTerm
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    CheckedHybridValuationUniversalBranches
      natListConsRowsTailUniversalZeroValuation
      (natListConsRowsTailUniversalBody tokenTable width tokenCount
        sourceBoundary targetBoundary)
      (termValue natListConsRowsTailUniversalZeroValuation
        (natListConsRowsTailUniversalBoundTerm sourceCount)) := by
  exact (natListConsRowsTailUniversalBoundValue_eq sourceCount).symm ▸
    compactAdditiveNatListConsRowsTailUniformBranches tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary rows

noncomputable def compactAdditiveNatListConsRowsTailRawUniversalCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    CheckedHybridValuationBoundedFormulaCertificate
      natListConsRowsTailUniversalZeroValuation
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (natListConsRowsTailUniversalBoundTerm sourceCount))
        (natListConsRowsTailUniversalBody tokenTable width tokenCount
          sourceBoundary targetBoundary)) :=
  CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
    (natListConsRowsTailUniversalBoundTerm sourceCount)
    (natListConsRowsTailUniversalBody tokenTable width tokenCount
      sourceBoundary targetBoundary)
    (compactAdditiveNatListConsRowsTailUniversalBranchesAtBoundTerm tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary rows)

noncomputable def compactAdditiveNatListConsRowsTailUniversalCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    CheckedHybridValuationBoundedFormulaCertificate
      natListConsRowsTailUniversalZeroValuation
      ((compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary).ballLT
          (shortBinaryNumeralTerm sourceCount)) :=
  CheckedHybridValuationBoundedFormulaCertificate.cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm sourceCount))
        (compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
          sourceBoundary targetBoundary)) =
        (compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
          sourceBoundary targetBoundary).ballLT
            (shortBinaryNumeralTerm sourceCount)
    rw [termBoundedUniversal_eq_ball]
    rfl)
    (compactAdditiveNatListConsRowsTailRawUniversalCertificate tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary rows)

#print axioms compactAdditiveNatListConsRowsTailRawUniversalCertificate
#print axioms compactAdditiveNatListConsRowsTailUniversalCertificate

end FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate
