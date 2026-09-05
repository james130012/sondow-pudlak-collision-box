import integration.FoundationCompactNumericListedDirectNatListConsRowsHeadBodyClosed
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailOuterFormulaClosed
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsCountFullyFixedBounds

/-! # Closedness of the complete natural-list cons-rows formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsClosedFormulaClosed

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsHeadBodyClosed
open FoundationCompactNumericListedDirectNatListConsRowsTailOuterFormulaClosed
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsCountFullyFixedBounds

theorem compactAdditiveNatListConsRowsClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount head : Nat) :
    (compactAdditiveNatListConsRowsClosedFormula tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount head).freeVariables =
        ∅ := by
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount) + 1”
  let headFormula := compactAdditiveNatListConsRowsHeadBody tokenTable width
    tokenCount targetBoundary head
  let tailFormula : ValuationFormula :=
    (compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
      sourceBoundary targetBoundary).ballLT
        (shortBinaryNumeralTerm sourceCount)
  have hcount : countFormula.freeVariables = ∅ := by
    dsimp only [countFormula]
    exact taskConsCountFormula_freeVariables_eq_empty sourceCount targetCount
  have hhead : headFormula.freeVariables = ∅ := by
    dsimp only [headFormula]
    exact compactAdditiveNatListConsRowsHeadBody_freeVariables_eq_empty
      tokenTable width tokenCount targetBoundary head
  have htail : tailFormula.freeVariables = ∅ := by
    have hraw :=
      compactAdditiveNatListConsRowsTailOuterFormula_freeVariables_eq_empty
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
    have halign :
        (∀⁰ termBoundedUniversalBody
          (Rew.bShift (shortBinaryNumeralTerm sourceCount))
          (compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
            sourceBoundary targetBoundary)) = tailFormula := by
      dsimp only [tailFormula]
      rw [termBoundedUniversal_eq_ball]
      rfl
    rw [← halign]
    exact hraw
  rw [compactAdditiveNatListConsRowsClosedFormula_alignment]
  unfold compactAdditiveNatListConsRowsExplicitFormula
  simp only [LO.FirstOrder.Semiformula.freeVariables_and, hcount, hhead,
    htail, Finset.union_empty, countFormula, headFormula, tailFormula]

#print axioms
  compactAdditiveNatListConsRowsClosedFormula_freeVariables_eq_empty

end FoundationCompactNumericListedDirectNatListConsRowsClosedFormulaClosed
