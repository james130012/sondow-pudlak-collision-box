import integration.FoundationCompactNumericListedDirectTokenSliceBitUniversalFreeVariables
import integration.FoundationCompactPAFreeFormulaVariableTransport

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceBitBodyFreeVariables

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAFreeFormulaVariableTransport
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate

theorem tokenSliceAtValuationBitBody_freeVariables_subset_singleton_of_explicit
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm : ValuationTerm)
    (hexplicit :
      (tokenSliceAtValuationExplicitBitFormula tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm).freeVariables ⊆ {0, 1}) :
    (tokenSliceAtValuationBitBody
      tokenTableTerm widthTerm sourceStartTerm
      targetStartTerm).freeVariables ⊆ {0} := by
  let body := tokenSliceAtValuationBitBody
    tokenTableTerm widthTerm sourceStartTerm targetStartTerm
  have halignment := tokenSliceAtValuationBitBody_free_alignment
    tokenTableTerm widthTerm sourceStartTerm targetStartTerm
  intro coordinate hcoordinate
  have hfree := freeFormula_succ_mem_of_mem body coordinate hcoordinate
  rw [halignment] at hfree
  have hsmall := hexplicit hfree
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsmall ⊢
  omega

#print axioms
  tokenSliceAtValuationBitBody_freeVariables_subset_singleton_of_explicit

end FoundationCompactNumericListedDirectTokenSliceBitBodyFreeVariables
