import integration.FoundationCompactNumericListedDirectTokenSliceBitBodyFreeVariables
import integration.FoundationCompactPATermBoundedUniversalFreeVariables

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceBitUniversalOuterVariables

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAFreeFormulaVariableTransport
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalFreeVariables
open FoundationCompactNumericListedDirectTokenSliceBitBodyFreeVariables
open FoundationCompactPATermBoundedUniversalFreeVariables

theorem tokenSliceAtValuationBitUniversalOuterVariables_subset_singleton_of_atoms
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm : ValuationTerm)
    (boundTerm : ValuationTerm)
    (hbound : boundTerm.freeVariables ⊆ {0})
    (hsource :
      (tokenSliceAtValuationBitAtom tokenTableTerm sourceStartTerm
        widthTerm).freeVariables ⊆ {0, 1})
    (htarget :
      (tokenSliceAtValuationBitAtom tokenTableTerm targetStartTerm
        widthTerm).freeVariables ⊆ {0, 1}) :
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift boundTerm)
      (tokenSliceAtValuationBitBody
        tokenTableTerm widthTerm sourceStartTerm
        targetStartTerm)).freeVariables ⊆ {0} := by
  have hshiftBound :
      (Rew.bShift boundTerm).freeVariables ⊆ {0} := by
    simpa only [bShiftTerm_freeVariables_eq] using hbound
  have hexplicit :
      (tokenSliceAtValuationExplicitBitFormula
        tokenTableTerm widthTerm sourceStartTerm
        targetStartTerm).freeVariables ⊆ {0, 1} :=
    tokenSliceAtValuationExplicitBitFormula_freeVariables_subset_of_atoms
      tokenTableTerm widthTerm sourceStartTerm targetStartTerm {0, 1}
      hsource htarget
  have hbody :
      (tokenSliceAtValuationBitBody
        tokenTableTerm widthTerm sourceStartTerm
        targetStartTerm).freeVariables ⊆ {0} :=
    tokenSliceAtValuationBitBody_freeVariables_subset_singleton_of_explicit
      tokenTableTerm widthTerm sourceStartTerm targetStartTerm hexplicit
  exact termBoundedUniversal_freeVariables_subset _ _ {0}
    hshiftBound hbody

#print axioms
  tokenSliceAtValuationBitUniversalOuterVariables_subset_singleton_of_atoms

end FoundationCompactNumericListedDirectTokenSliceBitUniversalOuterVariables
