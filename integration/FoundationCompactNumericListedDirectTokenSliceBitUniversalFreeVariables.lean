import integration.FoundationCompactNumericListedDirectTokenSliceBitUniversalFixedBounds

/-!
# Free variables of the token-slice inner universal

The three endpoints are intentionally separated from syntax-code bounds so the
large quoted formula is elaborated only once on memory-constrained machines.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceBitUniversalFreeVariables

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds

theorem tokenSliceAtValuationExplicitBitFormula_freeVariables_subset_of_atoms
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm : ValuationTerm)
    (vars : Finset Nat)
    (hsource :
      (tokenSliceAtValuationBitAtom tokenTableTerm sourceStartTerm
        widthTerm).freeVariables ⊆ vars)
    (htarget :
      (tokenSliceAtValuationBitAtom tokenTableTerm targetStartTerm
        widthTerm).freeVariables ⊆ vars) :
    (tokenSliceAtValuationExplicitBitFormula
      tokenTableTerm widthTerm sourceStartTerm
      targetStartTerm).freeVariables ⊆ vars := by
  simpa only [tokenSliceAtValuationExplicitBitFormula, LogicalConnective.iff,
    LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_imp] using
      Finset.union_subset
        (Finset.union_subset hsource htarget)
        (Finset.union_subset htarget hsource)

#print axioms
  tokenSliceAtValuationExplicitBitFormula_freeVariables_subset_of_atoms

end FoundationCompactNumericListedDirectTokenSliceBitUniversalFreeVariables
