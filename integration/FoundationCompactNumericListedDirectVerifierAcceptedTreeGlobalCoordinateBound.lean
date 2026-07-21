import integration.FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsGlobalBound
import integration.FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomGlobalBound
import integration.FoundationCompactNumericListedDirectVerifierTypedVerumGlobalBound
import integration.FoundationCompactNumericListedDirectVerifierTypedClosedGlobalBound
import integration.FoundationCompactNumericListedDirectVerifierTypedNonLeafGlobalBound

/-!
# One coordinate budget for every branch of a valid listed-tree execution

The sum is deliberately conservative.  Its purpose is to expose one public
number at the trace boundary while retaining branch-local proofs internally.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTreeGlobalCoordinateBound

open FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsGlobalBound
open FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomGlobalBound
open FoundationCompactNumericListedDirectVerifierTypedVerumGlobalBound
open FoundationCompactNumericListedDirectVerifierTypedClosedGlobalBound
open FoundationCompactNumericListedDirectVerifierTypedNonLeafGlobalBound

def compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
    (rowWeight : Nat) : Nat :=
  compactNumericVerifierNonParseGlobalCoordinateSizeBound rowWeight +
    compactNumericVerifierAcceptedPAAxiomGlobalCoordinateSizeBound rowWeight +
    compactNumericVerifierTypedVerumGlobalCoordinateSizeBound rowWeight +
    compactNumericVerifierTypedClosedGlobalCoordinateSizeBound rowWeight +
    compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound rowWeight

theorem compactNumericVerifierNonParseGlobal_le_acceptedTreeGlobal
    (rowWeight : Nat) :
    compactNumericVerifierNonParseGlobalCoordinateSizeBound rowWeight <=
      compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
        rowWeight := by
  unfold compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
  omega

theorem compactNumericVerifierAcceptedPAAxiomGlobal_le_acceptedTreeGlobal
    (rowWeight : Nat) :
    compactNumericVerifierAcceptedPAAxiomGlobalCoordinateSizeBound rowWeight <=
      compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
        rowWeight := by
  unfold compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
  omega

theorem compactNumericVerifierTypedVerumGlobal_le_acceptedTreeGlobal
    (rowWeight : Nat) :
    compactNumericVerifierTypedVerumGlobalCoordinateSizeBound rowWeight <=
      compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
        rowWeight := by
  unfold compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
  omega

theorem compactNumericVerifierTypedClosedGlobal_le_acceptedTreeGlobal
    (rowWeight : Nat) :
    compactNumericVerifierTypedClosedGlobalCoordinateSizeBound rowWeight <=
      compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
        rowWeight := by
  unfold compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
  omega

theorem compactNumericVerifierTypedNonLeafGlobal_le_acceptedTreeGlobal
    (rowWeight : Nat) :
    compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound rowWeight <=
      compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
        rowWeight := by
  unfold compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
  omega

#print axioms compactNumericVerifierNonParseGlobal_le_acceptedTreeGlobal
#print axioms compactNumericVerifierAcceptedPAAxiomGlobal_le_acceptedTreeGlobal
#print axioms compactNumericVerifierTypedVerumGlobal_le_acceptedTreeGlobal
#print axioms compactNumericVerifierTypedClosedGlobal_le_acceptedTreeGlobal
#print axioms compactNumericVerifierTypedNonLeafGlobal_le_acceptedTreeGlobal

end FoundationCompactNumericListedDirectVerifierAcceptedTreeGlobalCoordinateBound
