import integration.FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedProof

/-!
# Fully fixed natural-list row leaves for one checked sequent step

The three natural-list row leaves share one public numeric ceiling and one
public bit ceiling.  Their boundary-table bit bounds are derived from the
checked exact-size and boundary-area fields already present in each row graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedBounds

open FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedProof

def compactSequentFormulaStepNatListRowsNumericBound
    (width tokenCount : Nat) : Nat :=
  max width tokenCount

def compactSequentFormulaStepNatListRowsBitBound
    (tokenTable width tokenCount : Nat) : Nat :=
  max (Nat.size tokenTable)
    (max (Nat.size
      (compactSequentFormulaStepNatListRowsNumericBound width tokenCount))
      ((tokenCount + 1) * tokenCount))

def compactSequentFormulaStepNatListRowsPayloadPolynomial
    (tokenTable width tokenCount : Nat) : Nat :=
  compactNatListWitnessRowsFullyFixedPayloadPolynomial
    (compactSequentFormulaStepNatListRowsNumericBound width tokenCount)
    (compactSequentFormulaStepNatListRowsBitBound tokenTable width tokenCount)

theorem compactSequentFormulaStepNatListRows_width_le_numericBound
    (width tokenCount : Nat) :
    width <= compactSequentFormulaStepNatListRowsNumericBound width
      tokenCount := by
  exact Nat.le_max_left _ _

theorem compactSequentFormulaStepNatListRows_tokenCount_le_numericBound
    (width tokenCount : Nat) :
    tokenCount <= compactSequentFormulaStepNatListRowsNumericBound width
      tokenCount := by
  exact Nat.le_max_right _ _

theorem compactSequentFormulaStepNatListRows_tokenTableSize_le_bitBound
    (tokenTable width tokenCount : Nat) :
    Nat.size tokenTable <=
      compactSequentFormulaStepNatListRowsBitBound tokenTable width
        tokenCount := by
  exact Nat.le_max_left _ _

theorem compactSequentFormulaStepNatListRows_numericBoundSize_le_bitBound
    (tokenTable width tokenCount : Nat) :
    Nat.size (compactSequentFormulaStepNatListRowsNumericBound width
        tokenCount) <=
      compactSequentFormulaStepNatListRowsBitBound tokenTable width
        tokenCount := by
  exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem compactSequentFormulaStepNatListRows_boundaryTableSize_le_bitBound
    (tokenTable width tokenCount count boundaryTable boundarySize : Nat)
    (hcount : count <= tokenCount)
    (hsize : boundarySize = Nat.size boundaryTable)
    (harea : boundarySize <= (count + 1) * tokenCount) :
    Nat.size boundaryTable <=
      compactSequentFormulaStepNatListRowsBitBound tokenTable width
        tokenCount := by
  calc
    Nat.size boundaryTable = boundarySize := hsize.symm
    _ <= (count + 1) * tokenCount := harea
    _ <= (tokenCount + 1) * tokenCount :=
      Nat.mul_le_mul_right tokenCount (Nat.add_le_add_right hcount 1)
    _ <= compactSequentFormulaStepNatListRowsBitBound tokenTable width
        tokenCount :=
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

#print axioms
  compactSequentFormulaStepNatListRows_boundaryTableSize_le_bitBound

end FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedBounds
