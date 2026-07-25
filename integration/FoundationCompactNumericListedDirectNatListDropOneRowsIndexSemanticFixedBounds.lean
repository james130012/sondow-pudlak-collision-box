import integration.FoundationCompactNumericListedDirectNatListDropOneRowsIndexTermsFixedBounds

/-!
# Semantic bounds for the four drop-one row indices

The parser continuation branch consumes exactly one source row.  Its graph
equation `sourceCount = 1 + targetCount`, together with the bounded universal
row index, supplies every index bound used by the fixed-width entry compiler.
No index ceiling is accepted as an additional input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListDropOneRowsIndexSemanticFixedBounds

open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListDropOneRowsIndexTermsFixedBounds

private abbrev dropOneRowsZeroValuation : Nat -> Nat := fun _ => 0

def dropOneRowsValuation (index : Nat) : Nat -> Nat :=
  extendValuation index dropOneRowsZeroValuation

structure DropOneRowsIndexSemanticBounds
    (sourceCount targetCount index numericBound bitBound : Nat) : Prop where
  sourceIndexValue :
    termValue (dropOneRowsValuation index) dropOneSourceIndexTerm <=
      numericBound
  sourceNextValue :
    termValue (dropOneRowsValuation index) dropOneSourceNextTerm <=
      numericBound
  targetIndexValue :
    termValue (dropOneRowsValuation index) dropOneTargetIndexTerm <=
      numericBound
  targetNextValue :
    termValue (dropOneRowsValuation index) dropOneTargetNextTerm <=
      numericBound
  sourceIndexSize :
    Nat.size
        (termValue (dropOneRowsValuation index) dropOneSourceIndexTerm) <=
      bitBound
  sourceNextSize :
    Nat.size
        (termValue (dropOneRowsValuation index) dropOneSourceNextTerm) <=
      bitBound
  targetIndexSize :
    Nat.size
        (termValue (dropOneRowsValuation index) dropOneTargetIndexTerm) <=
      bitBound
  targetNextSize :
    Nat.size
        (termValue (dropOneRowsValuation index) dropOneTargetNextTerm) <=
      bitBound

theorem dropOneRowsIndexSemanticBounds_of_graph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 1)
    (index : Fin targetCount)
    (hsourceCount : sourceCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    DropOneRowsIndexSemanticBounds sourceCount targetCount index numericBound
      bitBound := by
  have hindexNextTarget : index.val + 1 <= targetCount :=
    Nat.succ_le_of_lt index.isLt
  have hsourceNextCount : 1 + index.val + 1 <= sourceCount := by
    rw [hgraph.2.1]
    omega
  have hsourceIndex : 1 + index.val <= numericBound :=
    (by omega : 1 + index.val <= sourceCount).trans hsourceCount
  have hsourceNext : 1 + index.val + 1 <= numericBound :=
    hsourceNextCount.trans hsourceCount
  have htargetIndex : index.val <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have htargetNext : index.val + 1 <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have hsourceIndexValue :
      termValue (dropOneRowsValuation index) dropOneSourceIndexTerm <=
        numericBound := by
    rw [termValue_dropOneSourceIndexTerm]
    exact hsourceIndex
  have hsourceNextValue :
      termValue (dropOneRowsValuation index) dropOneSourceNextTerm <=
        numericBound := by
    rw [termValue_dropOneSourceNextTerm]
    exact hsourceNext
  have htargetIndexValue :
      termValue (dropOneRowsValuation index) dropOneTargetIndexTerm <=
        numericBound := by
    rw [termValue_dropOneTargetIndexTerm]
    exact htargetIndex
  have htargetNextValue :
      termValue (dropOneRowsValuation index) dropOneTargetNextTerm <=
        numericBound := by
    rw [termValue_dropOneTargetNextTerm]
    exact htargetNext
  exact
    { sourceIndexValue := hsourceIndexValue
      sourceNextValue := hsourceNextValue
      targetIndexValue := htargetIndexValue
      targetNextValue := htargetNextValue
      sourceIndexSize :=
        (Nat.size_le_size hsourceIndexValue).trans hnumericSize
      sourceNextSize :=
        (Nat.size_le_size hsourceNextValue).trans hnumericSize
      targetIndexSize :=
        (Nat.size_le_size htargetIndexValue).trans hnumericSize
      targetNextSize :=
        (Nat.size_le_size htargetNextValue).trans hnumericSize }

#print axioms dropOneRowsIndexSemanticBounds_of_graph

end FoundationCompactNumericListedDirectNatListDropOneRowsIndexSemanticFixedBounds
