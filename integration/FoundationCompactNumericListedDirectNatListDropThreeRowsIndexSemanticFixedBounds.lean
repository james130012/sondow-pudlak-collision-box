import integration.FoundationCompactNumericListedDirectNatListDropThreeRowsIndexTermsFixedBounds

/-!
# Semantic bounds for the four drop-three row indices

The graph equation `sourceCount = 3 + targetCount` and the bounded target-row
index derive every value and bit-size bound; no index ceiling is an input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 50000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListDropThreeRowsIndexSemanticFixedBounds

open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListDropThreeRowsIndexTermsFixedBounds

private abbrev dropThreeRowsZeroValuation : Nat -> Nat := fun _ => 0

def dropThreeRowsValuation (index : Nat) : Nat -> Nat :=
  extendValuation index dropThreeRowsZeroValuation

structure DropThreeRowsIndexSemanticBounds
    (sourceCount targetCount index numericBound bitBound : Nat) : Prop where
  sourceIndexValue :
    termValue (dropThreeRowsValuation index) dropThreeSourceIndexTerm <=
      numericBound
  sourceNextValue :
    termValue (dropThreeRowsValuation index) dropThreeSourceNextTerm <=
      numericBound
  targetIndexValue :
    termValue (dropThreeRowsValuation index) dropThreeTargetIndexTerm <=
      numericBound
  targetNextValue :
    termValue (dropThreeRowsValuation index) dropThreeTargetNextTerm <=
      numericBound
  sourceIndexSize :
    Nat.size
        (termValue (dropThreeRowsValuation index) dropThreeSourceIndexTerm) <=
      bitBound
  sourceNextSize :
    Nat.size
        (termValue (dropThreeRowsValuation index) dropThreeSourceNextTerm) <=
      bitBound
  targetIndexSize :
    Nat.size
        (termValue (dropThreeRowsValuation index) dropThreeTargetIndexTerm) <=
      bitBound
  targetNextSize :
    Nat.size
        (termValue (dropThreeRowsValuation index) dropThreeTargetNextTerm) <=
      bitBound

theorem dropThreeRowsIndexSemanticBounds_of_graph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 3)
    (index : Fin targetCount)
    (hsourceCount : sourceCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    DropThreeRowsIndexSemanticBounds sourceCount targetCount index numericBound
      bitBound := by
  have hsourceNextCount : 3 + index.val + 1 <= sourceCount := by
    rw [hgraph.2.1]
    omega
  have hsourceIndex : 3 + index.val <= numericBound :=
    (by omega : 3 + index.val <= sourceCount).trans hsourceCount
  have hsourceNext : 3 + index.val + 1 <= numericBound :=
    hsourceNextCount.trans hsourceCount
  have htargetIndex : index.val <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have htargetNext : index.val + 1 <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have hsourceIndexValue :
      termValue (dropThreeRowsValuation index) dropThreeSourceIndexTerm <=
        numericBound := by
    rw [termValue_dropThreeSourceIndexTerm]
    exact hsourceIndex
  have hsourceNextValue :
      termValue (dropThreeRowsValuation index) dropThreeSourceNextTerm <=
        numericBound := by
    rw [termValue_dropThreeSourceNextTerm]
    exact hsourceNext
  have htargetIndexValue :
      termValue (dropThreeRowsValuation index) dropThreeTargetIndexTerm <=
        numericBound := by
    rw [termValue_dropThreeTargetIndexTerm]
    exact htargetIndex
  have htargetNextValue :
      termValue (dropThreeRowsValuation index) dropThreeTargetNextTerm <=
        numericBound := by
    rw [termValue_dropThreeTargetNextTerm]
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

#print axioms dropThreeRowsIndexSemanticBounds_of_graph

end FoundationCompactNumericListedDirectNatListDropThreeRowsIndexSemanticFixedBounds
