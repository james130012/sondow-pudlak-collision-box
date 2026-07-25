import integration.FoundationCompactNumericListedDirectNatListDropTwoRowsIndexTermsFixedBounds

/-!
# Semantic bounds for the four drop-two row indices

The graph equation `sourceCount = 2 + targetCount` and the bounded target-row
index derive every value and bit-size bound; no index ceiling is an input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 50000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListDropTwoRowsIndexSemanticFixedBounds

open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListDropTwoRowsIndexTermsFixedBounds

private abbrev dropTwoRowsZeroValuation : Nat -> Nat := fun _ => 0

def dropTwoRowsValuation (index : Nat) : Nat -> Nat :=
  extendValuation index dropTwoRowsZeroValuation

structure DropTwoRowsIndexSemanticBounds
    (sourceCount targetCount index numericBound bitBound : Nat) : Prop where
  sourceIndexValue :
    termValue (dropTwoRowsValuation index) dropTwoSourceIndexTerm <=
      numericBound
  sourceNextValue :
    termValue (dropTwoRowsValuation index) dropTwoSourceNextTerm <=
      numericBound
  targetIndexValue :
    termValue (dropTwoRowsValuation index) dropTwoTargetIndexTerm <=
      numericBound
  targetNextValue :
    termValue (dropTwoRowsValuation index) dropTwoTargetNextTerm <=
      numericBound
  sourceIndexSize :
    Nat.size
        (termValue (dropTwoRowsValuation index) dropTwoSourceIndexTerm) <=
      bitBound
  sourceNextSize :
    Nat.size
        (termValue (dropTwoRowsValuation index) dropTwoSourceNextTerm) <=
      bitBound
  targetIndexSize :
    Nat.size
        (termValue (dropTwoRowsValuation index) dropTwoTargetIndexTerm) <=
      bitBound
  targetNextSize :
    Nat.size
        (termValue (dropTwoRowsValuation index) dropTwoTargetNextTerm) <=
      bitBound

theorem dropTwoRowsIndexSemanticBounds_of_graph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 2)
    (index : Fin targetCount)
    (hsourceCount : sourceCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    DropTwoRowsIndexSemanticBounds sourceCount targetCount index numericBound
      bitBound := by
  have hsourceNextCount : 2 + index.val + 1 <= sourceCount := by
    rw [hgraph.2.1]
    omega
  have hsourceIndex : 2 + index.val <= numericBound :=
    (by omega : 2 + index.val <= sourceCount).trans hsourceCount
  have hsourceNext : 2 + index.val + 1 <= numericBound :=
    hsourceNextCount.trans hsourceCount
  have htargetIndex : index.val <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have htargetNext : index.val + 1 <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have hsourceIndexValue :
      termValue (dropTwoRowsValuation index) dropTwoSourceIndexTerm <=
        numericBound := by
    rw [termValue_dropTwoSourceIndexTerm]
    exact hsourceIndex
  have hsourceNextValue :
      termValue (dropTwoRowsValuation index) dropTwoSourceNextTerm <=
        numericBound := by
    rw [termValue_dropTwoSourceNextTerm]
    exact hsourceNext
  have htargetIndexValue :
      termValue (dropTwoRowsValuation index) dropTwoTargetIndexTerm <=
        numericBound := by
    rw [termValue_dropTwoTargetIndexTerm]
    exact htargetIndex
  have htargetNextValue :
      termValue (dropTwoRowsValuation index) dropTwoTargetNextTerm <=
        numericBound := by
    rw [termValue_dropTwoTargetNextTerm]
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

#print axioms dropTwoRowsIndexSemanticBounds_of_graph

end FoundationCompactNumericListedDirectNatListDropTwoRowsIndexSemanticFixedBounds
