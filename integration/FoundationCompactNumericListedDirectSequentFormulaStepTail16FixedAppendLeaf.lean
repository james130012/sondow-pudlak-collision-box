import integration.FoundationCompactNumericListedDirectSequentFormulaStepFormula
import integration.FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedProof
import integration.FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler

/-! # Fixed append-slices leaf 20 -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedAppendLeaf

open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedPolynomial
open FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedProof
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula

def compactSequentFormulaStepTail16AppendNumericBound
    (width tokenCount rightCount targetCount : Nat) : Nat :=
  width + tokenCount + rightCount + targetCount + 1

def compactSequentFormulaStepTail16AppendBitBound
    (tokenTable width tokenCount rightCount targetCount : Nat) : Nat :=
  Nat.size tokenTable +
    Nat.size (compactSequentFormulaStepTail16AppendNumericBound width
      tokenCount rightCount targetCount) + 1

noncomputable def compactSequentFormulaStepTail16FixedAppendLeafOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    ClosedDirectFormulaBound
      (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
        tokenCount row.value.start row.value.finish row.value.count
        row.next.start row.next.finish row.next.count
        row.current.start row.current.finish row.current.count)
      (appendSlicesFullyFixedPayloadPolynomial
        (compactSequentFormulaStepTail16AppendNumericBound width tokenCount
          row.next.count row.current.count)
        (compactSequentFormulaStepTail16AppendBitBound tokenTable width
          tokenCount row.next.count row.current.count)) := by
  rcases hgraph with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, happend,
      _⟩
  let appendNumeric :=
    compactSequentFormulaStepTail16AppendNumericBound width tokenCount
      row.next.count row.current.count
  let appendBit :=
    compactSequentFormulaStepTail16AppendBitBound tokenTable width tokenCount
      row.next.count row.current.count
  have hwidthAppend : width <= appendNumeric := by
    unfold appendNumeric compactSequentFormulaStepTail16AppendNumericBound
    omega
  have htokenCountAppend : tokenCount <= appendNumeric := by
    unfold appendNumeric compactSequentFormulaStepTail16AppendNumericBound
    omega
  have hrightCountAppend : row.next.count <= appendNumeric := by
    unfold appendNumeric compactSequentFormulaStepTail16AppendNumericBound
    omega
  have htargetCountAppend : row.current.count <= appendNumeric := by
    unfold appendNumeric compactSequentFormulaStepTail16AppendNumericBound
    omega
  have htableSizeAppend : Nat.size tokenTable <= appendBit := by
    unfold appendBit compactSequentFormulaStepTail16AppendBitBound
    omega
  have hnumericSizeAppend : Nat.size appendNumeric <= appendBit := by
    change Nat.size appendNumeric <=
      Nat.size tokenTable + Nat.size appendNumeric + 1
    omega
  let appendExists :=
    exists_compactAdditiveNatListAppendSlicesFullyFixedPAProof tokenTable width
      tokenCount row.value.start row.value.finish row.value.count
      row.next.start row.next.finish row.next.count row.current.start
      row.current.finish row.current.count appendNumeric appendBit happend
      htableSizeAppend hwidthAppend htokenCountAppend hrightCountAppend
      htargetCountAppend hnumericSizeAppend
  exact
    { proof := Classical.choose appendExists
      payloadLength_le := by
        simpa only [appendNumeric, appendBit] using
          (Classical.choose_spec appendExists) }

#print axioms compactSequentFormulaStepTail16FixedAppendLeafOfGraph

end FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedAppendLeaf
