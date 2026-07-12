import integration.FoundationCompactNumericListedDirectTraceNatListSlices

/-!
# Product splits for the two packed-stream trace components

Top-level components 2 and 4 are pairs of a Boolean payload list and a list of
binary-natural stream states.  Their additive encodings split at one exact
middle cursor before either list grammar is opened.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectTracePackedStreamSplits

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectTraceNatListSlices
open FoundationCompactNumericListedDirectAdditiveTypeLayouts

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericSequentValuePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericRootFieldBranchDirectTracePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericParserDirectTracesPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericParsedDirectTraceDataPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericDirectTraceTailPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.binaryNatStreamStateAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactFormulaTokenValuesResultAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactFormulaValuesNestedDirectTraceAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericRootFieldBranchDirectTraceAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactPackedTokenStreamDirectTraceAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierStateAdditiveCodec

/-- Any top-level component which is an additive pair has one exact strict
split between the encodings of its two fields. -/
theorem compactAdditiveProductSplit_at_component
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β]
    [CompactAdditiveNonemptyCodec α] [CompactAdditiveNonemptyCodec β]
    (components : List (List Nat)) (index : Nat) (left : α) (right : β)
    (hindex : index < components.length)
    (hcomponent : components.getI index =
      compactAdditiveEncode (left, right)) :
    CompactAdditiveProductSplit components.flatten.length
      ((compactAdditiveComponentBoundaries components).getI index)
      ((compactAdditiveComponentBoundaries components).getI index +
        (compactAdditiveEncode left).length)
      ((compactAdditiveComponentBoundaries components).getI (index + 1)) := by
  let boundaries := compactAdditiveComponentBoundaries components
  let start := boundaries.getI index
  let middle := start + (compactAdditiveEncode left).length
  let finish := boundaries.getI (index + 1)
  have hnext := compactAdditiveComponentBoundaries_getI_next
    components index hindex
  have hcomponentLength :
      (components.getI index).length =
        (compactAdditiveEncode left).length +
          (compactAdditiveEncode right).length := by
    rw [hcomponent, compactAdditiveEncode_prod, List.length_append]
  have hfinish : finish = middle +
      (compactAdditiveEncode right).length := by
    dsimp only [finish, middle, start, boundaries]
    rw [hcomponentLength] at hnext
    omega
  have hfinishDirect :
      (compactAdditiveComponentBoundaries components).getI (index + 1) =
        (compactAdditiveComponentBoundaries components).getI index +
          (compactAdditiveEncode left).length +
            (compactAdditiveEncode right).length := by
    simpa [finish, middle, start, boundaries] using hfinish
  have hleftPos : 0 < (compactAdditiveEncode left).length :=
    List.length_pos_iff.mpr (compactAdditiveEncode_ne_nil left)
  have hrightPos : 0 < (compactAdditiveEncode right).length :=
    List.length_pos_iff.mpr (compactAdditiveEncode_ne_nil right)
  have hboundaryIndex :
      index + 1 < boundaries.length := by
    simp [boundaries]
    omega
  have hfinishMem : finish ∈ boundaries := by
    dsimp only [finish]
    rw [List.getI_eq_getElem _ hboundaryIndex]
    exact List.getElem_mem hboundaryIndex
  have hfinishBound : finish ≤ components.flatten.length :=
    compactAdditiveComponentBoundaries_bounded
      components finish hfinishMem
  simp only [CompactAdditiveProductSplit]
  constructor
  · omega
  · constructor
    · omega
    · exact hfinishBound

/-- The proof-code and formula-code stream traces are split at indices 1 and
3 of the complete twelve-component trace. -/
theorem compactNumericListedDirectTrace_packedStream_product_splits
    (trace : CompactNumericListedDirectTrace) :
    let components := compactNumericListedDirectTraceComponentTokens trace
    let tokenCount := (compactNumericListedDirectTraceTokens trace).length
    let boundaries := compactAdditiveComponentBoundaries components
    CompactAdditiveProductSplit tokenCount
        (boundaries.getI 1)
        (boundaries.getI 1 +
          (compactAdditiveEncode
            (compactNumericDirectTraceCertifiedStreamTrace trace).1).length)
        (boundaries.getI 2) ∧
      CompactAdditiveProductSplit tokenCount
        (boundaries.getI 3)
        (boundaries.getI 3 +
          (compactAdditiveEncode
            (compactNumericDirectTraceFormulaStreamTrace trace).1).length)
        (boundaries.getI 4) := by
  let components := compactNumericListedDirectTraceComponentTokens trace
  let tokenCount := (compactNumericListedDirectTraceTokens trace).length
  let boundaries := compactAdditiveComponentBoundaries components
  have htokens : components.flatten =
      compactNumericListedDirectTraceTokens trace :=
    (compactNumericListedDirectTraceTokens_eq_flatten_components trace).symm
  have hone : 1 < components.length := by simp [components]
  have hthree : 3 < components.length := by simp [components]
  have hcomponentOne : components.getI 1 =
      compactAdditiveEncode
        (compactNumericDirectTraceCertifiedStreamTrace trace) := by
    simp [components, compactNumericListedDirectTraceComponentTokens]
  have hcomponentThree : components.getI 3 =
      compactAdditiveEncode
        (compactNumericDirectTraceFormulaStreamTrace trace) := by
    simp [components, compactNumericListedDirectTraceComponentTokens]
  have hproof := compactAdditiveProductSplit_at_component
    components 1
    (compactNumericDirectTraceCertifiedStreamTrace trace).1
    (compactNumericDirectTraceCertifiedStreamTrace trace).2
    hone hcomponentOne
  have hformula := compactAdditiveProductSplit_at_component
    components 3
    (compactNumericDirectTraceFormulaStreamTrace trace).1
    (compactNumericDirectTraceFormulaStreamTrace trace).2
    hthree hcomponentThree
  rw [htokens] at hproof hformula
  exact ⟨hproof, hformula⟩

#print axioms compactAdditiveProductSplit_at_component
#print axioms compactNumericListedDirectTrace_packedStream_product_splits

end FoundationCompactNumericListedDirectTracePackedStreamSplits
