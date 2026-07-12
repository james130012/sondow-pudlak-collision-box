import integration.FoundationCompactNumericListedDirectStructuredListCanonical

/-!
# Structured-list layouts inside the two packed-stream traces

Each packed-stream trace contains a Boolean payload list followed by a list of
binary-natural stream states.  Both fields now receive canonical shifted
element-boundary tables at the exact top-level product split.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectTracePackedStreamListLayouts

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectTraceNatListSlices
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectStructuredListCanonical

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

/-- A top-level pair of structured lists has two canonical list layouts whose
meeting cursor is exactly the additive product split. -/
theorem compactAdditivePairListLayouts_at_component
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β]
    [CompactAdditiveNonemptyCodec α] [CompactAdditiveNonemptyCodec β]
    (components : List (List Nat)) (index : Nat)
    (leftValues : List α) (rightValues : List β)
    (hindex : index < components.length)
    (hcomponent : components.getI index =
      compactAdditiveEncode (leftValues, rightValues)) :
    let tokens := components.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let boundaries := compactAdditiveComponentBoundaries components
    let start := boundaries.getI index
    let middle := start + (compactAdditiveEncode leftValues).length
    let finish := boundaries.getI (index + 1)
    ∃ leftBoundaryTable rightBoundaryTable,
      CompactAdditiveStructuredListLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length start leftValues.length middle
        leftBoundaryTable ∧
      CompactAdditiveStructuredListLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length middle rightValues.length finish
        rightBoundaryTable ∧
      Nat.size leftBoundaryTable ≤
        (leftValues.length + 1) * tokens.length ∧
      Nat.size rightBoundaryTable ≤
        (rightValues.length + 1) * tokens.length := by
  let tokens := components.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let boundaries := compactAdditiveComponentBoundaries components
  let start := boundaries.getI index
  let middle := start + (compactAdditiveEncode leftValues).length
  let finish := boundaries.getI (index + 1)
  let frontTokens := (components.take index).flatten
  let backTokens := (components.drop (index + 1)).flatten
  have hpairEncode : compactAdditiveEncode (leftValues, rightValues) =
      compactAdditiveEncode leftValues ++
        compactAdditiveEncode rightValues := by
    simp
  have hsplit := List.flatten_split_at components index hindex
  have htokens : tokens =
      frontTokens ++ compactAdditiveEncode leftValues ++
        compactAdditiveEncode rightValues ++ backTokens := by
    rw [hcomponent, compactAdditiveEncode_prod] at hsplit
    simpa [tokens, frontTokens, backTokens, List.append_assoc] using hsplit
  have hstart : start = frontTokens.length := by
    exact compactAdditiveComponentBoundaries_getI_eq_take
      components index (Nat.le_of_lt hindex)
  have hfinish : finish = middle +
      (compactAdditiveEncode rightValues).length := by
    have hnext := compactAdditiveComponentBoundaries_getI_next
      components index hindex
    rw [hcomponent, hpairEncode, List.length_append] at hnext
    dsimp only [finish, middle, start, boundaries]
    omega
  have hleftTokens :
      frontTokens ++ compactAdditiveEncode leftValues ++
          (compactAdditiveEncode rightValues ++ backTokens) = tokens := by
    simpa [List.append_assoc] using htokens.symm
  have hrightTokens :
      (frontTokens ++ compactAdditiveEncode leftValues) ++
          compactAdditiveEncode rightValues ++ backTokens = tokens := by
    simpa [List.append_assoc] using htokens.symm
  rcases compactAdditiveStructuredListLayout_canonical
      frontTokens leftValues
        (compactAdditiveEncode rightValues ++ backTokens) with
    ⟨leftBoundaryTable, hleftLayout, hleftSize⟩
  rcases compactAdditiveStructuredListLayout_canonical
      (frontTokens ++ compactAdditiveEncode leftValues)
      rightValues backTokens with
    ⟨rightBoundaryTable, hrightLayout, hrightSize⟩
  rw [hleftTokens] at hleftLayout hleftSize
  rw [hrightTokens] at hrightLayout hrightSize
  have hleftStart : frontTokens.length = start := hstart.symm
  have hleftFinish :
      frontTokens.length + (compactAdditiveEncode leftValues).length =
        middle := by
    simp [middle, hstart]
  have hrightStart :
      (frontTokens ++ compactAdditiveEncode leftValues).length =
        middle := by
    simp [List.length_append, middle, hstart]
  have hfinishDirect :
      middle + (compactAdditiveEncode rightValues).length = finish :=
    hfinish.symm
  have hleftLayout' : CompactAdditiveStructuredListLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start leftValues.length middle
      leftBoundaryTable := by
    simpa only [width, hleftStart, hleftFinish] using hleftLayout
  have hrightLayout' : CompactAdditiveStructuredListLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length middle rightValues.length finish
      rightBoundaryTable := by
    simpa only [width, hrightStart, hfinishDirect] using hrightLayout
  have hleftSize' : Nat.size leftBoundaryTable ≤
      (leftValues.length + 1) * tokens.length := by
    exact hleftSize
  have hrightSize' : Nat.size rightBoundaryTable ≤
      (rightValues.length + 1) * tokens.length := by
    exact hrightSize
  exact ⟨leftBoundaryTable, rightBoundaryTable,
    hleftLayout', hrightLayout', hleftSize', hrightSize'⟩

/-- Four concrete list fields inside the proof-code and formula-code stream
traces now have direct structured-list layouts. -/
theorem compactNumericListedDirectTrace_packedStream_list_layouts
    (trace : CompactNumericListedDirectTrace) :
    let components := compactNumericListedDirectTraceComponentTokens trace
    let tokens := compactNumericListedDirectTraceTokens trace
    let width := (compactBinaryNatPayloadBits tokens).length
    let boundaries := compactAdditiveComponentBoundaries components
    let proofMiddle := boundaries.getI 1 +
      (compactAdditiveEncode
        (compactNumericDirectTraceCertifiedStreamTrace trace).1).length
    let formulaMiddle := boundaries.getI 3 +
      (compactAdditiveEncode
        (compactNumericDirectTraceFormulaStreamTrace trace).1).length
    ∃ proofPayloadBoundaryTable proofStateBoundaryTable
        formulaPayloadBoundaryTable formulaStateBoundaryTable,
      CompactAdditiveStructuredListLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length (boundaries.getI 1)
        (compactNumericDirectTraceCertifiedStreamTrace trace).1.length
        proofMiddle proofPayloadBoundaryTable ∧
      CompactAdditiveStructuredListLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length proofMiddle
        (compactNumericDirectTraceCertifiedStreamTrace trace).2.length
        (boundaries.getI 2) proofStateBoundaryTable ∧
      CompactAdditiveStructuredListLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length (boundaries.getI 3)
        (compactNumericDirectTraceFormulaStreamTrace trace).1.length
        formulaMiddle formulaPayloadBoundaryTable ∧
      CompactAdditiveStructuredListLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length formulaMiddle
        (compactNumericDirectTraceFormulaStreamTrace trace).2.length
        (boundaries.getI 4) formulaStateBoundaryTable := by
  let components := compactNumericListedDirectTraceComponentTokens trace
  let tokens := compactNumericListedDirectTraceTokens trace
  let width := (compactBinaryNatPayloadBits tokens).length
  let boundaries := compactAdditiveComponentBoundaries components
  let proofMiddle := boundaries.getI 1 +
    (compactAdditiveEncode
      (compactNumericDirectTraceCertifiedStreamTrace trace).1).length
  let formulaMiddle := boundaries.getI 3 +
    (compactAdditiveEncode
      (compactNumericDirectTraceFormulaStreamTrace trace).1).length
  have htokens : components.flatten = tokens :=
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
  rcases compactAdditivePairListLayouts_at_component
      components 1
      (compactNumericDirectTraceCertifiedStreamTrace trace).1
      (compactNumericDirectTraceCertifiedStreamTrace trace).2
      hone hcomponentOne with
    ⟨proofPayloadBoundaryTable, proofStateBoundaryTable,
      hproofPayload, hproofStates, _hproofPayloadSize,
      _hproofStateSize⟩
  rcases compactAdditivePairListLayouts_at_component
      components 3
      (compactNumericDirectTraceFormulaStreamTrace trace).1
      (compactNumericDirectTraceFormulaStreamTrace trace).2
      hthree hcomponentThree with
    ⟨formulaPayloadBoundaryTable, formulaStateBoundaryTable,
      hformulaPayload, hformulaStates, _hformulaPayloadSize,
      _hformulaStateSize⟩
  rw [htokens] at hproofPayload hproofStates hformulaPayload hformulaStates
  exact ⟨proofPayloadBoundaryTable, proofStateBoundaryTable,
    formulaPayloadBoundaryTable, formulaStateBoundaryTable,
    hproofPayload, hproofStates, hformulaPayload, hformulaStates⟩

#print axioms compactAdditivePairListLayouts_at_component
#print axioms compactNumericListedDirectTrace_packedStream_list_layouts

end FoundationCompactNumericListedDirectTracePackedStreamListLayouts
