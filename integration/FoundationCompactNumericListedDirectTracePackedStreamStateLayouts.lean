import integration.FoundationCompactNumericListedDirectBinaryNatStreamStateListLayout

/-!
# State-row layouts inside the two packed-stream trace components

The generic state-list row theorem is installed at the exact proof-code and
formula-code stream components of one complete direct verifier trace.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectTracePackedStreamStateLayouts

open FoundationCompactAdditiveTokenCodec
open FoundationCompactBinaryNatStreamMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectTraceNatListSlices
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectStructuredListCanonical
open FoundationCompactNumericListedDirectBinaryNatStreamStateListLayout

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

/-- If a top-level component is a payload/state-list pair, then the state-list
suffix has one exact structured layout and one complete layout for every row. -/
theorem compactBinaryNatStreamStateListDirectLayout_at_pair_component
    (components : List (List Nat)) (index : Nat)
    (payload : List Bool) (states : List BinaryNatStreamState)
    (hindex : index < components.length)
    (hcomponent : components.getI index =
      compactAdditiveEncode (payload, states)) :
    let tokens := components.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let boundaries := compactAdditiveComponentBoundaries components
    let start := boundaries.getI index +
      (compactAdditiveEncode payload).length
    let finish := boundaries.getI (index + 1)
    ∃ boundaryTable,
      CompactAdditiveStructuredListLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length start states.length finish boundaryTable ∧
        CompactBinaryNatStreamStateListRowLayouts
          (compactFixedWidthTableCode width tokens)
          width tokens.length boundaryTable states ∧
        Nat.size boundaryTable ≤
          (states.length + 1) * tokens.length := by
  let tokens := components.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let boundaries := compactAdditiveComponentBoundaries components
  let start := boundaries.getI index +
    (compactAdditiveEncode payload).length
  let finish := boundaries.getI (index + 1)
  let frontTokens := (components.take index).flatten
  let backTokens := (components.drop (index + 1)).flatten
  let stateFront := frontTokens ++ compactAdditiveEncode payload
  let boundaryTable := compactBinaryNatStreamStateBoundaryTable
    tokens.length (start + 1) states
  have hsplit := List.flatten_split_at components index hindex
  have htokens : tokens =
      frontTokens ++ compactAdditiveEncode payload ++
        compactAdditiveEncode states ++ backTokens := by
    rw [hcomponent, compactAdditiveEncode_prod] at hsplit
    simpa [tokens, frontTokens, backTokens, List.append_assoc] using hsplit
  have hstateTokens :
      stateFront ++ compactAdditiveEncode states ++ backTokens = tokens := by
    simpa [stateFront, List.append_assoc] using htokens.symm
  have htopStart : boundaries.getI index = frontTokens.length := by
    exact compactAdditiveComponentBoundaries_getI_eq_take
      components index (Nat.le_of_lt hindex)
  have hstateFrontLength : stateFront.length = start := by
    simp [stateFront, start, htopStart]
  have hfinish : finish = start +
      (compactAdditiveEncode states).length := by
    have hnext := compactAdditiveComponentBoundaries_getI_next
      components index hindex
    rw [hcomponent, compactAdditiveEncode_prod, List.length_append] at hnext
    have hnext' :
        (compactAdditiveComponentBoundaries components).getI (index + 1) =
          (compactAdditiveComponentBoundaries components).getI index +
            ((compactAdditiveEncode payload).length +
              (compactAdditiveEncode states).length) := hnext
    dsimp only [finish, start, boundaries]
    omega
  have hcanonical :=
    compactBinaryNatStreamStateListDirectLayout_canonical
      stateFront states backTokens
  dsimp only at hcanonical
  rw [hstateTokens] at hcanonical
  rcases hcanonical with ⟨hlayout, hrows, hsize⟩
  have hlayout' : CompactAdditiveStructuredListLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start states.length finish boundaryTable := by
    simpa only [width, hstateFrontLength, hfinish,
      boundaryTable] using hlayout
  have hrows' : CompactBinaryNatStreamStateListRowLayouts
      (compactFixedWidthTableCode width tokens)
      width tokens.length boundaryTable states := by
    simpa only [width, hstateFrontLength, boundaryTable] using hrows
  have hsize' : Nat.size boundaryTable ≤
      (states.length + 1) * tokens.length := by
    simpa only [hstateFrontLength, boundaryTable] using hsize
  exact ⟨boundaryTable, hlayout', hrows', hsize'⟩

/-- Both concrete stream-state lists in one complete trace use the same public
trace token table and end exactly at top-level component boundaries 2 and 4. -/
theorem compactNumericListedDirectTrace_packedStream_state_layouts
    (trace : CompactNumericListedDirectTrace) :
    let components := compactNumericListedDirectTraceComponentTokens trace
    let tokens := compactNumericListedDirectTraceTokens trace
    let width := (compactBinaryNatPayloadBits tokens).length
    let boundaries := compactAdditiveComponentBoundaries components
    let proofStart := boundaries.getI 1 +
      (compactAdditiveEncode
        (compactNumericDirectTraceCertifiedStreamTrace trace).1).length
    let formulaStart := boundaries.getI 3 +
      (compactAdditiveEncode
        (compactNumericDirectTraceFormulaStreamTrace trace).1).length
    ∃ proofStateBoundaryTable formulaStateBoundaryTable,
      CompactAdditiveStructuredListLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length proofStart
          (compactNumericDirectTraceCertifiedStreamTrace trace).2.length
          (boundaries.getI 2) proofStateBoundaryTable ∧
        CompactBinaryNatStreamStateListRowLayouts
          (compactFixedWidthTableCode width tokens)
          width tokens.length proofStateBoundaryTable
          (compactNumericDirectTraceCertifiedStreamTrace trace).2 ∧
        Nat.size proofStateBoundaryTable ≤
          ((compactNumericDirectTraceCertifiedStreamTrace trace).2.length + 1) *
            tokens.length ∧
        CompactAdditiveStructuredListLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length formulaStart
          (compactNumericDirectTraceFormulaStreamTrace trace).2.length
          (boundaries.getI 4) formulaStateBoundaryTable ∧
        CompactBinaryNatStreamStateListRowLayouts
          (compactFixedWidthTableCode width tokens)
          width tokens.length formulaStateBoundaryTable
          (compactNumericDirectTraceFormulaStreamTrace trace).2 ∧
        Nat.size formulaStateBoundaryTable ≤
          ((compactNumericDirectTraceFormulaStreamTrace trace).2.length + 1) *
            tokens.length := by
  let components := compactNumericListedDirectTraceComponentTokens trace
  let tokens := compactNumericListedDirectTraceTokens trace
  let width := (compactBinaryNatPayloadBits tokens).length
  let boundaries := compactAdditiveComponentBoundaries components
  let proofStart := boundaries.getI 1 +
    (compactAdditiveEncode
      (compactNumericDirectTraceCertifiedStreamTrace trace).1).length
  let formulaStart := boundaries.getI 3 +
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
  rcases compactBinaryNatStreamStateListDirectLayout_at_pair_component
      components 1
      (compactNumericDirectTraceCertifiedStreamTrace trace).1
      (compactNumericDirectTraceCertifiedStreamTrace trace).2
      hone hcomponentOne with
    ⟨proofStateBoundaryTable, hproofLayout, hproofRows, hproofSize⟩
  rcases compactBinaryNatStreamStateListDirectLayout_at_pair_component
      components 3
      (compactNumericDirectTraceFormulaStreamTrace trace).1
      (compactNumericDirectTraceFormulaStreamTrace trace).2
      hthree hcomponentThree with
    ⟨formulaStateBoundaryTable, hformulaLayout, hformulaRows, hformulaSize⟩
  rw [htokens] at hproofLayout hproofRows hproofSize
  rw [htokens] at hformulaLayout hformulaRows hformulaSize
  exact ⟨proofStateBoundaryTable, formulaStateBoundaryTable,
    hproofLayout, hproofRows, hproofSize,
    hformulaLayout, hformulaRows, hformulaSize⟩

#print axioms compactBinaryNatStreamStateListDirectLayout_at_pair_component
#print axioms compactNumericListedDirectTrace_packedStream_state_layouts

end FoundationCompactNumericListedDirectTracePackedStreamStateLayouts
