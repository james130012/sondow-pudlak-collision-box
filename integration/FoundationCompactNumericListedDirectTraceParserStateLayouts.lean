import integration.FoundationCompactNumericListedDirectParserStateListLayout

/-!
# Parser-state row layouts inside the three parser-trace components

The canonical parser-state list theorem is installed at the exact proof,
certificate, and formula parser components of one complete direct verifier
trace.  All three components use the same public token table and length scale.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectTraceParserStateLayouts

open FoundationCompactAdditiveTokenCodec
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectTraceNatListSlices
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectParserStateListLayout

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericSequentValuePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericRootFieldBranchDirectTracePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericParserDirectTracesPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericParsedDirectTraceDataPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericDirectTraceTailPrimcodable

attribute [local instance]
  compactSyntaxTaskAdditiveCodec
  compactUnifiedParserStateAdditiveCodec
  binaryNatStreamStateAdditiveCodec
  compactFormulaTokenValuesResultAdditiveCodec
  compactFormulaValuesNestedDirectTraceAdditiveCodec
  compactNumericNodeFieldsAdditiveCodec
  compactNumericRootFieldBranchDirectTraceAdditiveCodec
  compactPackedTokenStreamDirectTraceAdditiveCodec
  compactNumericVerifierTaskAdditiveCodec
  compactNumericChildResultAdditiveCodec
  compactNumericVerifierStateAdditiveCodec

def CompactUnifiedParserStateListComponentLayout
    (tokenTable width tokenCount start finish boundaryTable : Nat)
    (states : List CompactUnifiedParserState) : Prop :=
  CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start states.length finish boundaryTable ∧
    CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount boundaryTable states ∧
    Nat.size boundaryTable ≤ (states.length + 1) * tokenCount

/-- Any top-level component that is a parser-state list has one exact direct
layout between its two canonical component boundaries. -/
theorem compactUnifiedParserStateListDirectLayout_at_component
    (components : List (List Nat)) (index : Nat)
    (states : List CompactUnifiedParserState)
    (hindex : index < components.length)
    (hcomponent : components.getI index = compactAdditiveEncode states) :
    let tokens := components.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let boundaries := compactAdditiveComponentBoundaries components
    let start := boundaries.getI index
    let finish := boundaries.getI (index + 1)
    ∃ boundaryTable,
      CompactUnifiedParserStateListComponentLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length start finish boundaryTable states := by
  let tokens := components.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let boundaries := compactAdditiveComponentBoundaries components
  let start := boundaries.getI index
  let finish := boundaries.getI (index + 1)
  let frontTokens := (components.take index).flatten
  let backTokens := (components.drop (index + 1)).flatten
  let boundaryTable := compactUnifiedParserStateBoundaryTable
    tokens.length (start + 1) states
  have hsplit := List.flatten_split_at components index hindex
  have htokens :
      frontTokens ++ compactAdditiveEncode states ++ backTokens = tokens := by
    rw [hcomponent] at hsplit
    simpa [tokens, frontTokens, backTokens, List.append_assoc] using
      hsplit.symm
  have htopStart : boundaries.getI index = frontTokens.length := by
    exact compactAdditiveComponentBoundaries_getI_eq_take
      components index (Nat.le_of_lt hindex)
  have hfrontLength : frontTokens.length = start := by
    exact htopStart.symm
  have hfinish : finish = start +
      (compactAdditiveEncode states).length := by
    have hnext := compactAdditiveComponentBoundaries_getI_next
      components index hindex
    rw [hcomponent] at hnext
    exact hnext
  have hcanonical :=
    compactUnifiedParserStateListDirectLayout_canonical
      frontTokens states backTokens
  dsimp only at hcanonical
  rw [htokens] at hcanonical
  rcases hcanonical with ⟨hlayout, hrows, hsize⟩
  have hlayout' : CompactAdditiveStructuredListLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start states.length finish boundaryTable := by
    simpa only [width, hfrontLength, hfinish, boundaryTable] using hlayout
  have hrows' : CompactUnifiedParserStateListRowLayouts
      (compactFixedWidthTableCode width tokens)
      width tokens.length boundaryTable states := by
    simpa only [width, hfrontLength, boundaryTable] using hrows
  have hsize' : Nat.size boundaryTable ≤
      (states.length + 1) * tokens.length := by
    simpa only [hfrontLength, boundaryTable] using hsize
  exact ⟨boundaryTable, hlayout', hrows', hsize'⟩

/-- The proof, certificate, and formula parser traces occupy components
4, 5, and 6, ending exactly at component boundaries 5, 6, and 7. -/
theorem compactNumericListedDirectTrace_parser_state_layouts
    (trace : CompactNumericListedDirectTrace) :
    let components := compactNumericListedDirectTraceComponentTokens trace
    let tokens := compactNumericListedDirectTraceTokens trace
    let width := (compactBinaryNatPayloadBits tokens).length
    let boundaries := compactAdditiveComponentBoundaries components
    ∃ proofBoundaryTable certificateBoundaryTable formulaBoundaryTable,
      CompactUnifiedParserStateListComponentLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length (boundaries.getI 4) (boundaries.getI 5)
          proofBoundaryTable
          (compactNumericDirectTraceProofParserTrace trace) ∧
        CompactUnifiedParserStateListComponentLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length (boundaries.getI 5) (boundaries.getI 6)
          certificateBoundaryTable
          (compactNumericDirectTraceCertificateParserTrace trace) ∧
        CompactUnifiedParserStateListComponentLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length (boundaries.getI 6) (boundaries.getI 7)
          formulaBoundaryTable
          (compactNumericDirectTraceFormulaParserTrace trace) := by
  let components := compactNumericListedDirectTraceComponentTokens trace
  let tokens := compactNumericListedDirectTraceTokens trace
  let width := (compactBinaryNatPayloadBits tokens).length
  let boundaries := compactAdditiveComponentBoundaries components
  have htokens : components.flatten = tokens :=
    (compactNumericListedDirectTraceTokens_eq_flatten_components trace).symm
  have hfour : 4 < components.length := by simp [components]
  have hfive : 5 < components.length := by simp [components]
  have hsix : 6 < components.length := by simp [components]
  have hcomponentFour : components.getI 4 =
      compactAdditiveEncode
        (compactNumericDirectTraceProofParserTrace trace) := by
    simp [components, compactNumericListedDirectTraceComponentTokens]
  have hcomponentFive : components.getI 5 =
      compactAdditiveEncode
        (compactNumericDirectTraceCertificateParserTrace trace) := by
    simp [components, compactNumericListedDirectTraceComponentTokens]
  have hcomponentSix : components.getI 6 =
      compactAdditiveEncode
        (compactNumericDirectTraceFormulaParserTrace trace) := by
    simp [components, compactNumericListedDirectTraceComponentTokens]
  rcases compactUnifiedParserStateListDirectLayout_at_component
      components 4 (compactNumericDirectTraceProofParserTrace trace)
      hfour hcomponentFour with
    ⟨proofBoundaryTable, hproof⟩
  rcases compactUnifiedParserStateListDirectLayout_at_component
      components 5 (compactNumericDirectTraceCertificateParserTrace trace)
      hfive hcomponentFive with
    ⟨certificateBoundaryTable, hcertificate⟩
  rcases compactUnifiedParserStateListDirectLayout_at_component
      components 6 (compactNumericDirectTraceFormulaParserTrace trace)
      hsix hcomponentSix with
    ⟨formulaBoundaryTable, hformula⟩
  rw [htokens] at hproof hcertificate hformula
  exact ⟨proofBoundaryTable, certificateBoundaryTable,
    formulaBoundaryTable, hproof, hcertificate, hformula⟩

#print axioms compactUnifiedParserStateListDirectLayout_at_component
#print axioms compactNumericListedDirectTrace_parser_state_layouts

end FoundationCompactNumericListedDirectTraceParserStateLayouts
