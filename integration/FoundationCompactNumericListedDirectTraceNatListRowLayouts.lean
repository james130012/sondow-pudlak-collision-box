import integration.FoundationCompactNumericListedDirectTraceNatListSlices
import integration.FoundationCompactNumericListedDirectAtomicListLayouts

/-!
# Exact row layouts for top-level natural-list trace components

The certified input, formula input, and parsed formula value each receive one
canonical element-boundary table in the complete direct-trace token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectTraceNatListRowLayouts

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectTraceNatListSlices
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectStructuredListCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts

def CompactNatListComponentRowLayout
    (tokenTable width tokenCount start finish boundaryTable : Nat)
    (values : List Nat) : Prop :=
  CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start values.length finish boundaryTable ∧
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        boundaryTable values ∧
    Nat.size boundaryTable ≤ (values.length + 1) * tokenCount

theorem compactNatListComponentRowLayout_at_component
    (components : List (List Nat)) (index : Nat) (values : List Nat)
    (hindex : index < components.length)
    (hcomponent : components.getI index = compactAdditiveEncode values) :
    let tokens := components.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let boundaries := compactAdditiveComponentBoundaries components
    ∃ boundaryTable,
      CompactNatListComponentRowLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length (boundaries.getI index)
          (boundaries.getI (index + 1)) boundaryTable values := by
  let tokens := components.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let boundaries := compactAdditiveComponentBoundaries components
  let start := boundaries.getI index
  let finish := boundaries.getI (index + 1)
  let frontTokens := (components.take index).flatten
  let backTokens := (components.drop (index + 1)).flatten
  let boundaryTable := compactAdditiveStructuredListElementBoundaryTable
    tokens.length (start + 1) values
  have hsplit := List.flatten_split_at components index hindex
  have htokens :
      frontTokens ++ compactAdditiveEncode values ++ backTokens = tokens := by
    rw [hcomponent] at hsplit
    simpa [tokens, frontTokens, backTokens, List.append_assoc] using
      hsplit.symm
  have hstart : frontTokens.length = start := by
    exact (compactAdditiveComponentBoundaries_getI_eq_take
      components index (Nat.le_of_lt hindex)).symm
  have hfinish : finish = start + (compactAdditiveEncode values).length := by
    have hnext :=
      compactAdditiveComponentBoundaries_getI_next components index hindex
    rw [hcomponent] at hnext
    exact hnext
  have hcanonical := compactAdditiveNatListElementLayouts_canonical
    frontTokens values backTokens
  dsimp only at hcanonical
  rw [htokens] at hcanonical
  rcases hcanonical with ⟨hlayout, hrows, hsize⟩
  have hlayout' : CompactAdditiveStructuredListLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start values.length finish boundaryTable := by
    simpa only [width, hstart, hfinish, boundaryTable] using hlayout
  have hrows' : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length boundaryTable values := by
    simpa only [width, hstart, boundaryTable] using hrows
  have hsize' : Nat.size boundaryTable ≤
      (values.length + 1) * tokens.length := by
    simpa only [hstart, boundaryTable] using hsize
  exact ⟨boundaryTable, hlayout', hrows', hsize'⟩

theorem compactNumericListedDirectTrace_three_natList_row_layouts
    (trace : CompactNumericListedDirectTrace) :
    let components := compactNumericListedDirectTraceComponentTokens trace
    let tokens := compactNumericListedDirectTraceTokens trace
    let width := (compactBinaryNatPayloadBits tokens).length
    let boundaries := compactAdditiveComponentBoundaries components
    ∃ certifiedBoundary formulaBoundary formulaValueBoundary,
      CompactNatListComponentRowLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length (boundaries.getI 0) (boundaries.getI 1)
          certifiedBoundary (compactNumericDirectTraceCertifiedTokens trace) ∧
      CompactNatListComponentRowLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length (boundaries.getI 2) (boundaries.getI 3)
          formulaBoundary (compactNumericDirectTraceFormulaTokens trace) ∧
      CompactNatListComponentRowLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length (boundaries.getI 10) (boundaries.getI 11)
          formulaValueBoundary (compactNumericDirectTraceFormulaValue trace) := by
  let components := compactNumericListedDirectTraceComponentTokens trace
  let tokens := compactNumericListedDirectTraceTokens trace
  let width := (compactBinaryNatPayloadBits tokens).length
  let boundaries := compactAdditiveComponentBoundaries components
  have htokens : components.flatten = tokens :=
    (compactNumericListedDirectTraceTokens_eq_flatten_components trace).symm
  have hzero : 0 < components.length := by simp [components]
  have htwo : 2 < components.length := by simp [components]
  have hten : 10 < components.length := by simp [components]
  have hcomponentZero : components.getI 0 =
      compactAdditiveEncode (compactNumericDirectTraceCertifiedTokens trace) := by
    simp [components, compactNumericListedDirectTraceComponentTokens]
  have hcomponentTwo : components.getI 2 =
      compactAdditiveEncode (compactNumericDirectTraceFormulaTokens trace) := by
    simp [components, compactNumericListedDirectTraceComponentTokens]
  have hcomponentTen : components.getI 10 =
      compactAdditiveEncode (compactNumericDirectTraceFormulaValue trace) := by
    simp [components, compactNumericListedDirectTraceComponentTokens]
  rcases compactNatListComponentRowLayout_at_component components 0
      (compactNumericDirectTraceCertifiedTokens trace) hzero hcomponentZero with
    ⟨certifiedBoundary, hcertified⟩
  rcases compactNatListComponentRowLayout_at_component components 2
      (compactNumericDirectTraceFormulaTokens trace) htwo hcomponentTwo with
    ⟨formulaBoundary, hformula⟩
  rcases compactNatListComponentRowLayout_at_component components 10
      (compactNumericDirectTraceFormulaValue trace) hten hcomponentTen with
    ⟨formulaValueBoundary, hformulaValue⟩
  rw [htokens] at hcertified hformula hformulaValue
  exact ⟨certifiedBoundary, formulaBoundary, formulaValueBoundary,
    hcertified, hformula, hformulaValue⟩

#print axioms compactNatListComponentRowLayout_at_component
#print axioms compactNumericListedDirectTrace_three_natList_row_layouts

end FoundationCompactNumericListedDirectTraceNatListRowLayouts
