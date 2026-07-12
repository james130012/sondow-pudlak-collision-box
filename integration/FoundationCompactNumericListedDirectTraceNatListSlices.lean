import integration.FoundationCompactNumericListedDirectAdditiveTypeLayouts

/-!
# The three top-level `List Nat` trace slices

Components 1, 3, and 11 of the complete direct trace are respectively the
certified token stream, formula token stream, and parsed formula value.  This
module connects their exact top-level boundaries to the direct `List Nat`
slice formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectTraceNatListSlices

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectTraceComponentTableau

theorem compactAdditiveEncode_natList_eq
    (values : List Nat) :
    compactAdditiveEncode values = values.length :: values := by
  rw [compactAdditiveEncode_list]
  congr 1
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [ih]

@[simp] theorem compactAdditiveEncode_natList_length
    (values : List Nat) :
    (compactAdditiveEncode values).length = values.length + 1 := by
  rw [compactAdditiveEncode_natList_eq]
  simp

theorem compactAdditiveComponentBoundaries_getI_next
    (components : List (List Nat)) (index : Nat)
    (hindex : index < components.length) :
    (compactAdditiveComponentBoundaries components).getI (index + 1) =
      (compactAdditiveComponentBoundaries components).getI index +
        (components.getI index).length := by
  induction components generalizing index with
  | nil => simp at hindex
  | cons component components ih =>
      cases index with
      | zero =>
          rw [compactAdditiveComponentBoundaries_getI_zero]
          rw [compactAdditiveComponentBoundaries_getI_succ
            component components 0 (by simp)]
          simp
      | succ index =>
          have hindexTail : index < components.length := by
            simpa using hindex
          rw [compactAdditiveComponentBoundaries_getI_succ
            component components (index + 1) (by simp; omega)]
          rw [compactAdditiveComponentBoundaries_getI_succ
            component components index (by simp; omega)]
          rw [List.getI_cons_succ]
          rw [ih index hindexTail]
          omega

theorem List.flatten_split_at
    (components : List (List Nat)) (index : Nat)
    (hindex : index < components.length) :
    components.flatten =
      (components.take index).flatten ++
        components.getI index ++
          (components.drop (index + 1)).flatten := by
  have htakeDrop := List.take_append_drop index components
  have hdrop := List.drop_eq_getElem_cons hindex
  calc
    components.flatten =
        (components.take index ++ components.drop index).flatten := by
      rw [htakeDrop]
    _ = (components.take index).flatten ++
        (components.drop index).flatten := by
      rw [List.flatten_append]
    _ = (components.take index).flatten ++
        (components.getI index ::
          components.drop (index + 1)).flatten := by
      rw [hdrop]
      rw [List.getI_eq_getElem _ hindex]
    _ = (components.take index).flatten ++
        components.getI index ++
          (components.drop (index + 1)).flatten := by
      simp [List.append_assoc]

theorem compactAdditiveComponentBoundaries_getI_eq_take
    (components : List (List Nat)) (index : Nat)
    (hindex : index ≤ components.length) :
    (compactAdditiveComponentBoundaries components).getI index =
      (components.take index).flatten.length := by
  induction components generalizing index with
  | nil =>
      have : index = 0 := by simp at hindex; omega
      subst index
      rfl
  | cons component components ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have hindexTail : index ≤ components.length := by
            simpa using hindex
          rw [compactAdditiveComponentBoundaries_getI_succ
            component components index (by simp; omega)]
          rw [ih index hindexTail]
          simp [List.take_succ_cons, List.length_append]

/-- A component which is the additive encoding of a `List Nat` satisfies the
exact direct slice relation between its two cumulative boundaries. -/
theorem compactAdditiveNatListSlice_at_component
    (components : List (List Nat)) (index : Nat) (values : List Nat)
    (hindex : index < components.length)
    (hcomponent : components.getI index = compactAdditiveEncode values) :
    let tokens := components.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    CompactAdditiveNatListSlice
      (compactFixedWidthTableCode width tokens)
      width tokens.length
      ((compactAdditiveComponentBoundaries components).getI index)
      values.length
      ((compactAdditiveComponentBoundaries components).getI (index + 1)) := by
  let tokens := components.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := (compactAdditiveComponentBoundaries components).getI index
  let finish :=
    (compactAdditiveComponentBoundaries components).getI (index + 1)
  let frontTokens := (components.take index).flatten
  let backTokens := (components.drop (index + 1)).flatten
  have hsplit := List.flatten_split_at components index hindex
  have htokens : tokens =
      frontTokens ++ compactAdditiveEncode values ++ backTokens := by
    simpa [tokens, frontTokens, backTokens, hcomponent] using hsplit
  have hencode : compactAdditiveEncode values =
      values.length :: values :=
    compactAdditiveEncode_natList_eq values
  have hstart : start = frontTokens.length := by
    exact compactAdditiveComponentBoundaries_getI_eq_take
      components index (Nat.le_of_lt hindex)
  have hfinish : finish = start + values.length + 1 := by
    have hnext := compactAdditiveComponentBoundaries_getI_next
      components index hindex
    rw [hcomponent, compactAdditiveEncode_natList_length] at hnext
    omega
  have hwidth : ∀ token ∈ tokens, Nat.size token ≤ width := by
    intro token htoken
    exact compactBinaryNatToken_size_le_payloadLength tokens token htoken
  have hstartLt : start < tokens.length := by
    rw [htokens, hencode, hstart]
    simp
  have htokenAt : tokens.getI start = values.length := by
    rw [htokens, hencode, hstart]
    rw [List.append_assoc]
    rw [List.getI_append_right
      frontTokens (values.length :: values ++ backTokens)
      frontTokens.length (by rfl)]
    simp
  have hcellRaw := compactAdditiveTokenCell_canonical
    tokens width start hstartLt hwidth
  have hcell : CompactAdditiveTokenCell
      (compactFixedWidthTableCode width tokens)
      width tokens.length start values.length (start + 1) := by
    simpa [htokenAt] using hcellRaw
  have hremaining : start + 1 + values.length ≤ tokens.length := by
    rw [htokens, hencode, hstart]
    simp
    omega
  have hheader : CompactAdditiveListHeader
      (compactFixedWidthTableCode width tokens)
      width tokens.length start values.length (start + 1) :=
    ⟨hcell, hremaining⟩
  refine ⟨start + 1, ?_, hheader, ?_⟩
  · exact (Nat.le_add_right (start + 1) values.length).trans hremaining
  · omega

/-- Components 0, 2, and 10 are now connected to the direct `List Nat`
grammar at their exact canonical boundaries. -/
theorem compactNumericListedDirectTrace_three_natList_slices
    (trace : CompactNumericListedDirectTrace) :
    let components := compactNumericListedDirectTraceComponentTokens trace
    let tokens := compactNumericListedDirectTraceTokens trace
    let width := (compactBinaryNatPayloadBits tokens).length
    let boundaries := compactAdditiveComponentBoundaries components
    CompactAdditiveNatListSlice
        (compactFixedWidthTableCode width tokens)
        width tokens.length
        (boundaries.getI 0)
        (compactNumericDirectTraceCertifiedTokens trace).length
        (boundaries.getI 1) ∧
      CompactAdditiveNatListSlice
        (compactFixedWidthTableCode width tokens)
        width tokens.length
        (boundaries.getI 2)
        (compactNumericDirectTraceFormulaTokens trace).length
        (boundaries.getI 3) ∧
      CompactAdditiveNatListSlice
        (compactFixedWidthTableCode width tokens)
        width tokens.length
        (boundaries.getI 10)
        (compactNumericDirectTraceFormulaValue trace).length
        (boundaries.getI 11) := by
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
      compactAdditiveEncode
        (compactNumericDirectTraceCertifiedTokens trace) := by
    simp [components, compactNumericListedDirectTraceComponentTokens]
  have hcomponentTwo : components.getI 2 =
      compactAdditiveEncode
        (compactNumericDirectTraceFormulaTokens trace) := by
    simp [components, compactNumericListedDirectTraceComponentTokens]
  have hcomponentTen : components.getI 10 =
      compactAdditiveEncode
        (compactNumericDirectTraceFormulaValue trace) := by
    simp [components, compactNumericListedDirectTraceComponentTokens]
  have hfirst := compactAdditiveNatListSlice_at_component
    components 0 (compactNumericDirectTraceCertifiedTokens trace)
      hzero hcomponentZero
  have hthird := compactAdditiveNatListSlice_at_component
    components 2 (compactNumericDirectTraceFormulaTokens trace)
      htwo hcomponentTwo
  have heleventh := compactAdditiveNatListSlice_at_component
    components 10 (compactNumericDirectTraceFormulaValue trace)
      hten hcomponentTen
  rw [htokens] at hfirst hthird heleventh
  exact ⟨hfirst, hthird, heleventh⟩

#print axioms compactAdditiveEncode_natList_eq
#print axioms compactAdditiveComponentBoundaries_getI_next
#print axioms List.flatten_split_at
#print axioms compactAdditiveComponentBoundaries_getI_eq_take
#print axioms compactAdditiveNatListSlice_at_component
#print axioms compactNumericListedDirectTrace_three_natList_slices

end FoundationCompactNumericListedDirectTraceNatListSlices
