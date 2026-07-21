import integration.FoundationCompactNumericListedDirectVerifierStateSliceEquality
import integration.FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality

/-!
# Exact verifier-state equality across independent token tables

Every typed direct layout carries the exact flat additive encoding of its
value.  Therefore a bitwise cross-table equality between two complete state
slices equates their additive encodings, and codec injectivity equates the
states themselves.  The converse constructor follows from the same carrying
theorem and does not assume semantic equality as an arithmetic oracle.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStateCrossTableEquality

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectTraceNatListSlices
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericSequentValuePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierStateAdditiveCodec

def CompactFixedWidthSliceCarries
    (tokenTable width tokenCount start finish : Nat)
    (tokens : List Nat) : Prop :=
  finish = start + tokens.length ∧
    finish ≤ tokenCount ∧
    ∀ offset < tokens.length,
      CompactFixedWidthEntry tokenTable width (start + offset)
        (tokens.getI offset)

theorem CompactFixedWidthSliceCarries.nil
    {tokenTable width tokenCount start : Nat}
    (hstart : start ≤ tokenCount) :
    CompactFixedWidthSliceCarries
      tokenTable width tokenCount start start [] := by
  exact ⟨by simp, hstart, by simp⟩

theorem CompactFixedWidthSliceCarries.append
    {tokenTable width tokenCount start middle finish : Nat}
    {left right : List Nat}
    (hleft : CompactFixedWidthSliceCarries
      tokenTable width tokenCount start middle left)
    (hright : CompactFixedWidthSliceCarries
      tokenTable width tokenCount middle finish right) :
    CompactFixedWidthSliceCarries
      tokenTable width tokenCount start finish (left ++ right) := by
  rcases hleft with ⟨hmiddle, _hmiddleBound, hleftEntries⟩
  rcases hright with ⟨hfinish, hfinishBound, hrightEntries⟩
  refine ⟨?_, hfinishBound, ?_⟩
  · simp only [List.length_append]
    omega
  · intro offset hoffset
    by_cases hleftOffset : offset < left.length
    · have hentry := hleftEntries offset hleftOffset
      rw [List.getI_append left right offset hleftOffset]
      exact hentry
    · have hrightOffset : offset - left.length < right.length := by
        have hoffset' : offset < left.length + right.length := by
          simpa only [List.length_append] using hoffset
        omega
      have hentry := hrightEntries (offset - left.length) hrightOffset
      rw [List.getI_append_right left right offset (by omega)]
      convert hentry using 1 <;> omega

theorem CompactAdditiveTokenCell.toSliceCarries
    {tokenTable width tokenCount start value finish : Nat}
    (hcell : CompactAdditiveTokenCell
      tokenTable width tokenCount start value finish) :
    CompactFixedWidthSliceCarries
      tokenTable width tokenCount start finish [value] := by
  rcases hcell with ⟨hstart, hfinish, hentry⟩
  refine ⟨by simp [hfinish], by omega, ?_⟩
  intro offset hoffset
  have hoffsetZero : offset = 0 := by simpa using hoffset
  subst offset
  simpa using hentry

theorem CompactAdditiveNatListDirectLayout.toSliceCarries
    {tokenTable width tokenCount start finish : Nat}
    {values : List Nat}
    (hlayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount start finish values) :
    CompactFixedWidthSliceCarries tokenTable width tokenCount start finish
      (compactAdditiveEncode values) := by
  have hslice := CompactAdditiveNatListDirectLayout.toSlice hlayout
  rcases hslice with ⟨bodyStart, _hbodyBound, hheader, hfinish⟩
  have hbodyStart : bodyStart = start + 1 := hheader.1.2.1
  have hbodyFinishBound : bodyStart + values.length ≤ tokenCount := hheader.2
  have hfinishBound : finish ≤ tokenCount := by omega
  rw [compactAdditiveEncode_natList_eq]
  refine ⟨?_, hfinishBound, ?_⟩
  · simp
    omega
  intro offset hoffset
  cases offset with
  | zero =>
      simpa using hheader.1.2.2
  | succ index =>
      have hindex : index < values.length := by simpa using hoffset
      have hentry := CompactAdditiveNatListDirectLayout.valueEntry
        hlayout index hindex
      simpa [Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hentry

theorem CompactAdditiveStructuredListElementRowLayouts.toSliceCarries
    {alpha : Type*} [Inhabited alpha] [Primcodable alpha]
    [CompactAdditiveTokenCodec alpha]
    (ElementLayout : Nat → Nat → Nat → Nat → Nat → alpha → Prop)
    {tokenTable width tokenCount start finish boundaryTable : Nat}
    {values : List alpha}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start values.length finish boundaryTable)
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      ElementLayout tokenTable width tokenCount boundaryTable values)
    (helement : ∀ {left right : Nat} {value : alpha},
      ElementLayout tokenTable width tokenCount left right value →
        CompactFixedWidthSliceCarries tokenTable width tokenCount left right
          (compactAdditiveEncode value)) :
    CompactFixedWidthSliceCarries tokenTable width tokenCount start finish
      (compactAdditiveEncode values) := by
  rcases hlayout with
    ⟨bodyStart, _hbodyBound, hheader, hboundaries⟩
  have hheaderCarries := CompactAdditiveTokenCell.toSliceCarries hheader.1
  let rec bodyCarries
      (index : Nat) (hindex : index ≤ values.length)
      (cursor : Nat)
      (hcursor : CompactFixedWidthEntry
        boundaryTable tokenCount index cursor) :
      CompactFixedWidthSliceCarries tokenTable width tokenCount cursor finish
        ((values.drop index).flatMap compactAdditiveEncode) := by
    by_cases hend : index = values.length
    · subst index
      have hcursorFinish : cursor = finish :=
        (CompactFixedWidthEntry.value_eq_tableValue hcursor).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hboundaries.2.2.2.1).symm
      subst cursor
      simpa using CompactFixedWidthSliceCarries.nil hboundaries.2.1
    · have hrow : index < values.length := by omega
      rcases hrows index hrow with
        ⟨left, _hleft, right, _hright,
          hleftEntry, hrightEntry, hvalue⟩
      have hcursorLeft : cursor = left :=
        (CompactFixedWidthEntry.value_eq_tableValue hcursor).trans
          (CompactFixedWidthEntry.value_eq_tableValue hleftEntry).symm
      subst left
      have hhead := helement hvalue
      have htail := bodyCarries (index + 1) (by omega)
        right hrightEntry
      have hcombined := CompactFixedWidthSliceCarries.append hhead htail
      have htokens :
          (values.drop index).flatMap compactAdditiveEncode =
            compactAdditiveEncode (values.getI index) ++
              (values.drop (index + 1)).flatMap compactAdditiveEncode := by
        rw [List.drop_eq_getElem_cons hrow]
        simp only [List.flatMap_cons]
        rw [List.getI_eq_getElem values hrow]
      rw [htokens]
      exact hcombined
    termination_by values.length - index
  have hbody := bodyCarries 0 (by omega) bodyStart hboundaries.2.2.1
  have hall := CompactFixedWidthSliceCarries.append hheaderCarries hbody
  simpa [compactAdditiveEncode_list] using hall

theorem CompactAdditiveNatListListDirectLayout.toSliceCarries
    {tokenTable width tokenCount start finish : Nat}
    {values : List (List Nat)}
    (hlayout : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount start finish values) :
    CompactFixedWidthSliceCarries tokenTable width tokenCount start finish
      (compactAdditiveEncode values) := by
  rcases hlayout with ⟨boundaryTable, hstructure, hrows, _hsize⟩
  exact CompactAdditiveStructuredListElementRowLayouts.toSliceCarries
    CompactAdditiveNatListDirectLayout hstructure hrows
      (fun hvalue =>
        CompactAdditiveNatListDirectLayout.toSliceCarries hvalue)

theorem CompactNumericNodeFieldsDirectLayout.toSliceCarries
    {tokenTable width tokenCount start finish : Nat}
    {fields : CompactNumericNodeFields}
    (hlayout : CompactNumericNodeFieldsDirectLayout
      tokenTable width tokenCount start finish fields) :
    CompactFixedWidthSliceCarries tokenTable width tokenCount start finish
      (compactAdditiveEncode fields) := by
  rcases hlayout with
    ⟨gammaFinish, firstFinish, secondFinish, witnessFinish,
      hgamma, hfirst, hsecond, hwitness, hsuffix⟩
  have hall := CompactFixedWidthSliceCarries.append
    (CompactAdditiveNatListListDirectLayout.toSliceCarries hgamma) <|
    CompactFixedWidthSliceCarries.append
      (CompactAdditiveNatListDirectLayout.toSliceCarries hfirst) <|
      CompactFixedWidthSliceCarries.append
        (CompactAdditiveNatListDirectLayout.toSliceCarries hsecond) <|
        CompactFixedWidthSliceCarries.append
          (CompactAdditiveNatListDirectLayout.toSliceCarries hwitness)
          (CompactAdditiveNatListDirectLayout.toSliceCarries hsuffix)
  simpa [compactAdditiveEncode_prod, List.append_assoc] using hall

theorem CompactNumericVerifierTaskDirectLayout.toSliceCarries
    {tokenTable width tokenCount start finish : Nat}
    {task : CompactNumericVerifierTask}
    (hlayout : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount start finish task) :
    CompactFixedWidthSliceCarries tokenTable width tokenCount start finish
      (compactAdditiveEncode task) := by
  rcases hlayout with ⟨fieldsStart, htag, hfields⟩
  have hall := CompactFixedWidthSliceCarries.append
    (CompactAdditiveTokenCell.toSliceCarries htag)
    (CompactNumericNodeFieldsDirectLayout.toSliceCarries hfields)
  simpa [compactAdditiveEncode_prod] using hall

theorem CompactNumericChildResultDirectLayout.toSliceCarries
    {tokenTable width tokenCount start finish : Nat}
    {value : CompactNumericChildResult}
    (hlayout : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount start finish value) :
    CompactFixedWidthSliceCarries tokenTable width tokenCount start finish
      (compactAdditiveEncode value) := by
  rcases hlayout with
    ⟨gammaFinish, gammaBoundary, boolValue,
      _hproduct, hgammaLayout, hgammaRows, hboolValue, hbool, hgammaSize⟩
  have hgamma : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount start gammaFinish value.1 :=
    ⟨gammaBoundary, hgammaLayout, hgammaRows, hgammaSize⟩
  have hboolCell : CompactAdditiveTokenCell
      tokenTable width tokenCount gammaFinish
        (compactAdditiveBoolTag value.2) finish := by
    simpa only [hboolValue] using hbool.1
  have hall := CompactFixedWidthSliceCarries.append
    (CompactAdditiveNatListListDirectLayout.toSliceCarries hgamma)
    (CompactAdditiveTokenCell.toSliceCarries hboolCell)
  simpa [compactAdditiveEncode_prod, compactAdditiveEncode_bool,
    compactAdditiveBoolTag] using hall

theorem CompactAdditiveOptionBoolDirectLayout.toSliceCarries
    {tokenTable width tokenCount start finish : Nat}
    {status : Option Bool}
    (hlayout : CompactAdditiveOptionBoolDirectLayout
      tokenTable width tokenCount start finish status) :
    CompactFixedWidthSliceCarries tokenTable width tokenCount start finish
      (compactAdditiveEncode status) := by
  rcases hlayout with ⟨tag, payloadStart, hoption, hcase⟩
  cases status with
  | none =>
      rcases hcase with hnone | hsome
      · rcases hnone with ⟨_hstatus, htag, hfinish⟩
        have htagCell : CompactAdditiveTokenCell
            tokenTable width tokenCount start 0 payloadStart := by
          simpa only [htag] using hoption.1
        simpa [compactAdditiveEncode_option_none, hfinish] using
          CompactAdditiveTokenCell.toSliceCarries htagCell
      · rcases hsome with ⟨result, hstatus, _htag, _hbool⟩
        simp at hstatus
  | some result =>
      rcases hcase with hnone | hsome
      · rcases hnone with ⟨hstatus, _htag, _hfinish⟩
        simp at hstatus
      · rcases hsome with
          ⟨storedResult, hstatus, htag, hbool⟩
        have hresult : storedResult = result := Option.some.inj hstatus.symm
        subst storedResult
        have htagCell : CompactAdditiveTokenCell
            tokenTable width tokenCount start 1 payloadStart := by
          simpa only [htag] using hoption.1
        have hall := CompactFixedWidthSliceCarries.append
          (CompactAdditiveTokenCell.toSliceCarries htagCell)
          (CompactAdditiveTokenCell.toSliceCarries hbool.1)
        simpa [compactAdditiveEncode_option_some,
          compactAdditiveEncode_bool, compactAdditiveBoolTag] using hall

theorem CompactNumericVerifierStateDirectLayout.toSliceCarries
    {tokenTable width tokenCount start finish : Nat}
    {state : CompactNumericVerifierState}
    (hlayout : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount start finish state) :
    CompactFixedWidthSliceCarries tokenTable width tokenCount start finish
      (compactAdditiveEncode state) := by
  rcases hlayout with
    ⟨proofFinish, certificateFinish, tasksFinish, valuesFinish,
      taskBoundary, valueBoundary,
      hproof, hcertificate, htaskLayout, htaskRows, _htaskSize,
      hvalueLayout, hvalueRows, _hvalueSize, hstatus⟩
  have htasks :=
    CompactAdditiveStructuredListElementRowLayouts.toSliceCarries
      CompactNumericVerifierTaskDirectLayout htaskLayout htaskRows
      (fun htask =>
        CompactNumericVerifierTaskDirectLayout.toSliceCarries htask)
  have hvalues :=
    CompactAdditiveStructuredListElementRowLayouts.toSliceCarries
      CompactNumericChildResultDirectLayout hvalueLayout hvalueRows
      (fun hvalue =>
        CompactNumericChildResultDirectLayout.toSliceCarries hvalue)
  have hall := CompactFixedWidthSliceCarries.append
    (CompactAdditiveNatListDirectLayout.toSliceCarries hproof) <|
    CompactFixedWidthSliceCarries.append
      (CompactAdditiveNatListDirectLayout.toSliceCarries hcertificate) <|
      CompactFixedWidthSliceCarries.append htasks <|
        CompactFixedWidthSliceCarries.append hvalues
          (CompactAdditiveOptionBoolDirectLayout.toSliceCarries hstatus)
  simpa [compactAdditiveEncode_prod, List.append_assoc] using hall

private theorem fixedWidthEntry_cross_true_iff
    {sourceTable sourceWidth sourceIndex
      targetTable targetWidth targetIndex value bitIndex : Nat}
    (hsource : CompactFixedWidthEntry
      sourceTable sourceWidth sourceIndex value)
    (htarget : CompactFixedWidthEntry
      targetTable targetWidth targetIndex value) :
    (bitIndex < sourceWidth ∧
        sourceTable.testBit (sourceIndex * sourceWidth + bitIndex) = true) ↔
      (bitIndex < targetWidth ∧
        targetTable.testBit (targetIndex * targetWidth + bitIndex) = true) := by
  constructor
  · rintro ⟨hsourceWidth, hsourceTrue⟩
    have hvalueTrue : value.testBit bitIndex = true := by
      rw [← hsource.2 bitIndex hsourceWidth]
      exact hsourceTrue
    have htargetWidth : bitIndex < targetWidth := by
      by_contra hnot
      have hvalueLt : value < 2 ^ bitIndex :=
        Nat.size_le.mp (htarget.1.trans (Nat.le_of_not_gt hnot))
      rw [Nat.testBit_eq_false_of_lt hvalueLt] at hvalueTrue
      simp at hvalueTrue
    exact ⟨htargetWidth, by
      rw [htarget.2 bitIndex htargetWidth]
      exact hvalueTrue⟩
  · rintro ⟨htargetWidth, htargetTrue⟩
    have hvalueTrue : value.testBit bitIndex = true := by
      rw [← htarget.2 bitIndex htargetWidth]
      exact htargetTrue
    have hsourceWidth : bitIndex < sourceWidth := by
      by_contra hnot
      have hvalueLt : value < 2 ^ bitIndex :=
        Nat.size_le.mp (hsource.1.trans (Nat.le_of_not_gt hnot))
      rw [Nat.testBit_eq_false_of_lt hvalueLt] at hvalueTrue
      simp at hvalueTrue
    exact ⟨hsourceWidth, by
      rw [hsource.2 bitIndex hsourceWidth]
      exact hvalueTrue⟩

theorem CompactFixedWidthSliceCarries.crossTableSlicesEq
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat}
    {tokens : List Nat}
    (hsource : CompactFixedWidthSliceCarries
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish tokens)
    (htarget : CompactFixedWidthSliceCarries
      targetTable targetWidth targetTokenCount targetStart targetFinish tokens) :
    CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish := by
  rcases hsource with
    ⟨hsourceFinish, hsourceBound, hsourceEntries⟩
  rcases htarget with
    ⟨htargetFinish, htargetBound, htargetEntries⟩
  refine ⟨tokens.length, ?_, ?_, hsourceFinish, htargetFinish,
    hsourceBound, htargetBound, ?_⟩
  · omega
  · omega
  · intro offset hoffset bitIndex _hbitIndex
    exact fixedWidthEntry_cross_true_iff
      (hsourceEntries offset hoffset) (htargetEntries offset hoffset)

theorem CompactFixedWidthCrossTableSlicesEq.carriedTokens_eq
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat}
    {sourceTokens targetTokens : List Nat}
    (heq : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish)
    (hsource : CompactFixedWidthSliceCarries
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
        sourceTokens)
    (htarget : CompactFixedWidthSliceCarries
      targetTable targetWidth targetTokenCount targetStart targetFinish
        targetTokens) :
    targetTokens = sourceTokens := by
  rcases hsource with
    ⟨hsourceCarriesFinish, hsourceCarriesBound, hsourceEntries⟩
  rcases htarget with
    ⟨htargetCarriesFinish, htargetCarriesBound, htargetEntries⟩
  rcases heq with
    ⟨count, hsourceCount, htargetCount,
      hsourceFinish, htargetFinish,
      hsourceBound, htargetBound, hbits⟩
  have hlength : targetTokens.length = sourceTokens.length := by
    omega
  let heq' : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish :=
    ⟨count, hsourceCount, htargetCount,
      hsourceFinish, htargetFinish,
      hsourceBound, htargetBound, hbits⟩
  apply List.ext_getElem
  · exact hlength
  · intro index htargetIndex hsourceIndex
    have hvalue := heq'.entryValue_eq_at_offset
      (by omega) (hsourceEntries index hsourceIndex)
        (htargetEntries index htargetIndex)
    simpa [List.getI_eq_getElem _ hsourceIndex,
      List.getI_eq_getElem _ htargetIndex] using hvalue.symm

theorem compactAdditiveEncode_injective
    {alpha : Type*} [Primcodable alpha] [CompactAdditiveTokenCodec alpha] :
    Function.Injective (@compactAdditiveEncode alpha _ _) := by
  intro left right hencode
  have hleft := compactAdditiveDecode_encode_append left ([] : List Nat)
  have hright := compactAdditiveDecode_encode_append right ([] : List Nat)
  have hdecoded :
      (some (left, ([] : List Nat)) : Option (alpha × List Nat)) =
        some (right, ([] : List Nat)) := by
    rw [← hleft, ← hright]
    simpa using congrArg
      (fun tokens => compactAdditiveDecode tokens) hencode
  exact congrArg Prod.fst (Option.some.inj hdecoded)

theorem CompactFixedWidthCrossTableSlicesEq.of_verifierStateLayouts
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat}
    {state : CompactNumericVerifierState}
    (hsource : CompactNumericVerifierStateDirectLayout
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish state)
    (htarget : CompactNumericVerifierStateDirectLayout
      targetTable targetWidth targetTokenCount targetStart targetFinish state) :
    CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish :=
  CompactFixedWidthSliceCarries.crossTableSlicesEq
    (CompactNumericVerifierStateDirectLayout.toSliceCarries hsource)
    (CompactNumericVerifierStateDirectLayout.toSliceCarries htarget)

theorem CompactFixedWidthCrossTableSlicesEq.verifierStateValue_eq
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat}
    {sourceState targetState : CompactNumericVerifierState}
    (heq : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish)
    (hsource : CompactNumericVerifierStateDirectLayout
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
        sourceState)
    (htarget : CompactNumericVerifierStateDirectLayout
      targetTable targetWidth targetTokenCount targetStart targetFinish
        targetState) :
    targetState = sourceState := by
  have htokens :=
    CompactFixedWidthCrossTableSlicesEq.carriedTokens_eq heq
    (CompactNumericVerifierStateDirectLayout.toSliceCarries hsource)
    (CompactNumericVerifierStateDirectLayout.toSliceCarries htarget)
  exact compactAdditiveEncode_injective htokens

#print axioms CompactFixedWidthSliceCarries.append
#print axioms CompactAdditiveNatListDirectLayout.toSliceCarries
#print axioms
  CompactAdditiveStructuredListElementRowLayouts.toSliceCarries
#print axioms CompactAdditiveNatListListDirectLayout.toSliceCarries
#print axioms CompactNumericVerifierStateDirectLayout.toSliceCarries
#print axioms CompactFixedWidthSliceCarries.crossTableSlicesEq
#print axioms CompactFixedWidthCrossTableSlicesEq.carriedTokens_eq
#print axioms compactAdditiveEncode_injective
#print axioms
  CompactFixedWidthCrossTableSlicesEq.of_verifierStateLayouts
#print axioms CompactFixedWidthCrossTableSlicesEq.verifierStateValue_eq

end FoundationCompactNumericListedDirectVerifierStateCrossTableEquality
