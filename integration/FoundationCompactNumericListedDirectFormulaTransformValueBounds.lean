import integration.FoundationCompactNumericListedDirectTraceBounds
import integration.FoundationCompactNumericFormulaTransformTrace
import integration.FoundationCompactSyntaxTransformationCodeBounds

/-!
# Public value-weight bounds for canonical formula transformations

The verifier stores the complete emitted output and every intermediate parser
state.  This file bounds those concrete values directly from the executable
definitions.  No trace, output, or length bound is supplied as an input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformValueBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericFormulaFree
open FoundationCompactNumericFormulaShift
open FoundationCompactNumericFormulaSubstitution
open FoundationCompactNumericFormulaNegation
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactParserDirectTrace

private theorem natSize_add_le (left right : Nat) :
    Nat.size (left + right) ≤ Nat.size left + Nat.size right + 1 := by
  rw [Nat.size_le]
  have hleft : left < 2 ^ Nat.size left := Nat.lt_size_self left
  have hright : right < 2 ^ Nat.size right := Nat.lt_size_self right
  have hleftPower : 2 ^ Nat.size left ≤
      2 ^ (Nat.size left + Nat.size right) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      (Nat.le_add_right (Nat.size left) (Nat.size right))
  have hrightPower : 2 ^ Nat.size right ≤
      2 ^ (Nat.size left + Nat.size right) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      (Nat.le_add_left (Nat.size right) (Nat.size left))
  calc
    left + right < 2 ^ Nat.size left + 2 ^ Nat.size right :=
      Nat.add_lt_add hleft hright
    _ ≤ 2 ^ (Nat.size left + Nat.size right) +
        2 ^ (Nat.size left + Nat.size right) :=
      Nat.add_le_add hleftPower hrightPower
    _ = 2 ^ (Nat.size left + Nat.size right + 1) := by
      rw [pow_succ]
      omega

theorem compactAdditiveValueWeight_list_append_le
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (left right : List α) :
    compactAdditiveValueWeight (left ++ right) ≤
      compactAdditiveValueWeight left +
        compactAdditiveValueWeight right := by
  rw [compactAdditiveValueWeight_list,
    compactAdditiveValueWeight_list,
    compactAdditiveValueWeight_list]
  simp only [List.length_append, List.map_append, List.sum_append]
  have hsize := natSize_add_le left.length right.length
  omega

theorem compactAdditiveValueWeight_take_le
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (count : Nat) (values : List α) :
    compactAdditiveValueWeight (values.take count) ≤
      compactAdditiveValueWeight values := by
  exact compactAdditiveValueWeight_infix_le
    (List.take_prefix count values).isInfix

theorem compactAdditiveValueWeight_mem_le
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    {value : α} {values : List α} (hvalue : value ∈ values) :
    compactAdditiveValueWeight value ≤
      compactAdditiveValueWeight values := by
  have hinfix : [value] <:+: values :=
    (List.singleton_infix_iff value values).2 hvalue
  have hsingleton := compactAdditiveValueWeight_infix_le hinfix
  have hitem :
      compactAdditiveValueWeight value ≤
        compactAdditiveValueWeight [value] := by
    rw [compactAdditiveValueWeight_list]
    simp only [List.length_cons, List.length_nil, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil]
    omega
  exact hitem.trans hsingleton

theorem compactAdditiveValueWeight_fst_le
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β]
    (value : α × β) :
    compactAdditiveValueWeight value.1 ≤
      compactAdditiveValueWeight value := by
  rw [compactAdditiveValueWeight_prod]
  omega

theorem compactAdditiveValueWeight_snd_le
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β]
    (value : α × β) :
    compactAdditiveValueWeight value.2 ≤
      compactAdditiveValueWeight value := by
  rw [compactAdditiveValueWeight_prod]
  omega

theorem compactAdditiveValueWeight_listOfLists_length_le
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (values : List (List α)) :
    values.length ≤ compactAdditiveValueWeight values := by
  have hsum :
      values.length ≤
        (values.map compactAdditiveValueWeight).sum := by
    induction values with
    | nil => simp
    | cons value values ih =>
        have hvalue : 1 ≤ compactAdditiveValueWeight value := by
          exact compactAdditiveValueWeight_list_pos value
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        omega
  rw [compactAdditiveValueWeight_list]
  omega

theorem compactTokenAt_weight_le
    (tokens : List Nat) (index : Nat) :
    compactAdditiveValueWeight (compactTokenAt index tokens) ≤
      compactAdditiveValueWeight tokens := by
  unfold compactTokenAt
  cases hget : tokens[index]? with
  | none =>
      change compactAdditiveValueWeight 0 ≤
        compactAdditiveValueWeight tokens
      simpa [compactAdditiveValueWeight_nat] using
        compactAdditiveValueWeight_list_pos tokens
  | some token =>
      exact compactAdditiveValueWeight_mem_le
        (List.mem_of_getElem? hget)

theorem consumedTokenPrefix_weight_le
    (tokens suffix : List Nat) :
    compactAdditiveValueWeight (consumedTokenPrefix tokens suffix) ≤
      compactAdditiveValueWeight tokens := by
  exact compactAdditiveValueWeight_take_le
    (tokens.length - suffix.length) tokens

private theorem compactAdditiveValueWeight_succ_le
    (value : Nat) :
    compactAdditiveValueWeight (value + 1) ≤
      compactAdditiveValueWeight value + 1 := by
  simp only [compactAdditiveValueWeight_nat]
  exact Nat.add_le_add_right (natSize_add_one_le value) 1

private theorem compactAdditiveValueWeight_pair_le
    (first second bound : Nat)
    (hfirst : compactAdditiveValueWeight first ≤ bound)
    (hsecond : compactAdditiveValueWeight second ≤ bound) :
    compactAdditiveValueWeight [first, second] ≤ 2 * bound + 3 := by
  rw [compactAdditiveValueWeight_list]
  simp only [List.length_cons, List.length_nil, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  have hsize : Nat.size 2 = 2 := by decide
  rw [hsize]
  omega

private theorem compactAdditiveValueWeight_zero_eq :
    compactAdditiveValueWeight 0 = 1 := by
  simp

private theorem compactAdditiveValueWeight_one_eq :
    compactAdditiveValueWeight 1 = 2 := by
  norm_num [compactAdditiveValueWeight_nat, Nat.size]

private theorem nat_le_two_mul_add_six (value : Nat) :
    value ≤ 2 * value + 6 := by
  omega

theorem compactShiftConsumedTermHeader_weight_le
    (tokens : List Nat) :
    compactAdditiveValueWeight (compactShiftConsumedTermHeader tokens) ≤
      2 * compactAdditiveValueWeight tokens + 6 := by
  unfold compactShiftConsumedTermHeader
  split
  · have hindex := compactTokenAt_weight_le tokens 1
    have hsucc :=
      compactAdditiveValueWeight_succ_le (compactTokenAt 1 tokens)
    have hpositive := compactAdditiveValueWeight_list_pos tokens
    have hpair := compactAdditiveValueWeight_pair_le
      1 (compactTokenAt 1 tokens + 1)
      (compactAdditiveValueWeight tokens + 1) (by
        rw [compactAdditiveValueWeight_one_eq]
        omega) (by omega)
    exact hpair.trans (by omega)
  · omega

theorem compactFreeConsumedTermHeader_weight_le
    (binderArity : Nat) (tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFreeConsumedTermHeader binderArity tokens) ≤
      2 * compactAdditiveValueWeight tokens + 6 := by
  by_cases hlength : tokens.length = 2
  · by_cases hbound : compactTokenAt 0 tokens = 0
    · by_cases hlast : compactTokenAt 1 tokens + 1 = binderArity
      · have hpositive := compactAdditiveValueWeight_list_pos tokens
        have hpair := compactAdditiveValueWeight_pair_le
          1 0 (compactAdditiveValueWeight tokens + 1) (by
            rw [compactAdditiveValueWeight_one_eq]
            omega) (by
            rw [compactAdditiveValueWeight_zero_eq]
            omega)
        have hresult :
            compactAdditiveValueWeight [1, 0] ≤
              2 * compactAdditiveValueWeight tokens + 6 :=
          hpair.trans (by omega)
        simpa [compactFreeConsumedTermHeader,
          hlength, hbound, hlast] using hresult
      · simpa [compactFreeConsumedTermHeader,
          hlength, hbound, hlast] using
            nat_le_two_mul_add_six
              (compactAdditiveValueWeight tokens)
    · by_cases hfree : compactTokenAt 0 tokens = 1
      · have hindex := compactTokenAt_weight_le tokens 1
        have hsucc :=
          compactAdditiveValueWeight_succ_le (compactTokenAt 1 tokens)
        have hpositive := compactAdditiveValueWeight_list_pos tokens
        have hpair := compactAdditiveValueWeight_pair_le
          1 (compactTokenAt 1 tokens + 1)
          (compactAdditiveValueWeight tokens + 1) (by
            rw [compactAdditiveValueWeight_one_eq]
            omega) (by omega)
        have hresult :
            compactAdditiveValueWeight
                [1, compactTokenAt 1 tokens + 1] ≤
              2 * compactAdditiveValueWeight tokens + 6 :=
          hpair.trans (by omega)
        simpa [compactFreeConsumedTermHeader,
          hlength, hbound, hfree] using hresult
      · simpa [compactFreeConsumedTermHeader,
          hlength, hbound, hfree] using
            nat_le_two_mul_add_six
              (compactAdditiveValueWeight tokens)
  · simpa [compactFreeConsumedTermHeader, hlength] using
      nat_le_two_mul_add_six (compactAdditiveValueWeight tokens)

theorem compactSubstituteConsumedTermHeader_weight_le
    (binderArity : Nat) (witness consumed : List Nat) :
    compactAdditiveValueWeight
        (compactSubstituteConsumedTermHeader
          binderArity (witness, consumed)) ≤
      compactAdditiveValueWeight witness +
        compactAdditiveValueWeight consumed := by
  by_cases hlength : consumed.length = 2
  · by_cases hbound : compactTokenAt 0 consumed = 0
    · by_cases hlast : compactTokenAt 1 consumed + 1 = binderArity
      · simp [compactSubstituteConsumedTermHeader,
          hlength, hbound, hlast]
      · simp [compactSubstituteConsumedTermHeader,
          hlength, hbound, hlast]
    · simp [compactSubstituteConsumedTermHeader,
        hlength, hbound]
  · simp [compactSubstituteConsumedTermHeader, hlength]

private theorem compactNegationFormulaTag_weight_le
    (tag : Nat) :
    compactAdditiveValueWeight (compactNegationFormulaTag tag) ≤
      compactAdditiveValueWeight tag + 6 := by
  by_cases h0 : tag = 0
  · subst tag
    decide
  by_cases h1 : tag = 1
  · subst tag
    decide
  by_cases h2 : tag = 2
  · subst tag
    decide
  by_cases h3 : tag = 3
  · subst tag
    decide
  by_cases h4 : tag = 4
  · subst tag
    decide
  by_cases h5 : tag = 5
  · subst tag
    decide
  by_cases h6 : tag = 6
  · subst tag
    decide
  by_cases h7 : tag = 7
  · subst tag
    decide
  simp [compactNegationFormulaTag, h0, h1, h2, h3, h4, h5, h6, h7]

theorem compactNegateConsumedFormulaHeader_weight_le
    (tokens : List Nat) :
    compactAdditiveValueWeight
        (compactNegateConsumedFormulaHeader tokens) ≤
      compactAdditiveValueWeight tokens + 6 := by
  cases tokens with
  | nil => simp [compactNegateConsumedFormulaHeader]
  | cons tag tail =>
      have htag := compactNegationFormulaTag_weight_le tag
      rw [compactNegateConsumedFormulaHeader,
        compactAdditiveValueWeight_list,
        compactAdditiveValueWeight_list]
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

def compactFormulaTransformEmissionWeightBound
    (streamWeight witnessWeight : Nat) : Nat :=
  2 * streamWeight + witnessWeight + 6

theorem compactFormulaTransformEmissionWeightBound_mono
    {streamLeft streamRight witnessLeft witnessRight : Nat}
    (hstream : streamLeft ≤ streamRight)
    (hwitness : witnessLeft ≤ witnessRight) :
    compactFormulaTransformEmissionWeightBound
        streamLeft witnessLeft ≤
      compactFormulaTransformEmissionWeightBound
        streamRight witnessRight := by
  unfold compactFormulaTransformEmissionWeightBound
  omega

theorem compactFormulaFreeEmission_weight_le
    (task : CompactSyntaxTask) (consumed : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaFreeEmission task consumed) ≤
      2 * compactAdditiveValueWeight consumed + 6 := by
  unfold compactFormulaFreeEmission
  split
  · exact compactFreeConsumedTermHeader_weight_le task.2.1 consumed
  · exact nat_le_two_mul_add_six
      (compactAdditiveValueWeight consumed)

theorem compactFormulaShiftEmission_weight_le
    (taskKind : Nat) (consumed : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaShiftEmission taskKind consumed) ≤
      2 * compactAdditiveValueWeight consumed + 6 := by
  unfold compactFormulaShiftEmission
  split
  · exact compactShiftConsumedTermHeader_weight_le consumed
  · exact nat_le_two_mul_add_six
      (compactAdditiveValueWeight consumed)

theorem compactFormulaSubstitutionEmission_weight_le
    (task : CompactSyntaxTask) (witness consumed : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaSubstitutionEmission task (witness, consumed)) ≤
      compactAdditiveValueWeight witness +
        compactAdditiveValueWeight consumed := by
  unfold compactFormulaSubstitutionEmission
  split
  · exact compactSubstituteConsumedTermHeader_weight_le
      task.2.1 witness consumed
  · have hwitness := compactAdditiveValueWeight_list_pos witness
    change compactAdditiveValueWeight consumed ≤
      compactAdditiveValueWeight witness +
        compactAdditiveValueWeight consumed
    omega

theorem compactFormulaNegationEmission_weight_le
    (taskKind : Nat) (consumed : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaNegationEmission taskKind consumed) ≤
      compactAdditiveValueWeight consumed + 6 := by
  unfold compactFormulaNegationEmission
  split
  · exact compactNegateConsumedFormulaHeader_weight_le consumed
  · omega

theorem compactFormulaFreeStep_output_weight_le
    (witness : List Nat) (state : CompactFormulaTransformState) :
    compactAdditiveValueWeight
        (compactFormulaFreeStep state).2 ≤
      compactAdditiveValueWeight state.2 +
        compactFormulaTransformEmissionWeightBound
          (compactAdditiveValueWeight state.1.1)
          (compactAdditiveValueWeight witness) := by
  let consumed :=
    consumedTokenPrefix state.1.1
      (compactSyntaxParserStep state.1).1
  have hconsumed : compactAdditiveValueWeight consumed ≤
      compactAdditiveValueWeight state.1.1 := by
    exact consumedTokenPrefix_weight_le _ _
  have hemitted :=
    compactFormulaFreeEmission_weight_le
      (FoundationCompactNumericFormulaFree.compactSyntaxCurrentTask
        state.1) consumed
  have happend := compactAdditiveValueWeight_list_append_le
    state.2
    (compactFormulaFreeEmission
      (FoundationCompactNumericFormulaFree.compactSyntaxCurrentTask
        state.1) consumed)
  have hwitness := compactAdditiveValueWeight_list_pos witness
  change compactAdditiveValueWeight
      (state.2 ++ compactFormulaFreeEmission
        (FoundationCompactNumericFormulaFree.compactSyntaxCurrentTask
          state.1) consumed) ≤ _
  unfold compactFormulaTransformEmissionWeightBound
  omega

theorem compactFormulaShiftStep_output_weight_le
    (witness : List Nat) (state : CompactFormulaTransformState) :
    compactAdditiveValueWeight
        (compactFormulaShiftStep state).2 ≤
      compactAdditiveValueWeight state.2 +
        compactFormulaTransformEmissionWeightBound
          (compactAdditiveValueWeight state.1.1)
          (compactAdditiveValueWeight witness) := by
  let consumed :=
    consumedTokenPrefix state.1.1
      (compactSyntaxParserStep state.1).1
  have hconsumed : compactAdditiveValueWeight consumed ≤
      compactAdditiveValueWeight state.1.1 := by
    exact consumedTokenPrefix_weight_le _ _
  have hemitted :=
    compactFormulaShiftEmission_weight_le
      (FoundationCompactNumericFormulaShift.compactSyntaxCurrentTaskKind
        state.1) consumed
  have happend := compactAdditiveValueWeight_list_append_le
    state.2
    (compactFormulaShiftEmission
      (FoundationCompactNumericFormulaShift.compactSyntaxCurrentTaskKind
        state.1) consumed)
  have hwitness := compactAdditiveValueWeight_list_pos witness
  change compactAdditiveValueWeight
      (state.2 ++ compactFormulaShiftEmission
        (FoundationCompactNumericFormulaShift.compactSyntaxCurrentTaskKind
          state.1) consumed) ≤ _
  unfold compactFormulaTransformEmissionWeightBound
  omega

theorem compactFormulaSubstitutionStep_output_weight_le
    (witness : List Nat) (state : CompactFormulaTransformState) :
    compactAdditiveValueWeight
        (compactFormulaSubstitutionStep witness state).2 ≤
      compactAdditiveValueWeight state.2 +
        compactFormulaTransformEmissionWeightBound
          (compactAdditiveValueWeight state.1.1)
          (compactAdditiveValueWeight witness) := by
  let consumed :=
    consumedTokenPrefix state.1.1
      (compactSyntaxParserStep state.1).1
  have hconsumed : compactAdditiveValueWeight consumed ≤
      compactAdditiveValueWeight state.1.1 := by
    exact consumedTokenPrefix_weight_le _ _
  have hemitted :=
    compactFormulaSubstitutionEmission_weight_le
      (FoundationCompactNumericFormulaSubstitution.compactSyntaxCurrentTask
        state.1) witness consumed
  have happend := compactAdditiveValueWeight_list_append_le
    state.2
    (compactFormulaSubstitutionEmission
      (FoundationCompactNumericFormulaSubstitution.compactSyntaxCurrentTask
        state.1) (witness, consumed))
  change compactAdditiveValueWeight
      (state.2 ++ compactFormulaSubstitutionEmission
        (FoundationCompactNumericFormulaSubstitution.compactSyntaxCurrentTask
          state.1) (witness, consumed)) ≤ _
  unfold compactFormulaTransformEmissionWeightBound
  omega

theorem compactFormulaNegationStep_output_weight_le
    (witness : List Nat) (state : CompactFormulaTransformState) :
    compactAdditiveValueWeight
        (compactFormulaNegationStep state).2 ≤
      compactAdditiveValueWeight state.2 +
        compactFormulaTransformEmissionWeightBound
          (compactAdditiveValueWeight state.1.1)
          (compactAdditiveValueWeight witness) := by
  let consumed :=
    consumedTokenPrefix state.1.1
      (compactSyntaxParserStep state.1).1
  have hconsumed : compactAdditiveValueWeight consumed ≤
      compactAdditiveValueWeight state.1.1 := by
    exact consumedTokenPrefix_weight_le _ _
  have hemitted :=
    compactFormulaNegationEmission_weight_le
      (FoundationCompactNumericFormulaNegation.compactSyntaxCurrentTaskKind
        state.1) consumed
  have happend := compactAdditiveValueWeight_list_append_le
    state.2
    (compactFormulaNegationEmission
      (FoundationCompactNumericFormulaNegation.compactSyntaxCurrentTaskKind
        state.1) consumed)
  have hwitness := compactAdditiveValueWeight_list_pos witness
  change compactAdditiveValueWeight
      (state.2 ++ compactFormulaNegationEmission
        (FoundationCompactNumericFormulaNegation.compactSyntaxCurrentTaskKind
          state.1) consumed) ≤ _
  unfold compactFormulaTransformEmissionWeightBound
  omega

theorem compactFormulaTransformStep_output_weight_le
    (mode : Nat) (witness : List Nat)
    (state : CompactFormulaTransformState) (hmode : mode ≤ 3) :
    compactAdditiveValueWeight
        (compactFormulaTransformStep (mode, witness) state).2 ≤
      compactAdditiveValueWeight state.2 +
        compactFormulaTransformEmissionWeightBound
          (compactAdditiveValueWeight state.1.1)
          (compactAdditiveValueWeight witness) := by
  by_cases hzero : mode = 0
  · subst mode
    simpa using compactFormulaFreeStep_output_weight_le witness state
  by_cases hone : mode = 1
  · subst mode
    simpa using compactFormulaShiftStep_output_weight_le witness state
  by_cases htwo : mode = 2
  · subst mode
    simpa using
      compactFormulaSubstitutionStep_output_weight_le witness state
  have hthree : mode = 3 := by omega
  subst mode
  simpa using compactFormulaNegationStep_output_weight_le witness state

theorem compactFormulaTransformStep_parser
    (mode : Nat) (witness : List Nat)
    (state : CompactFormulaTransformState) :
    (compactFormulaTransformStep (mode, witness) state).1 =
      compactSyntaxParserStep state.1 := by
  simp only [compactFormulaTransformStep]
  split_ifs <;> rfl

theorem compactFormulaTransformStateAt_parser
    (mode : Nat) (witness : List Nat)
    (start : CompactFormulaTransformState) (stepIndex : Nat) :
    (compactFormulaTransformStateAt
        (mode, witness) start stepIndex).1 =
      compactParserStateAt compactSyntaxParserStep
        start.1 stepIndex := by
  induction stepIndex with
  | zero => rfl
  | succ stepIndex ih =>
      have ih' :
          (((compactFormulaTransformStep (mode, witness))^[stepIndex])
            start).1 =
          ((compactSyntaxParserStep^[stepIndex]) start.1) := by
        simpa [compactFormulaTransformStateAt,
          compactParserStateAt] using ih
      rw [compactFormulaTransformStateAt,
        compactParserStateAt,
        Function.iterate_succ_apply',
        Function.iterate_succ_apply',
        compactFormulaTransformStep_parser,
        ih']

theorem compactFormulaTransformStateAt_parser_source
    (mode binderArity stepIndex : Nat)
    (witness tokens : List Nat) :
    CompactSyntaxParserStateSourceOf tokens
      (binderArity + stepIndex)
      (compactFormulaTransformStateAt
        (mode, witness)
        (compactFormulaTransformInitialState binderArity tokens)
        stepIndex).1 := by
  rw [compactFormulaTransformStateAt_parser]
  exact compactFormulaParserStateAt_source
    binderArity tokens stepIndex

theorem compactFormulaTransformStateAt_parser_task_length_le
    (mode binderArity stepIndex : Nat)
    (witness tokens : List Nat) :
    (compactFormulaTransformStateAt
      (mode, witness)
      (compactFormulaTransformInitialState binderArity tokens)
      stepIndex).1.2.1.length ≤ 1 + stepIndex := by
  rw [compactFormulaTransformStateAt_parser]
  exact compactFormulaParserStateAt_task_length_le
    binderArity tokens stepIndex

def compactFormulaTransformOutputWeightBound
    (streamWeight witnessWeight stepIndex : Nat) : Nat :=
  1 + stepIndex *
    compactFormulaTransformEmissionWeightBound
      streamWeight witnessWeight

theorem compactFormulaTransformOutputWeightBound_mono
    {streamLeft streamRight witnessLeft witnessRight
      stepLeft stepRight : Nat}
    (hstream : streamLeft ≤ streamRight)
    (hwitness : witnessLeft ≤ witnessRight)
    (hstep : stepLeft ≤ stepRight) :
    compactFormulaTransformOutputWeightBound
        streamLeft witnessLeft stepLeft ≤
      compactFormulaTransformOutputWeightBound
        streamRight witnessRight stepRight := by
  have hemitted := compactFormulaTransformEmissionWeightBound_mono
    hstream hwitness
  have hproduct := Nat.mul_le_mul hstep hemitted
  unfold compactFormulaTransformOutputWeightBound
  omega

theorem compactFormulaTransformStateAt_output_weight_le
    (mode binderArity stepIndex : Nat)
    (witness tokens : List Nat) (hmode : mode ≤ 3) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateAt
          (mode, witness)
          (compactFormulaTransformInitialState binderArity tokens)
          stepIndex).2 ≤
      compactFormulaTransformOutputWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight witness)
        stepIndex := by
  induction stepIndex with
  | zero =>
      simp [compactFormulaTransformStateAt,
        compactFormulaTransformInitialState,
        compactFormulaTransformOutputWeightBound]
  | succ stepIndex ih =>
      let current :=
        compactFormulaTransformStateAt
          (mode, witness)
          (compactFormulaTransformInitialState binderArity tokens)
          stepIndex
      have hstep :=
        compactFormulaTransformStep_output_weight_le
          mode witness current hmode
      have hsource :=
        compactFormulaTransformStateAt_parser_source
          mode binderArity stepIndex witness tokens
      have hstream :
          compactAdditiveValueWeight current.1.1 ≤
            compactAdditiveValueWeight tokens := by
        simpa [current] using
          compactAdditiveValueWeight_suffix_le hsource.1
      have ihCurrent :
          compactAdditiveValueWeight current.2 ≤
            compactFormulaTransformOutputWeightBound
              (compactAdditiveValueWeight tokens)
              (compactAdditiveValueWeight witness)
              stepIndex := by
        simpa [current] using ih
      have hemittedBound :=
        compactFormulaTransformEmissionWeightBound_mono
          hstream
          (Nat.le_refl (compactAdditiveValueWeight witness))
      have hstepPublic :
          compactAdditiveValueWeight
              (compactFormulaTransformStep
                (mode, witness) current).2 ≤
            compactAdditiveValueWeight current.2 +
              compactFormulaTransformEmissionWeightBound
                (compactAdditiveValueWeight tokens)
                (compactAdditiveValueWeight witness) :=
        hstep.trans
          (Nat.add_le_add_left hemittedBound
            (compactAdditiveValueWeight current.2))
      have hfinal :
          compactAdditiveValueWeight
              (compactFormulaTransformStep
                (mode, witness) current).2 ≤
            compactFormulaTransformOutputWeightBound
              (compactAdditiveValueWeight tokens)
              (compactAdditiveValueWeight witness)
              (stepIndex + 1) := by
        unfold compactFormulaTransformOutputWeightBound at ihCurrent ⊢
        simp only [Nat.add_mul, one_mul]
        omega
      simpa [current, compactFormulaTransformStateAt,
        Function.iterate_succ_apply'] using hfinal

theorem compactFormulaParserStateAt_weight_le
    (binderArity stepIndex : Nat) (tokens : List Nat) :
    compactAdditiveValueWeight
        (compactParserStateAt compactSyntaxParserStep
          (compactFormulaParserInitialState binderArity tokens)
          stepIndex) ≤
      compactNumericFormulaParserStateWeightBound
        (compactAdditiveValueWeight tokens)
        (binderArity + stepIndex) stepIndex := by
  let state :=
    compactParserStateAt compactSyntaxParserStep
      (compactFormulaParserInitialState binderArity tokens)
      stepIndex
  have hsource :
      CompactSyntaxParserStateSourceOf tokens
        (binderArity + stepIndex) state := by
    simpa [state] using
      compactFormulaParserStateAt_source
        binderArity tokens stepIndex
  have hstream :=
    compactAdditiveValueWeight_suffix_le hsource.1
  have htaskLength :
      state.2.1.length ≤ 1 + stepIndex := by
    simpa [state] using
      compactFormulaParserStateAt_task_length_le
        binderArity tokens stepIndex
  have htasksRaw := compactAdditiveValueWeight_list_le state.2.1
    (compactNumericSyntaxParserTaskWeightBound
      (compactAdditiveValueWeight tokens)
      (binderArity + stepIndex))
    (fun task htask => (hsource.2.1 task htask).weight_le)
  have htaskSize := Nat.size_le_size htaskLength
  have htaskProduct := Nat.mul_le_mul_right
    (compactNumericSyntaxParserTaskWeightBound
      (compactAdditiveValueWeight tokens)
      (binderArity + stepIndex))
    htaskLength
  have htasks :
      compactAdditiveValueWeight state.2.1 ≤
        Nat.size (1 + stepIndex) + 1 +
          (1 + stepIndex) *
            compactNumericSyntaxParserTaskWeightBound
              (compactAdditiveValueWeight tokens)
              (binderArity + stepIndex) := by
    omega
  have hstatus := hsource.status_weight_le
  change compactAdditiveValueWeight state ≤ _
  rw [compactAdditiveValueWeight_prod,
    compactAdditiveValueWeight_prod]
  unfold compactNumericFormulaParserStateWeightBound
  omega

theorem compactFormulaTransformStateAt_parser_weight_le
    (mode binderArity stepIndex : Nat)
    (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateAt
          (mode, witness)
          (compactFormulaTransformInitialState binderArity tokens)
          stepIndex).1 ≤
      compactNumericFormulaParserStateWeightBound
        (compactAdditiveValueWeight tokens)
        (binderArity + stepIndex) stepIndex := by
  rw [compactFormulaTransformStateAt_parser]
  exact compactFormulaParserStateAt_weight_le
    binderArity stepIndex tokens

def compactFormulaTransformStateWeightBound
    (streamWeight witnessWeight binderArity fuel : Nat) : Nat :=
  compactNumericFormulaParserStateWeightBound
      streamWeight (binderArity + fuel) fuel +
    compactFormulaTransformOutputWeightBound
      streamWeight witnessWeight fuel

theorem compactFormulaTransformStateWeightBound_mono
    {streamLeft streamRight witnessLeft witnessRight
      binderLeft binderRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft ≤ streamRight)
    (hwitness : witnessLeft ≤ witnessRight)
    (hbinder : binderLeft ≤ binderRight)
    (hfuel : fuelLeft ≤ fuelRight) :
    compactFormulaTransformStateWeightBound
        streamLeft witnessLeft binderLeft fuelLeft ≤
      compactFormulaTransformStateWeightBound
        streamRight witnessRight binderRight fuelRight := by
  have hbinderFuel :
      binderLeft + fuelLeft ≤ binderRight + fuelRight := by
    omega
  have hparser := compactNumericFormulaParserStateWeightBound_mono
    hstream hbinderFuel hfuel
  have houtput := compactFormulaTransformOutputWeightBound_mono
    hstream hwitness hfuel
  unfold compactFormulaTransformStateWeightBound
  omega

theorem compactFormulaTransformStateAt_weight_le
    (mode binderArity stepIndex fuel : Nat)
    (witness tokens : List Nat)
    (hmode : mode ≤ 3) (hstepIndex : stepIndex ≤ fuel) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateAt
          (mode, witness)
          (compactFormulaTransformInitialState binderArity tokens)
          stepIndex) ≤
      compactFormulaTransformStateWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight witness)
        binderArity fuel := by
  have hparserRaw :=
    compactFormulaTransformStateAt_parser_weight_le
      mode binderArity stepIndex witness tokens
  have hparser :
      compactAdditiveValueWeight
          (compactFormulaTransformStateAt
            (mode, witness)
            (compactFormulaTransformInitialState binderArity tokens)
            stepIndex).1 ≤
        compactNumericFormulaParserStateWeightBound
          (compactAdditiveValueWeight tokens)
          (binderArity + fuel) fuel :=
    hparserRaw.trans
      (compactNumericFormulaParserStateWeightBound_mono
        (Nat.le_refl _)
        (by omega)
        hstepIndex)
  have houtputRaw :=
    compactFormulaTransformStateAt_output_weight_le
      mode binderArity stepIndex witness tokens hmode
  have houtput :
      compactAdditiveValueWeight
          (compactFormulaTransformStateAt
            (mode, witness)
            (compactFormulaTransformInitialState binderArity tokens)
            stepIndex).2 ≤
        compactFormulaTransformOutputWeightBound
          (compactAdditiveValueWeight tokens)
          (compactAdditiveValueWeight witness)
          fuel :=
    houtputRaw.trans
      (compactFormulaTransformOutputWeightBound_mono
        (Nat.le_refl _) (Nat.le_refl _) hstepIndex)
  rw [compactAdditiveValueWeight_prod]
  unfold compactFormulaTransformStateWeightBound
  omega

def compactFormulaTransformTraceWeightBound
    (streamWeight witnessWeight binderArity fuel : Nat) : Nat :=
  Nat.size (fuel + 1) + 1 +
    (fuel + 1) *
      compactFormulaTransformStateWeightBound
        streamWeight witnessWeight binderArity fuel

theorem compactFormulaTransformTraceWeightBound_mono
    {streamLeft streamRight witnessLeft witnessRight
      binderLeft binderRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft ≤ streamRight)
    (hwitness : witnessLeft ≤ witnessRight)
    (hbinder : binderLeft ≤ binderRight)
    (hfuel : fuelLeft ≤ fuelRight) :
    compactFormulaTransformTraceWeightBound
        streamLeft witnessLeft binderLeft fuelLeft ≤
      compactFormulaTransformTraceWeightBound
        streamRight witnessRight binderRight fuelRight := by
  have hfuelAdd : fuelLeft + 1 ≤ fuelRight + 1 := by
    omega
  have hsize := Nat.size_le_size hfuelAdd
  have hstate := compactFormulaTransformStateWeightBound_mono
    hstream hwitness hbinder hfuel
  have hproduct := Nat.mul_le_mul hfuelAdd hstate
  unfold compactFormulaTransformTraceWeightBound
  omega

theorem compactFormulaTransformStateTrace_weight_le
    (mode binderArity fuel : Nat)
    (witness tokens : List Nat) (hmode : mode ≤ 3) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (mode, witness) fuel
          (compactFormulaTransformInitialState binderArity tokens)) ≤
      compactFormulaTransformTraceWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight witness)
        binderArity fuel := by
  have hrows := compactAdditiveValueWeight_list_le
    (compactFormulaTransformStateTrace
      (mode, witness) fuel
      (compactFormulaTransformInitialState binderArity tokens))
    (compactFormulaTransformStateWeightBound
      (compactAdditiveValueWeight tokens)
      (compactAdditiveValueWeight witness)
      binderArity fuel)
    (fun state hstate => by
      rw [compactFormulaTransformStateTrace] at hstate
      rcases List.mem_map.mp hstate with
        ⟨stepIndex, hstepIndex, rfl⟩
      simp only [List.mem_range] at hstepIndex
      exact compactFormulaTransformStateAt_weight_le
        mode binderArity stepIndex fuel witness tokens
        hmode (by omega))
  unfold compactFormulaTransformTraceWeightBound
  rw [compactFormulaTransformStateTrace_length] at hrows
  exact hrows

def compactFormulaTransformCanonicalTraceWeightBound
    (streamWeight witnessWeight binderArity : Nat) : Nat :=
  compactFormulaTransformTraceWeightBound
    streamWeight witnessWeight binderArity
    (compactNumericCertificateParserFuelWeightBound streamWeight)

theorem compactFormulaTransformCanonicalTraceWeightBound_mono
    {streamLeft streamRight witnessLeft witnessRight
      binderLeft binderRight : Nat}
    (hstream : streamLeft ≤ streamRight)
    (hwitness : witnessLeft ≤ witnessRight)
    (hbinder : binderLeft ≤ binderRight) :
    compactFormulaTransformCanonicalTraceWeightBound
        streamLeft witnessLeft binderLeft ≤
      compactFormulaTransformCanonicalTraceWeightBound
        streamRight witnessRight binderRight := by
  exact compactFormulaTransformTraceWeightBound_mono
    hstream hwitness hbinder
    (compactNumericCertificateParserFuelWeightBound_mono hstream)

theorem compactFormulaTransformCanonicalStateTrace_weight_le
    (mode binderArity : Nat)
    (witness tokens : List Nat) (hmode : mode ≤ 3) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (mode, witness)
          (compactSyntaxRunFuelBound tokens)
          (compactFormulaTransformInitialState binderArity tokens)) ≤
      compactFormulaTransformCanonicalTraceWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight witness)
        binderArity := by
  have hraw := compactFormulaTransformStateTrace_weight_le
    mode binderArity (compactSyntaxRunFuelBound tokens)
    witness tokens hmode
  have hfuel := compactSyntaxRunFuelBound_le_weightBound
    (Nat.le_refl (compactAdditiveValueWeight tokens))
  exact hraw.trans
    (compactFormulaTransformTraceWeightBound_mono
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hfuel)

def compactFormulaTransformCanonicalOutputWeightBound
    (streamWeight witnessWeight : Nat) : Nat :=
  compactFormulaTransformOutputWeightBound
    streamWeight witnessWeight
    (compactNumericCertificateParserFuelWeightBound streamWeight)

theorem compactFormulaTransformCanonicalOutputWeightBound_mono
    {streamLeft streamRight witnessLeft witnessRight : Nat}
    (hstream : streamLeft ≤ streamRight)
    (hwitness : witnessLeft ≤ witnessRight) :
    compactFormulaTransformCanonicalOutputWeightBound
        streamLeft witnessLeft ≤
      compactFormulaTransformCanonicalOutputWeightBound
        streamRight witnessRight := by
  exact compactFormulaTransformOutputWeightBound_mono
    hstream hwitness
    (compactNumericCertificateParserFuelWeightBound_mono hstream)

theorem compactFormulaTransformCanonicalStateOutput_weight_le
    (mode binderArity : Nat)
    (witness tokens : List Nat) (hmode : mode ≤ 3) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateAt
          (mode, witness)
          (compactFormulaTransformInitialState binderArity tokens)
          (compactSyntaxRunFuelBound tokens)).2 ≤
      compactFormulaTransformCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight witness) := by
  have hraw := compactFormulaTransformStateAt_output_weight_le
    mode binderArity (compactSyntaxRunFuelBound tokens)
      witness tokens hmode
  have hfuel := compactSyntaxRunFuelBound_le_weightBound
    (Nat.le_refl (compactAdditiveValueWeight tokens))
  exact hraw.trans
    (compactFormulaTransformOutputWeightBound_mono
      (Nat.le_refl _) (Nat.le_refl _) hfuel)

#print axioms compactAdditiveValueWeight_list_append_le
#print axioms compactAdditiveValueWeight_take_le
#print axioms compactAdditiveValueWeight_mem_le
#print axioms compactTokenAt_weight_le
#print axioms consumedTokenPrefix_weight_le
#print axioms compactShiftConsumedTermHeader_weight_le
#print axioms compactFreeConsumedTermHeader_weight_le
#print axioms compactSubstituteConsumedTermHeader_weight_le
#print axioms compactNegateConsumedFormulaHeader_weight_le
#print axioms compactFormulaTransformStep_output_weight_le
#print axioms compactFormulaTransformStep_parser
#print axioms compactFormulaTransformStateAt_parser_source
#print axioms compactFormulaTransformStateAt_output_weight_le
#print axioms compactFormulaParserStateAt_weight_le
#print axioms compactFormulaTransformStateAt_weight_le
#print axioms compactFormulaTransformStateTrace_weight_le
#print axioms compactFormulaTransformCanonicalStateTrace_weight_le
#print axioms compactFormulaTransformCanonicalStateOutput_weight_le

end FoundationCompactNumericListedDirectFormulaTransformValueBounds
