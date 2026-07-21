import integration.FoundationCompactNumericListedDirectFormulaTransformValueBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformExactFormula

/-!
# Additive weight bounds for mode-5 formula-transform traces

The `fixitr` transform appends each concrete step emission to its current
output.  Hence every intermediate emitted list is a prefix of the final one.
Together with the mode-independent parser-state bound, this gives a trace
bound depending only on the source weight, final output weight, binder arity,
and fuel.  In particular, no bound on an eagerly expanded route is used.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaFixitrTraceWeightBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericFormulaFixitr
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectFormulaTransformValueBounds
open FoundationCompactNumericListedDirectFormulaTransformExactFormula

private theorem fixitrNatSize_add_le (left right : Nat) :
    Nat.size (left + right) <= Nat.size left + Nat.size right + 1 := by
  rw [Nat.size_le]
  have hleft : left < 2 ^ Nat.size left := Nat.lt_size_self left
  have hright : right < 2 ^ Nat.size right := Nat.lt_size_self right
  have hleftPower : 2 ^ Nat.size left <=
      2 ^ (Nat.size left + Nat.size right) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      (Nat.le_add_right (Nat.size left) (Nat.size right))
  have hrightPower : 2 ^ Nat.size right <=
      2 ^ (Nat.size left + Nat.size right) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      (Nat.le_add_left (Nat.size right) (Nat.size left))
  calc
    left + right < 2 ^ Nat.size left + 2 ^ Nat.size right :=
      Nat.add_lt_add hleft hright
    _ <= 2 ^ (Nat.size left + Nat.size right) +
        2 ^ (Nat.size left + Nat.size right) :=
      Nat.add_le_add hleftPower hrightPower
    _ = 2 ^ (Nat.size left + Nat.size right + 1) := by
      rw [pow_succ]
      omega

private theorem fixitrNatSize_le_self (value : Nat) :
    Nat.size value <= value := by
  rw [Nat.size_le]
  exact value.lt_two_pow_self

private theorem compactFormulaFixitrPairWeight_eq
    (first second : Nat) :
    compactAdditiveValueWeight [first, second] =
      3 + compactAdditiveValueWeight first +
        compactAdditiveValueWeight second := by
  rw [compactAdditiveValueWeight_list]
  simp only [List.length_cons, List.length_nil, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  have htwo : Nat.size 2 = 2 := by decide
  rw [htwo]
  omega

/-- The concrete `fixitr` term-header rewrite is independent of the magnitude
of `captureCount`: the count is used only by a comparison and a subtraction.
The only growing branch emits `binderArity + sourceIndex`. -/
theorem compactFixitrConsumedTermHeader_weight_le
    (binderArity captureCount : Nat) (tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFixitrConsumedTermHeader
          (binderArity, captureCount) tokens) <=
      compactAdditiveValueWeight tokens + binderArity + 8 := by
  by_cases hlength : tokens.length = 2
  · by_cases hfree : compactTokenAt 0 tokens = 1
    · by_cases hcaptured : compactTokenAt 1 tokens < captureCount
      · have hindex := compactTokenAt_weight_le tokens 1
        simp only [compactAdditiveValueWeight_nat] at hindex
        have hadd := fixitrNatSize_add_le
          binderArity (compactTokenAt 1 tokens)
        have hbinder := fixitrNatSize_le_self binderArity
        rw [compactFixitrConsumedTermHeader, if_pos hlength,
          if_pos hfree, if_pos hcaptured,
          compactFormulaFixitrPairWeight_eq]
        simp only [compactAdditiveValueWeight_nat]
        have hzero : Nat.size 0 = 0 := by decide
        rw [hzero]
        omega
      · have hindex := compactTokenAt_weight_le tokens 1
        have hsub := compactAdditiveValueWeight_nat_sub_le
          (compactTokenAt 1 tokens) captureCount
        simp only [compactAdditiveValueWeight_nat] at hindex hsub
        rw [compactFixitrConsumedTermHeader, if_pos hlength,
          if_pos hfree, if_neg hcaptured,
          compactFormulaFixitrPairWeight_eq]
        simp only [compactAdditiveValueWeight_nat]
        have hone : Nat.size 1 = 1 := by decide
        rw [hone]
        omega
    · simp [compactFixitrConsumedTermHeader, hlength, hfree]
      omega
  · simp [compactFixitrConsumedTermHeader, hlength]
    omega

/-- Per-step mode-5 emission envelope. -/
def compactFormulaFixitrEmissionWeightBound
    (streamWeight binderCap : Nat) : Nat :=
  streamWeight + binderCap + 8

theorem compactFormulaFixitrEmissionWeightBound_mono
    {streamLeft streamRight binderLeft binderRight : Nat}
    (hstream : streamLeft <= streamRight)
    (hbinder : binderLeft <= binderRight) :
    compactFormulaFixitrEmissionWeightBound streamLeft binderLeft <=
      compactFormulaFixitrEmissionWeightBound streamRight binderRight := by
  unfold compactFormulaFixitrEmissionWeightBound
  omega

theorem compactFormulaFixitrEmission_weight_le
    (task : CompactSyntaxTask) (captureCount : Nat)
    (consumed : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaFixitrEmission task (captureCount, consumed)) <=
      compactFormulaFixitrEmissionWeightBound
        (compactAdditiveValueWeight consumed) task.2.1 := by
  simp only [compactFormulaFixitrEmission]
  split
  · exact compactFixitrConsumedTermHeader_weight_le
      task.2.1 captureCount consumed
  · unfold compactFormulaFixitrEmissionWeightBound
    omega

theorem compactFormulaFixitrCurrentTask_binder_le_of_source
    {initialTokens : List Nat} {binderCap : Nat}
    {state : CompactSyntaxParserState}
    (hsource : CompactSyntaxParserStateSourceOf
      initialTokens binderCap state) :
    (compactSyntaxCurrentTask state).2.1 <= binderCap := by
  rcases state with ⟨tokens, tasks, status⟩
  cases tasks with
  | nil => simp [compactSyntaxCurrentTask]
  | cons task tasks =>
      have htask := hsource.2.1 task (by simp)
      simpa [compactSyntaxCurrentTask] using htask.2.1

theorem compactFormulaFixitrStep_output_weight_le
    (captureCount : Nat) (state : CompactFormulaFixitrState) :
    compactAdditiveValueWeight
        (compactFormulaFixitrStep captureCount state).2 <=
      compactAdditiveValueWeight state.2 +
        compactFormulaFixitrEmissionWeightBound
          (compactAdditiveValueWeight state.1.1)
          (compactSyntaxCurrentTask state.1).2.1 := by
  let consumed := consumedTokenPrefix state.1.1
    (compactSyntaxParserStep state.1).1
  have hconsumed : compactAdditiveValueWeight consumed <=
      compactAdditiveValueWeight state.1.1 := by
    exact consumedTokenPrefix_weight_le _ _
  have hemitted := compactFormulaFixitrEmission_weight_le
    (compactSyntaxCurrentTask state.1) captureCount consumed
  have hemittedPublic :
      compactAdditiveValueWeight
          (compactFormulaFixitrEmission
            (compactSyntaxCurrentTask state.1) (captureCount, consumed)) <=
        compactFormulaFixitrEmissionWeightBound
          (compactAdditiveValueWeight state.1.1)
          (compactSyntaxCurrentTask state.1).2.1 :=
    hemitted.trans
      (compactFormulaFixitrEmissionWeightBound_mono
        hconsumed (Nat.le_refl _))
  have happend := compactAdditiveValueWeight_list_append_le
    state.2
    (compactFormulaFixitrEmission
      (compactSyntaxCurrentTask state.1) (captureCount, consumed))
  change compactAdditiveValueWeight
      (state.2 ++ compactFormulaFixitrEmission
        (compactSyntaxCurrentTask state.1) (captureCount, consumed)) <= _
  exact happend.trans
    (Nat.add_le_add_left hemittedPublic
      (compactAdditiveValueWeight state.2))

theorem compactFormulaTransformStep_fixitr_output_weight_le
    (witness : List Nat) (state : CompactFormulaTransformState) :
    compactAdditiveValueWeight
        (compactFormulaTransformStep (5, witness) state).2 <=
      compactAdditiveValueWeight state.2 +
        compactFormulaFixitrEmissionWeightBound
          (compactAdditiveValueWeight state.1.1)
          (compactSyntaxCurrentTask state.1).2.1 := by
  rw [compactFormulaTransformStep_fixitr]
  exact compactFormulaFixitrStep_output_weight_le witness.length state

/-- Final-output envelope at a specified fuel.  It is a fixed polynomial and,
more strongly than required, has no dependence on `captureCount`. -/
def compactFormulaFixitrOutputWeightBound
    (streamWeight binderArity fuel : Nat) : Nat :=
  1 + fuel * compactFormulaFixitrEmissionWeightBound
    streamWeight (binderArity + fuel)

theorem compactFormulaFixitrOutputWeightBound_mono
    {streamLeft streamRight binderLeft binderRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft <= streamRight)
    (hbinder : binderLeft <= binderRight)
    (hfuel : fuelLeft <= fuelRight) :
    compactFormulaFixitrOutputWeightBound
        streamLeft binderLeft fuelLeft <=
      compactFormulaFixitrOutputWeightBound
        streamRight binderRight fuelRight := by
  have hemitted := compactFormulaFixitrEmissionWeightBound_mono
    hstream (Nat.add_le_add hbinder hfuel)
  have hproduct := Nat.mul_le_mul hfuel hemitted
  unfold compactFormulaFixitrOutputWeightBound
  omega

/-- Output after `stepIndex` steps, using one fixed binder cap for the whole
prefix.  This is the induction form behind the final-output theorem. -/
theorem compactFormulaTransformStateAt_fixitr_output_weight_le_with_fuel
    (binderArity stepIndex fuel : Nat) (witness tokens : List Nat)
    (hstepIndex : stepIndex <= fuel) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateAt
          (5, witness)
          (compactFormulaTransformInitialState binderArity tokens)
          stepIndex).2 <=
      1 + stepIndex * compactFormulaFixitrEmissionWeightBound
        (compactAdditiveValueWeight tokens) (binderArity + fuel) := by
  induction stepIndex with
  | zero =>
      simp [compactFormulaTransformStateAt,
        compactFormulaTransformInitialState]
  | succ stepIndex ih =>
      let current := compactFormulaTransformStateAt
        (5, witness)
        (compactFormulaTransformInitialState binderArity tokens)
        stepIndex
      have hstep :=
        compactFormulaTransformStep_fixitr_output_weight_le
          witness current
      have hsource := compactFormulaTransformStateAt_parser_source
        5 binderArity stepIndex witness tokens
      have hstream : compactAdditiveValueWeight current.1.1 <=
          compactAdditiveValueWeight tokens := by
        simpa [current] using
          compactAdditiveValueWeight_suffix_le hsource.1
      have hbinderRaw :
          (compactSyntaxCurrentTask current.1).2.1 <=
            binderArity + stepIndex := by
        exact compactFormulaFixitrCurrentTask_binder_le_of_source
          (by simpa [current] using hsource)
      have hbinder :
          (compactSyntaxCurrentTask current.1).2.1 <=
            binderArity + fuel := by
        exact hbinderRaw.trans (by omega)
      have hemitted := compactFormulaFixitrEmissionWeightBound_mono
        hstream hbinder
      have hstepPublic :
          compactAdditiveValueWeight
              (compactFormulaTransformStep (5, witness) current).2 <=
            compactAdditiveValueWeight current.2 +
              compactFormulaFixitrEmissionWeightBound
                (compactAdditiveValueWeight tokens)
                (binderArity + fuel) :=
        hstep.trans
          (Nat.add_le_add_left hemitted
            (compactAdditiveValueWeight current.2))
      have ihCurrent : compactAdditiveValueWeight current.2 <=
          1 + stepIndex * compactFormulaFixitrEmissionWeightBound
            (compactAdditiveValueWeight tokens)
            (binderArity + fuel) := by
        simpa [current] using ih (by omega)
      have hfinal :
          compactAdditiveValueWeight
              (compactFormulaTransformStep (5, witness) current).2 <=
            1 + (stepIndex + 1) *
              compactFormulaFixitrEmissionWeightBound
                (compactAdditiveValueWeight tokens)
                (binderArity + fuel) := by
        calc
          _ <= compactAdditiveValueWeight current.2 +
              compactFormulaFixitrEmissionWeightBound
                (compactAdditiveValueWeight tokens)
                (binderArity + fuel) := hstepPublic
          _ <= (1 + stepIndex *
                compactFormulaFixitrEmissionWeightBound
                  (compactAdditiveValueWeight tokens)
                  (binderArity + fuel)) +
              compactFormulaFixitrEmissionWeightBound
                (compactAdditiveValueWeight tokens)
                (binderArity + fuel) :=
            Nat.add_le_add_right ihCurrent _
          _ = _ := by
            rw [Nat.add_mul, one_mul]
            omega
      simpa [current, compactFormulaTransformStateAt,
        Function.iterate_succ_apply'] using hfinal

theorem compactFormulaTransformStateAt_fixitr_output_source_weight_le
    (binderArity fuel : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateAt
          (5, witness)
          (compactFormulaTransformInitialState binderArity tokens)
          fuel).2 <=
      compactFormulaFixitrOutputWeightBound
        (compactAdditiveValueWeight tokens) binderArity fuel := by
  simpa [compactFormulaFixitrOutputWeightBound] using
    compactFormulaTransformStateAt_fixitr_output_weight_le_with_fuel
      binderArity fuel fuel witness tokens (Nat.le_refl fuel)

theorem compactFormulaTransformRun_fixitr_output_source_weight_le
    (binderArity : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaTransformRun
          (5, witness) (binderArity, tokens)).2 <=
      compactFormulaFixitrOutputWeightBound
        (compactAdditiveValueWeight tokens) binderArity
        (compactSyntaxRunFuelBound tokens) := by
  simpa [compactFormulaTransformRun,
    compactFormulaTransformStateAt] using
      compactFormulaTransformStateAt_fixitr_output_source_weight_le
        binderArity (compactSyntaxRunFuelBound tokens) witness tokens

/-- Source-only fixed-polynomial envelope for the canonical final output. -/
def compactFormulaFixitrCanonicalOutputWeightBound
    (streamWeight binderArity : Nat) : Nat :=
  compactFormulaFixitrOutputWeightBound streamWeight binderArity
    (compactNumericCertificateParserFuelWeightBound streamWeight)

theorem compactFormulaFixitrCanonicalOutputWeightBound_mono
    {streamLeft streamRight binderLeft binderRight : Nat}
    (hstream : streamLeft <= streamRight)
    (hbinder : binderLeft <= binderRight) :
    compactFormulaFixitrCanonicalOutputWeightBound
        streamLeft binderLeft <=
      compactFormulaFixitrCanonicalOutputWeightBound
        streamRight binderRight := by
  exact compactFormulaFixitrOutputWeightBound_mono
    hstream hbinder
    (compactNumericCertificateParserFuelWeightBound_mono hstream)

theorem compactFormulaTransformCanonicalRun_fixitr_output_source_weight_le
    (binderArity : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaTransformRun
          (5, witness) (binderArity, tokens)).2 <=
      compactFormulaFixitrCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens) binderArity := by
  have hraw := compactFormulaTransformRun_fixitr_output_source_weight_le
    binderArity witness tokens
  have hfuel := compactSyntaxRunFuelBound_le_weightBound
    (Nat.le_refl (compactAdditiveValueWeight tokens))
  exact hraw.trans (by
    unfold compactFormulaFixitrCanonicalOutputWeightBound
    exact compactFormulaFixitrOutputWeightBound_mono
      (Nat.le_refl _) (Nat.le_refl _) hfuel)

theorem compactFormulaTransformResult_fixitr_output_source_weight_le
    (binderArity : Nat) (witness tokens output suffix : List Nat)
    (hresult : compactFormulaTransformResult
      (5, witness) (binderArity, tokens) = some (output, suffix)) :
    compactAdditiveValueWeight output <=
      compactFormulaFixitrCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens) binderArity := by
  have hfinalOutput :
      (compactFormulaTransformRun
        (5, witness) (binderArity, tokens)).2 = output :=
    (compactFormulaTransformStateOutput_eq_some_iff.mp hresult).2
  simpa only [hfinalOutput] using
    compactFormulaTransformCanonicalRun_fixitr_output_source_weight_le
      binderArity witness tokens

theorem compactFormulaTransformExactResult_fixitr_output_source_weight_le
    (binderArity : Nat) (witness tokens output : List Nat)
    (hresult : compactExactFormulaTransformResult
      (compactFormulaTransformResult
        (5, witness) (binderArity, tokens)) = some output) :
    compactAdditiveValueWeight output <=
      compactFormulaFixitrCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens) binderArity := by
  have hrunResult : compactFormulaTransformResult
      (5, witness) (binderArity, tokens) = some (output, []) :=
    compactExactFormulaTransformResult_eq_some_iff.mp hresult
  exact compactFormulaTransformResult_fixitr_output_source_weight_le
    binderArity witness tokens output [] hrunResult

/-- Executable-data form: guarded induction stores the exact result with
`[]` as its failure default. -/
theorem compactFormulaTransformExactResultGetD_fixitr_output_source_weight_le
    (binderArity : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        ((compactExactFormulaTransformResult
          (compactFormulaTransformResult
            (5, witness) (binderArity, tokens))).getD []) <=
      compactFormulaFixitrCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens) binderArity := by
  cases hresult : compactExactFormulaTransformResult
      (compactFormulaTransformResult
        (5, witness) (binderArity, tokens)) with
  | none =>
      simp [compactFormulaFixitrCanonicalOutputWeightBound,
        compactFormulaFixitrOutputWeightBound]
  | some output =>
      simpa [hresult] using
        compactFormulaTransformExactResult_fixitr_output_source_weight_le
          binderArity witness tokens output hresult

/-- Final-output form shared by guarded-induction chunks 29, 32, and 36. -/
theorem compactFormulaTransformExactResult_fixitr_zeroBinder_output_weight_le
    (witness tokens output : List Nat)
    (hresult : compactExactFormulaTransformResult
      (compactFormulaTransformResult (5, witness) (0, tokens)) =
        some output) :
    compactAdditiveValueWeight output <=
      compactFormulaFixitrCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens) 0 := by
  exact compactFormulaTransformExactResult_fixitr_output_source_weight_le
    0 witness tokens output hresult

theorem
    compactFormulaTransformExactResultGetD_fixitr_zeroBinder_output_weight_le
    (witness tokens : List Nat) :
    compactAdditiveValueWeight
        ((compactExactFormulaTransformResult
          (compactFormulaTransformResult
            (5, witness) (0, tokens))).getD []) <=
      compactFormulaFixitrCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens) 0 := by
  exact compactFormulaTransformExactResultGetD_fixitr_output_source_weight_le
    0 witness tokens

/-- Per-state envelope for a mode-5 trace whose final emitted list has the
given additive weight. -/
def compactFormulaFixitrTransformStateWeightBound
    (streamWeight outputWeight binderArity fuel : Nat) : Nat :=
  compactNumericFormulaParserStateWeightBound
      streamWeight (binderArity + fuel) fuel +
    outputWeight

/-- Whole-trace envelope obtained from the exact canonical trace length. -/
def compactFormulaFixitrTransformTraceWeightBound
    (streamWeight outputWeight binderArity fuel : Nat) : Nat :=
  Nat.size (fuel + 1) + 1 +
    (fuel + 1) *
      compactFormulaFixitrTransformStateWeightBound
        streamWeight outputWeight binderArity fuel

/-- Fixed-polynomial-fuel envelope used by canonical formula-transform
traces. -/
def compactFormulaFixitrTransformCanonicalTraceWeightBound
    (streamWeight outputWeight binderArity : Nat) : Nat :=
  compactFormulaFixitrTransformTraceWeightBound
    streamWeight outputWeight binderArity
    (compactNumericCertificateParserFuelWeightBound streamWeight)

/-- Fully source-only canonical trace envelope, after substituting the
semantic mode-5 final-output bound. -/
def compactFormulaFixitrTransformCanonicalSourceTraceWeightBound
    (streamWeight binderArity : Nat) : Nat :=
  compactFormulaFixitrTransformCanonicalTraceWeightBound
    streamWeight
    (compactFormulaFixitrCanonicalOutputWeightBound
      streamWeight binderArity)
    binderArity

/-- The real mode-5 step only appends its computed emission. -/
theorem compactFormulaFixitrStep_output_prefix
    (captureCount : Nat) (state : CompactFormulaFixitrState) :
    state.2 <+: (compactFormulaFixitrStep captureCount state).2 := by
  simp only [compactFormulaFixitrStep]
  exact List.prefix_append _ _

theorem compactFormulaTransformStep_fixitr_output_prefix
    (witness : List Nat) (state : CompactFormulaTransformState) :
    state.2 <+:
      (compactFormulaTransformStep (5, witness) state).2 := by
  rw [compactFormulaTransformStep_fixitr]
  exact compactFormulaFixitrStep_output_prefix witness.length state

theorem compactFormulaTransformIterate_fixitr_output_prefix
    (witness : List Nat) (state : CompactFormulaTransformState)
    (steps : Nat) :
    state.2 <+:
      (((compactFormulaTransformStep (5, witness))^[steps]) state).2 := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans
        (compactFormulaTransformStep_fixitr_output_prefix witness _)

theorem compactFormulaTransformStateAt_fixitr_output_prefix
    (witness : List Nat) (start : CompactFormulaTransformState)
    {first last : Nat} (hsteps : first <= last) :
    (compactFormulaTransformStateAt (5, witness) start first).2 <+:
      (compactFormulaTransformStateAt (5, witness) start last).2 := by
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le hsteps
  have hcompose :
      compactFormulaTransformStateAt (5, witness) start (first + steps) =
        ((compactFormulaTransformStep (5, witness))^[steps])
          (compactFormulaTransformStateAt (5, witness) start first) := by
    simp only [compactFormulaTransformStateAt]
    rw [Nat.add_comm first steps, Function.iterate_add_apply]
  rw [hcompose]
  exact compactFormulaTransformIterate_fixitr_output_prefix witness
    (compactFormulaTransformStateAt (5, witness) start first) steps

theorem compactFormulaTransformStateAt_fixitr_output_weight_mono
    (witness : List Nat) (start : CompactFormulaTransformState)
    {first last : Nat} (hsteps : first <= last) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateAt (5, witness) start first).2 <=
      compactAdditiveValueWeight
        (compactFormulaTransformStateAt (5, witness) start last).2 := by
  exact compactAdditiveValueWeight_infix_le
    (compactFormulaTransformStateAt_fixitr_output_prefix
      witness start hsteps).isInfix

theorem compactFormulaFixitrTransformStateWeightBound_mono
    {streamLeft streamRight outputLeft outputRight
      binderLeft binderRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft <= streamRight)
    (houtput : outputLeft <= outputRight)
    (hbinder : binderLeft <= binderRight)
    (hfuel : fuelLeft <= fuelRight) :
    compactFormulaFixitrTransformStateWeightBound
        streamLeft outputLeft binderLeft fuelLeft <=
      compactFormulaFixitrTransformStateWeightBound
        streamRight outputRight binderRight fuelRight := by
  have hparser :
      compactNumericFormulaParserStateWeightBound
          streamLeft (binderLeft + fuelLeft) fuelLeft <=
        compactNumericFormulaParserStateWeightBound
          streamRight (binderRight + fuelRight) fuelRight :=
    compactNumericFormulaParserStateWeightBound_mono
      hstream (by omega) hfuel
  unfold compactFormulaFixitrTransformStateWeightBound
  omega

theorem compactFormulaFixitrTransformTraceWeightBound_mono
    {streamLeft streamRight outputLeft outputRight
      binderLeft binderRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft <= streamRight)
    (houtput : outputLeft <= outputRight)
    (hbinder : binderLeft <= binderRight)
    (hfuel : fuelLeft <= fuelRight) :
    compactFormulaFixitrTransformTraceWeightBound
        streamLeft outputLeft binderLeft fuelLeft <=
      compactFormulaFixitrTransformTraceWeightBound
        streamRight outputRight binderRight fuelRight := by
  have hfuelAdd : fuelLeft + 1 <= fuelRight + 1 := by omega
  have hfuelSize := Nat.size_le_size hfuelAdd
  have hstate := compactFormulaFixitrTransformStateWeightBound_mono
    hstream houtput hbinder hfuel
  have hproduct := Nat.mul_le_mul hfuelAdd hstate
  unfold compactFormulaFixitrTransformTraceWeightBound
  omega

/-- Every mode-5 state through `fuel` is controlled by the parser envelope and
the actual output stored at the final state. -/
theorem compactFormulaTransformStateAt_fixitr_weight_le
    (binderArity stepIndex fuel : Nat)
    (witness tokens : List Nat) (hstepIndex : stepIndex <= fuel) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateAt
          (5, witness)
          (compactFormulaTransformInitialState binderArity tokens)
          stepIndex) <=
      compactFormulaFixitrTransformStateWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight
          (compactFormulaTransformStateAt
            (5, witness)
            (compactFormulaTransformInitialState binderArity tokens)
            fuel).2)
        binderArity fuel := by
  let start := compactFormulaTransformInitialState binderArity tokens
  let current := compactFormulaTransformStateAt
    (5, witness) start stepIndex
  let final := compactFormulaTransformStateAt
    (5, witness) start fuel
  have hparserRaw :=
    compactFormulaTransformStateAt_parser_weight_le
      5 binderArity stepIndex witness tokens
  have hparser :
      compactAdditiveValueWeight current.1 <=
        compactNumericFormulaParserStateWeightBound
          (compactAdditiveValueWeight tokens)
          (binderArity + fuel) fuel := by
    exact hparserRaw.trans
      (compactNumericFormulaParserStateWeightBound_mono
        (Nat.le_refl _) (by omega) hstepIndex)
  have houtput : compactAdditiveValueWeight current.2 <=
      compactAdditiveValueWeight final.2 := by
    exact compactFormulaTransformStateAt_fixitr_output_weight_mono
      witness start hstepIndex
  unfold compactFormulaFixitrTransformStateWeightBound
  rw [compactAdditiveValueWeight_prod]
  exact Nat.add_le_add hparser houtput

/-- Explicit actual-fuel bound for the complete mode-5 state trace. -/
theorem compactFormulaTransformStateTrace_fixitr_weight_le
    (binderArity fuel : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (5, witness) fuel
          (compactFormulaTransformInitialState binderArity tokens)) <=
      compactFormulaFixitrTransformTraceWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight
          (compactFormulaTransformStateAt
            (5, witness)
            (compactFormulaTransformInitialState binderArity tokens)
            fuel).2)
        binderArity fuel := by
  have hrows := compactAdditiveValueWeight_list_le
    (compactFormulaTransformStateTrace
      (5, witness) fuel
      (compactFormulaTransformInitialState binderArity tokens))
    (compactFormulaFixitrTransformStateWeightBound
      (compactAdditiveValueWeight tokens)
      (compactAdditiveValueWeight
        (compactFormulaTransformStateAt
          (5, witness)
          (compactFormulaTransformInitialState binderArity tokens)
          fuel).2)
      binderArity fuel)
    (fun state hstate => by
      rw [compactFormulaTransformStateTrace] at hstate
      rcases List.mem_map.mp hstate with
        ⟨stepIndex, hstepIndex, rfl⟩
      simp only [List.mem_range] at hstepIndex
      exact compactFormulaTransformStateAt_fixitr_weight_le
        binderArity stepIndex fuel witness tokens (by omega))
  unfold compactFormulaFixitrTransformTraceWeightBound
  rw [compactFormulaTransformStateTrace_length] at hrows
  exact hrows

/-- Canonical mode-5 trace bound.  The only output quantity is the actual
final emitted list; witness size does not occur. -/
theorem compactFormulaTransformCanonicalStateTrace_fixitr_weight_le
    (binderArity : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (5, witness)
          (compactSyntaxRunFuelBound tokens)
          (compactFormulaTransformInitialState binderArity tokens)) <=
      compactFormulaFixitrTransformCanonicalTraceWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight
          (compactFormulaTransformRun
            (5, witness) (binderArity, tokens)).2)
        binderArity := by
  let fuel := compactSyntaxRunFuelBound tokens
  have hraw := compactFormulaTransformStateTrace_fixitr_weight_le
    binderArity fuel witness tokens
  have hfuel : fuel <=
      compactNumericCertificateParserFuelWeightBound
        (compactAdditiveValueWeight tokens) :=
    compactSyntaxRunFuelBound_le_weightBound (Nat.le_refl _)
  have hfinal :
      (compactFormulaTransformStateAt
        (5, witness)
        (compactFormulaTransformInitialState binderArity tokens)
        fuel).2 =
      (compactFormulaTransformRun
        (5, witness) (binderArity, tokens)).2 := by
    rfl
  rw [hfinal] at hraw
  exact hraw.trans
    (compactFormulaFixitrTransformTraceWeightBound_mono
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hfuel)

theorem compactFormulaTransformCanonicalStateTrace_fixitr_source_weight_le
    (binderArity : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (5, witness)
          (compactSyntaxRunFuelBound tokens)
          (compactFormulaTransformInitialState binderArity tokens)) <=
      compactFormulaFixitrTransformCanonicalSourceTraceWeightBound
        (compactAdditiveValueWeight tokens) binderArity := by
  have htrace :=
    compactFormulaTransformCanonicalStateTrace_fixitr_weight_le
      binderArity witness tokens
  have houtput :=
    compactFormulaTransformCanonicalRun_fixitr_output_source_weight_le
      binderArity witness tokens
  exact htrace.trans (by
    unfold compactFormulaFixitrTransformCanonicalSourceTraceWeightBound
      compactFormulaFixitrTransformCanonicalTraceWeightBound
    exact compactFormulaFixitrTransformTraceWeightBound_mono
      (Nat.le_refl _) houtput (Nat.le_refl _) (Nat.le_refl _))

theorem
    compactFormulaTransformCanonicalStateTrace_fixitr_zeroBinder_source_weight_le
    (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (5, witness)
          (compactSyntaxRunFuelBound tokens)
          (compactFormulaTransformInitialState 0 tokens)) <=
      compactFormulaFixitrTransformCanonicalSourceTraceWeightBound
        (compactAdditiveValueWeight tokens) 0 := by
  exact compactFormulaTransformCanonicalStateTrace_fixitr_source_weight_le
    0 witness tokens

/-- A successful mode-5 result identifies the final emitted list used by the
canonical trace bound. -/
theorem compactFormulaTransformCanonicalStateTrace_fixitr_weight_le_of_result
    (binderArity : Nat) (witness tokens output suffix : List Nat)
    (hresult : compactFormulaTransformResult
      (5, witness) (binderArity, tokens) = some (output, suffix)) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (5, witness)
          (compactSyntaxRunFuelBound tokens)
          (compactFormulaTransformInitialState binderArity tokens)) <=
      compactFormulaFixitrTransformCanonicalTraceWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight output)
        binderArity := by
  have hfinalOutput :
      (compactFormulaTransformRun
        (5, witness) (binderArity, tokens)).2 = output :=
    (compactFormulaTransformStateOutput_eq_some_iff.mp hresult).2
  simpa only [hfinalOutput] using
    compactFormulaTransformCanonicalStateTrace_fixitr_weight_le
      binderArity witness tokens

/-- Chunk-facing form for guarded-induction exact transforms, including state
trace chunks 29, 32, and 36. -/
theorem compactFormulaTransformCanonicalStateTrace_fixitr_weight_le_of_exactResult
    (binderArity : Nat) (witness tokens output : List Nat)
    (hresult : compactExactFormulaTransformResult
      (compactFormulaTransformResult
        (5, witness) (binderArity, tokens)) = some output) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (5, witness)
          (compactSyntaxRunFuelBound tokens)
          (compactFormulaTransformInitialState binderArity tokens)) <=
      compactFormulaFixitrTransformCanonicalTraceWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight output)
        binderArity := by
  have hrunResult : compactFormulaTransformResult
      (5, witness) (binderArity, tokens) = some (output, []) :=
    compactExactFormulaTransformResult_eq_some_iff.mp hresult
  exact compactFormulaTransformCanonicalStateTrace_fixitr_weight_le_of_result
    binderArity witness tokens output [] hrunResult

/-- The exact shape shared by guarded-induction route chunks 29, 32, and 36.
Its right-hand side depends only on source and final-output weights; the fuel
is the fixed polynomial envelope computed from the source weight. -/
theorem compactFormulaTransformCanonicalStateTrace_fixitr_zeroBinder_weight_le
    (witness tokens output : List Nat)
    (hresult : compactExactFormulaTransformResult
      (compactFormulaTransformResult (5, witness) (0, tokens)) =
        some output) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (5, witness)
          (compactSyntaxRunFuelBound tokens)
          (compactFormulaTransformInitialState 0 tokens)) <=
      compactFormulaFixitrTransformCanonicalTraceWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight output)
        0 := by
  exact
    compactFormulaTransformCanonicalStateTrace_fixitr_weight_le_of_exactResult
      0 witness tokens output hresult

#print axioms compactFixitrConsumedTermHeader_weight_le
#print axioms compactFormulaFixitrEmission_weight_le
#print axioms compactFormulaTransformStateAt_fixitr_output_source_weight_le
#print axioms
  compactFormulaTransformCanonicalRun_fixitr_output_source_weight_le
#print axioms
  compactFormulaTransformExactResult_fixitr_output_source_weight_le
#print axioms
  compactFormulaTransformExactResultGetD_fixitr_output_source_weight_le
#print axioms
  compactFormulaTransformCanonicalStateTrace_fixitr_source_weight_le
#print axioms compactFormulaFixitrStep_output_prefix
#print axioms compactFormulaTransformStateAt_fixitr_output_prefix
#print axioms compactFormulaTransformStateTrace_fixitr_weight_le
#print axioms
  compactFormulaTransformCanonicalStateTrace_fixitr_weight_le_of_exactResult
#print axioms
  compactFormulaTransformCanonicalStateTrace_fixitr_zeroBinder_weight_le

end FoundationCompactNumericListedDirectFormulaFixitrTraceWeightBounds
