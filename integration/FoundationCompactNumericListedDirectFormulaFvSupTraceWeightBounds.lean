import integration.FoundationCompactNumericListedDirectFormulaTransformValueBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformExactFormula

/-!
# Additive weight bounds for mode-4 formula-transform traces

The free-variable-list transform only appends each step's emission to its
current output.  Thus every intermediate output is a prefix of the final
output.  Combining that semantic fact with the mode-independent parser-state
bound gives a trace bound depending only on the source weight, final output
weight, binder arity, and fuel.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaFvSupTraceWeightBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTransformationTraceCore
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericFormulaFvSup
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectFormulaTransformValueBounds
open FoundationCompactNumericListedDirectFormulaTransformExactFormula

/-- Per-state envelope for a mode-4 trace whose final emitted list has the
given additive weight. -/
def compactFormulaFvSupTransformStateWeightBound
    (streamWeight outputWeight binderArity fuel : Nat) : Nat :=
  compactNumericFormulaParserStateWeightBound
      streamWeight (binderArity + fuel) fuel +
    outputWeight

/-- Whole-trace envelope obtained from the exact canonical trace length. -/
def compactFormulaFvSupTransformTraceWeightBound
    (streamWeight outputWeight binderArity fuel : Nat) : Nat :=
  Nat.size (fuel + 1) + 1 +
    (fuel + 1) *
      compactFormulaFvSupTransformStateWeightBound
        streamWeight outputWeight binderArity fuel

/-- Fixed-fuel public envelope used by canonical formula-transform traces. -/
def compactFormulaFvSupTransformCanonicalTraceWeightBound
    (streamWeight outputWeight binderArity : Nat) : Nat :=
  compactFormulaFvSupTransformTraceWeightBound
    streamWeight outputWeight binderArity
    (compactNumericCertificateParserFuelWeightBound streamWeight)

theorem compactFormulaTransformStep_fvSup_output_prefix
    (witness : List Nat) (state : CompactFormulaTransformState) :
    state.2 <+:
      (compactFormulaTransformStep (4, witness) state).2 := by
  simp only [compactFormulaTransformStep_fvList,
    compactFormulaFvListStep]
  exact List.prefix_append _ _

theorem compactFormulaTransformIterate_fvSup_output_prefix
    (witness : List Nat) (state : CompactFormulaTransformState)
    (steps : Nat) :
    state.2 <+:
      (((compactFormulaTransformStep (4, witness))^[steps]) state).2 := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans
        (compactFormulaTransformStep_fvSup_output_prefix witness _)

theorem compactFormulaTransformStateAt_fvSup_output_prefix
    (witness : List Nat) (start : CompactFormulaTransformState)
    {first last : Nat} (hsteps : first <= last) :
    (compactFormulaTransformStateAt (4, witness) start first).2 <+:
      (compactFormulaTransformStateAt (4, witness) start last).2 := by
  rcases Nat.exists_eq_add_of_le hsteps with ⟨steps, rfl⟩
  change
    (((compactFormulaTransformStep (4, witness))^[first]) start).2 <+:
      (((compactFormulaTransformStep (4, witness))^[first + steps]) start).2
  rw [show first + steps = steps + first by omega,
    Function.iterate_add_apply]
  exact compactFormulaTransformIterate_fvSup_output_prefix witness
    (compactFormulaTransformStateAt (4, witness) start first) steps

theorem compactFormulaFvSupTransformStateWeightBound_mono
    {streamLeft streamRight outputLeft outputRight
      binderLeft binderRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft <= streamRight)
    (houtput : outputLeft <= outputRight)
    (hbinder : binderLeft <= binderRight)
    (hfuel : fuelLeft <= fuelRight) :
    compactFormulaFvSupTransformStateWeightBound
        streamLeft outputLeft binderLeft fuelLeft <=
      compactFormulaFvSupTransformStateWeightBound
        streamRight outputRight binderRight fuelRight := by
  have hbinderFuel : binderLeft + fuelLeft <=
      binderRight + fuelRight := Nat.add_le_add hbinder hfuel
  have hparser := compactNumericFormulaParserStateWeightBound_mono
    hstream hbinderFuel hfuel
  unfold compactFormulaFvSupTransformStateWeightBound
  exact Nat.add_le_add hparser houtput

theorem compactFormulaFvSupTransformTraceWeightBound_mono
    {streamLeft streamRight outputLeft outputRight
      binderLeft binderRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft <= streamRight)
    (houtput : outputLeft <= outputRight)
    (hbinder : binderLeft <= binderRight)
    (hfuel : fuelLeft <= fuelRight) :
    compactFormulaFvSupTransformTraceWeightBound
        streamLeft outputLeft binderLeft fuelLeft <=
      compactFormulaFvSupTransformTraceWeightBound
        streamRight outputRight binderRight fuelRight := by
  have hfuelAdd : fuelLeft + 1 <= fuelRight + 1 := by omega
  have hfuelSize := Nat.size_le_size hfuelAdd
  have hstate := compactFormulaFvSupTransformStateWeightBound_mono
    hstream houtput hbinder hfuel
  have hproduct := Nat.mul_le_mul hfuelAdd hstate
  unfold compactFormulaFvSupTransformTraceWeightBound
  omega

theorem compactFormulaTransformStateAt_fvSup_weight_le
    (binderArity stepIndex fuel : Nat)
    (witness tokens : List Nat) (hstepIndex : stepIndex <= fuel) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateAt
          (4, witness)
          (compactFormulaTransformInitialState binderArity tokens)
          stepIndex) <=
      compactFormulaFvSupTransformStateWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight
          (compactFormulaTransformStateAt
            (4, witness)
            (compactFormulaTransformInitialState binderArity tokens)
            fuel).2)
        binderArity fuel := by
  let start := compactFormulaTransformInitialState binderArity tokens
  let current := compactFormulaTransformStateAt
    (4, witness) start stepIndex
  let final := compactFormulaTransformStateAt
    (4, witness) start fuel
  have hparserRaw :=
    compactFormulaTransformStateAt_parser_weight_le
      4 binderArity stepIndex witness tokens
  have hparser :
      compactAdditiveValueWeight current.1 <=
        compactNumericFormulaParserStateWeightBound
          (compactAdditiveValueWeight tokens)
          (binderArity + fuel) fuel := by
    simpa only [current, start] using
      hparserRaw.trans
        (compactNumericFormulaParserStateWeightBound_mono
          (Nat.le_refl _) (by omega) hstepIndex)
  have hprefix : current.2 <+: final.2 := by
    exact compactFormulaTransformStateAt_fvSup_output_prefix
      witness start hstepIndex
  have houtput : compactAdditiveValueWeight current.2 <=
      compactAdditiveValueWeight final.2 :=
    compactAdditiveValueWeight_infix_le hprefix.isInfix
  change compactAdditiveValueWeight current <= _
  rw [compactAdditiveValueWeight_prod]
  unfold compactFormulaFvSupTransformStateWeightBound
  exact Nat.add_le_add hparser houtput

theorem compactFormulaTransformStateTrace_fvSup_weight_le
    (binderArity fuel : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (4, witness) fuel
          (compactFormulaTransformInitialState binderArity tokens)) <=
      compactFormulaFvSupTransformTraceWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight
          (compactFormulaTransformStateAt
            (4, witness)
            (compactFormulaTransformInitialState binderArity tokens)
            fuel).2)
        binderArity fuel := by
  have hrows := compactAdditiveValueWeight_list_le
    (compactFormulaTransformStateTrace
      (4, witness) fuel
      (compactFormulaTransformInitialState binderArity tokens))
    (compactFormulaFvSupTransformStateWeightBound
      (compactAdditiveValueWeight tokens)
      (compactAdditiveValueWeight
        (compactFormulaTransformStateAt
          (4, witness)
          (compactFormulaTransformInitialState binderArity tokens)
          fuel).2)
      binderArity fuel)
    (fun state hstate => by
      rw [compactFormulaTransformStateTrace] at hstate
      rcases List.mem_map.mp hstate with
        ⟨stepIndex, hstepIndex, rfl⟩
      simp only [List.mem_range] at hstepIndex
      exact compactFormulaTransformStateAt_fvSup_weight_le
        binderArity stepIndex fuel witness tokens (by omega))
  unfold compactFormulaFvSupTransformTraceWeightBound
  rw [compactFormulaTransformStateTrace_length] at hrows
  exact hrows

theorem compactFormulaTransformCanonicalStateTrace_fvSup_weight_le
    (binderArity : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (4, witness)
          (compactSyntaxRunFuelBound tokens)
          (compactFormulaTransformInitialState binderArity tokens)) <=
      compactFormulaFvSupTransformCanonicalTraceWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight
          (compactFormulaTransformRun
            (4, witness) (binderArity, tokens)).2)
        binderArity := by
  let fuel := compactSyntaxRunFuelBound tokens
  have hraw := compactFormulaTransformStateTrace_fvSup_weight_le
    binderArity fuel witness tokens
  have hfuel : fuel <=
      compactNumericCertificateParserFuelWeightBound
        (compactAdditiveValueWeight tokens) :=
    compactSyntaxRunFuelBound_le_weightBound (Nat.le_refl _)
  have hfinal :
      (compactFormulaTransformStateAt
        (4, witness)
        (compactFormulaTransformInitialState binderArity tokens)
        fuel).2 =
      (compactFormulaTransformRun
        (4, witness) (binderArity, tokens)).2 := by
    rfl
  rw [hfinal] at hraw
  exact hraw.trans
    (compactFormulaFvSupTransformTraceWeightBound_mono
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hfuel)

/-- Chunk-facing form: an exact successful mode-4 result identifies the final
emitted list with the supplied `output` (the guarded-induction fvar list). -/
theorem compactFormulaTransformCanonicalStateTrace_fvSup_weight_le_of_exactResult
    (binderArity : Nat) (witness tokens output : List Nat)
    (hresult : compactExactFormulaTransformResult
      (compactFormulaTransformResult
        (4, witness) (binderArity, tokens)) = some output) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (4, witness)
          (compactSyntaxRunFuelBound tokens)
          (compactFormulaTransformInitialState binderArity tokens)) <=
      compactFormulaFvSupTransformCanonicalTraceWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight output)
        binderArity := by
  have hrunResult : compactFormulaTransformResult
      (4, witness) (binderArity, tokens) = some (output, []) :=
    compactExactFormulaTransformResult_eq_some_iff.mp hresult
  have hfinalOutput :
      (compactFormulaTransformRun
        (4, witness) (binderArity, tokens)).2 = output :=
    (compactFormulaTransformStateOutput_eq_some_iff.mp hrunResult).2
  simpa only [hfinalOutput] using
    compactFormulaTransformCanonicalStateTrace_fvSup_weight_le
      binderArity witness tokens

/-- A genuine mode-4 term-header emission is either empty or a singleton
whose sole token was read from the consumed source prefix. -/
theorem compactFvListConsumedTermHeader_weight_le
    (tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFvListConsumedTermHeader tokens) <=
      compactAdditiveValueWeight tokens + 2 := by
  unfold compactFvListConsumedTermHeader
  split_ifs
  · have htoken := compactTokenAt_weight_le tokens 1
    rw [compactAdditiveValueWeight_list]
    simp only [List.length_cons, List.length_nil, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil]
    have hsize : Nat.size 1 = 1 := by decide
    rw [hsize]
    omega
  · simp [compactAdditiveValueWeight_list]
  · simp [compactAdditiveValueWeight_list]

/-- Every real mode-4 emission has additive weight at most the weight of the
consumed source prefix plus the singleton-list overhead. -/
theorem compactFormulaFvListEmission_weight_le
    (taskKind : Nat) (consumed : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaFvListEmission taskKind consumed) <=
      compactAdditiveValueWeight consumed + 2 := by
  by_cases htask : taskKind = 0
  · simpa [compactFormulaFvListEmission, htask] using
      compactFvListConsumedTermHeader_weight_le consumed
  · simp [compactFormulaFvListEmission, htask,
      compactAdditiveValueWeight_list]

/-- One mode-4 step increases output weight by at most the current parser
source weight plus the singleton-list overhead. -/
theorem compactFormulaTransformStep_fvSup_output_weight_le
    (witness : List Nat) (state : CompactFormulaTransformState) :
    compactAdditiveValueWeight
        (compactFormulaTransformStep (4, witness) state).2 <=
      compactAdditiveValueWeight state.2 +
        compactAdditiveValueWeight state.1.1 + 2 := by
  let nextParserState := compactSyntaxParserStep state.1
  let consumed := consumedTokenPrefix state.1.1 nextParserState.1
  let emitted := compactFormulaFvListEmission
    (compactSyntaxCurrentTaskKind state.1) consumed
  have happend := compactAdditiveValueWeight_list_append_le
    state.2 emitted
  have hemitted : compactAdditiveValueWeight emitted <=
      compactAdditiveValueWeight consumed + 2 := by
    simpa [emitted] using compactFormulaFvListEmission_weight_le
      (compactSyntaxCurrentTaskKind state.1) consumed
  have hconsumed : compactAdditiveValueWeight consumed <=
      compactAdditiveValueWeight state.1.1 := by
    simpa [consumed, nextParserState] using
      consumedTokenPrefix_weight_le state.1.1
        (compactSyntaxParserStep state.1).1
  have hbound :
      compactAdditiveValueWeight (state.2 ++ emitted) <=
        compactAdditiveValueWeight state.2 +
          compactAdditiveValueWeight state.1.1 + 2 := by
    omega
  simpa [compactFormulaTransformStep_fvList,
    compactFormulaFvListStep, nextParserState, consumed, emitted] using hbound

/-- Fuel-indexed polynomial envelope for every mode-4 output. -/
def compactFormulaFvSupOutputWeightBound
    (streamWeight fuel : Nat) : Nat :=
  1 + fuel * (streamWeight + 2)

theorem compactFormulaFvSupOutputWeightBound_mono
    {streamLeft streamRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft <= streamRight)
    (hfuel : fuelLeft <= fuelRight) :
    compactFormulaFvSupOutputWeightBound streamLeft fuelLeft <=
      compactFormulaFvSupOutputWeightBound streamRight fuelRight := by
  have hfactor : streamLeft + 2 <= streamRight + 2 := by omega
  have hproduct := Nat.mul_le_mul hfuel hfactor
  unfold compactFormulaFvSupOutputWeightBound
  omega

/-- The output after any prefix of the real mode-4 state graph depends only
on the original source weight and the prefix length. -/
theorem compactFormulaTransformStateAt_fvSup_output_weight_le
    (binderArity stepIndex : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateAt
          (4, witness)
          (compactFormulaTransformInitialState binderArity tokens)
          stepIndex).2 <=
      compactFormulaFvSupOutputWeightBound
        (compactAdditiveValueWeight tokens) stepIndex := by
  induction stepIndex with
  | zero =>
      simp [compactFormulaTransformStateAt,
        compactFormulaTransformInitialState,
        compactFormulaFvSupOutputWeightBound]
  | succ stepIndex ih =>
      let current := compactFormulaTransformStateAt
        (4, witness)
        (compactFormulaTransformInitialState binderArity tokens)
        stepIndex
      have hstep := compactFormulaTransformStep_fvSup_output_weight_le
        witness current
      have hsource := compactFormulaTransformStateAt_parser_source
        4 binderArity stepIndex witness tokens
      have hstream : compactAdditiveValueWeight current.1.1 <=
          compactAdditiveValueWeight tokens := by
        simpa [current] using
          compactAdditiveValueWeight_suffix_le hsource.1
      have ihCurrent : compactAdditiveValueWeight current.2 <=
          compactFormulaFvSupOutputWeightBound
            (compactAdditiveValueWeight tokens) stepIndex := by
        simpa [current] using ih
      have hfinal :
          compactAdditiveValueWeight
              (compactFormulaTransformStep (4, witness) current).2 <=
            compactFormulaFvSupOutputWeightBound
              (compactAdditiveValueWeight tokens) (stepIndex + 1) := by
        unfold compactFormulaFvSupOutputWeightBound at ihCurrent ⊢
        rw [Nat.add_mul]
        simp only [one_mul]
        omega
      simpa [current, compactFormulaTransformStateAt,
        Function.iterate_succ_apply'] using hfinal

/-- Source-only polynomial envelope obtained by substituting the canonical
quadratic parser-fuel bound. -/
def compactFormulaFvSupCanonicalOutputWeightBound
    (streamWeight : Nat) : Nat :=
  compactFormulaFvSupOutputWeightBound streamWeight
    (compactNumericCertificateParserFuelWeightBound streamWeight)

theorem compactFormulaFvSupCanonicalOutputWeightBound_mono
    {streamLeft streamRight : Nat} (hstream : streamLeft <= streamRight) :
    compactFormulaFvSupCanonicalOutputWeightBound streamLeft <=
      compactFormulaFvSupCanonicalOutputWeightBound streamRight := by
  exact compactFormulaFvSupOutputWeightBound_mono hstream
    (compactNumericCertificateParserFuelWeightBound_mono hstream)

/-- The canonical mode-4 run output is bounded without assuming success and
without taking the output itself as a bound parameter. -/
theorem compactFormulaTransformCanonicalRun_fvSup_output_weight_le
    (binderArity : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaTransformRun
          (4, witness) (binderArity, tokens)).2 <=
      compactFormulaFvSupCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens) := by
  have hraw := compactFormulaTransformStateAt_fvSup_output_weight_le
    binderArity (compactSyntaxRunFuelBound tokens) witness tokens
  have hfuel := compactSyntaxRunFuelBound_le_weightBound
    (Nat.le_refl (compactAdditiveValueWeight tokens))
  exact hraw.trans
    (compactFormulaFvSupOutputWeightBound_mono (Nat.le_refl _) hfuel)

/-- Chunk-facing exact-result form: the guarded-induction `fvarList` weight is
bounded solely by the source sentence-token weight. -/
theorem compactFormulaTransformCanonicalExactResult_fvSup_output_weight_le
    (binderArity : Nat) (witness tokens output : List Nat)
    (hresult : compactExactFormulaTransformResult
      (compactFormulaTransformResult
        (4, witness) (binderArity, tokens)) = some output) :
    compactAdditiveValueWeight output <=
      compactFormulaFvSupCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens) := by
  have hrunResult : compactFormulaTransformResult
      (4, witness) (binderArity, tokens) = some (output, []) :=
    compactExactFormulaTransformResult_eq_some_iff.mp hresult
  have hfinalOutput :
      (compactFormulaTransformRun
        (4, witness) (binderArity, tokens)).2 = output :=
    (compactFormulaTransformStateOutput_eq_some_iff.mp hrunResult).2
  simpa only [hfinalOutput] using
    compactFormulaTransformCanonicalRun_fvSup_output_weight_le
      binderArity witness tokens

/-- Canonical trace envelope with the final-output parameter eliminated. -/
def compactFormulaFvSupTransformCanonicalSourceTraceWeightBound
    (streamWeight binderArity : Nat) : Nat :=
  compactFormulaFvSupTransformCanonicalTraceWeightBound
    streamWeight
    (compactFormulaFvSupCanonicalOutputWeightBound streamWeight)
    binderArity

theorem compactFormulaTransformCanonicalStateTrace_fvSup_source_weight_le_of_exactResult
    (binderArity : Nat) (witness tokens output : List Nat)
    (hresult : compactExactFormulaTransformResult
      (compactFormulaTransformResult
        (4, witness) (binderArity, tokens)) = some output) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (4, witness)
          (compactSyntaxRunFuelBound tokens)
          (compactFormulaTransformInitialState binderArity tokens)) <=
      compactFormulaFvSupTransformCanonicalSourceTraceWeightBound
        (compactAdditiveValueWeight tokens) binderArity := by
  have htrace :=
    compactFormulaTransformCanonicalStateTrace_fvSup_weight_le_of_exactResult
      binderArity witness tokens output hresult
  have houtput :=
    compactFormulaTransformCanonicalExactResult_fvSup_output_weight_le
      binderArity witness tokens output hresult
  unfold compactFormulaFvSupTransformCanonicalSourceTraceWeightBound
    compactFormulaFvSupTransformCanonicalTraceWeightBound at htrace ⊢
  exact htrace.trans
    (compactFormulaFvSupTransformTraceWeightBound_mono
      (Nat.le_refl _) houtput (Nat.le_refl _) (Nat.le_refl _))

#print axioms compactFormulaTransformStateAt_fvSup_output_prefix
#print axioms compactFormulaTransformStateTrace_fvSup_weight_le
#print axioms
  compactFormulaTransformCanonicalStateTrace_fvSup_weight_le_of_exactResult
#print axioms compactFvListConsumedTermHeader_weight_le
#print axioms compactFormulaFvListEmission_weight_le
#print axioms compactFormulaTransformStateAt_fvSup_output_weight_le
#print axioms
  compactFormulaTransformCanonicalExactResult_fvSup_output_weight_le
#print axioms
  compactFormulaTransformCanonicalStateTrace_fvSup_source_weight_le_of_exactResult

end FoundationCompactNumericListedDirectFormulaFvSupTraceWeightBounds
