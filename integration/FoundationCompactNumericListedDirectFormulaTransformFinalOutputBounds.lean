import integration.FoundationCompactNumericListedDirectFormulaTransformValueBounds

/-!
# Formula-transform trace bounds from the final emitted output

Every one of the six concrete transform machines only appends to its emitted
output.  Consequently every intermediate output is a prefix of the final
output.  This gives a mode-independent bound for the complete state trace and,
in particular, covers the free-variable-list and `fixitr` modes without an
assumed per-step cost bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformFinalOutputBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectFormulaTransformValueBounds

theorem compactFormulaTransformStep_output_prefix
    (control : CompactFormulaTransformControl)
    (state : CompactFormulaTransformState) :
    state.2 <+: (compactFormulaTransformStep control state).2 := by
  rcases control with ⟨mode, witness⟩
  simp only [compactFormulaTransformStep]
  split_ifs <;>
    simp only [
      FoundationCompactNumericFormulaFree.compactFormulaFreeStep,
      FoundationCompactNumericFormulaShift.compactFormulaShiftStep,
      FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionStep,
      FoundationCompactNumericFormulaFvSup.compactFormulaFvListStep,
      FoundationCompactNumericFormulaFixitr.compactFormulaFixitrStep,
      FoundationCompactNumericFormulaNegation.compactFormulaNegationStep] <;>
    exact List.prefix_append _ _

theorem compactFormulaTransformStateAt_output_prefix_succ
    (control : CompactFormulaTransformControl)
    (start : CompactFormulaTransformState) (stepIndex : Nat) :
    (compactFormulaTransformStateAt control start stepIndex).2 <+:
      (compactFormulaTransformStateAt control start (stepIndex + 1)).2 := by
  simpa [compactFormulaTransformStateAt, Function.iterate_succ_apply'] using
    compactFormulaTransformStep_output_prefix control
      (compactFormulaTransformStateAt control start stepIndex)

theorem compactFormulaTransformStateAt_output_prefix_of_le
    (control : CompactFormulaTransformControl)
    (start : CompactFormulaTransformState) {left right : Nat}
    (hleft : left ≤ right) :
    (compactFormulaTransformStateAt control start left).2 <+:
      (compactFormulaTransformStateAt control start right).2 := by
  obtain ⟨distance, rfl⟩ := Nat.exists_eq_add_of_le hleft
  clear hleft
  induction distance with
  | zero => exact List.prefix_rfl
  | succ distance ih =>
      exact ih.trans (by
        simpa [Nat.add_assoc] using
          compactFormulaTransformStateAt_output_prefix_succ
            control start (left + distance))

def compactFormulaTransformFinalOutputStateWeightBound
    (streamWeight finalOutputWeight binderArity fuel : Nat) : Nat :=
  compactNumericFormulaParserStateWeightBound
      streamWeight (binderArity + fuel) fuel +
    finalOutputWeight

theorem compactFormulaTransformFinalOutputStateWeightBound_mono
    {streamLeft streamRight outputLeft outputRight
      binderLeft binderRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft ≤ streamRight)
    (houtput : outputLeft ≤ outputRight)
    (hbinder : binderLeft ≤ binderRight)
    (hfuel : fuelLeft ≤ fuelRight) :
    compactFormulaTransformFinalOutputStateWeightBound
        streamLeft outputLeft binderLeft fuelLeft ≤
      compactFormulaTransformFinalOutputStateWeightBound
        streamRight outputRight binderRight fuelRight := by
  have hparser := compactNumericFormulaParserStateWeightBound_mono
    hstream (Nat.add_le_add hbinder hfuel) hfuel
  unfold compactFormulaTransformFinalOutputStateWeightBound
  omega

theorem compactFormulaTransformStateAt_weight_le_finalOutput
    (mode binderArity stepIndex fuel : Nat)
    (witness tokens finalOutput : List Nat)
    (hstepIndex : stepIndex ≤ fuel)
    (hfinal :
      (compactFormulaTransformStateAt
        (mode, witness)
        (compactFormulaTransformInitialState binderArity tokens)
        fuel).2 = finalOutput) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateAt
          (mode, witness)
          (compactFormulaTransformInitialState binderArity tokens)
          stepIndex) ≤
      compactFormulaTransformFinalOutputStateWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight finalOutput)
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
        (Nat.add_le_add_left hstepIndex binderArity)
        hstepIndex)
  have hprefix := compactFormulaTransformStateAt_output_prefix_of_le
    (mode, witness)
    (compactFormulaTransformInitialState binderArity tokens)
    hstepIndex
  rw [hfinal] at hprefix
  have houtput := compactAdditiveValueWeight_infix_le hprefix.isInfix
  rw [compactAdditiveValueWeight_prod]
  unfold compactFormulaTransformFinalOutputStateWeightBound
  omega

def compactFormulaTransformFinalOutputTraceWeightBound
    (streamWeight finalOutputWeight binderArity fuel : Nat) : Nat :=
  Nat.size (fuel + 1) + 1 +
    (fuel + 1) *
      compactFormulaTransformFinalOutputStateWeightBound
        streamWeight finalOutputWeight binderArity fuel

theorem compactFormulaTransformFinalOutputTraceWeightBound_mono
    {streamLeft streamRight outputLeft outputRight
      binderLeft binderRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft ≤ streamRight)
    (houtput : outputLeft ≤ outputRight)
    (hbinder : binderLeft ≤ binderRight)
    (hfuel : fuelLeft ≤ fuelRight) :
    compactFormulaTransformFinalOutputTraceWeightBound
        streamLeft outputLeft binderLeft fuelLeft ≤
      compactFormulaTransformFinalOutputTraceWeightBound
        streamRight outputRight binderRight fuelRight := by
  have hfuelAdd : fuelLeft + 1 ≤ fuelRight + 1 := by omega
  have hsize := Nat.size_le_size hfuelAdd
  have hstate := compactFormulaTransformFinalOutputStateWeightBound_mono
    hstream houtput hbinder hfuel
  have hproduct := Nat.mul_le_mul hfuelAdd hstate
  unfold compactFormulaTransformFinalOutputTraceWeightBound
  omega

theorem compactFormulaTransformStateTrace_weight_le_finalOutput
    (mode binderArity fuel : Nat)
    (witness tokens finalOutput : List Nat)
    (hfinal :
      (compactFormulaTransformStateAt
        (mode, witness)
        (compactFormulaTransformInitialState binderArity tokens)
        fuel).2 = finalOutput) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (mode, witness) fuel
          (compactFormulaTransformInitialState binderArity tokens)) ≤
      compactFormulaTransformFinalOutputTraceWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight finalOutput)
        binderArity fuel := by
  have hstates := compactAdditiveValueWeight_list_le
    (compactFormulaTransformStateTrace
      (mode, witness) fuel
      (compactFormulaTransformInitialState binderArity tokens))
    (compactFormulaTransformFinalOutputStateWeightBound
      (compactAdditiveValueWeight tokens)
      (compactAdditiveValueWeight finalOutput)
      binderArity fuel)
    (fun state hstate => by
      rw [compactFormulaTransformStateTrace] at hstate
      rcases List.mem_map.mp hstate with ⟨stepIndex, hstepIndex, rfl⟩
      simp only [List.mem_range] at hstepIndex
      exact compactFormulaTransformStateAt_weight_le_finalOutput
        mode binderArity stepIndex fuel witness tokens finalOutput
        (by omega) hfinal)
  rw [compactFormulaTransformStateTrace_length] at hstates
  unfold compactFormulaTransformFinalOutputTraceWeightBound
  exact hstates

def compactFormulaTransformCanonicalFinalOutputTraceWeightBound
    (streamWeight finalOutputWeight binderArity : Nat) : Nat :=
  compactFormulaTransformFinalOutputTraceWeightBound
    streamWeight finalOutputWeight binderArity
      (compactNumericCertificateParserFuelWeightBound streamWeight)

theorem compactFormulaTransformCanonicalStateTrace_weight_le_finalOutput
    (mode binderArity : Nat) (witness tokens finalOutput : List Nat)
    (hfinal :
      (compactFormulaTransformStateAt
        (mode, witness)
        (compactFormulaTransformInitialState binderArity tokens)
        (compactSyntaxRunFuelBound tokens)).2 = finalOutput) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (mode, witness)
          (compactSyntaxRunFuelBound tokens)
          (compactFormulaTransformInitialState binderArity tokens)) ≤
      compactFormulaTransformCanonicalFinalOutputTraceWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight finalOutput)
        binderArity := by
  have hraw := compactFormulaTransformStateTrace_weight_le_finalOutput
    mode binderArity (compactSyntaxRunFuelBound tokens)
    witness tokens finalOutput hfinal
  have hfuel := compactSyntaxRunFuelBound_le_weightBound
    (Nat.le_refl (compactAdditiveValueWeight tokens))
  exact hraw.trans (by
    unfold compactFormulaTransformCanonicalFinalOutputTraceWeightBound
    exact compactFormulaTransformFinalOutputTraceWeightBound_mono
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hfuel)

#print axioms compactFormulaTransformStep_output_prefix
#print axioms compactFormulaTransformStateAt_output_prefix_of_le
#print axioms compactFormulaTransformStateTrace_weight_le_finalOutput
#print axioms compactFormulaTransformCanonicalStateTrace_weight_le_finalOutput

end FoundationCompactNumericListedDirectFormulaTransformFinalOutputBounds
