import integration.FoundationCompactNumericListedDirectParserStateAtRows
import integration.FoundationCompactNumericListedDirectParserSyntaxStepFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformTraceInstallation

/-!
# Installation of the complete syntax-parser step graph into finite traces

Every adjacent pair of a canonical syntax-parser trace is exposed through two
exact state-table rows and the already checked 26-variable bounded step graph.
The only side invariant required by step completeness is preserved by the real
parser and therefore holds at every trace index.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxTraceInstallation

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformTraceInstallation

private theorem getI_eq_of_parserTraceState?_eq_some
    {states : List CompactUnifiedParserState} {index : Nat}
    {state : CompactUnifiedParserState}
    (hstate : compactParserTraceState? states index = some state) :
    states.getI index = state := by
  unfold compactParserTraceState? at hstate
  rw [List.getI_eq_getElem?_getD, hstate]
  rfl

theorem CompactParserLocalTraceValid.getI_eq_stateAt
    {step : CompactUnifiedParserState → CompactUnifiedParserState}
    {fuel : Nat} {start : CompactUnifiedParserState}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid step fuel start states)
    {stepIndex : Nat} (hstepIndex : stepIndex ≤ fuel) :
    states.getI stepIndex = compactParserStateAt step start stepIndex := by
  exact getI_eq_of_parserTraceState?_eq_some
    (compactParserLocalTraceValid_stateAt hvalid hstepIndex)

theorem CompactParserLocalTraceValid.getI_step
    {step : CompactUnifiedParserState → CompactUnifiedParserState}
    {fuel : Nat} {start : CompactUnifiedParserState}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid step fuel start states)
    {stepIndex : Nat} (hstepIndex : stepIndex < fuel) :
    states.getI (stepIndex + 1) = step (states.getI stepIndex) := by
  rw [CompactParserLocalTraceValid.getI_eq_stateAt hvalid (by omega),
    CompactParserLocalTraceValid.getI_eq_stateAt
      hvalid (Nat.le_of_lt hstepIndex)]
  simp [compactParserStateAt, Function.iterate_succ_apply']

theorem compactSyntaxParserStateAt_task_fields_well_formed
    (start : CompactUnifiedParserState)
    (hstart : CompactSyntaxTaskStackFieldsWellFormed start.2.1)
    (stepIndex : Nat) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactParserStateAt compactSyntaxParserStep start stepIndex).2.1 := by
  induction stepIndex with
  | zero =>
      simpa [compactParserStateAt] using hstart
  | succ stepIndex ih =>
      rw [compactParserStateAt, Function.iterate_succ_apply']
      exact compactSyntaxParserStep_preserves_task_fields_well_formed _ ih

theorem CompactParserLocalTraceValid.getI_task_fields_well_formed
    {fuel : Nat} {start : CompactUnifiedParserState}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid
      compactSyntaxParserStep fuel start states)
    (hstart : CompactSyntaxTaskStackFieldsWellFormed start.2.1)
    {stepIndex : Nat} (hstepIndex : stepIndex ≤ fuel) :
    CompactSyntaxTaskStackFieldsWellFormed
      (states.getI stepIndex).2.1 := by
  rw [CompactParserLocalTraceValid.getI_eq_stateAt hvalid hstepIndex]
  exact compactSyntaxParserStateAt_task_fields_well_formed
    start hstart stepIndex

@[simp] theorem compactTermParserInitialState_task_fields_well_formed
    (binderArity : Nat) (tokens : List Nat) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactTermParserInitialState binderArity tokens).2.1 := by
  simp [compactTermParserInitialState, compactTermTask,
    CompactSyntaxTaskStackFieldsWellFormed,
    CompactSyntaxTaskFieldsWellFormed]

@[simp] theorem compactFormulaParserInitialState_task_fields_well_formed
    (binderArity : Nat) (tokens : List Nat) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactFormulaParserInitialState binderArity tokens).2.1 := by
  simp [compactFormulaParserInitialState, compactFormulaTask,
    CompactSyntaxTaskStackFieldsWellFormed,
    CompactSyntaxTaskFieldsWellFormed]

/-- Every adjacent state pair has a complete bounded syntax-step witness. -/
def CompactUnifiedParserSyntaxStateListAdjacentStepRows
    (tokenTable width tokenCount stateBoundary : Nat)
    (states : List CompactUnifiedParserState) : Prop :=
  ∀ index < states.length - 1,
    ∃ currentCoordinates currentSize nextCoordinates nextSize stepWitness,
      CompactUnifiedParserStateAtRows
          tokenTable width tokenCount stateBoundary states.length index
            currentCoordinates currentSize ∧
        CompactUnifiedParserStateAtRows
          tokenTable width tokenCount stateBoundary states.length (index + 1)
            nextCoordinates nextSize ∧
        CompactUnifiedParserSyntaxStepRows
          tokenTable width tokenCount currentCoordinates nextCoordinates
            stepWitness

theorem syntaxStateListAdjacentStepRows_of_localTrace
    {tokenTable width tokenCount stateBoundary fuel : Nat}
    {start : CompactUnifiedParserState}
    {states : List CompactUnifiedParserState}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hvalid : CompactParserLocalTraceValid
      compactSyntaxParserStep fuel start states)
    (hstart : CompactSyntaxTaskStackFieldsWellFormed start.2.1) :
    CompactUnifiedParserSyntaxStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states := by
  intro index hindex
  have hstepIndex : index < fuel := by
    rw [hvalid.1] at hindex
    omega
  have hcurrentIndex : index < states.length := by
    rw [hvalid.1]
    omega
  have hnextIndex : index + 1 < states.length := by
    rw [hvalid.1]
    omega
  rcases exists_compactUnifiedParserStateAtRows_with_fixed_layout
      hrows hcurrentIndex with
    ⟨currentCoordinates, currentSize, hcurrentRows, hcurrentFixed⟩
  rcases exists_compactUnifiedParserStateAtRows_with_fixed_layout
      hrows hnextIndex with
    ⟨nextCoordinates, nextSize, hnextRows, hnextFixed⟩
  have hwell : CompactSyntaxTaskStackFieldsWellFormed
      (states.getI index).2.1 :=
    CompactParserLocalTraceValid.getI_task_fields_well_formed
      hvalid hstart (Nat.le_of_lt hstepIndex)
  have hstep : states.getI (index + 1) =
      compactSyntaxParserStep (states.getI index) :=
    CompactParserLocalTraceValid.getI_step hvalid hstepIndex
  rcases compactUnifiedParserSyntaxStepRows_complete
      hcurrentFixed hnextFixed hwell hstep with
    ⟨stepWitness, hstepRows⟩
  exact ⟨currentCoordinates, currentSize, nextCoordinates, nextSize,
    stepWitness, hcurrentRows, hnextRows, hstepRows⟩

theorem syntaxStateListAdjacentStepRows_of_termLocalTrace
    {tokenTable width tokenCount stateBoundary fuel binderArity : Nat}
    {tokens : List Nat} {states : List CompactUnifiedParserState}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hvalid : CompactParserLocalTraceValid compactSyntaxParserStep fuel
      (compactTermParserInitialState binderArity tokens) states) :
    CompactUnifiedParserSyntaxStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states := by
  exact syntaxStateListAdjacentStepRows_of_localTrace hrows hvalid
    (compactTermParserInitialState_task_fields_well_formed binderArity tokens)

theorem syntaxStateListAdjacentStepRows_of_formulaLocalTrace
    {tokenTable width tokenCount stateBoundary fuel binderArity : Nat}
    {tokens : List Nat} {states : List CompactUnifiedParserState}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hvalid : CompactParserLocalTraceValid compactSyntaxParserStep fuel
      (compactFormulaParserInitialState binderArity tokens) states) :
    CompactUnifiedParserSyntaxStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states := by
  exact syntaxStateListAdjacentStepRows_of_localTrace hrows hvalid
    (compactFormulaParserInitialState_task_fields_well_formed
      binderArity tokens)

#print axioms CompactParserLocalTraceValid.getI_eq_stateAt
#print axioms CompactParserLocalTraceValid.getI_step
#print axioms compactSyntaxParserStateAt_task_fields_well_formed
#print axioms CompactParserLocalTraceValid.getI_task_fields_well_formed
#print axioms syntaxStateListAdjacentStepRows_of_localTrace
#print axioms syntaxStateListAdjacentStepRows_of_termLocalTrace
#print axioms syntaxStateListAdjacentStepRows_of_formulaLocalTrace

end FoundationCompactNumericListedDirectParserSyntaxTraceInstallation
