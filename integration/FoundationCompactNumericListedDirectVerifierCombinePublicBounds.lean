import integration.FoundationCompactNumericListedDirectVerifierCombineAuxiliaryBounds
import integration.FoundationCompactNumericListedDirectVerifierCombineCanonicalCompleteness
import integration.FoundationCompactNumericListedDirectVerifierStepCoordinateBounds

/-!
# Public bounds for executable combine choices

The canonical combine completeness theorem chooses an auxiliary token suffix
inside an existential.  This file exposes the same choice as a deterministic
function of the actual task and child-result stack, then bounds its full
additive weight from the public input weight.  No suffix-size witness is an
input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombinePublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectFormulaTransformValueBounds
open FoundationCompactNumericListedDirectVerifierCombineCanonicalGraph
open FoundationCompactNumericListedDirectVerifierCombineAuxiliaryBounds
open FoundationCompactNumericListedDirectVerifierCombineCanonicalCompleteness
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectFormulaShiftExactListRowsCompleteness
open FoundationCompactNumericListedDirectAllShiftCombineRuleRowsCompleteness
open FoundationCompactNumericListedDirectVerifierCombineAllShiftStateGraphCompleteness
open FoundationCompactNumericListedDirectExsCutCombineRuleRowsCompleteness
open FoundationCompactNumericListedDirectVerifierCombineExsCutStateGraphCompleteness
open FoundationCompactNumericListedDirectVerifierCombineRuleWitnessBounds
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula

/-- The exact auxiliary suffix used by each executable nontrivial combine
branch.  Malformed stacks and simple branches use the empty suffix. -/
def compactNumericVerifierPublicCombineAuxiliaryTokens
    (task : CompactNumericVerifierTask)
    (source : List CompactNumericChildResult) : List Nat :=
  if task.1 = 5 then
    match source with
    | [] => []
    | _ :: _ =>
        compactNumericAllCombineAuxiliaryTokens task.2.1 task.2.2.1
  else if task.1 = 6 then
    match source with
    | [] => []
    | _ :: _ =>
        compactNumericExsCombineAuxiliaryTokens
          task.2.2.1 task.2.2.2.2.1
  else if task.1 = 8 then
    match source with
    | [] => []
    | (premise, _) :: _ =>
        compactNumericShiftCombineAuxiliaryTokens premise
  else if task.1 = 9 then
    match source with
    | _ :: _ :: _ =>
        compactNumericCutCombineAuxiliaryTokens task.2.2.1
    | _ => []
  else
    []

theorem compactNumericVerifierTask_gamma_weight_le
    (task : CompactNumericVerifierTask) :
    compactAdditiveValueWeight task.2.1 ≤
      compactAdditiveValueWeight task := by
  exact (compactAdditiveValueWeight_fst_le task.2).trans
    (compactAdditiveValueWeight_snd_le task)

theorem compactNumericVerifierTask_formula_weight_le
    (task : CompactNumericVerifierTask) :
    compactAdditiveValueWeight task.2.2.1 ≤
      compactAdditiveValueWeight task := by
  exact (compactAdditiveValueWeight_fst_le task.2.2).trans
    ((compactAdditiveValueWeight_snd_le task.2).trans
      (compactAdditiveValueWeight_snd_le task))

theorem compactNumericVerifierTask_witness_weight_le
    (task : CompactNumericVerifierTask) :
    compactAdditiveValueWeight task.2.2.2.2.1 ≤
      compactAdditiveValueWeight task := by
  exact (compactAdditiveValueWeight_fst_le task.2.2.2.2).trans
    ((compactAdditiveValueWeight_snd_le task.2.2.2).trans
      ((compactAdditiveValueWeight_snd_le task.2.2).trans
        ((compactAdditiveValueWeight_snd_le task.2).trans
          (compactAdditiveValueWeight_snd_le task))))

theorem compactNumericChildResult_formula_weight_le_source
    (premise : List (List Nat)) (valid : Bool)
    (tail : List CompactNumericChildResult) :
    compactAdditiveValueWeight premise ≤
      compactAdditiveValueWeight ((premise, valid) :: tail) := by
  exact (compactAdditiveValueWeight_fst_le (premise, valid)).trans
    (compactAdditiveValueWeight_mem_le (by simp))

theorem compactNumericVerifierCombineInput_weight_le_currentState
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult) :
    compactAdditiveValueWeight (task, source) ≤
      compactAdditiveValueWeight
        ((((proofTokens, certificateTokens), (task :: tasks, source)), none) :
          CompactNumericVerifierState) := by
  have htask :
      compactAdditiveValueWeight task ≤
        compactAdditiveValueWeight (task :: tasks) :=
    compactAdditiveValueWeight_mem_le (by simp)
  have hpair :
      compactAdditiveValueWeight (task, source) ≤
        compactAdditiveValueWeight (task :: tasks, source) := by
    calc
      compactAdditiveValueWeight (task, source) =
          compactAdditiveValueWeight task +
            compactAdditiveValueWeight source :=
        compactAdditiveValueWeight_prod (task, source)
      _ ≤ compactAdditiveValueWeight (task :: tasks) +
          compactAdditiveValueWeight source :=
        Nat.add_le_add_right htask _
      _ = compactAdditiveValueWeight (task :: tasks, source) :=
        (compactAdditiveValueWeight_prod (task :: tasks, source)).symm
  exact hpair.trans
    ((compactAdditiveValueWeight_snd_le
      ((proofTokens, certificateTokens), (task :: tasks, source))).trans
      (compactAdditiveValueWeight_fst_le
        ((((proofTokens, certificateTokens), (task :: tasks, source)), none) :
          CompactNumericVerifierState)))

theorem compactNumericVerifierPublicCombineAuxiliaryTokens_weight_le
    (task : CompactNumericVerifierTask)
    (source : List CompactNumericChildResult) :
    compactAdditiveTokenWeight
        (compactNumericVerifierPublicCombineAuxiliaryTokens task source) ≤
      compactNumericVerifierCombineAuxiliaryTokenWeightBound
        (compactAdditiveValueWeight (task, source)) := by
  let inputWeight := compactAdditiveValueWeight (task, source)
  have htask :
      compactAdditiveValueWeight task ≤ inputWeight := by
    exact compactAdditiveValueWeight_fst_le (task, source)
  have hGamma :
      compactAdditiveValueWeight task.2.1 ≤ inputWeight :=
    (compactNumericVerifierTask_gamma_weight_le task).trans htask
  have hformula :
      compactAdditiveValueWeight task.2.2.1 ≤ inputWeight :=
    (compactNumericVerifierTask_formula_weight_le task).trans htask
  have hwitness :
      compactAdditiveValueWeight task.2.2.2.2.1 ≤ inputWeight :=
    (compactNumericVerifierTask_witness_weight_le task).trans htask
  have hpositive : 1 ≤ inputWeight := by
    exact (compactAdditiveValueWeight_list_pos source).trans
      (compactAdditiveValueWeight_snd_le (task, source))
  by_cases htag5 : task.1 = 5
  · cases source with
    | nil =>
        simp [compactNumericVerifierPublicCombineAuxiliaryTokens, htag5]
    | cons child tail =>
        simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, htag5,
          inputWeight] using
          compactNumericAllCombineAuxiliaryTokens_weight_le_public
            hGamma hformula hpositive
  by_cases htag6 : task.1 = 6
  · cases source with
    | nil =>
        simp [compactNumericVerifierPublicCombineAuxiliaryTokens, htag6]
    | cons child tail =>
        simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, htag6,
          inputWeight] using
          compactNumericExsCombineAuxiliaryTokens_weight_le_public
            hformula hwitness
  by_cases htag8 : task.1 = 8
  · cases source with
    | nil =>
        simp [compactNumericVerifierPublicCombineAuxiliaryTokens, htag8]
    | cons child tail =>
        rcases child with ⟨premise, valid⟩
        have hpremise :
            compactAdditiveValueWeight premise ≤ inputWeight := by
          exact
            (compactNumericChildResult_formula_weight_le_source
              premise valid tail).trans
              (compactAdditiveValueWeight_snd_le (task,
                ((premise, valid) :: tail)))
        simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, htag8,
          inputWeight] using
          compactNumericShiftCombineAuxiliaryTokens_weight_le_public hpremise
  by_cases htag9 : task.1 = 9
  · cases source with
    | nil =>
        simp [compactNumericVerifierPublicCombineAuxiliaryTokens, htag9]
    | cons right rest =>
        cases rest with
        | nil =>
            simp [compactNumericVerifierPublicCombineAuxiliaryTokens, htag9]
        | cons left tail =>
            simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, htag9,
              inputWeight] using
              compactNumericCutCombineAuxiliaryTokens_weight_le_public
                hformula hpositive
  simp [compactNumericVerifierPublicCombineAuxiliaryTokens, htag5, htag6,
    htag8, htag9]

theorem compactNumericVerifierPublicCombineAuxiliaryTokens_weight_le_currentState
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult) :
    compactAdditiveTokenWeight
        (compactNumericVerifierPublicCombineAuxiliaryTokens task source) ≤
      compactNumericVerifierCombineAuxiliaryTokenWeightBound
        (compactAdditiveValueWeight
          ((((proofTokens, certificateTokens), (task :: tasks, source)), none) :
            CompactNumericVerifierState)) := by
  exact
    (compactNumericVerifierPublicCombineAuxiliaryTokens_weight_le
      task source).trans
      (compactNumericVerifierCombineAuxiliaryTokenWeightBound_mono
        (compactNumericVerifierCombineInput_weight_le_currentState
          proofTokens certificateTokens task tasks source))

/-- Public total-token budget for one canonical combine row. -/
def compactNumericVerifierPublicCombineTokenWeightBound
    (currentWeight nextWeight : Nat) : Nat :=
  currentWeight + nextWeight +
    compactNumericVerifierCombineAuxiliaryTokenWeightBound currentWeight

theorem compactNumericVerifierPublicCombineTokenWeightBound_mono
    {currentLeft currentRight nextLeft nextRight : Nat}
    (hcurrent : currentLeft ≤ currentRight)
    (hnext : nextLeft ≤ nextRight) :
    compactNumericVerifierPublicCombineTokenWeightBound
        currentLeft nextLeft ≤
      compactNumericVerifierPublicCombineTokenWeightBound
        currentRight nextRight := by
  have hauxiliary :=
    compactNumericVerifierCombineAuxiliaryTokenWeightBound_mono hcurrent
  unfold compactNumericVerifierPublicCombineTokenWeightBound
  omega

theorem compactAdditiveTokenList_length_le_weight (tokens : List Nat) :
    tokens.length ≤ compactAdditiveTokenWeight tokens := by
  induction tokens with
  | nil => simp
  | cons token tokens ih =>
      simp only [List.length_cons, compactAdditiveTokenWeight_cons]
      omega

theorem compactNumericVerifierPublicCombineTokens_weight_le
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool) :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (task :: tasks, source)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let backTokens :=
      compactNumericVerifierPublicCombineAuxiliaryTokens task source
    let tokens := currentTokens ++ nextTokens ++ backTokens
    compactAdditiveTokenWeight tokens ≤
      compactNumericVerifierPublicCombineTokenWeightBound
        (compactAdditiveValueWeight currentState)
        (compactAdditiveValueWeight nextState) := by
  dsimp only
  rw [compactAdditiveTokenWeight_append,
    compactAdditiveTokenWeight_append]
  change
    compactAdditiveValueWeight
        ((((proofTokens, certificateTokens), (task :: tasks, source)), none) :
          CompactNumericVerifierState) +
      compactAdditiveValueWeight
        ((((proofTokens, certificateTokens), (tasks, target)), nextStatus) :
          CompactNumericVerifierState) +
      compactAdditiveTokenWeight
        (compactNumericVerifierPublicCombineAuxiliaryTokens task source) ≤ _
  have hauxiliary :=
    compactNumericVerifierPublicCombineAuxiliaryTokens_weight_le_currentState
      proofTokens certificateTokens task tasks source
  unfold compactNumericVerifierPublicCombineTokenWeightBound
  omega

theorem compactNumericVerifierPublicCombineTokens_length_le
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool) :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (task :: tasks, source)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let backTokens :=
      compactNumericVerifierPublicCombineAuxiliaryTokens task source
    let tokens := currentTokens ++ nextTokens ++ backTokens
    tokens.length ≤
      compactNumericVerifierPublicCombineTokenWeightBound
        (compactAdditiveValueWeight currentState)
        (compactAdditiveValueWeight nextState) := by
  dsimp only
  exact
    (compactAdditiveTokenList_length_le_weight _).trans
      (compactNumericVerifierPublicCombineTokens_weight_le
        proofTokens certificateTokens task tasks source target nextStatus)

theorem compactNumericVerifierPublicCombineWidth_le
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool) :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (task :: tasks, source)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let backTokens :=
      compactNumericVerifierPublicCombineAuxiliaryTokens task source
    let tokens := currentTokens ++ nextTokens ++ backTokens
    (compactBinaryNatPayloadBits tokens).length ≤
      2 * compactNumericVerifierPublicCombineTokenWeightBound
        (compactAdditiveValueWeight currentState)
        (compactAdditiveValueWeight nextState) := by
  dsimp only
  have hweight :=
    compactNumericVerifierPublicCombineTokens_weight_le
      proofTokens certificateTokens task tasks source target nextStatus
  have hwidth :
      (compactBinaryNatPayloadBits
        (compactAdditiveEncode
            ((((proofTokens, certificateTokens),
              (task :: tasks, source)), none) :
              CompactNumericVerifierState) ++
          compactAdditiveEncode
            ((((proofTokens, certificateTokens),
              (tasks, target)), nextStatus) :
              CompactNumericVerifierState) ++
          compactNumericVerifierPublicCombineAuxiliaryTokens
            task source)).length =
        2 * compactAdditiveTokenWeight
          (compactAdditiveEncode
              ((((proofTokens, certificateTokens),
                (task :: tasks, source)), none) :
                CompactNumericVerifierState) ++
            compactAdditiveEncode
              ((((proofTokens, certificateTokens),
                (tasks, target)), nextStatus) :
                CompactNumericVerifierState) ++
            compactNumericVerifierPublicCombineAuxiliaryTokens
              task source) := by
    change compactAdditiveTokenBitLength _ =
      2 * compactAdditiveTokenWeight _
    exact compactAdditiveTokenBitLength_eq_two_mul_weight _
  rw [hwidth]
  exact Nat.mul_le_mul_left 2 hweight

/-- One exact-row envelope containing all three canonical combine-rule budget
families.  The selected branch contributes only one summand. -/
def compactNumericVerifierCanonicalCombineRuleCoordinateEnvelope
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (backTokens : List Nat) : Nat :=
  compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound
      proofTokens certificateTokens task tasks source target
        nextStatus backTokens +
    compactNumericVerifierCanonicalAllShiftRuleCoordinateSizeBound
      proofTokens certificateTokens task tasks source target
        nextStatus backTokens +
    compactNumericVerifierCanonicalExsCutRuleCoordinateSizeBound
      proofTokens certificateTokens task tasks source target
        nextStatus backTokens

theorem compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound_le_envelope
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (backTokens : List Nat) :
    compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound
        proofTokens certificateTokens task tasks source target
          nextStatus backTokens ≤
      compactNumericVerifierCanonicalCombineRuleCoordinateEnvelope
        proofTokens certificateTokens task tasks source target
          nextStatus backTokens := by
  unfold compactNumericVerifierCanonicalCombineRuleCoordinateEnvelope
  omega

theorem compactNumericVerifierCanonicalAllShiftRuleCoordinateSizeBound_le_envelope
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (backTokens : List Nat) :
    compactNumericVerifierCanonicalAllShiftRuleCoordinateSizeBound
        proofTokens certificateTokens task tasks source target
          nextStatus backTokens ≤
      compactNumericVerifierCanonicalCombineRuleCoordinateEnvelope
        proofTokens certificateTokens task tasks source target
          nextStatus backTokens := by
  unfold compactNumericVerifierCanonicalCombineRuleCoordinateEnvelope
  omega

theorem compactNumericVerifierCanonicalExsCutRuleCoordinateSizeBound_le_envelope
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (backTokens : List Nat) :
    compactNumericVerifierCanonicalExsCutRuleCoordinateSizeBound
        proofTokens certificateTokens task tasks source target
          nextStatus backTokens ≤
      compactNumericVerifierCanonicalCombineRuleCoordinateEnvelope
        proofTokens certificateTokens task tasks source target
          nextStatus backTokens := by
  unfold compactNumericVerifierCanonicalCombineRuleCoordinateEnvelope
  omega

theorem compactBinaryNatStreamStepWitnessPublicWidth_mono
    {left right : Nat} (h : left ≤ right) :
    compactBinaryNatStreamStepWitnessPublicWidth left ≤
      compactBinaryNatStreamStepWitnessPublicWidth right := by
  have hsucc : left + 1 ≤ right + 1 := Nat.add_le_add_right h 1
  have harea := Nat.mul_le_mul hsucc h
  unfold compactBinaryNatStreamStepWitnessPublicWidth
  omega

theorem compactFormulaTransformAdjacentStepPublicWidth_mono
    {widthLeft widthRight tokenLeft tokenRight : Nat}
    (hwidth : widthLeft ≤ widthRight)
    (htoken : tokenLeft ≤ tokenRight) :
    compactFormulaTransformAdjacentStepPublicWidth widthLeft tokenLeft ≤
      compactFormulaTransformAdjacentStepPublicWidth widthRight tokenRight := by
  have hstream :=
    compactBinaryNatStreamStepWitnessPublicWidth_mono htoken
  unfold compactFormulaTransformAdjacentStepPublicWidth
  omega

private theorem compactQuadraticParserFuelBound_mono
    {left right : Nat} (h : left ≤ right) :
    16 * (left + 1) * (left + 1) + 8 ≤
      16 * (right + 1) * (right + 1) + 8 := by
  have hsucc : left + 1 ≤ right + 1 := Nat.add_le_add_right h 1
  have hscaled := Nat.mul_le_mul_left 16 hsucc
  have hsquare := Nat.mul_le_mul hscaled hsucc
  omega

theorem compactFormulaTransformCanonicalTableWidthBound_mono
    {widthLeft widthRight tokenLeft tokenRight fuelLeft fuelRight : Nat}
    (hwidth : widthLeft ≤ widthRight)
    (htoken : tokenLeft ≤ tokenRight)
    (hfuel : fuelLeft ≤ fuelRight) :
    compactFormulaTransformCanonicalTableWidthBound
        widthLeft tokenLeft fuelLeft ≤
      compactFormulaTransformCanonicalTableWidthBound
        widthRight tokenRight fuelRight := by
  have hadjacent :=
    compactFormulaTransformAdjacentStepPublicWidth_mono hwidth htoken
  have hcolumns :=
    Nat.mul_le_mul_right
      compactFormulaTransformAdjacentStepWitnessColumnCount hfuel
  have hrows := Nat.mul_le_mul hcolumns hadjacent
  have hsucc : tokenLeft + 1 ≤ tokenRight + 1 :=
    Nat.add_le_add_right htoken 1
  have harea := Nat.mul_le_mul hsucc htoken
  have htail := Nat.mul_le_mul_left 31 hadjacent
  unfold compactFormulaTransformCanonicalTableWidthBound
  omega

theorem compactFormulaShiftExactListPublicFuelBound_mono
    {left right : Nat} (h : left ≤ right) :
    compactFormulaShiftExactListPublicFuelBound left ≤
      compactFormulaShiftExactListPublicFuelBound right := by
  unfold compactFormulaShiftExactListPublicFuelBound
  exact compactQuadraticParserFuelBound_mono h

theorem compactFormulaShiftExactListCoordinateSizeBound_mono
    {widthLeft widthRight tokenLeft tokenRight : Nat}
    (hwidth : widthLeft ≤ widthRight)
    (htoken : tokenLeft ≤ tokenRight) :
    compactFormulaShiftExactListCoordinateSizeBound widthLeft tokenLeft ≤
      compactFormulaShiftExactListCoordinateSizeBound widthRight tokenRight := by
  have hfuel :=
    compactFormulaShiftExactListPublicFuelBound_mono htoken
  have hadjacent :=
    compactFormulaTransformAdjacentStepPublicWidth_mono hwidth htoken
  have hsucc : tokenLeft + 1 ≤ tokenRight + 1 :=
    Nat.add_le_add_right htoken 1
  have harea := Nat.mul_le_mul hsucc htoken
  have hfuelSucc :
      compactFormulaShiftExactListPublicFuelBound tokenLeft + 2 ≤
        compactFormulaShiftExactListPublicFuelBound tokenRight + 2 :=
    Nat.add_le_add_right hfuel 2
  have hfuelRows := Nat.mul_le_mul hfuelSucc htoken
  have htable :=
    compactFormulaTransformCanonicalTableWidthBound_mono
      hwidth htoken hfuel
  simp only [compactFormulaShiftExactListCoordinateSizeBound]
  omega

theorem compactNumericAllShiftCombineRuleCoordinateSizeBound_mono
    {widthLeft widthRight tokenLeft tokenRight : Nat}
    (hwidth : widthLeft ≤ widthRight)
    (htoken : tokenLeft ≤ tokenRight) :
    compactNumericAllShiftCombineRuleCoordinateSizeBound widthLeft tokenLeft ≤
      compactNumericAllShiftCombineRuleCoordinateSizeBound
        widthRight tokenRight := by
  have hcritical :=
    compactFormulaShiftExactListCoordinateSizeBound_mono hwidth htoken
  unfold compactNumericAllShiftCombineRuleCoordinateSizeBound
  unfold compactNumericAllShiftCriticalCoordinateSizeBound
  omega

theorem compactNumericExsCutFormulaTransformPublicFuelBound_mono
    {left right : Nat} (h : left ≤ right) :
    compactNumericExsCutFormulaTransformPublicFuelBound left ≤
      compactNumericExsCutFormulaTransformPublicFuelBound right := by
  unfold compactNumericExsCutFormulaTransformPublicFuelBound
  exact compactQuadraticParserFuelBound_mono h

theorem compactNumericExsCutCombineRuleCoordinateSizeBound_mono
    {widthLeft widthRight tokenLeft tokenRight : Nat}
    (hwidth : widthLeft ≤ widthRight)
    (htoken : tokenLeft ≤ tokenRight) :
    compactNumericExsCutCombineRuleCoordinateSizeBound widthLeft tokenLeft ≤
      compactNumericExsCutCombineRuleCoordinateSizeBound
        widthRight tokenRight := by
  have hfuel :=
    compactNumericExsCutFormulaTransformPublicFuelBound_mono htoken
  have hadjacent :=
    compactFormulaTransformAdjacentStepPublicWidth_mono hwidth htoken
  have hsucc : tokenLeft + 1 ≤ tokenRight + 1 :=
    Nat.add_le_add_right htoken 1
  have harea := Nat.mul_le_mul hsucc htoken
  have hfuelSucc :
      compactNumericExsCutFormulaTransformPublicFuelBound tokenLeft + 2 ≤
        compactNumericExsCutFormulaTransformPublicFuelBound tokenRight + 2 :=
    Nat.add_le_add_right hfuel 2
  have hfuelRows := Nat.mul_le_mul hfuelSucc htoken
  have htable :=
    compactFormulaTransformCanonicalTableWidthBound_mono
      hwidth htoken hfuel
  simp only [compactNumericExsCutCombineRuleCoordinateSizeBound,
    compactNumericExsCutCriticalCoordinateSizeBound]
  omega

theorem compactNumericVerifierSimpleCombineRuleCoordinateSizeBound_mono
    {left right : Nat} (h : left ≤ right) :
    compactNumericVerifierSimpleCombineRuleCoordinateSizeBound left ≤
      compactNumericVerifierSimpleCombineRuleCoordinateSizeBound right := by
  have hsucc : left + 1 ≤ right + 1 := Nat.add_le_add_right h 1
  have harea := Nat.mul_le_mul hsucc h
  unfold compactNumericVerifierSimpleCombineRuleCoordinateSizeBound
  omega

/-- Fixed public rule-coordinate envelope once the total token weight budget is
known. -/
def compactNumericVerifierPublicCombineRuleCoordinateBound
    (tokenWeightBound : Nat) : Nat :=
  compactNumericVerifierSimpleCombineRuleCoordinateSizeBound
      tokenWeightBound +
    compactNumericAllShiftCombineRuleCoordinateSizeBound
      (2 * tokenWeightBound) tokenWeightBound +
    compactNumericExsCutCombineRuleCoordinateSizeBound
      (2 * tokenWeightBound) tokenWeightBound

theorem compactNumericVerifierCanonicalCombineRuleCoordinateEnvelope_le_public
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool) :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (task :: tasks, source)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
    let backTokens :=
      compactNumericVerifierPublicCombineAuxiliaryTokens task source
    let tokenWeightBound :=
      compactNumericVerifierPublicCombineTokenWeightBound
        (compactAdditiveValueWeight currentState)
        (compactAdditiveValueWeight nextState)
    compactNumericVerifierCanonicalCombineRuleCoordinateEnvelope
        proofTokens certificateTokens task tasks source target nextStatus
          backTokens ≤
      compactNumericVerifierPublicCombineRuleCoordinateBound
        tokenWeightBound := by
  dsimp only
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let backTokens :=
    compactNumericVerifierPublicCombineAuxiliaryTokens task source
  let tokens := currentTokens ++ nextTokens ++ backTokens
  let tokenWeightBound :=
    compactNumericVerifierPublicCombineTokenWeightBound
      (compactAdditiveValueWeight currentState)
      (compactAdditiveValueWeight nextState)
  have htokenCount : tokens.length ≤ tokenWeightBound := by
    simpa only [tokens, currentTokens, nextTokens, backTokens,
      currentState, nextState, tokenWeightBound] using
      compactNumericVerifierPublicCombineTokens_length_le
        proofTokens certificateTokens task tasks source target nextStatus
  have hwidth :
      (compactBinaryNatPayloadBits tokens).length ≤
        2 * tokenWeightBound := by
    simpa only [tokens, currentTokens, nextTokens, backTokens,
      currentState, nextState, tokenWeightBound] using
      compactNumericVerifierPublicCombineWidth_le
        proofTokens certificateTokens task tasks source target nextStatus
  have hsimple :=
    compactNumericVerifierSimpleCombineRuleCoordinateSizeBound_mono
      htokenCount
  have hallShift :=
    compactNumericAllShiftCombineRuleCoordinateSizeBound_mono
      hwidth htokenCount
  have hexsCut :=
    compactNumericExsCutCombineRuleCoordinateSizeBound_mono
      hwidth htokenCount
  dsimp only [
    compactNumericVerifierCanonicalCombineRuleCoordinateEnvelope,
    compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound,
    compactNumericVerifierCanonicalAllShiftRuleCoordinateSizeBound,
    compactNumericVerifierCanonicalExsCutRuleCoordinateSizeBound,
    compactNumericVerifierPublicCombineRuleCoordinateBound,
    currentState, nextState, currentTokens, nextTokens, backTokens,
    tokens, tokenWeightBound] at hsimple hallShift hexsCut ⊢
  exact Nat.add_le_add (Nat.add_le_add hsimple hallShift) hexsCut

theorem compactNumericVerifierStateCoreCoordinateSizeBound_mono
    {widthLeft widthRight tokenLeft tokenRight : Nat}
    (hwidth : widthLeft ≤ widthRight)
    (htoken : tokenLeft ≤ tokenRight) :
    compactNumericVerifierStateCoreCoordinateSizeBound
        widthLeft tokenLeft ≤
      compactNumericVerifierStateCoreCoordinateSizeBound
        widthRight tokenRight := by
  have hrectangle := Nat.mul_le_mul htoken hwidth
  have hsucc : tokenLeft + 1 ≤ tokenRight + 1 :=
    Nat.add_le_add_right htoken 1
  have harea := Nat.mul_le_mul hsucc htoken
  unfold compactNumericVerifierStateCoreCoordinateSizeBound
  unfold compactNumericVerifierTaskRowTableWidth
  unfold compactNumericChildResultRowTableWidth
  omega

theorem compactNumericVerifierCanonicalCombineStepCoordinateSizeBound_mono
    {widthLeft widthRight tokenLeft tokenRight ruleLeft ruleRight : Nat}
    (hwidth : widthLeft ≤ widthRight)
    (htoken : tokenLeft ≤ tokenRight)
    (hrule : ruleLeft ≤ ruleRight) :
    compactNumericVerifierCanonicalCombineStepCoordinateSizeBound
        widthLeft tokenLeft ruleLeft ≤
      compactNumericVerifierCanonicalCombineStepCoordinateSizeBound
        widthRight tokenRight ruleRight := by
  have hstate :=
    compactNumericVerifierStateCoreCoordinateSizeBound_mono hwidth htoken
  have hsum := Nat.add_le_add hstate hrule
  have hscaled := Nat.mul_le_mul_left 384 hsum
  simp only [compactNumericVerifierCanonicalCombineStepCoordinateSizeBound]
  omega

/-- Final fixed coordinate budget for the real 429-column combine row. -/
def compactNumericVerifierPublicCombineStepCoordinateSizeBound
    (tokenWeightBound : Nat) : Nat :=
  compactNumericVerifierCanonicalCombineStepCoordinateSizeBound
    (2 * tokenWeightBound) tokenWeightBound
    (compactNumericVerifierPublicCombineRuleCoordinateBound tokenWeightBound)

theorem compactNumericVerifierCanonicalCombineStepCoordinateSizeBound_le_public
    {width tokenCount ruleCoordinateBound tokenWeightBound : Nat}
    (hwidth : width ≤ 2 * tokenWeightBound)
    (htokenCount : tokenCount ≤ tokenWeightBound)
    (hrule : ruleCoordinateBound ≤
      compactNumericVerifierPublicCombineRuleCoordinateBound
        tokenWeightBound) :
    compactNumericVerifierCanonicalCombineStepCoordinateSizeBound
        width tokenCount ruleCoordinateBound ≤
      compactNumericVerifierPublicCombineStepCoordinateSizeBound
        tokenWeightBound := by
  exact compactNumericVerifierCanonicalCombineStepCoordinateSizeBound_mono
    hwidth htokenCount hrule

/-- Canonical combine completeness with the auxiliary suffix fixed by the
public executable task and source stack rather than hidden in an existential. -/
def CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult) : Prop :=
  ∃ target nextStatus ruleCoordinateBound,
    compactNumericCombineState task
        ((proofTokens, certificateTokens), (tasks, source)) =
      (((proofTokens, certificateTokens), (tasks, target)), nextStatus) ∧
    CompactNumericVerifierCanonicalCombineBoundedGraph
      proofTokens certificateTokens task tasks source target nextStatus
        (compactNumericVerifierPublicCombineAuxiliaryTokens task source)
        ruleCoordinateBound ∧
    ruleCoordinateBound ≤
      compactNumericVerifierCanonicalCombineRuleCoordinateEnvelope
        proofTokens certificateTokens task tasks source target nextStatus
          (compactNumericVerifierPublicCombineAuxiliaryTokens task source)

theorem
    CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.toBoundedStateGraph
    {proofTokens certificateTokens : List Nat}
    {task : CompactNumericVerifierTask}
    {tasks : List CompactNumericVerifierTask}
    {source : List CompactNumericChildResult}
    (hgraph : CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph
      proofTokens certificateTokens task tasks source) :
    CompactNumericVerifierCanonicalCombineBoundedStateGraph
      proofTokens certificateTokens task tasks source := by
  rcases hgraph with
    ⟨target, nextStatus, ruleCoordinateBound, htransition, hcanonical, _⟩
  exact ⟨target, nextStatus,
    compactNumericVerifierPublicCombineAuxiliaryTokens task source,
    ruleCoordinateBound, htransition, hcanonical⟩

theorem
    CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.of_transition_none
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult)
    (htaskNe : task.1 ≠ 10)
    (htransition : compactNumericCombineTransition task source = none)
    (hauxiliary :
      compactNumericVerifierPublicCombineAuxiliaryTokens task source = []) :
    CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph
      proofTokens certificateTokens task tasks source := by
  refine ⟨source, some false, 0, ?_, ?_, ?_⟩
  · simp [compactNumericCombineState, htransition]
  · rw [hauxiliary]
    exact
      CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_failure
        proofTokens certificateTokens task tasks source htaskNe htransition
  · omega

theorem
    CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.exists_of_public_step
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult)
    (htaskNe : task.1 ≠ 10) :
    CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph
      proofTokens certificateTokens task tasks source := by
  rcases task with
    ⟨tag, ⟨Gamma,
      ⟨firstFormula, ⟨secondFormula, ⟨witness, suffix⟩⟩⟩⟩⟩
  by_cases htag3 : tag = 3
  · subst tag
    cases source with
    | nil =>
        apply
          CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.of_transition_none
            proofTokens certificateTokens
            (3, (Gamma,
              (firstFormula, (secondFormula, (witness, suffix)))))
            tasks [] (by simp)
        · simp [compactNumericCombineTransition]
        · simp [compactNumericVerifierPublicCombineAuxiliaryTokens]
    | cons right rest =>
        rcases right with ⟨rightConclusion, rightValid⟩
        cases rest with
        | nil =>
            apply
              CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.of_transition_none
                proofTokens certificateTokens
                (3, (Gamma,
                  (firstFormula, (secondFormula, (witness, suffix)))))
                tasks [(rightConclusion, rightValid)] (by simp)
            · simp [compactNumericCombineTransition]
            · simp [compactNumericVerifierPublicCombineAuxiliaryTokens]
        | cons left tail =>
            rcases left with ⟨leftConclusion, leftValid⟩
            let target : List CompactNumericChildResult :=
              (Gamma, compactAndRuleCheck
                (Gamma, firstFormula, secondFormula,
                  (leftConclusion, leftValid),
                  rightConclusion, rightValid)) :: tail
            refine ⟨target, none,
              compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound
                proofTokens certificateTokens
                (3, (Gamma,
                  (firstFormula, (secondFormula, (witness, suffix)))))
                tasks
                ((rightConclusion, rightValid) ::
                  (leftConclusion, leftValid) :: tail)
                target none [], ?_, ?_, ?_⟩
            · simp [compactNumericCombineState,
                compactNumericCombineTransition, target]
            · simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, target]
                using
                  CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_and
                    proofTokens certificateTokens Gamma firstFormula
                    secondFormula witness suffix tasks rightConclusion
                    leftConclusion rightValid leftValid tail
            · simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, target]
                using
                  compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound_le_envelope
                    proofTokens certificateTokens
                    (3, (Gamma,
                      (firstFormula, (secondFormula, (witness, suffix)))))
                    tasks
                    ((rightConclusion, rightValid) ::
                      (leftConclusion, leftValid) :: tail)
                    target none []
  by_cases htag4 : tag = 4
  · subst tag
    cases source with
    | nil =>
        apply
          CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.of_transition_none
            proofTokens certificateTokens
            (4, (Gamma,
              (firstFormula, (secondFormula, (witness, suffix)))))
            tasks [] (by simp)
        · simp [compactNumericCombineTransition]
        · simp [compactNumericVerifierPublicCombineAuxiliaryTokens]
    | cons right tail =>
        rcases right with ⟨rightConclusion, rightValid⟩
        let target : List CompactNumericChildResult :=
          (Gamma, compactOrRuleCheck
            (Gamma, firstFormula, secondFormula,
              rightConclusion, rightValid)) :: tail
        refine ⟨target, none,
          compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound
            proofTokens certificateTokens
            (4, (Gamma,
              (firstFormula, (secondFormula, (witness, suffix)))))
            tasks ((rightConclusion, rightValid) :: tail)
            target none [], ?_, ?_, ?_⟩
        · simp [compactNumericCombineState,
            compactNumericCombineTransition, target]
        · simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, target]
            using
              CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_or
                proofTokens certificateTokens Gamma firstFormula
                secondFormula witness suffix tasks rightConclusion
                rightValid tail
        · simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, target]
            using
              compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound_le_envelope
                proofTokens certificateTokens
                (4, (Gamma,
                  (firstFormula, (secondFormula, (witness, suffix)))))
                tasks ((rightConclusion, rightValid) :: tail)
                target none []
  by_cases htag5 : tag = 5
  · subst tag
    cases source with
    | nil =>
        apply
          CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.of_transition_none
            proofTokens certificateTokens
            (5, (Gamma,
              (firstFormula, (secondFormula, (witness, suffix)))))
            tasks [] (by simp)
        · simp [compactNumericCombineTransition]
        · simp [compactNumericVerifierPublicCombineAuxiliaryTokens]
    | cons premise tail =>
        rcases premise with ⟨premise, premiseValid⟩
        let target : List CompactNumericChildResult :=
          (Gamma, compactAllRuleCheck
            (Gamma, firstFormula, premise, premiseValid)) :: tail
        refine ⟨target, none,
          compactNumericVerifierCanonicalAllShiftRuleCoordinateSizeBound
            proofTokens certificateTokens
            (5, (Gamma,
              (firstFormula, (secondFormula, (witness, suffix)))))
            tasks ((premise, premiseValid) :: tail)
            target none
            (compactNumericAllCombineAuxiliaryTokens Gamma firstFormula),
          ?_, ?_, ?_⟩
        · simp [compactNumericCombineState,
            compactNumericCombineTransition, target]
        · simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, target]
            using
              CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_all
                proofTokens certificateTokens Gamma firstFormula
                secondFormula witness suffix tasks premise premiseValid tail
        · simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, target]
            using
              compactNumericVerifierCanonicalAllShiftRuleCoordinateSizeBound_le_envelope
                proofTokens certificateTokens
                (5, (Gamma,
                  (firstFormula, (secondFormula, (witness, suffix)))))
                tasks ((premise, premiseValid) :: tail) target none
                (compactNumericAllCombineAuxiliaryTokens Gamma firstFormula)
  by_cases htag6 : tag = 6
  · subst tag
    cases source with
    | nil =>
        apply
          CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.of_transition_none
            proofTokens certificateTokens
            (6, (Gamma,
              (firstFormula, (secondFormula, (witness, suffix)))))
            tasks [] (by simp)
        · simp [compactNumericCombineTransition]
        · simp [compactNumericVerifierPublicCombineAuxiliaryTokens]
    | cons right tail =>
        rcases right with ⟨rightConclusion, rightValid⟩
        let target : List CompactNumericChildResult :=
          (Gamma, compactExsRuleCheck
            (Gamma, firstFormula, witness,
              rightConclusion, rightValid)) :: tail
        refine ⟨target, none,
          compactNumericVerifierCanonicalExsCutRuleCoordinateSizeBound
            proofTokens certificateTokens
            (6, (Gamma,
              (firstFormula, (secondFormula, (witness, suffix)))))
            tasks ((rightConclusion, rightValid) :: tail)
            target none
            (compactNumericExsCombineAuxiliaryTokens
              firstFormula witness),
          ?_, ?_, ?_⟩
        · simp [compactNumericCombineState,
            compactNumericCombineTransition, target]
        · simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, target]
            using
              CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_exs
                proofTokens certificateTokens Gamma firstFormula
                secondFormula witness suffix tasks rightConclusion
                rightValid tail
        · simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, target]
            using
              compactNumericVerifierCanonicalExsCutRuleCoordinateSizeBound_le_envelope
                proofTokens certificateTokens
                (6, (Gamma,
                  (firstFormula, (secondFormula, (witness, suffix)))))
                tasks ((rightConclusion, rightValid) :: tail) target none
                (compactNumericExsCombineAuxiliaryTokens
                  firstFormula witness)
  by_cases htag7 : tag = 7
  · subst tag
    cases source with
    | nil =>
        apply
          CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.of_transition_none
            proofTokens certificateTokens
            (7, (Gamma,
              (firstFormula, (secondFormula, (witness, suffix)))))
            tasks [] (by simp)
        · simp [compactNumericCombineTransition]
        · simp [compactNumericVerifierPublicCombineAuxiliaryTokens]
    | cons right tail =>
        rcases right with ⟨rightConclusion, rightValid⟩
        let target : List CompactNumericChildResult :=
          (Gamma, compactWkRuleCheck
            (Gamma, rightConclusion, rightValid)) :: tail
        refine ⟨target, none,
          compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound
            proofTokens certificateTokens
            (7, (Gamma,
              (firstFormula, (secondFormula, (witness, suffix)))))
            tasks ((rightConclusion, rightValid) :: tail)
            target none [], ?_, ?_, ?_⟩
        · simp [compactNumericCombineState,
            compactNumericCombineTransition, target]
        · simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, target]
            using
              CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_wk
                proofTokens certificateTokens Gamma firstFormula
                secondFormula witness suffix tasks rightConclusion
                rightValid tail
        · simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, target]
            using
              compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound_le_envelope
                proofTokens certificateTokens
                (7, (Gamma,
                  (firstFormula, (secondFormula, (witness, suffix)))))
                tasks ((rightConclusion, rightValid) :: tail)
                target none []
  by_cases htag8 : tag = 8
  · subst tag
    cases source with
    | nil =>
        apply
          CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.of_transition_none
            proofTokens certificateTokens
            (8, (Gamma,
              (firstFormula, (secondFormula, (witness, suffix)))))
            tasks [] (by simp)
        · simp [compactNumericCombineTransition]
        · simp [compactNumericVerifierPublicCombineAuxiliaryTokens]
    | cons premise tail =>
        rcases premise with ⟨premise, premiseValid⟩
        let target : List CompactNumericChildResult :=
          (Gamma, compactShiftRuleCheck
            (Gamma, premise, premiseValid)) :: tail
        refine ⟨target, none,
          compactNumericVerifierCanonicalAllShiftRuleCoordinateSizeBound
            proofTokens certificateTokens
            (8, (Gamma,
              (firstFormula, (secondFormula, (witness, suffix)))))
            tasks ((premise, premiseValid) :: tail)
            target none
            (compactNumericShiftCombineAuxiliaryTokens premise),
          ?_, ?_, ?_⟩
        · simp [compactNumericCombineState,
            compactNumericCombineTransition, target]
        · simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, target]
            using
              CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_shift
                proofTokens certificateTokens Gamma firstFormula
                secondFormula witness suffix tasks premise premiseValid tail
        · simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, target]
            using
              compactNumericVerifierCanonicalAllShiftRuleCoordinateSizeBound_le_envelope
                proofTokens certificateTokens
                (8, (Gamma,
                  (firstFormula, (secondFormula, (witness, suffix)))))
                tasks ((premise, premiseValid) :: tail) target none
                (compactNumericShiftCombineAuxiliaryTokens premise)
  by_cases htag9 : tag = 9
  · subst tag
    cases source with
    | nil =>
        apply
          CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.of_transition_none
            proofTokens certificateTokens
            (9, (Gamma,
              (firstFormula, (secondFormula, (witness, suffix)))))
            tasks [] (by simp)
        · simp [compactNumericCombineTransition]
        · simp [compactNumericVerifierPublicCombineAuxiliaryTokens]
    | cons right rest =>
        rcases right with ⟨rightConclusion, rightValid⟩
        cases rest with
        | nil =>
            apply
              CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.of_transition_none
                proofTokens certificateTokens
                (9, (Gamma,
                  (firstFormula, (secondFormula, (witness, suffix)))))
                tasks [(rightConclusion, rightValid)] (by simp)
            · simp [compactNumericCombineTransition]
            · simp [compactNumericVerifierPublicCombineAuxiliaryTokens]
        | cons left tail =>
            rcases left with ⟨leftConclusion, leftValid⟩
            let target : List CompactNumericChildResult :=
              (Gamma, compactCutRuleCheck
                (Gamma, firstFormula, (leftConclusion, leftValid),
                  rightConclusion, rightValid)) :: tail
            refine ⟨target, none,
              compactNumericVerifierCanonicalExsCutRuleCoordinateSizeBound
                proofTokens certificateTokens
                (9, (Gamma,
                  (firstFormula, (secondFormula, (witness, suffix)))))
                tasks
                ((rightConclusion, rightValid) ::
                  (leftConclusion, leftValid) :: tail)
                target none
                (compactNumericCutCombineAuxiliaryTokens firstFormula),
              ?_, ?_, ?_⟩
            · simp [compactNumericCombineState,
                compactNumericCombineTransition, target]
            · simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, target]
                using
                  CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_cut
                    proofTokens certificateTokens Gamma firstFormula
                    secondFormula witness suffix tasks rightConclusion
                    leftConclusion rightValid leftValid tail
            · simpa [compactNumericVerifierPublicCombineAuxiliaryTokens, target]
                using
                  compactNumericVerifierCanonicalExsCutRuleCoordinateSizeBound_le_envelope
                    proofTokens certificateTokens
                    (9, (Gamma,
                      (firstFormula, (secondFormula, (witness, suffix)))))
                    tasks
                    ((rightConclusion, rightValid) ::
                      (leftConclusion, leftValid) :: tail)
                    target none
                    (compactNumericCutCombineAuxiliaryTokens firstFormula)
  apply
    CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.of_transition_none
      proofTokens certificateTokens
      (tag, (Gamma,
        (firstFormula, (secondFormula, (witness, suffix)))))
      tasks source (by simpa using htaskNe)
  · simp [compactNumericCombineTransition, htag3, htag4, htag5,
      htag6, htag7, htag8, htag9]
  · simp [compactNumericVerifierPublicCombineAuxiliaryTokens,
      htag5, htag6, htag8, htag9]

/-- Every executable combine step realizes its actual 429-column formula row
under a bound depending only on the two public endpoint-state weights.  The
auxiliary suffix, exact row width, token count, and selected rule budget are
all constructed internally. -/
theorem
    exists_compactNumericVerifierPublicCombineStepFormulaWitness_with_fixed_sizeBound
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult)
    (htaskNe : task.1 ≠ 10) :
    ∃ target nextStatus,
      compactNumericCombineState task
          ((proofTokens, certificateTokens), (tasks, source)) =
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus) ∧
      let currentState : CompactNumericVerifierState :=
        (((proofTokens, certificateTokens), (task :: tasks, source)), none)
      let nextState : CompactNumericVerifierState :=
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
      let currentTokens := compactAdditiveEncode currentState
      let nextTokens := compactAdditiveEncode nextState
      let backTokens :=
        compactNumericVerifierPublicCombineAuxiliaryTokens task source
      let tokens := currentTokens ++ nextTokens ++ backTokens
      let width := (compactBinaryNatPayloadBits tokens).length
      ∃ witness : CompactNumericVerifierStepFormulaWitness
          (compactFixedWidthTableCode width tokens) width tokens.length
          0 currentTokens.length currentTokens.length
          (currentTokens.length + nextTokens.length),
        ∀ coordinate : Fin 429,
          Nat.size (witness.environment coordinate) ≤
            compactNumericVerifierPublicCombineStepCoordinateSizeBound
              (compactNumericVerifierPublicCombineTokenWeightBound
                (compactAdditiveValueWeight currentState)
                (compactAdditiveValueWeight nextState)) := by
  rcases
      CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.exists_of_public_step
        proofTokens certificateTokens task tasks source htaskNe with
    ⟨target, nextStatus, ruleCoordinateBound,
      htransition, hcanonical, hruleEnvelope⟩
  refine ⟨target, nextStatus, htransition, ?_⟩
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let backTokens :=
    compactNumericVerifierPublicCombineAuxiliaryTokens task source
  let tokens := currentTokens ++ nextTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenWeightBound :=
    compactNumericVerifierPublicCombineTokenWeightBound
      (compactAdditiveValueWeight currentState)
      (compactAdditiveValueWeight nextState)
  have htokenCount : tokens.length ≤ tokenWeightBound := by
    simpa only [tokens, currentTokens, nextTokens, backTokens,
      currentState, nextState, tokenWeightBound] using
      compactNumericVerifierPublicCombineTokens_length_le
        proofTokens certificateTokens task tasks source target nextStatus
  have hwidth : width ≤ 2 * tokenWeightBound := by
    simpa only [width, tokens, currentTokens, nextTokens, backTokens,
      currentState, nextState, tokenWeightBound] using
      compactNumericVerifierPublicCombineWidth_le
        proofTokens certificateTokens task tasks source target nextStatus
  have henvelope :
      compactNumericVerifierCanonicalCombineRuleCoordinateEnvelope
          proofTokens certificateTokens task tasks source target nextStatus
            backTokens ≤
        compactNumericVerifierPublicCombineRuleCoordinateBound
          tokenWeightBound := by
    simpa only [backTokens, currentState, nextState, tokenWeightBound] using
      compactNumericVerifierCanonicalCombineRuleCoordinateEnvelope_le_public
        proofTokens certificateTokens task tasks source target nextStatus
  have hrulePublic :
      ruleCoordinateBound ≤
        compactNumericVerifierPublicCombineRuleCoordinateBound
          tokenWeightBound := by
    exact hruleEnvelope.trans henvelope
  have hcoordinateBound :
      compactNumericVerifierCanonicalCombineStepCoordinateSizeBound
          width tokens.length ruleCoordinateBound ≤
        compactNumericVerifierPublicCombineStepCoordinateSizeBound
          tokenWeightBound :=
    compactNumericVerifierCanonicalCombineStepCoordinateSizeBound_le_public
      hwidth htokenCount hrulePublic
  have hstep :=
    exists_compactNumericVerifierBoundedCombineStepFormulaWitness_with_sizeBound
      proofTokens certificateTokens task tasks source target nextStatus
      backTokens ruleCoordinateBound hcanonical
  dsimp only at hstep
  rcases hstep with
    ⟨_taskCoordinates, _taskSizeWitness, _ruleWitness,
      witness, hwitness⟩
  refine ⟨witness, ?_⟩
  intro coordinate
  have hraw := hwitness coordinate
  simpa only [currentState, nextState, currentTokens, nextTokens,
    backTokens, tokens, width, tokenWeightBound] using
    hraw.trans hcoordinateBound

#print axioms compactNumericVerifierPublicCombineAuxiliaryTokens_weight_le
#print axioms
  compactNumericVerifierPublicCombineAuxiliaryTokens_weight_le_currentState
#print axioms
  CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.exists_of_public_step
#print axioms
  exists_compactNumericVerifierPublicCombineStepFormulaWitness_with_fixed_sizeBound

end FoundationCompactNumericListedDirectVerifierCombinePublicBounds
