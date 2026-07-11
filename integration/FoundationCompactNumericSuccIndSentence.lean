import integration.FoundationCompactNumericFormulaNegation
import integration.FoundationCompactNumericFormulaShift
import integration.FoundationCompactNumericFormulaSubstitution
import integration.FoundationCompactNumericFormulaFixitr
import integration.FoundationCompactSyntaxTransformationTrace

/-!
# Pure numeric successor-induction sentence construction

This module composes the already checked token machines for shift,
substitution, fixitr, and negation. Runtime inputs and outputs contain only
naturals and lists of naturals. Every component transform must consume the
entire supplied formula-token value before its result can enter the next
stage.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericSuccIndSentence

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericFormulaNegation
open FoundationCompactNumericFormulaShift
open FoundationCompactNumericFormulaSubstitution
open FoundationCompactNumericFormulaFixitr
open FoundationCompactSyntaxTransformationTrace
open FoundationCompactSyntaxNegationTrace

def compactExactFormulaTransformResult
    (result : Option (List Nat × List Nat)) : Option (List Nat) :=
  result.bind fun outputAndSuffix =>
    if outputAndSuffix.2 = [] then some outputAndSuffix.1 else none

theorem compactExactFormulaTransformResult_primrec :
    Primrec compactExactFormulaTransformResult := by
  have hempty : PrimrecPred (fun outputAndSuffix : List Nat × List Nat =>
      outputAndSuffix.2 = []) :=
    Primrec.eq.comp Primrec.snd (Primrec.const [])
  have hsuccess : Primrec (fun outputAndSuffix : List Nat × List Nat =>
      some outputAndSuffix.1) :=
    Primrec.option_some.comp Primrec.fst
  have hcontinue : Primrec (fun outputAndSuffix : List Nat × List Nat =>
      if outputAndSuffix.2 = [] then some outputAndSuffix.1 else none) :=
    Primrec.ite hempty hsuccess (Primrec.const none)
  exact
    (Primrec.option_bind Primrec.id
      (hcontinue.comp₂ Primrec₂.right)).of_eq fun result => by
        cases result with
        | none => rfl
        | some outputAndSuffix =>
            simp [compactExactFormulaTransformResult]

def compactFormulaShiftExact
    (binderArity : Nat) (tokens : List Nat) : Option (List Nat) :=
  compactExactFormulaTransformResult
    (compactFormulaShiftTokenTransform binderArity tokens)

theorem compactFormulaShiftExact_primrec :
    Primrec₂ compactFormulaShiftExact := by
  exact compactExactFormulaTransformResult_primrec.comp₂
    compactFormulaShiftTokenTransform_primrec

def compactFormulaSubstitutionExact
    (binderArity : Nat) (witnessAndTokens : List Nat × List Nat) :
    Option (List Nat) :=
  compactExactFormulaTransformResult
    (compactFormulaSubstitutionTokenTransform binderArity witnessAndTokens)

theorem compactFormulaSubstitutionExact_primrec :
    Primrec₂ compactFormulaSubstitutionExact := by
  exact compactExactFormulaTransformResult_primrec.comp₂
    compactFormulaSubstitutionTokenTransform_primrec

def compactFormulaFixitrExact
    (baseArity : Nat) (captureAndTokens : Nat × List Nat) :
    Option (List Nat) :=
  compactExactFormulaTransformResult
    (compactFormulaFixitrTokenTransform baseArity captureAndTokens)

theorem compactFormulaFixitrExact_primrec :
    Primrec₂ compactFormulaFixitrExact := by
  exact compactExactFormulaTransformResult_primrec.comp₂
    compactFormulaFixitrTokenTransform_primrec

def compactFormulaNegationExact
    (binderArity : Nat) (tokens : List Nat) : Option (List Nat) :=
  compactExactFormulaTransformResult
    (compactFormulaNegationTokenTransform binderArity tokens)

theorem compactFormulaNegationExact_primrec :
    Primrec₂ compactFormulaNegationExact := by
  exact compactExactFormulaTransformResult_primrec.comp₂
    compactFormulaNegationTokenTransform_primrec

@[simp] theorem compactFormulaShiftExact_canonical
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) :
    compactFormulaShiftExact binderArity
        (compactArithmeticFormulaTokens formula) =
      some (compactArithmeticFormulaTokens (Rewriting.shift formula)) := by
  unfold compactFormulaShiftExact
  rw [show compactFormulaShiftTokenTransform binderArity
      (compactArithmeticFormulaTokens formula) =
        some (compactArithmeticFormulaTokens (Rewriting.shift formula), []) by
    simpa using compactFormulaShiftTokenTransform_canonical_append formula []]
  rfl

@[simp] theorem compactFormulaSubstitutionExact_canonical
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactFormulaSubstitutionExact 1
        (compactArithmeticTermTokens witness,
          compactArithmeticFormulaTokens formula) =
      some (compactArithmeticFormulaTokens
        (Rewriting.app (Rew.subst ![witness]) formula)) := by
  unfold compactFormulaSubstitutionExact
  rw [show compactFormulaSubstitutionTokenTransform 1
      (compactArithmeticTermTokens witness,
        compactArithmeticFormulaTokens formula) =
        some (compactArithmeticFormulaTokens
          (Rewriting.app (Rew.subst ![witness]) formula), []) by
    simpa using
      compactFormulaSubstitutionTokenTransform_canonical_append
        witness formula []]
  rfl

@[simp] theorem compactFormulaFixitrExact_canonical
    (baseArity captureCount : Nat)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat baseArity) :
    compactFormulaFixitrExact baseArity
        (captureCount, compactArithmeticFormulaTokens formula) =
      some (compactArithmeticFormulaTokens
        (Rewriting.app
          (Rew.fixitr (L := ℒₒᵣ) baseArity captureCount) formula)) := by
  unfold compactFormulaFixitrExact
  rw [show compactFormulaFixitrTokenTransform baseArity
      (captureCount, compactArithmeticFormulaTokens formula) =
        some (compactArithmeticFormulaTokens
          (Rewriting.app
            (Rew.fixitr (L := ℒₒᵣ) baseArity captureCount) formula), []) by
    simpa using compactFormulaFixitrTokenTransform_canonical_append
      baseArity captureCount formula []]
  rfl

@[simp] theorem compactFormulaNegationExact_canonical
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) :
    compactFormulaNegationExact binderArity
        (compactArithmeticFormulaTokens formula) =
      some (compactArithmeticFormulaTokens (∼formula)) := by
  unfold compactFormulaNegationExact
  rw [show compactFormulaNegationTokenTransform binderArity
      (compactArithmeticFormulaTokens formula) =
        some (compactArithmeticFormulaTokens (∼formula), []) by
    simpa using compactFormulaNegationTokenTransform_canonical_append formula []]
  rfl

def compactSuccIndZeroWitnessTokens : List Nat := [2, 0, 0]

def compactSuccIndOpenZeroWitnessTokens : List Nat := [1, 0]

def compactSuccIndOpenSuccessorWitnessTokens : List Nat :=
  [2, 2, 0, 1, 0, 2, 0, 1]

@[simp] theorem compactSuccIndZeroWitnessTokens_canonical :
    compactSuccIndZeroWitnessTokens =
      compactArithmeticTermTokens succIndZeroWitness := by
  rfl

@[simp] theorem compactSuccIndOpenZeroWitnessTokens_canonical :
    compactSuccIndOpenZeroWitnessTokens =
      compactArithmeticTermTokens succIndOpenZeroWitness := by
  rfl

@[simp] theorem compactSuccIndOpenSuccessorWitnessTokens_canonical :
    compactSuccIndOpenSuccessorWitnessTokens =
      compactArithmeticTermTokens succIndOpenSuccessorWitness := by
  rfl

def compactSuccIndBaseFormula
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    LO.FirstOrder.ArithmeticProposition :=
  Rewriting.app (Rew.subst ![succIndZeroWitness]) body

def compactSuccIndStepZeroFormula
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  Rewriting.app (Rew.subst ![(#0 :
    LO.FirstOrder.ArithmeticSemiterm Nat 1)]) body

def compactSuccIndStepSuccessorFormula
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  Rewriting.app (Rew.subst ![(‘#0 + 1’ :
    LO.FirstOrder.ArithmeticSemiterm Nat 1)]) body

def compactSuccIndConstructedFormula
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    LO.FirstOrder.ArithmeticProposition :=
  (∼compactSuccIndBaseFormula body) ⋎
    ((∼(∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
      compactSuccIndStepSuccessorFormula body))) ⋎
        (∀⁰ compactSuccIndStepZeroFormula body))

theorem compactSuccIndConstructedFormula_eq_succInd
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactSuccIndConstructedFormula body = succInd body := by
  rw [← binarySuccIndTrace_result body]
  simp only [binarySuccIndTrace]
  rw [binaryFormulaSubstitutionOneTrace_result,
    binaryFormulaOpenZeroSubstitutionTrace_result,
    binaryFormulaOpenSuccessorSubstitutionTrace_result]
  simp only [binaryFormulaNegTrace_result]
  rfl

def compactSuccIndBaseTokens (bodyTokens : List Nat) : Option (List Nat) :=
  compactFormulaSubstitutionExact 1
    (compactSuccIndZeroWitnessTokens, bodyTokens)

theorem compactSuccIndBaseTokens_primrec :
    Primrec compactSuccIndBaseTokens := by
  exact compactFormulaSubstitutionExact_primrec.comp
    (Primrec.const 1)
    (Primrec.pair (Primrec.const compactSuccIndZeroWitnessTokens) Primrec.id)

@[simp] theorem compactSuccIndBaseTokens_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactSuccIndBaseTokens (compactArithmeticFormulaTokens body) =
      some (compactArithmeticFormulaTokens
        (compactSuccIndBaseFormula body)) := by
  simp [compactSuccIndBaseTokens, compactSuccIndBaseFormula]

def compactSuccIndOpenSubstitutionTokens
    (bodyAndWitness : List Nat × List Nat) : Option (List Nat) := do
  let shifted <- compactFormulaShiftExact 1 bodyAndWitness.1
  let substituted <- compactFormulaSubstitutionExact 1
    (bodyAndWitness.2, shifted)
  compactFormulaFixitrExact 0 (1, substituted)

theorem compactSuccIndOpenSubstitutionTokens_primrec :
    Primrec compactSuccIndOpenSubstitutionTokens := by
  let Input := List Nat × List Nat
  have hshift : Primrec (fun input : Input =>
      compactFormulaShiftExact 1 input.1) :=
    compactFormulaShiftExact_primrec.comp
      (Primrec.const 1) Primrec.fst
  have hsubstitution : Primrec (fun state : Input × List Nat =>
      compactFormulaSubstitutionExact 1 (state.1.2, state.2)) :=
    compactFormulaSubstitutionExact_primrec.comp
      (Primrec.const 1)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hfixitr : Primrec₂ (fun (_state : Input × List Nat)
      (substituted : List Nat) =>
        compactFormulaFixitrExact 0 (1, substituted)) :=
    compactFormulaFixitrExact_primrec.comp₂
      (Primrec₂.const 0)
      (Primrec₂.pair.comp₂ (Primrec₂.const 1) Primrec₂.right)
  have hsubstitutionThenFixitr : Primrec₂
      (fun (input : Input) (shifted : List Nat) =>
        (compactFormulaSubstitutionExact 1 (input.2, shifted)).bind
          fun substituted =>
            compactFormulaFixitrExact 0 (1, substituted)) := by
    apply Primrec₂.mk
    exact Primrec.option_bind hsubstitution hfixitr
  exact
    (Primrec.option_bind hshift hsubstitutionThenFixitr).of_eq
      fun input => by
        simp [compactSuccIndOpenSubstitutionTokens]

theorem compactSuccIndOpenSubstitutionTokens_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticTerm Nat) :
    compactSuccIndOpenSubstitutionTokens
        (compactArithmeticFormulaTokens body,
          compactArithmeticTermTokens witness) =
      some (compactArithmeticFormulaTokens
        (Rewriting.app (Rew.subst ![
          (Rew.fixitr (L := ℒₒᵣ) 0 1) witness]) body)) := by
  unfold compactSuccIndOpenSubstitutionTokens
  rw [compactFormulaShiftExact_canonical]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [compactFormulaSubstitutionExact_canonical]
  simp only [Option.bind_some]
  rw [compactFormulaFixitrExact_canonical]
  congr 2
  change
    Rewriting.app (Rew.fixitr (L := ℒₒᵣ) 0 1)
        (Rewriting.app (Rew.subst ![witness])
          (Rewriting.app Rew.shift body)) = _
  calc
    _ = Rewriting.app
          ((Rew.fixitr (L := ℒₒᵣ) 0 1).comp (Rew.subst ![witness]))
          (Rewriting.app Rew.shift body) := by
        symm
        exact TransitiveRewriting.comp_app _ _ _
    _ = Rewriting.app
          (((Rew.fixitr (L := ℒₒᵣ) 0 1).comp
            (Rew.subst ![witness])).comp
              (Rew.shift : Rew ℒₒᵣ Nat 1 Nat 1)) body := by
        symm
        exact TransitiveRewriting.comp_app _ _ _
    _ = _ := by rw [fixitrOne_comp_substitution_comp_shift]

def compactSuccIndOpenZeroTokens
    (bodyTokens : List Nat) : Option (List Nat) :=
  compactSuccIndOpenSubstitutionTokens
    (bodyTokens, compactSuccIndOpenZeroWitnessTokens)

theorem compactSuccIndOpenZeroTokens_primrec :
    Primrec compactSuccIndOpenZeroTokens := by
  exact compactSuccIndOpenSubstitutionTokens_primrec.comp
    (Primrec.pair Primrec.id
      (Primrec.const compactSuccIndOpenZeroWitnessTokens))

@[simp] theorem compactSuccIndOpenZeroTokens_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactSuccIndOpenZeroTokens (compactArithmeticFormulaTokens body) =
      some (compactArithmeticFormulaTokens
        (compactSuccIndStepZeroFormula body)) := by
  unfold compactSuccIndOpenZeroTokens
  rw [compactSuccIndOpenZeroWitnessTokens_canonical]
  rw [compactSuccIndOpenSubstitutionTokens_canonical]
  have hbridge :=
    (binaryFormulaOpenSubstitutionTrace_result body
      succIndOpenZeroWitness).symm
  have hnormalized := binaryFormulaOpenZeroSubstitutionTrace_result body
  rw [binaryFormulaOpenZeroSubstitutionTrace] at hnormalized
  simpa [compactSuccIndStepZeroFormula] using
    congrArg (fun formula => some (compactArithmeticFormulaTokens formula))
      (hbridge.trans hnormalized)

def compactSuccIndOpenSuccessorTokens
    (bodyTokens : List Nat) : Option (List Nat) :=
  compactSuccIndOpenSubstitutionTokens
    (bodyTokens, compactSuccIndOpenSuccessorWitnessTokens)

theorem compactSuccIndOpenSuccessorTokens_primrec :
    Primrec compactSuccIndOpenSuccessorTokens := by
  exact compactSuccIndOpenSubstitutionTokens_primrec.comp
    (Primrec.pair Primrec.id
      (Primrec.const compactSuccIndOpenSuccessorWitnessTokens))

@[simp] theorem compactSuccIndOpenSuccessorTokens_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactSuccIndOpenSuccessorTokens
        (compactArithmeticFormulaTokens body) =
      some (compactArithmeticFormulaTokens
        (compactSuccIndStepSuccessorFormula body)) := by
  unfold compactSuccIndOpenSuccessorTokens
  rw [compactSuccIndOpenSuccessorWitnessTokens_canonical]
  rw [compactSuccIndOpenSubstitutionTokens_canonical]
  have hbridge :=
    (binaryFormulaOpenSubstitutionTrace_result body
      succIndOpenSuccessorWitness).symm
  have hnormalized :=
    binaryFormulaOpenSuccessorSubstitutionTrace_result body
  rw [binaryFormulaOpenSuccessorSubstitutionTrace] at hnormalized
  simpa [compactSuccIndStepSuccessorFormula] using
    congrArg (fun formula => some (compactArithmeticFormulaTokens formula))
      (hbridge.trans hnormalized)

def compactSuccIndStepPairTokens
    (bodyTokens : List Nat) : Option (List Nat × List Nat) := do
  let stepZero <- compactSuccIndOpenZeroTokens bodyTokens
  let stepSuccessor <- compactSuccIndOpenSuccessorTokens bodyTokens
  some (stepZero, stepSuccessor)

theorem compactSuccIndStepPairTokens_primrec :
    Primrec compactSuccIndStepPairTokens := by
  have hsuccessor : Primrec
      (fun state : List Nat × List Nat =>
        compactSuccIndOpenSuccessorTokens state.1) :=
    compactSuccIndOpenSuccessorTokens_primrec.comp Primrec.fst
  have hpair : Primrec₂
      (fun (state : List Nat × List Nat) (stepSuccessor : List Nat) =>
        (state.2, stepSuccessor)) :=
    Primrec₂.pair.comp₂
      ((Primrec.snd.comp Primrec.fst).to₂) Primrec₂.right
  have hmapped : Primrec
      (fun state : List Nat × List Nat =>
        (compactSuccIndOpenSuccessorTokens state.1).map
          fun stepSuccessor => (state.2, stepSuccessor)) :=
    Primrec.option_map hsuccessor hpair
  exact
    (Primrec.option_bind compactSuccIndOpenZeroTokens_primrec
      hmapped.to₂).of_eq fun bodyTokens => by
        cases hzero : compactSuccIndOpenZeroTokens bodyTokens with
        | none => simp [compactSuccIndStepPairTokens, hzero]
        | some stepZero =>
            cases hsuccessor :
                compactSuccIndOpenSuccessorTokens bodyTokens <;>
              simp [compactSuccIndStepPairTokens, hzero, hsuccessor]

@[simp] theorem compactSuccIndStepPairTokens_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactSuccIndStepPairTokens (compactArithmeticFormulaTokens body) =
      some (compactArithmeticFormulaTokens
          (compactSuccIndStepZeroFormula body),
        compactArithmeticFormulaTokens
          (compactSuccIndStepSuccessorFormula body)) := by
  simp [compactSuccIndStepPairTokens]

def compactSuccIndQuantifiedStepTokens
    (bodyTokens : List Nat) : Option (List Nat) := do
  let stepPair <- compactSuccIndStepPairTokens bodyTokens
  let negatedStepZero <- compactFormulaNegationExact 1 stepPair.1
  some (tokenFormulaAll
    (tokenFormulaOr negatedStepZero stepPair.2))

theorem compactSuccIndQuantifiedStepTokens_primrec :
    Primrec compactSuccIndQuantifiedStepTokens := by
  let State := List Nat × (List Nat × List Nat)
  have hnegation : Primrec (fun state : State =>
      compactFormulaNegationExact 1 state.2.1) :=
    compactFormulaNegationExact_primrec.comp
      (Primrec.const 1) (Primrec.fst.comp Primrec.snd)
  have hstepSuccessor : Primrec₂
      (fun (state : State) (_negatedStepZero : List Nat) => state.2.2) :=
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).to₂
  have hor : Primrec₂
      (fun (state : State) (negatedStepZero : List Nat) =>
        tokenFormulaOr negatedStepZero state.2.2) :=
    tokenFormulaOr_primrec.comp₂ Primrec₂.right hstepSuccessor
  have hall : Primrec₂
      (fun (state : State) (negatedStepZero : List Nat) =>
        tokenFormulaAll
          (tokenFormulaOr negatedStepZero state.2.2)) :=
    tokenFormulaAll_primrec.comp₂ hor
  have hmapped : Primrec (fun state : State =>
      (compactFormulaNegationExact 1 state.2.1).map
        fun negatedStepZero =>
          tokenFormulaAll
            (tokenFormulaOr negatedStepZero state.2.2)) :=
    Primrec.option_map hnegation hall
  exact
    (Primrec.option_bind compactSuccIndStepPairTokens_primrec
      hmapped.to₂).of_eq fun bodyTokens => by
        cases hpair : compactSuccIndStepPairTokens bodyTokens with
        | none => simp [compactSuccIndQuantifiedStepTokens, hpair]
        | some stepPair =>
            cases hnegation :
                compactFormulaNegationExact 1 stepPair.1 <;>
              simp [compactSuccIndQuantifiedStepTokens, hpair, hnegation]

@[simp] theorem compactSuccIndQuantifiedStepTokens_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactSuccIndQuantifiedStepTokens
        (compactArithmeticFormulaTokens body) =
      some (compactArithmeticFormulaTokens
        (∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
          compactSuccIndStepSuccessorFormula body))) := by
  simp [compactSuccIndQuantifiedStepTokens]

def compactSuccIndQuantifiedFinalTokens
    (bodyTokens : List Nat) : Option (List Nat) :=
  (compactSuccIndOpenZeroTokens bodyTokens).map tokenFormulaAll

theorem compactSuccIndQuantifiedFinalTokens_primrec :
    Primrec compactSuccIndQuantifiedFinalTokens := by
  exact
    (Primrec.option_map compactSuccIndOpenZeroTokens_primrec
      (tokenFormulaAll_primrec.comp₂ Primrec₂.right)).of_eq
        fun bodyTokens => by rfl

@[simp] theorem compactSuccIndQuantifiedFinalTokens_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactSuccIndQuantifiedFinalTokens
        (compactArithmeticFormulaTokens body) =
      some (compactArithmeticFormulaTokens
        (∀⁰ compactSuccIndStepZeroFormula body)) := by
  simp [compactSuccIndQuantifiedFinalTokens]

def compactSuccIndNegatedBaseTokens
    (bodyTokens : List Nat) : Option (List Nat) := do
  let base <- compactSuccIndBaseTokens bodyTokens
  compactFormulaNegationExact 0 base

theorem compactSuccIndNegatedBaseTokens_primrec :
    Primrec compactSuccIndNegatedBaseTokens := by
  have hnegation : Primrec₂
      (fun (_bodyTokens : List Nat) (base : List Nat) =>
        compactFormulaNegationExact 0 base) :=
    compactFormulaNegationExact_primrec.comp₂
      (Primrec₂.const 0) Primrec₂.right
  exact
    (Primrec.option_bind compactSuccIndBaseTokens_primrec hnegation).of_eq
      fun bodyTokens => by simp [compactSuccIndNegatedBaseTokens]

@[simp] theorem compactSuccIndNegatedBaseTokens_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactSuccIndNegatedBaseTokens
        (compactArithmeticFormulaTokens body) =
      some (compactArithmeticFormulaTokens
        (∼compactSuccIndBaseFormula body)) := by
  simp [compactSuccIndNegatedBaseTokens]

def compactSuccIndNegatedStepTokens
    (bodyTokens : List Nat) : Option (List Nat) := do
  let quantifiedStep <- compactSuccIndQuantifiedStepTokens bodyTokens
  compactFormulaNegationExact 0 quantifiedStep

theorem compactSuccIndNegatedStepTokens_primrec :
    Primrec compactSuccIndNegatedStepTokens := by
  have hnegation : Primrec₂
      (fun (_bodyTokens : List Nat) (quantifiedStep : List Nat) =>
        compactFormulaNegationExact 0 quantifiedStep) :=
    compactFormulaNegationExact_primrec.comp₂
      (Primrec₂.const 0) Primrec₂.right
  exact
    (Primrec.option_bind compactSuccIndQuantifiedStepTokens_primrec
      hnegation).of_eq fun bodyTokens => by
        simp [compactSuccIndNegatedStepTokens]

@[simp] theorem compactSuccIndNegatedStepTokens_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactSuccIndNegatedStepTokens
        (compactArithmeticFormulaTokens body) =
      some (compactArithmeticFormulaTokens
        (∼(∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
          compactSuccIndStepSuccessorFormula body)))) := by
  simp [compactSuccIndNegatedStepTokens]

def compactSuccIndOuterPairTokens
    (bodyTokens : List Nat) : Option (List Nat × List Nat) := do
  let negatedBase <- compactSuccIndNegatedBaseTokens bodyTokens
  let negatedStep <- compactSuccIndNegatedStepTokens bodyTokens
  some (negatedBase, negatedStep)

theorem compactSuccIndOuterPairTokens_primrec :
    Primrec compactSuccIndOuterPairTokens := by
  have hstep : Primrec (fun state : List Nat × List Nat =>
      compactSuccIndNegatedStepTokens state.1) :=
    compactSuccIndNegatedStepTokens_primrec.comp Primrec.fst
  have hpair : Primrec₂
      (fun (state : List Nat × List Nat) (negatedStep : List Nat) =>
        (state.2, negatedStep)) :=
    Primrec₂.pair.comp₂
      ((Primrec.snd.comp Primrec.fst).to₂) Primrec₂.right
  have hmapped : Primrec (fun state : List Nat × List Nat =>
      (compactSuccIndNegatedStepTokens state.1).map
        fun negatedStep => (state.2, negatedStep)) :=
    Primrec.option_map hstep hpair
  exact
    (Primrec.option_bind compactSuccIndNegatedBaseTokens_primrec
      hmapped.to₂).of_eq fun bodyTokens => by
        cases hbase : compactSuccIndNegatedBaseTokens bodyTokens with
        | none => simp [compactSuccIndOuterPairTokens, hbase]
        | some negatedBase =>
            cases hstep : compactSuccIndNegatedStepTokens bodyTokens <;>
              simp [compactSuccIndOuterPairTokens, hbase, hstep]

@[simp] theorem compactSuccIndOuterPairTokens_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactSuccIndOuterPairTokens
        (compactArithmeticFormulaTokens body) =
      some (compactArithmeticFormulaTokens
          (∼compactSuccIndBaseFormula body),
        compactArithmeticFormulaTokens
          (∼(∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
            compactSuccIndStepSuccessorFormula body)))) := by
  simp [compactSuccIndOuterPairTokens]

def compactSuccIndSentenceTokens
    (bodyTokens : List Nat) : Option (List Nat) := do
  let outerPair <- compactSuccIndOuterPairTokens bodyTokens
  let quantifiedFinal <- compactSuccIndQuantifiedFinalTokens bodyTokens
  some (tokenFormulaOr outerPair.1
    (tokenFormulaOr outerPair.2 quantifiedFinal))

theorem compactSuccIndSentenceTokens_primrec :
    Primrec compactSuccIndSentenceTokens := by
  let State := List Nat × (List Nat × List Nat)
  have hfinal : Primrec (fun state : State =>
      compactSuccIndQuantifiedFinalTokens state.1) :=
    compactSuccIndQuantifiedFinalTokens_primrec.comp Primrec.fst
  have hnegatedBase : Primrec₂
      (fun (state : State) (_quantifiedFinal : List Nat) => state.2.1) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).to₂
  have hnegatedStep : Primrec₂
      (fun (state : State) (_quantifiedFinal : List Nat) => state.2.2) :=
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).to₂
  have hinner : Primrec₂
      (fun (state : State) (quantifiedFinal : List Nat) =>
        tokenFormulaOr state.2.2 quantifiedFinal) :=
    tokenFormulaOr_primrec.comp₂ hnegatedStep Primrec₂.right
  have houter : Primrec₂
      (fun (state : State) (quantifiedFinal : List Nat) =>
        tokenFormulaOr state.2.1
          (tokenFormulaOr state.2.2 quantifiedFinal)) :=
    tokenFormulaOr_primrec.comp₂ hnegatedBase hinner
  have hmapped : Primrec (fun state : State =>
      (compactSuccIndQuantifiedFinalTokens state.1).map
        fun quantifiedFinal =>
          tokenFormulaOr state.2.1
            (tokenFormulaOr state.2.2 quantifiedFinal)) :=
    Primrec.option_map hfinal houter
  exact
    (Primrec.option_bind compactSuccIndOuterPairTokens_primrec
      hmapped.to₂).of_eq fun bodyTokens => by
        cases houter : compactSuccIndOuterPairTokens bodyTokens with
        | none => simp [compactSuccIndSentenceTokens, houter]
        | some outerPair =>
            cases hfinal : compactSuccIndQuantifiedFinalTokens bodyTokens <;>
              simp [compactSuccIndSentenceTokens, houter, hfinal]

theorem compactSuccIndSentenceTokens_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactSuccIndSentenceTokens (compactArithmeticFormulaTokens body) =
      some (compactArithmeticFormulaTokens (succInd body)) := by
  rw [← compactSuccIndConstructedFormula_eq_succInd body]
  simp [compactSuccIndSentenceTokens, compactSuccIndConstructedFormula]

#print axioms compactExactFormulaTransformResult_primrec
#print axioms compactFormulaShiftExact_primrec
#print axioms compactFormulaSubstitutionExact_primrec
#print axioms compactFormulaFixitrExact_primrec
#print axioms compactFormulaNegationExact_primrec
#print axioms compactSuccIndBaseTokens_primrec
#print axioms compactSuccIndOpenSubstitutionTokens_primrec
#print axioms compactSuccIndOpenSubstitutionTokens_canonical
#print axioms compactSuccIndOpenZeroTokens_primrec
#print axioms compactSuccIndOpenSuccessorTokens_primrec
#print axioms compactSuccIndOpenZeroTokens_canonical
#print axioms compactSuccIndOpenSuccessorTokens_canonical
#print axioms compactSuccIndStepPairTokens_primrec
#print axioms compactSuccIndQuantifiedStepTokens_primrec
#print axioms compactSuccIndQuantifiedFinalTokens_primrec
#print axioms compactSuccIndNegatedBaseTokens_primrec
#print axioms compactSuccIndNegatedStepTokens_primrec
#print axioms compactSuccIndOuterPairTokens_primrec
#print axioms compactSuccIndSentenceTokens_primrec
#print axioms compactSuccIndSentenceTokens_canonical

end FoundationCompactNumericSuccIndSentence
