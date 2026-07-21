import integration.FoundationCompactNumericListedDirectArithmeticPrimitives
import integration.FoundationCompactNumericListedDirectTokenStreamTableau
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactPAFastArithmeticLeafRecognizer
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for a compact binary-natural token segment

The bounded bit branches are materialized by recursion, so this certificate
does not rely on the generic Sigma-zero truth builder.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPATokenSegmentExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPABinaryLengthRuleCompiler
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFastArithmeticLeafRecognizer
open FoundationCompactPAExponentialShortNumeralCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

def compactBinaryNatTokenSegmentClosedFormula
    (payload offset token next : Nat) : ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat) compactBinaryNatTokenSegmentDef.val) ⇜
    ![shortBinaryNumeralTerm payload, shortBinaryNumeralTerm offset,
      shortBinaryNumeralTerm token, shortBinaryNumeralTerm next]

private def tokenSegmentWitnessBitBody (payload offset token : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 2 :=
  “!bitDef
      (!!(Rew.bShift (Rew.bShift (shortBinaryNumeralTerm offset))) +
        2 * #0)
      !!(Rew.bShift (Rew.bShift (shortBinaryNumeralTerm payload))) ∧
    (!bitDef
        (!!(Rew.bShift (Rew.bShift (shortBinaryNumeralTerm offset))) +
          2 * #0 + 1)
        !!(Rew.bShift (Rew.bShift (shortBinaryNumeralTerm payload))) ↔
      !bitDef #0
        !!(Rew.bShift (Rew.bShift (shortBinaryNumeralTerm token))))”

private def tokenSegmentNextFormula (offset next : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!!(Rew.bShift (shortBinaryNumeralTerm next)) =
    !!(Rew.bShift (shortBinaryNumeralTerm offset)) + 2 * #0 + 2”

private def tokenSegmentWitnessLengthBody (token : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!lengthDef #0 !!(Rew.bShift (shortBinaryNumeralTerm token))”

private def tokenSegmentTerminalZeroFormula (payload offset _token : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “¬!bitDef
    (!!(Rew.bShift (shortBinaryNumeralTerm offset)) + 2 * #0)
    !!(Rew.bShift (shortBinaryNumeralTerm payload))”

private def tokenSegmentTerminalOneFormula (payload offset _token : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “¬!bitDef
    (!!(Rew.bShift (shortBinaryNumeralTerm offset)) + 2 * #0 + 1)
    !!(Rew.bShift (shortBinaryNumeralTerm payload))”

private def tokenSegmentSourceBitBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 6 :=
  “!bitDef (#3 + 2 * #0) #2 ∧
    (!bitDef (#3 + 2 * #0 + 1) #2 ↔ !bitDef #0 #4)”

private def tokenSegmentSourceUniversal :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  tokenSegmentSourceBitBody.ballLT
    (#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5)

private def tokenSegmentSourceUniversalRaw :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  “∀ index < #0,
    (#3 + 2 * index) ∈ #2 ∧
    ((#3 + 2 * index + 1) ∈ #2 ↔ index ∈ #4)”

private def tokenSegmentSourceLength :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  “!lengthDef #0 #3”

private def tokenSegmentSourceNext :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  “#4 = #2 + 2 * #0 + 2”

private def tokenSegmentSourceTerminalZero :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  “(#2 + 2 * #0) ∉ #1”

private def tokenSegmentSourceTerminalOne :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  “(#2 + 2 * #0 + 1) ∉ #1”

private def tokenSegmentSourceTail :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  tokenSegmentSourceLength ⋏
    (tokenSegmentSourceNext ⋏
      (tokenSegmentSourceUniversalRaw ⋏
        (tokenSegmentSourceTerminalZero ⋏
          tokenSegmentSourceTerminalOne)))

private def tokenSegmentSourceBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  “#0 < #3 + 1” ⋏ tokenSegmentSourceTail

private theorem bShift_tokenSegmentSourceBound :
    Rew.bShift
        (‘#2 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 4) =
      (‘#3 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 5) := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    LO.FirstOrder.Semiterm.Operator.One.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem compactBinaryNatTokenSegmentDef_val_eq_exists :
    compactBinaryNatTokenSegmentDef.val = ∃⁰ tokenSegmentSourceBody := by
  unfold compactBinaryNatTokenSegmentDef compactNatSizeDef
  change tokenSegmentSourceTail.bexsLTSucc
      (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 4) =
      ∃⁰ tokenSegmentSourceBody
  unfold tokenSegmentSourceBody tokenSegmentSourceTail
  unfold LO.FirstOrder.Semiformula.bexsLTSucc
  unfold LO.FirstOrder.Semiformula.bexsLT
  rw [bShift_tokenSegmentSourceBound]
  rfl

private def tokenSegmentOuterTerms (payload offset token next : Nat) :
    Fin 4 -> ValuationTerm :=
  ![shortBinaryNumeralTerm payload, shortBinaryNumeralTerm offset,
    shortBinaryNumeralTerm token, shortBinaryNumeralTerm next]

private def tokenSegmentBodyTerms (payload offset token next : Nat) :
    Fin 5 -> LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
    Rew.bShift (shortBinaryNumeralTerm payload),
    Rew.bShift (shortBinaryNumeralTerm offset),
    Rew.bShift (shortBinaryNumeralTerm token),
    Rew.bShift (shortBinaryNumeralTerm next)]

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹
        ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹
        ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app,
        TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem rewriting_formulaOperator
    {sourceVariables targetVariables : Type*}
    {operatorArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (operator : LO.FirstOrder.Semiformula.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ operator.operator terms =
      operator.operator (rewriting ∘ terms) := by
  unfold LO.FirstOrder.Semiformula.Operator.operator
  exact rewriting_embeddedFormulaSubstitution
    rewriting operator.sentence terms

private theorem rewriting_termOperator
    {sourceVariables targetVariables : Type*}
    {operatorArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (operator : LO.FirstOrder.Semiterm.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting (operator.operator terms) =
      operator.operator (rewriting ∘ terms) := by
  unfold LO.FirstOrder.Semiterm.Operator.operator
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            sourceVariables operatorArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            targetVariables operatorArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting (Rew.subst terms (Rew.emb operator.term)) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            sourceVariables operatorArity)) operator.term := by
      rw [Rew.comp_app, Rew.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            targetVariables operatorArity)) operator.term := by
      rw [hcomposition]
    _ = Rew.subst (rewriting ∘ terms) (Rew.emb operator.term) := by
      rw [Rew.comp_app]

private theorem rewriting_emb_empty
    {boundArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty boundArity) :
    (Rewriting.emb (ξ := Empty) formula) = formula := by
  change
    (Rew.emb : Rew ℒₒᵣ Empty boundArity Empty boundArity) ▹ formula = formula
  rw [Rew.emb_eq_id]
  exact ReflectiveRewriting.id_app formula

private theorem rewriting_ballLT
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (body : LO.FirstOrder.ArithmeticSemiformula sourceVariables
      (sourceArity + 1))
    (bound : LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ body.ballLT bound =
      (rewriting.q ▹ body).ballLT (rewriting bound) := by
  have hguardTerms :
      rewriting.q ∘
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm sourceVariables
              (sourceArity + 1)), Rew.bShift bound] =
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm targetVariables
              (targetArity + 1)), Rew.bShift (rewriting bound)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => exact Rew.q_bvar_zero rewriting
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Rew.q_comp_bShift_app rewriting bound
        | succ coordinate => exact Fin.elim0 coordinate
  unfold LO.FirstOrder.Semiformula.ballLT
  rw [Rewriting.smul_ball, rewriting_formulaOperator, hguardTerms]

private theorem tokenSegmentSourceLength_rewrite
    (payload offset token next : Nat) :
    Rew.embSubsts (tokenSegmentBodyTerms payload offset token next) ▹
        tokenSegmentSourceLength =
      tokenSegmentWitnessLengthBody token := by
  have hterms :
      Rew.embSubsts (tokenSegmentBodyTerms payload offset token next) ∘
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5),
            (#3 : LO.FirstOrder.ArithmeticSemiterm Empty 5)] =
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
          Rew.bShift (shortBinaryNumeralTerm token)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => simp [tokenSegmentBodyTerms]
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => simp [tokenSegmentBodyTerms]
        | succ coordinate => exact Fin.elim0 coordinate
  have hsource :
      tokenSegmentSourceLength =
        (Rewriting.emb (ξ := Empty) lengthDef.val) ⇜
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5), #3] := by
    unfold tokenSegmentSourceLength
    rw [rewriting_emb_empty]
  have htarget :
      tokenSegmentWitnessLengthBody token =
        (Rewriting.emb (ξ := Nat) lengthDef.val) ⇜
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
            Rew.bShift (shortBinaryNumeralTerm token)] := by
    unfold tokenSegmentWitnessLengthBody
    rfl
  rw [hsource, htarget,
    rewriting_embeddedFormulaSubstitution, hterms]

private theorem tokenSegmentBodyQ_zero
    (payload offset token next : Nat) :
    (Rew.embSubsts
        (tokenSegmentBodyTerms payload offset token next)).q
        (#0 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) := by
  rw [Rew.q_bvar_zero, Rew.q_bvar_zero]

private theorem tokenSegmentBodyQ_payload
    (payload offset token next : Nat) :
    (Rew.embSubsts
        (tokenSegmentBodyTerms payload offset token next)).q
        (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q
        (Rew.bShift (shortBinaryNumeralTerm payload)) := by
  change
    (Rew.embSubsts
        (tokenSegmentBodyTerms payload offset token next)).q
        (#((1 : Fin 5).succ)) = _
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar,
    Rew.q_comp_bShift_app]
  rfl

private theorem tokenSegmentBodyQ_offset
    (payload offset token next : Nat) :
    (Rew.embSubsts
        (tokenSegmentBodyTerms payload offset token next)).q
        (#3 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q
        (Rew.bShift (shortBinaryNumeralTerm offset)) := by
  change
    (Rew.embSubsts
        (tokenSegmentBodyTerms payload offset token next)).q
        (#((2 : Fin 5).succ)) = _
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar,
    Rew.q_comp_bShift_app]
  rfl

private theorem tokenSegmentBodyQ_token
    (payload offset token next : Nat) :
    (Rew.embSubsts
        (tokenSegmentBodyTerms payload offset token next)).q
        (#4 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q
        (Rew.bShift (shortBinaryNumeralTerm token)) := by
  change
    (Rew.embSubsts
        (tokenSegmentBodyTerms payload offset token next)).q
        (#((3 : Fin 5).succ)) = _
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar,
    Rew.q_comp_bShift_app]
  rfl

private theorem tokenSegmentSourceNext_rewrite
    (payload offset token next : Nat) :
    Rew.embSubsts (tokenSegmentBodyTerms payload offset token next) ▹
        tokenSegmentSourceNext =
      tokenSegmentNextFormula offset next := by
  simp [tokenSegmentSourceNext, tokenSegmentNextFormula,
    tokenSegmentBodyTerms, rewriting_formulaOperator,
    rewriting_termOperator]

private theorem tokenSegmentSourceUniversal_rewrite
    (payload offset token next : Nat) :
    Rew.embSubsts (tokenSegmentBodyTerms payload offset token next) ▹
        tokenSegmentSourceUniversalRaw =
      (tokenSegmentWitnessBitBody payload offset token).ballLT
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) := by
  simp only [tokenSegmentSourceUniversalRaw, rewriting_ballLT]
  have hbound :
      Rew.embSubsts (tokenSegmentBodyTerms payload offset token next)
          (#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5) =
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) := by
    simp [tokenSegmentBodyTerms]
  rw [hbound]
  congr 1
  simp [tokenSegmentWitnessBitBody,
    LO.FirstOrder.Semiformula.iff_eq,
    LO.FirstOrder.Semiformula.Operator.operator,
    LO.FirstOrder.Arithmetic.operator_mem_def,
    tokenSegmentBodyQ_zero, tokenSegmentBodyQ_payload,
    tokenSegmentBodyQ_offset, tokenSegmentBodyQ_token,
    rewriting_termOperator]
  simp [rewriting_embeddedFormulaSubstitution,
    tokenSegmentBodyQ_zero, tokenSegmentBodyQ_payload,
    tokenSegmentBodyQ_offset, tokenSegmentBodyQ_token,
    rewriting_termOperator]

private theorem tokenSegmentSourceTerminalZero_rewrite
    (payload offset token next : Nat) :
    Rew.embSubsts (tokenSegmentBodyTerms payload offset token next) ▹
        tokenSegmentSourceTerminalZero =
      tokenSegmentTerminalZeroFormula payload offset token := by
  simp [tokenSegmentSourceTerminalZero,
    tokenSegmentTerminalZeroFormula,
    LO.FirstOrder.Semiformula.Operator.operator,
    LO.FirstOrder.Arithmetic.operator_mem_def]
  rw [rewriting_embeddedFormulaSubstitution]
  simp [tokenSegmentBodyTerms, rewriting_termOperator]

private theorem tokenSegmentSourceTerminalOne_rewrite
    (payload offset token next : Nat) :
    Rew.embSubsts (tokenSegmentBodyTerms payload offset token next) ▹
        tokenSegmentSourceTerminalOne =
      tokenSegmentTerminalOneFormula payload offset token := by
  simp [tokenSegmentSourceTerminalOne,
    tokenSegmentTerminalOneFormula,
    LO.FirstOrder.Semiformula.Operator.operator,
    LO.FirstOrder.Arithmetic.operator_mem_def]
  rw [rewriting_embeddedFormulaSubstitution]
  simp [tokenSegmentBodyTerms, rewriting_termOperator]

private def tokenSegmentExplicitWitnessBody
    (payload offset token next : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift (shortBinaryNumeralTerm token)) + 1” ⋏
    (tokenSegmentWitnessLengthBody token ⋏
      (tokenSegmentNextFormula offset next ⋏
        ((tokenSegmentWitnessBitBody payload offset token).ballLT
            (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) ⋏
          (tokenSegmentTerminalZeroFormula payload offset token ⋏
            tokenSegmentTerminalOneFormula payload offset token))))

def tokenSegmentWitnessBody (payload offset token next : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  Rew.embSubsts (tokenSegmentBodyTerms payload offset token next) ▹
    tokenSegmentSourceBody

private theorem tokenSegmentWitnessBody_eq_explicit
    (payload offset token next : Nat) :
    tokenSegmentWitnessBody payload offset token next =
      tokenSegmentExplicitWitnessBody payload offset token next := by
  unfold tokenSegmentWitnessBody tokenSegmentSourceBody
  unfold tokenSegmentSourceTail tokenSegmentExplicitWitnessBody
  simp only [LogicalConnective.HomClass.map_and]
  rw [tokenSegmentSourceLength_rewrite,
    tokenSegmentSourceNext_rewrite,
    tokenSegmentSourceUniversal_rewrite,
    tokenSegmentSourceTerminalZero_rewrite,
    tokenSegmentSourceTerminalOne_rewrite]
  simp [tokenSegmentBodyTerms, rewriting_termOperator]

private theorem tokenSegmentBodyRewriting_eq_embSubsts
    (payload offset token next : Nat) :
    (Rew.subst (tokenSegmentOuterTerms payload offset token next)).q.comp
        (Rew.emb : Rew ℒₒᵣ Empty 5 Nat 5) =
      Rew.embSubsts (tokenSegmentBodyTerms payload offset token next) := by
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        rw [Rew.comp_app, Rew.emb_bvar, Rew.embSubsts_bvar]
        change (Rew.subst (tokenSegmentOuterTerms payload offset token next)).q
          (#0) = #0
        exact Rew.q_bvar_zero _
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            rw [Rew.comp_app, Rew.emb_bvar, Rew.embSubsts_bvar,
              Rew.q_bvar_succ, Rew.subst_bvar]
            rfl
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero =>
                rw [Rew.comp_app, Rew.emb_bvar, Rew.embSubsts_bvar,
                  Rew.q_bvar_succ, Rew.subst_bvar]
                rfl
            | succ coordinate =>
                cases coordinate using Fin.cases with
                | zero =>
                    rw [Rew.comp_app, Rew.emb_bvar, Rew.embSubsts_bvar,
                      Rew.q_bvar_succ, Rew.subst_bvar]
                    rfl
                | succ coordinate =>
                    cases coordinate using Fin.cases with
                    | zero =>
                        rw [Rew.comp_app, Rew.emb_bvar, Rew.embSubsts_bvar,
                          Rew.q_bvar_succ, Rew.subst_bvar]
                        rfl
                    | succ coordinate => exact Fin.elim0 coordinate
  · exact Empty.elim coordinate

private theorem compactBinaryNatTokenSegmentClosedFormula_eq_exists
  (payload offset token next : Nat) :
    compactBinaryNatTokenSegmentClosedFormula payload offset token next =
      ∃⁰ tokenSegmentWitnessBody payload offset token next := by
  unfold compactBinaryNatTokenSegmentClosedFormula
  rw [compactBinaryNatTokenSegmentDef_val_eq_exists]
  simp only [Rewriting.app_exs, Rew.q_emb]
  rw [← TransitiveRewriting.comp_app]
  change ∃⁰ (((Rew.subst
      (tokenSegmentOuterTerms payload offset token next)).q.comp
        (Rew.emb : Rew ℒₒᵣ Empty 5 Nat 5)) ▹ tokenSegmentSourceBody) =
      ∃⁰ tokenSegmentWitnessBody payload offset token next
  unfold tokenSegmentWitnessBody
  rw [tokenSegmentBodyRewriting_eq_embSubsts]

/-- The closed four-coordinate instance has the exact explicit size witness
body used by the token-segment certificate construction. -/
theorem compactBinaryNatTokenSegmentClosedFormula_formula_alignment
    (payload offset token next : Nat) :
    compactBinaryNatTokenSegmentClosedFormula payload offset token next =
      ∃⁰ tokenSegmentWitnessBody payload offset token next :=
  compactBinaryNatTokenSegmentClosedFormula_eq_exists payload offset token next

private def tokenSegmentWitnessGuardFormula (token : Nat) :
    ArithmeticProposition :=
  “!!(shortBinaryNumeralTerm (Nat.size token)) <
    !!(shortBinaryNumeralTerm token) + 1”

private def tokenSegmentLengthFormula (token : Nat) :
    ArithmeticProposition :=
  binaryLengthAtValuationFormula
    (shortBinaryNumeralTerm (Nat.size token))
    (shortBinaryNumeralTerm token)

private def tokenSegmentClosedNextFormula
    (offset token next : Nat) : ArithmeticProposition :=
  “!!(shortBinaryNumeralTerm next) =
    !!(shortBinaryNumeralTerm offset) +
      2 * !!(shortBinaryNumeralTerm (Nat.size token)) + 2”

private def tokenSegmentBitBody
    (payload offset token : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!bitDef
      (!!(Rew.bShift (shortBinaryNumeralTerm offset)) + 2 * #0)
      !!(Rew.bShift (shortBinaryNumeralTerm payload)) ∧
    (!bitDef
        (!!(Rew.bShift (shortBinaryNumeralTerm offset)) + 2 * #0 + 1)
        !!(Rew.bShift (shortBinaryNumeralTerm payload)) ↔
      !bitDef #0 !!(Rew.bShift (shortBinaryNumeralTerm token)))”

private def tokenSegmentClosedUniversalFormula
    (payload offset token : Nat) : ArithmeticProposition :=
  (tokenSegmentBitBody payload offset token).ballLT
    (shortBinaryNumeralTerm (Nat.size token))

private def tokenSegmentClosedTerminalZeroFormula
    (payload offset token : Nat) : ArithmeticProposition :=
  (tokenSegmentTerminalZeroFormula payload offset token)/[
    shortBinaryNumeralTerm (Nat.size token)]

private def tokenSegmentClosedTerminalOneFormula
    (payload offset token : Nat) : ArithmeticProposition :=
  (tokenSegmentTerminalOneFormula payload offset token)/[
    shortBinaryNumeralTerm (Nat.size token)]

private def tokenSegmentPostWitnessFormula
    (payload offset token next : Nat) : ArithmeticProposition :=
  tokenSegmentWitnessGuardFormula token ⋏
    (tokenSegmentLengthFormula token ⋏
      (tokenSegmentClosedNextFormula offset token next ⋏
        (tokenSegmentClosedUniversalFormula payload offset token ⋏
          (tokenSegmentClosedTerminalZeroFormula payload offset token ⋏
            tokenSegmentClosedTerminalOneFormula payload offset token))))

private theorem tokenSegmentWitnessBody_subst
    (payload offset token next : Nat) :
    (tokenSegmentWitnessBody payload offset token next)/[
        shortBinaryNumeralTerm (Nat.size token)] =
      tokenSegmentPostWitnessFormula payload offset token next := by
  rw [tokenSegmentWitnessBody_eq_explicit]
  simp [tokenSegmentExplicitWitnessBody,
    tokenSegmentPostWitnessFormula, tokenSegmentWitnessGuardFormula,
    tokenSegmentLengthFormula, tokenSegmentClosedNextFormula,
    tokenSegmentClosedUniversalFormula,
    tokenSegmentClosedTerminalZeroFormula,
    tokenSegmentClosedTerminalOneFormula,
    tokenSegmentNextFormula, tokenSegmentWitnessBitBody, tokenSegmentBitBody,
    tokenSegmentTerminalZeroFormula, tokenSegmentTerminalOneFormula,
    binaryLengthAtValuationFormula,
    tokenSegmentWitnessLengthBody, subst_lengthDef_instance,
    subst_bitDef_instance, rewriting_ballLT,
    rewriting_embeddedFormulaSubstitution, rewriting_termOperator,
    Rew.q_comp_bShift_app, Rew.subst_bShift_app,
    Rew.subst_bvar, Rew.func]

private abbrev TokenSegmentHybridCertificate
    (valuation : Nat -> Nat) (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate valuation formula

private abbrev TokenSegmentHybridBranches
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bound : Nat) :=
  CheckedHybridValuationUniversalBranches valuation body bound

private def markerIndexTerm (offset : Nat) : ValuationTerm :=
  ‘!!(Rew.shift (shortBinaryNumeralTerm offset)) + 2 * &0’

private def dataIndexTerm (offset : Nat) : ValuationTerm :=
  ‘!!(Rew.shift (shortBinaryNumeralTerm offset)) + 2 * &0 + 1’

private def payloadTerm (payload : Nat) : ValuationTerm :=
  Rew.shift (shortBinaryNumeralTerm payload)

private def tokenIndexTerm : ValuationTerm := &0

private def tokenValueTerm (token : Nat) : ValuationTerm :=
  Rew.shift (shortBinaryNumeralTerm token)

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ :
      LO.FirstOrder.ArithmeticSemiterm Variable boundArity) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Variable boundArity) :
    (‘!!left * !!right’ :
      LO.FirstOrder.ArithmeticSemiterm Variable boundArity) =
      LO.FirstOrder.Semiterm.func Language.Mul.mul ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Mul.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left + !!right’) =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left * !!right’) =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  simp [termValue, LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem termValue_arithmeticTwo (valuation : Nat -> Nat) :
    termValue valuation (‘2’ : ValuationTerm) = 2 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

private theorem bitVariables
    (expected : Bool) (indexTerm valueTerm : ValuationTerm) :
    indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
      (binaryBitAtValuationFormula expected indexTerm valueTerm).freeVariables := by
  cases expected <;>
    simpa [binaryBitAtValuationFormula, binaryBitLiteralAtTerms,
      binaryBitAtomAtTerms,
      FoundationCompactPAFastArithmeticLeafRecognizer.bitInstance] using
        bitInstance_argument_freeVariables_union_subset indexTerm valueTerm

private theorem tokenSegmentBitBody_free
    (payload offset token : Nat) :
    Rewriting.free (tokenSegmentBitBody payload offset token) =
      (binaryBitAtomAtTerms (markerIndexTerm offset) (payloadTerm payload) ⋏
        (binaryBitAtomAtTerms (dataIndexTerm offset) (payloadTerm payload) 🡘
          binaryBitAtomAtTerms tokenIndexTerm (tokenValueTerm token))) := by
  simp [tokenSegmentBitBody, markerIndexTerm, dataIndexTerm,
    payloadTerm, tokenIndexTerm, tokenValueTerm,
    binaryBitAtomAtTerms, LO.FirstOrder.Semiformula.iff_eq,
    rewriting_embeddedFormulaSubstitution, Rew.subst_bShift_app,
    Rew.func]

private noncomputable def witnessGuardCertificate
    (token : Nat) :
    TokenSegmentHybridCertificate zeroValuation
      (tokenSegmentWitnessGuardFormula token) := by
  have hsize : Nat.size token ≤ token := by
    have h := LO.FirstOrder.Arithmetic.length_le (V := Nat) token
    have heq : (‖token‖ : Nat) =
        LO.FirstOrder.Arithmetic.binaryLength token := rfl
    rw [heq, binaryLength_nat_eq_size] at h
    exact (foundationNatLE_iff_standard _ _).mp h
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm (Nat.size token),
        (‘!!(shortBinaryNumeralTerm token) + 1’ : ValuationTerm)] (by
          change termValue zeroValuation
              (shortBinaryNumeralTerm (Nat.size token)) <
            termValue zeroValuation
              (‘!!(shortBinaryNumeralTerm token) + 1’ : ValuationTerm)
          simpa [termValue_arithmeticAdd, termValue_arithmeticOne,
            termValue_shortBinaryNumeralTerm] using
            Nat.lt_succ_of_le hsize)
  exact .cast (by
    unfold tokenSegmentWitnessGuardFormula
    exact (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm) direct

private noncomputable def lengthCertificate
    (token : Nat) :
    TokenSegmentHybridCertificate zeroValuation
      (tokenSegmentLengthFormula token) := by
  exact .binaryLength zeroValuation
    (shortBinaryNumeralTerm (Nat.size token))
    (shortBinaryNumeralTerm token) (by
      simp [termValue_shortBinaryNumeralTerm])

private noncomputable def nextCertificate
    (offset token next : Nat)
    (hnext : next = offset + 2 * Nat.size token + 2) :
    TokenSegmentHybridCertificate zeroValuation
      (tokenSegmentClosedNextFormula offset token next) := by
  let right : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm offset) +
      2 * !!(shortBinaryNumeralTerm (Nat.size token)) + 2’
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm next, right] (by
        change termValue zeroValuation (shortBinaryNumeralTerm next) =
          termValue zeroValuation right
        simpa [right, termValue_arithmeticAdd, termValue_arithmeticMul,
          termValue_arithmeticTwo, termValue_shortBinaryNumeralTerm] using hnext)
  exact .cast (by
    unfold tokenSegmentClosedNextFormula right
    exact (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm) direct

private noncomputable def bitBranchCertificate
    (payload offset token index : Nat)
    (hmarker : payload.testBit (offset + 2 * index) = true)
    (hdata : payload.testBit (offset + 2 * index + 1) =
      token.testBit index) :
    TokenSegmentHybridCertificate
      (extendValuation index zeroValuation)
      (Rewriting.free (tokenSegmentBitBody payload offset token)) := by
  let valuation := extendValuation index zeroValuation
  let markerAtom := binaryBitAtomAtTerms
    (markerIndexTerm offset) (payloadTerm payload)
  let dataAtom := binaryBitAtomAtTerms
    (dataIndexTerm offset) (payloadTerm payload)
  let sourceAtom := binaryBitAtomAtTerms
    tokenIndexTerm (tokenValueTerm token)
  let marker := CheckedHybridValuationBoundedFormulaCertificate.binaryBit true
    valuation (markerIndexTerm offset) (payloadTerm payload) (by
      simpa [valuation, markerIndexTerm, payloadTerm,
        termValue_arithmeticAdd, termValue_arithmeticMul,
        termValue_arithmeticTwo, termValue_shift,
        termValue_shortBinaryNumeralTerm] using hmarker)
    (bitVariables true _ _)
  cases hsource : token.testBit index with
  | false =>
      let data := CheckedHybridValuationBoundedFormulaCertificate.binaryBit false
        valuation (dataIndexTerm offset) (payloadTerm payload) (by
          simpa [valuation, dataIndexTerm, payloadTerm,
            termValue_arithmeticAdd, termValue_arithmeticMul,
            termValue_arithmeticOne, termValue_arithmeticTwo,
            termValue_shift, termValue_shortBinaryNumeralTerm, hsource] using hdata)
        (bitVariables false _ _)
      let source := CheckedHybridValuationBoundedFormulaCertificate.binaryBit false
        valuation tokenIndexTerm (tokenValueTerm token) (by
          simpa [valuation, tokenIndexTerm, tokenValueTerm,
            termValue_shift, termValue_shortBinaryNumeralTerm] using hsource)
        (bitVariables false _ _)
      let iffProof := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := sourceAtom) data)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := dataAtom) source)
      let result := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        marker iffProof
      exact .cast (by
        rw [tokenSegmentBitBody_free]
        change (markerAtom ⋏
          ((∼dataAtom ⋎ sourceAtom) ⋏ (∼sourceAtom ⋎ dataAtom))) = _
        rw [← LO.FirstOrder.Semiformula.iff_eq]) result
  | true =>
      let data := CheckedHybridValuationBoundedFormulaCertificate.binaryBit true
        valuation (dataIndexTerm offset) (payloadTerm payload) (by
          simpa [valuation, dataIndexTerm, payloadTerm,
            termValue_arithmeticAdd, termValue_arithmeticMul,
            termValue_arithmeticOne, termValue_arithmeticTwo,
            termValue_shift, termValue_shortBinaryNumeralTerm, hsource] using hdata)
        (bitVariables true _ _)
      let source := CheckedHybridValuationBoundedFormulaCertificate.binaryBit true
        valuation tokenIndexTerm (tokenValueTerm token) (by
          simpa [valuation, tokenIndexTerm, tokenValueTerm,
            termValue_shift, termValue_shortBinaryNumeralTerm] using hsource)
        (bitVariables true _ _)
      let iffProof := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := ∼dataAtom) source)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := ∼sourceAtom) data)
      let result := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        marker iffProof
      exact .cast (by
        rw [tokenSegmentBitBody_free]
        change (markerAtom ⋏
          ((∼dataAtom ⋎ sourceAtom) ⋏ (∼sourceAtom ⋎ dataAtom))) = _
        rw [← LO.FirstOrder.Semiformula.iff_eq]) result

private noncomputable def bitBranches
    (payload offset token count : Nat)
    (hbits : ∀ index < count,
      payload.testBit (offset + 2 * index) = true ∧
      payload.testBit (offset + 2 * index + 1) = token.testBit index) :
    TokenSegmentHybridBranches zeroValuation
      (tokenSegmentBitBody payload offset token) count := by
  induction count with
  | zero => exact .nil zeroValuation _
  | succ previous ih =>
      exact .snoc
        (ih (fun index hindex => hbits index (Nat.lt_trans hindex
          (Nat.lt_succ_self previous))))
        (bitBranchCertificate payload offset token previous
          (hbits previous (Nat.lt_succ_self previous)).1
          (hbits previous (Nat.lt_succ_self previous)).2)

private noncomputable def universalCertificate
    (payload offset token : Nat)
    (hbits : ∀ index < Nat.size token,
      payload.testBit (offset + 2 * index) = true ∧
      payload.testBit (offset + 2 * index + 1) = token.testBit index) :
    TokenSegmentHybridCertificate zeroValuation
      (tokenSegmentClosedUniversalFormula payload offset token) := by
  let bound : ValuationTerm := shortBinaryNumeralTerm (Nat.size token)
  let direct := CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
    bound (tokenSegmentBitBody payload offset token) (by
      simpa [bound, termValue_shortBinaryNumeralTerm] using
        bitBranches payload offset token (Nat.size token) hbits)
  exact .cast (by
    change (∀⁰ termBoundedUniversalBody (Rew.bShift bound)
      (tokenSegmentBitBody payload offset token)) =
        tokenSegmentClosedUniversalFormula payload offset token
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

private noncomputable def terminalZeroCertificate
    (payload offset token : Nat)
    (hzero : payload.testBit (offset + 2 * Nat.size token) = false) :
    TokenSegmentHybridCertificate zeroValuation
      (tokenSegmentClosedTerminalZeroFormula payload offset token) := by
  let indexTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm offset) +
      2 * !!(shortBinaryNumeralTerm (Nat.size token))’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.binaryBit false
    zeroValuation indexTerm (shortBinaryNumeralTerm payload) (by
      simpa [indexTerm, termValue_arithmeticAdd, termValue_arithmeticMul,
        termValue_arithmeticTwo, termValue_shortBinaryNumeralTerm] using hzero)
    (bitVariables false _ _)
  exact .cast (by
    simp [tokenSegmentClosedTerminalZeroFormula,
      tokenSegmentTerminalZeroFormula, indexTerm,
      binaryBitAtValuationFormula, binaryBitLiteralAtTerms,
      binaryBitAtomAtTerms,
      subst_bitDef_instance, Rew.subst_bShift_app, Rew.func]) direct

private noncomputable def terminalOneCertificate
    (payload offset token : Nat)
    (hone : payload.testBit (offset + 2 * Nat.size token + 1) = false) :
    TokenSegmentHybridCertificate zeroValuation
      (tokenSegmentClosedTerminalOneFormula payload offset token) := by
  let indexTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm offset) +
      2 * !!(shortBinaryNumeralTerm (Nat.size token)) + 1’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.binaryBit false
    zeroValuation indexTerm (shortBinaryNumeralTerm payload) (by
      simpa [indexTerm, termValue_arithmeticAdd, termValue_arithmeticMul,
        termValue_arithmeticOne, termValue_arithmeticTwo,
        termValue_shortBinaryNumeralTerm] using hone)
    (bitVariables false _ _)
  exact .cast (by
    simp [tokenSegmentClosedTerminalOneFormula,
      tokenSegmentTerminalOneFormula, indexTerm,
      binaryBitAtValuationFormula, binaryBitLiteralAtTerms,
      binaryBitAtomAtTerms,
      subst_bitDef_instance, Rew.subst_bShift_app, Rew.func]) direct

/-- Explicit hybrid certificate for one compact token segment. -/
noncomputable def compactBinaryNatTokenSegmentExplicitHybridCertificate
    (payload offset token next : Nat)
    (hsegment : CompactBinaryNatTokenSegment payload offset token next) :
    TokenSegmentHybridCertificate zeroValuation
      (compactBinaryNatTokenSegmentClosedFormula payload offset token next) := by
  rcases hsegment with ⟨hnext, hbits, hzero, hone⟩
  rw [compactBinaryNatTokenSegmentClosedFormula_eq_exists]
  refine .existsWitness
    (tokenSegmentWitnessBody payload offset token next)
    (Nat.size token) ?_
  let post := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (witnessGuardCertificate token)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (lengthCertificate token)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nextCertificate offset token next hnext)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (universalCertificate payload offset token hbits)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (terminalZeroCertificate payload offset token hzero)
            (terminalOneCertificate payload offset token hone)))))
  exact .cast
    (tokenSegmentWitnessBody_subst payload offset token next).symm post

theorem compactBinaryNatTokenSegmentClosedFormula_freeVariables_eq_empty
    (payload offset token next : Nat) :
    (compactBinaryNatTokenSegmentClosedFormula
      payload offset token next).freeVariables = ∅ := by
  unfold compactBinaryNatTokenSegmentClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  cases coordinate using Fin.cases with
  | zero => exact shortBinaryNumeralTerm_freeVariables_eq_empty payload
  | succ coordinate =>
      cases coordinate using Fin.cases with
      | zero => exact shortBinaryNumeralTerm_freeVariables_eq_empty offset
      | succ coordinate =>
          cases coordinate using Fin.cases with
          | zero => exact shortBinaryNumeralTerm_freeVariables_eq_empty token
          | succ coordinate =>
              cases coordinate using Fin.cases with
              | zero => exact shortBinaryNumeralTerm_freeVariables_eq_empty next
              | succ coordinate => exact Fin.elim0 coordinate

/-- Empty-context proof compiled from the explicit certificate. -/
noncomputable def compileCompactBinaryNatTokenSegmentExplicitHybridContext
    (payload offset token next : Nat)
    (hsegment : CompactBinaryNatTokenSegment payload offset token next) :
    FoundationCompactCertifiedContextProof.CertifiedPAContextProof ∅
      (compactBinaryNatTokenSegmentClosedFormula payload offset token next) := by
  let raw :=
    (compactBinaryNatTokenSegmentExplicitHybridCertificate
      payload offset token next hsegment).compile
  have hcontext :
      valuationContext
          (compactBinaryNatTokenSegmentClosedFormula
            payload offset token next).freeVariables zeroValuation = ∅ := by
    rw [compactBinaryNatTokenSegmentClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact FoundationCompactCertifiedContextProof.CertifiedPAContextProof.castContext
    hcontext raw

/-- Proof-free structural payload resource for the explicit certificate. -/
noncomputable def compactBinaryNatTokenSegmentExplicitHybridStructuralResource
    (payload offset token next : Nat)
    (hsegment : CompactBinaryNatTokenSegment payload offset token next) : Nat :=
  CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
    (compactBinaryNatTokenSegmentExplicitHybridCertificate
      payload offset token next hsegment)

theorem compileCompactBinaryNatTokenSegmentExplicitHybridContext_payloadLength_le
    (payload offset token next : Nat)
    (hsegment : CompactBinaryNatTokenSegment payload offset token next) :
    (compileCompactBinaryNatTokenSegmentExplicitHybridContext
      payload offset token next hsegment).payloadLength ≤
      compactBinaryNatTokenSegmentExplicitHybridStructuralResource
        payload offset token next hsegment := by
  unfold compileCompactBinaryNatTokenSegmentExplicitHybridContext
  rw [FoundationCompactCertifiedContextProof.CertifiedPAContextProof.castContext_payloadLength]
  exact
    CheckedHybridValuationBoundedFormulaCertificate.compile_payloadLength_le_structuralPayloadBound
      (compactBinaryNatTokenSegmentExplicitHybridCertificate
        payload offset token next hsegment)

#print axioms compactBinaryNatTokenSegmentClosedFormula_formula_alignment
#print axioms compactBinaryNatTokenSegmentExplicitHybridCertificate
#print axioms compileCompactBinaryNatTokenSegmentExplicitHybridContext
#print axioms compileCompactBinaryNatTokenSegmentExplicitHybridContext_payloadLength_le

end FoundationCompactPATokenSegmentExplicitHybridCertificate
