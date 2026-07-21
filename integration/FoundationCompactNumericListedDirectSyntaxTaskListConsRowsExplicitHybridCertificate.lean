import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRows
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactPAExplicitHybridUniversalBranches
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for syntax-task list cons rows

The head row and every shifted tail row retain their concrete bounded
witnesses.  The tail's three-cell task equality uses the public row certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

private abbrev HybridCertificate := CheckedHybridValuationBoundedFormulaCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left : ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
      ArithmeticSemiformula targetVariables targetArity) = Rewriting.app right := by
  cases h
  rfl

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity -> ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜ (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜ (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem rewriting_emptyFormulaSubstitution
    {targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Empty sourceArity targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity -> ArithmeticSemiterm Empty sourceArity) :
    rewriting ▹ (formula ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜ (rewriting ∘ terms) := by
  have hcomposition :
      rewriting.comp (Rew.subst terms) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ (formula ⇜ terms) =
        (rewriting.comp (Rew.subst terms)) ▹ formula := by
      rw [TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜ (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem rewriting_formulaOperator
    {sourceVariables targetVariables : Type*}
    {operatorArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity)
    (operator : Semiformula.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity -> ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ operator.operator terms = operator.operator (rewriting ∘ terms) := by
  unfold Semiformula.Operator.operator
  exact rewriting_embeddedFormulaSubstitution rewriting operator.sentence terms

private theorem rewriting_ballLT
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1))
    (bound : ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ body.ballLT bound =
      (rewriting.q ▹ body).ballLT (rewriting bound) := by
  have hguardTerms : rewriting.q ∘
      ![(#0 : ArithmeticSemiterm sourceVariables (sourceArity + 1)), Rew.bShift bound] =
        ![(#0 : ArithmeticSemiterm targetVariables (targetArity + 1)),
          Rew.bShift (rewriting bound)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => exact Rew.q_bvar_zero rewriting
    | succ coordinate =>
      cases coordinate using Fin.cases with
      | zero => exact Rew.q_comp_bShift_app rewriting bound
      | succ coordinate => exact Fin.elim0 coordinate
  unfold Semiformula.ballLT
  rw [Rewriting.smul_ball, rewriting_formulaOperator, hguardTerms]

@[simp] private theorem rewriting_bexsLTSucc
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity)
    (bound : ArithmeticSemiterm sourceVariables sourceArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1)) :
    rewriting ▹ body.bexsLTSucc bound =
      (rewriting.q ▹ body).bexsLTSucc (rewriting bound) := by
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT]

private def closedShift : (k : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat k
  | 0, term => term
  | k + 1, term => Rew.bShift (closedShift k term)

def unaryNumeralTerm (value : Nat) : ValuationTerm :=
  Semiterm.Operator.operator (Semiterm.Operator.numeral ℒₒᵣ value) ![]

@[simp] theorem termValue_unaryNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (unaryNumeralTerm value) = value := by
  unfold termValue unaryNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘ (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) =
        (![] : Fin 0 -> Nat) by
      funext index
      exact Fin.elim0 index]
  simp

private def syntaxTaskListConsOuterTerms
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    Fin 10 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm sourceBoundary,
    shortBinaryNumeralTerm sourceCount, shortBinaryNumeralTerm targetBoundary,
    shortBinaryNumeralTerm targetCount, headKindTerm,
    headBinderArityTerm, headRepeatCountTerm]

private def syntaxTaskListConsDepthOneTerms
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    Fin 11 -> ArithmeticSemiterm Nat 1 :=
  ![#0, closedShift 1 (shortBinaryNumeralTerm tokenTable),
    closedShift 1 (shortBinaryNumeralTerm width),
    closedShift 1 (shortBinaryNumeralTerm tokenCount),
    closedShift 1 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 1 (shortBinaryNumeralTerm sourceCount),
    closedShift 1 (shortBinaryNumeralTerm targetBoundary),
    closedShift 1 (shortBinaryNumeralTerm targetCount),
    closedShift 1 headKindTerm,
    closedShift 1 headBinderArityTerm,
    closedShift 1 headRepeatCountTerm]

private def syntaxTaskListConsDepthTwoTerms
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    Fin 12 -> ArithmeticSemiterm Nat 2 :=
  ![#0, #1, closedShift 2 (shortBinaryNumeralTerm tokenTable),
    closedShift 2 (shortBinaryNumeralTerm width),
    closedShift 2 (shortBinaryNumeralTerm tokenCount),
    closedShift 2 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 2 (shortBinaryNumeralTerm sourceCount),
    closedShift 2 (shortBinaryNumeralTerm targetBoundary),
    closedShift 2 (shortBinaryNumeralTerm targetCount),
    closedShift 2 headKindTerm,
    closedShift 2 headBinderArityTerm,
    closedShift 2 headRepeatCountTerm]

private def syntaxTaskListConsDepthThreeTerms
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    Fin 13 -> ArithmeticSemiterm Nat 3 :=
  ![#0, #1, #2, closedShift 3 (shortBinaryNumeralTerm tokenTable),
    closedShift 3 (shortBinaryNumeralTerm width),
    closedShift 3 (shortBinaryNumeralTerm tokenCount),
    closedShift 3 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 3 (shortBinaryNumeralTerm sourceCount),
    closedShift 3 (shortBinaryNumeralTerm targetBoundary),
    closedShift 3 (shortBinaryNumeralTerm targetCount),
    closedShift 3 headKindTerm,
    closedShift 3 headBinderArityTerm,
    closedShift 3 headRepeatCountTerm]

private def syntaxTaskListConsDepthFourTerms
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    Fin 14 -> ArithmeticSemiterm Nat 4 :=
  ![#0, #1, #2, #3, closedShift 4 (shortBinaryNumeralTerm tokenTable),
    closedShift 4 (shortBinaryNumeralTerm width),
    closedShift 4 (shortBinaryNumeralTerm tokenCount),
    closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 4 (shortBinaryNumeralTerm sourceCount),
    closedShift 4 (shortBinaryNumeralTerm targetBoundary),
    closedShift 4 (shortBinaryNumeralTerm targetCount),
    closedShift 4 headKindTerm,
    closedShift 4 headBinderArityTerm,
    closedShift 4 headRepeatCountTerm]

private def syntaxTaskListConsDepthFiveTerms
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    Fin 15 -> ArithmeticSemiterm Nat 5 :=
  ![#0, #1, #2, #3, #4, closedShift 5 (shortBinaryNumeralTerm tokenTable),
    closedShift 5 (shortBinaryNumeralTerm width),
    closedShift 5 (shortBinaryNumeralTerm tokenCount),
    closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 5 (shortBinaryNumeralTerm sourceCount),
    closedShift 5 (shortBinaryNumeralTerm targetBoundary),
    closedShift 5 (shortBinaryNumeralTerm targetCount),
    closedShift 5 headKindTerm,
    closedShift 5 headBinderArityTerm,
    closedShift 5 headRepeatCountTerm]

private theorem syntaxTaskListConsOuterRewriting_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKind headBinderArity headRepeatCount : ValuationTerm) :
    (Rew.subst (syntaxTaskListConsOuterTerms tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount)).comp
        (Rew.emb : Rew ℒₒᵣ Empty 10 Nat 10) =
      Rew.embSubsts (syntaxTaskListConsOuterTerms tokenTable width tokenCount sourceBoundary
        sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount) := by
  ext coordinate
  · simp [Rew.comp_app]
  · exact Empty.elim coordinate

private theorem syntaxTaskListConsOuterQ1_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKind headBinderArity headRepeatCount : ValuationTerm) :
    (Rew.embSubsts (syntaxTaskListConsOuterTerms tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount)).q =
      Rew.embSubsts (syntaxTaskListConsDepthOneTerms tokenTable width tokenCount sourceBoundary
        sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount) := by
  ext coordinate
  · fin_cases coordinate <;>
      simp [syntaxTaskListConsOuterTerms, syntaxTaskListConsDepthOneTerms, closedShift, Rew.q]
  · exact Empty.elim coordinate

private theorem syntaxTaskListConsOuterQ2_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKind headBinderArity headRepeatCount : ValuationTerm) :
    (Rew.embSubsts (syntaxTaskListConsOuterTerms tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount)).q.q =
      Rew.embSubsts (syntaxTaskListConsDepthTwoTerms tokenTable width tokenCount sourceBoundary
        sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount) := by
  rw [syntaxTaskListConsOuterQ1_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [syntaxTaskListConsDepthOneTerms, syntaxTaskListConsDepthTwoTerms,
        closedShift, Rew.q]
  · exact Empty.elim coordinate

private theorem syntaxTaskListConsOuterQ3_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKind headBinderArity headRepeatCount : ValuationTerm) :
    (Rew.embSubsts (syntaxTaskListConsOuterTerms tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount)).q.q.q =
      Rew.embSubsts (syntaxTaskListConsDepthThreeTerms tokenTable width tokenCount sourceBoundary
        sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount) := by
  rw [syntaxTaskListConsOuterQ2_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [syntaxTaskListConsDepthTwoTerms, syntaxTaskListConsDepthThreeTerms,
        closedShift, Rew.q]
  · exact Empty.elim coordinate

private theorem syntaxTaskListConsOuterQ4_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKind headBinderArity headRepeatCount : ValuationTerm) :
    (Rew.embSubsts (syntaxTaskListConsOuterTerms tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount)).q.q.q.q =
      Rew.embSubsts (syntaxTaskListConsDepthFourTerms tokenTable width tokenCount sourceBoundary
        sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount) := by
  rw [syntaxTaskListConsOuterQ3_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [syntaxTaskListConsDepthThreeTerms, syntaxTaskListConsDepthFourTerms,
        closedShift, Rew.q]
  · exact Empty.elim coordinate

private theorem syntaxTaskListConsOuterQ5_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKind headBinderArity headRepeatCount : ValuationTerm) :
    (Rew.embSubsts (syntaxTaskListConsOuterTerms tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount)).q.q.q.q.q =
      Rew.embSubsts (syntaxTaskListConsDepthFiveTerms tokenTable width tokenCount sourceBoundary
        sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount) := by
  rw [syntaxTaskListConsOuterQ4_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [syntaxTaskListConsDepthFourTerms, syntaxTaskListConsDepthFiveTerms,
        closedShift, Rew.q]
  · exact Empty.elim coordinate

def compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskListConsRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm sourceBoundary,
      shortBinaryNumeralTerm sourceCount, shortBinaryNumeralTerm targetBoundary,
      shortBinaryNumeralTerm targetCount, headKindTerm,
      headBinderArityTerm, headRepeatCountTerm]

def compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal
    (tokenTable width tokenCount targetBoundary : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    ArithmeticSemiformula Nat 2 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm targetBoundary),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 (unaryNumeralTerm 0), (#1 : ArithmeticSemiterm Nat 2)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm targetBoundary),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          closedShift 2 (unaryNumeralTerm 1), (#0 : ArithmeticSemiterm Nat 2)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactSyntaxTaskDirectLayoutDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
          closedShift 2 (shortBinaryNumeralTerm width),
          closedShift 2 (shortBinaryNumeralTerm tokenCount), (#1 : ArithmeticSemiterm Nat 2),
          (#0 : ArithmeticSemiterm Nat 2), closedShift 2 headKindTerm,
          closedShift 2 headBinderArityTerm,
          closedShift 2 headRepeatCountTerm]))

def compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody
    (tokenTable width tokenCount targetBoundary : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    ValuationFormula :=
  ((compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal tokenTable width tokenCount
      targetBoundary headKindTerm headBinderArityTerm headRepeatCountTerm).bexsLTSucc
        (closedShift 1 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (shortBinaryNumeralTerm tokenCount)

def compactAdditiveSyntaxTaskListConsRowsClosedFormula
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      headKind headBinderArity headRepeatCount : Nat) : ValuationFormula :=
  compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable width tokenCount
    sourceBoundary sourceCount targetBoundary targetCount (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity) (shortBinaryNumeralTerm headRepeatCount)

def compactAdditiveSyntaxTaskListConsRowsHeadTerminal
    (tokenTable width tokenCount targetBoundary headKind headBinderArity headRepeatCount : Nat) :
    ArithmeticSemiformula Nat 2 :=
  compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal tokenTable width tokenCount
    targetBoundary (shortBinaryNumeralTerm headKind) (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)

def compactAdditiveSyntaxTaskListConsRowsHeadBody
    (tokenTable width tokenCount targetBoundary headKind headBinderArity headRepeatCount : Nat) :
    ValuationFormula :=
  compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody tokenTable width tokenCount
    targetBoundary (shortBinaryNumeralTerm headKind) (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)

def compactAdditiveSyntaxTaskListConsRowsTailTerminal
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 5 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 5 (shortBinaryNumeralTerm tokenCount), (#4 : ArithmeticSemiterm Nat 5),
        (#3 : ArithmeticSemiterm Nat 5)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
          closedShift 5 (shortBinaryNumeralTerm tokenCount), ‘#4 + 1’,
          (#2 : ArithmeticSemiterm Nat 5)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![closedShift 5 (shortBinaryNumeralTerm targetBoundary),
            closedShift 5 (shortBinaryNumeralTerm tokenCount), ‘#4 + 1’,
            (#1 : ArithmeticSemiterm Nat 5)]) ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
            ![closedShift 5 (shortBinaryNumeralTerm targetBoundary),
              closedShift 5 (shortBinaryNumeralTerm tokenCount), ‘#4 + 2’,
              (#0 : ArithmeticSemiterm Nat 5)]) ⋏
          ((Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
            ![closedShift 5 (shortBinaryNumeralTerm tokenTable),
              closedShift 5 (shortBinaryNumeralTerm width),
              closedShift 5 (shortBinaryNumeralTerm tokenCount), (#3 : ArithmeticSemiterm Nat 5),
              (#2 : ArithmeticSemiterm Nat 5), (#1 : ArithmeticSemiterm Nat 5),
              (#0 : ArithmeticSemiterm Nat 5)]))))

def compactAdditiveSyntaxTaskListConsRowsTailBody
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) : ArithmeticSemiformula Nat 1 :=
  ((((compactAdditiveSyntaxTaskListConsRowsTailTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary).bexsLTSucc
        (closedShift 4 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (closedShift 3 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
    (closedShift 2 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (closedShift 1 (shortBinaryNumeralTerm tokenCount))

def compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitFormula
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount) + 1” ⋏
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody tokenTable width tokenCount
      targetBoundary headKindTerm headBinderArityTerm headRepeatCountTerm ⋏
      (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary).ballLT (shortBinaryNumeralTerm sourceCount))

def compactAdditiveSyntaxTaskListConsRowsExplicitFormula
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      headKind headBinderArity headRepeatCount : Nat) : ValuationFormula :=
  compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitFormula tokenTable width
    tokenCount sourceBoundary sourceCount targetBoundary targetCount
      (shortBinaryNumeralTerm headKind) (shortBinaryNumeralTerm headBinderArity)
        (shortBinaryNumeralTerm headRepeatCount)

private def syntaxTaskListConsSourceHeadTerminal :
    ArithmeticSemiformula Empty 12 :=
  (compactFixedWidthEntryDef.val ⇜
      ![(#7 : ArithmeticSemiterm Empty 12), #4, ‘0’, #1]) ⋏
    ((compactFixedWidthEntryDef.val ⇜
        ![(#7 : ArithmeticSemiterm Empty 12), #4, ‘1’, #0]) ⋏
      (compactSyntaxTaskDirectLayoutDef.val ⇜
        ![(#2 : ArithmeticSemiterm Empty 12), #3, #4, #1, #0, #9, #10, #11]))

private def syntaxTaskListConsSourceHeadBody : ArithmeticSemiformula Empty 10 :=
  (syntaxTaskListConsSourceHeadTerminal.bexsLTSucc
      (#3 : ArithmeticSemiterm Empty 11)).bexsLTSucc
    (#2 : ArithmeticSemiterm Empty 10)

private def syntaxTaskListConsSourceTailTerminal :
    ArithmeticSemiformula Empty 15 :=
  (compactFixedWidthEntryDef.val ⇜
      ![(#8 : ArithmeticSemiterm Empty 15), #7, #4, #3]) ⋏
    ((compactFixedWidthEntryDef.val ⇜
        ![(#8 : ArithmeticSemiterm Empty 15), #7, ‘#4 + 1’, #2]) ⋏
      ((compactFixedWidthEntryDef.val ⇜
          ![(#10 : ArithmeticSemiterm Empty 15), #7, ‘#4 + 1’, #1]) ⋏
        ((compactFixedWidthEntryDef.val ⇜
            ![(#10 : ArithmeticSemiterm Empty 15), #7, ‘#4 + 2’, #0]) ⋏
          (compactAdditiveSyntaxTaskRowEqDef.val ⇜
            ![(#5 : ArithmeticSemiterm Empty 15), #6, #7, #3, #2, #1, #0]))))

private def syntaxTaskListConsSourceTailBody : ArithmeticSemiformula Empty 11 :=
  ((((syntaxTaskListConsSourceTailTerminal.bexsLTSucc
      (#6 : ArithmeticSemiterm Empty 14)).bexsLTSucc
        (#5 : ArithmeticSemiterm Empty 13)).bexsLTSucc
      (#4 : ArithmeticSemiterm Empty 12)).bexsLTSucc
    (#3 : ArithmeticSemiterm Empty 11))

private def syntaxTaskListConsSourceDecomposedFormula :
    ArithmeticSemiformula Empty 10 :=
  (“#6 = #4 + 1” : ArithmeticSemiformula Empty 10) ⋏
    (syntaxTaskListConsSourceHeadBody ⋏
      syntaxTaskListConsSourceTailBody.ballLT (#4 : ArithmeticSemiterm Empty 10))

private theorem compactAdditiveSyntaxTaskListConsRowsDef_val_eq_sourceDecomposed :
    compactAdditiveSyntaxTaskListConsRowsDef.val =
      syntaxTaskListConsSourceDecomposedFormula := by
  unfold compactAdditiveSyntaxTaskListConsRowsDef
  unfold syntaxTaskListConsSourceDecomposedFormula
  unfold syntaxTaskListConsSourceHeadBody syntaxTaskListConsSourceHeadTerminal
  unfold syntaxTaskListConsSourceTailBody syntaxTaskListConsSourceTailTerminal
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT]

private theorem syntaxTaskListConsSourceCount_rewrite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKind headBinderArity headRepeatCount : ValuationTerm) :
    Rew.embSubsts
        (syntaxTaskListConsOuterTerms tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount headKind headBinderArity headRepeatCount) ▹
        (“#6 = #4 + 1” : ArithmeticSemiformula Empty 10) =
      “!!(shortBinaryNumeralTerm targetCount) =
        !!(shortBinaryNumeralTerm sourceCount) + 1” := by
  simp [syntaxTaskListConsOuterTerms]

private theorem syntaxTaskListConsSourceHeadTerminal_rewrite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKind headBinderArity headRepeatCount : ValuationTerm) :
    Rew.embSubsts
        (syntaxTaskListConsDepthTwoTerms tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount headKind headBinderArity headRepeatCount) ▹
        syntaxTaskListConsSourceHeadTerminal =
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal tokenTable width tokenCount
        targetBoundary headKind headBinderArity headRepeatCount := by
  unfold syntaxTaskListConsSourceHeadTerminal
  unfold compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal
  simp [rewriting_emptyFormulaSubstitution, syntaxTaskListConsDepthTwoTerms,
    unaryNumeralTerm, closedShift, Function.comp_def]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;> simp

private theorem syntaxTaskListConsSourceHeadBody_rewrite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKind headBinderArity headRepeatCount : ValuationTerm) :
    Rew.embSubsts
        (syntaxTaskListConsOuterTerms tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount headKind headBinderArity headRepeatCount) ▹
        syntaxTaskListConsSourceHeadBody =
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody tokenTable width tokenCount
        targetBoundary headKind headBinderArity headRepeatCount := by
  unfold syntaxTaskListConsSourceHeadBody
  unfold compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody
  rw [rewriting_bexsLTSucc, rewriting_bexsLTSucc]
  rw [syntaxTaskListConsOuterQ2_eq_embSubsts,
    syntaxTaskListConsSourceHeadTerminal_rewrite,
    syntaxTaskListConsOuterQ1_eq_embSubsts]
  simp [syntaxTaskListConsOuterTerms, syntaxTaskListConsDepthOneTerms, closedShift]

private theorem syntaxTaskListConsSourceTailTerminal_rewrite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKind headBinderArity headRepeatCount : ValuationTerm) :
    Rew.embSubsts
        (syntaxTaskListConsDepthFiveTerms tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount headKind headBinderArity headRepeatCount) ▹
        syntaxTaskListConsSourceTailTerminal =
      compactAdditiveSyntaxTaskListConsRowsTailTerminal tokenTable width tokenCount
        sourceBoundary targetBoundary := by
  unfold syntaxTaskListConsSourceTailTerminal
  unfold compactAdditiveSyntaxTaskListConsRowsTailTerminal
  simp [rewriting_emptyFormulaSubstitution, syntaxTaskListConsDepthFiveTerms,
    closedShift, Function.comp_def]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;> simp

private theorem syntaxTaskListConsSourceTailBody_rewrite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKind headBinderArity headRepeatCount : ValuationTerm) :
    (Rew.embSubsts
        (syntaxTaskListConsOuterTerms tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount headKind headBinderArity headRepeatCount)).q ▹
        syntaxTaskListConsSourceTailBody =
      compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary := by
  unfold syntaxTaskListConsSourceTailBody
  unfold compactAdditiveSyntaxTaskListConsRowsTailBody
  rw [rewriting_bexsLTSucc, rewriting_bexsLTSucc,
    rewriting_bexsLTSucc, rewriting_bexsLTSucc]
  rw [syntaxTaskListConsOuterQ5_eq_embSubsts,
    syntaxTaskListConsSourceTailTerminal_rewrite,
    syntaxTaskListConsOuterQ4_eq_embSubsts,
    syntaxTaskListConsOuterQ3_eq_embSubsts,
    syntaxTaskListConsOuterQ2_eq_embSubsts,
    syntaxTaskListConsOuterQ1_eq_embSubsts]
  simp [syntaxTaskListConsDepthOneTerms, syntaxTaskListConsDepthTwoTerms,
    syntaxTaskListConsDepthThreeTerms, syntaxTaskListConsDepthFourTerms, closedShift]

theorem compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula_alignment
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (headKind headBinderArity headRepeatCount : ValuationTerm) :
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount headKind headBinderArity
          headRepeatCount =
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitFormula tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount headKind
          headBinderArity headRepeatCount := by
  unfold compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
  change Rew.subst
      (syntaxTaskListConsOuterTerms tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount headKind headBinderArity headRepeatCount) ▹
      ((Rew.emb : Rew ℒₒᵣ Empty 10 Nat 10) ▹
        compactAdditiveSyntaxTaskListConsRowsDef.val) = _
  rw [← TransitiveRewriting.comp_app,
    syntaxTaskListConsOuterRewriting_eq_embSubsts]
  rw [compactAdditiveSyntaxTaskListConsRowsDef_val_eq_sourceDecomposed]
  let rewriting := Rew.embSubsts
    (syntaxTaskListConsOuterTerms tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount headKind headBinderArity headRepeatCount)
  change rewriting ▹ syntaxTaskListConsSourceDecomposedFormula =
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitFormula tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount headKind headBinderArity
      headRepeatCount
  unfold syntaxTaskListConsSourceDecomposedFormula
  unfold compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitFormula
  simp only [LogicalConnective.HomClass.map_and]
  rw [show rewriting ▹ (“#6 = #4 + 1” : ArithmeticSemiformula Empty 10) =
      “!!(shortBinaryNumeralTerm targetCount) =
        !!(shortBinaryNumeralTerm sourceCount) + 1” by
    exact syntaxTaskListConsSourceCount_rewrite tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount]
  rw [show rewriting ▹ syntaxTaskListConsSourceHeadBody =
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody tokenTable width tokenCount
        targetBoundary headKind headBinderArity headRepeatCount by
    exact syntaxTaskListConsSourceHeadBody_rewrite tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount]
  rw [rewriting_ballLT]
  rw [show rewriting.q ▹ syntaxTaskListConsSourceTailBody =
      compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary by
    exact syntaxTaskListConsSourceTailBody_rewrite tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount]
  simp [rewriting, syntaxTaskListConsOuterTerms]

theorem compactAdditiveSyntaxTaskListConsRowsClosedFormula_alignment
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      headKind headBinderArity headRepeatCount : Nat) :
    compactAdditiveSyntaxTaskListConsRowsClosedFormula tokenTable width tokenCount sourceBoundary
        sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount =
      compactAdditiveSyntaxTaskListConsRowsExplicitFormula tokenTable width tokenCount sourceBoundary
        sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount := by
  simpa [compactAdditiveSyntaxTaskListConsRowsClosedFormula,
    compactAdditiveSyntaxTaskListConsRowsExplicitFormula] using
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula_alignment tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
          (shortBinaryNumeralTerm headKind) (shortBinaryNumeralTerm headBinderArity)
            (shortBinaryNumeralTerm headRepeatCount)

private theorem substitute_closedShift {k : Nat} (values : Fin k -> ValuationTerm)
    (term : ValuationTerm) : Rew.subst values (closedShift k term) = term := by
  induction k with
  | zero =>
    have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) = Rew.id := by
      apply Rew.ext
      · intro coordinate
        exact Fin.elim0 coordinate
      · intro freeIndex
        rfl
    rw [hrew]
    exact Rew.id_app term
  | succ k ih =>
    have hrew : (Rew.subst values).comp Rew.bShift =
        Rew.subst (fun index : Fin k => values index.succ) := by
      apply Rew.ext
      · intro index
        simp [Rew.comp_app]
      · intro freeIndex
        simp [Rew.comp_app]
    calc
      Rew.subst values (closedShift (k + 1) term) =
          ((Rew.subst values).comp Rew.bShift) (closedShift k term) := by
            simp [closedShift, Rew.comp_app]
      _ = Rew.subst (fun index : Fin k => values index.succ) (closedShift k term) := by rw [hrew]
      _ = term := ih _

theorem compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_substitution_alignment
    (tokenTable width tokenCount targetBoundary targetLeft targetRight : Nat)
    (headKind headBinderArity headRepeatCount : ValuationTerm) :
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal tokenTable width tokenCount
      targetBoundary headKind headBinderArity headRepeatCount) ⇜
        ![shortBinaryNumeralTerm targetRight, shortBinaryNumeralTerm targetLeft] =
      (compactFixedWidthEntryAtValuationFormula (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 0)
          (shortBinaryNumeralTerm targetLeft) ⋏
        (compactFixedWidthEntryAtValuationFormula (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 1)
            (shortBinaryNumeralTerm targetRight) ⋏
          compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width tokenCount targetLeft
            targetRight headKind headBinderArity headRepeatCount)) := by
  unfold compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactSyntaxTaskDirectLayoutAtValuationTermsFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
    · intro coordinate
      exact Empty.elim coordinate

theorem compactAdditiveSyntaxTaskListConsRowsHeadTerminal_substitution_alignment
    (tokenTable width tokenCount targetBoundary headKind headBinderArity headRepeatCount
      targetLeft targetRight : Nat) :
    (compactAdditiveSyntaxTaskListConsRowsHeadTerminal tokenTable width tokenCount targetBoundary
      headKind headBinderArity headRepeatCount) ⇜
        ![shortBinaryNumeralTerm targetRight, shortBinaryNumeralTerm targetLeft] =
      (compactFixedWidthEntryAtValuationFormula (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 0)
          (shortBinaryNumeralTerm targetLeft) ⋏
        (compactFixedWidthEntryAtValuationFormula (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 1)
            (shortBinaryNumeralTerm targetRight) ⋏
          compactSyntaxTaskDirectLayoutClosedFormula tokenTable width tokenCount targetLeft
            targetRight headKind headBinderArity headRepeatCount)) := by
  simpa [compactAdditiveSyntaxTaskListConsRowsHeadTerminal,
    compactSyntaxTaskDirectLayoutClosedFormula] using
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_substitution_alignment
        tokenTable width tokenCount targetBoundary targetLeft targetRight
          (shortBinaryNumeralTerm headKind) (shortBinaryNumeralTerm headBinderArity)
            (shortBinaryNumeralTerm headRepeatCount)

def compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 4 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 4 (shortBinaryNumeralTerm tokenCount), (&0 : ArithmeticSemiterm Nat 4),
        (#3 : ArithmeticSemiterm Nat 4)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
          closedShift 4 (shortBinaryNumeralTerm tokenCount), (‘&0 + 1’ : ArithmeticSemiterm Nat 4),
          (#2 : ArithmeticSemiterm Nat 4)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
            closedShift 4 (shortBinaryNumeralTerm tokenCount), (‘&0 + 1’ : ArithmeticSemiterm Nat 4),
            (#1 : ArithmeticSemiterm Nat 4)]) ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
            ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
              closedShift 4 (shortBinaryNumeralTerm tokenCount), (‘&0 + 2’ : ArithmeticSemiterm Nat 4),
              (#0 : ArithmeticSemiterm Nat 4)]) ⋏
          ((Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
            ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
              closedShift 4 (shortBinaryNumeralTerm width),
              closedShift 4 (shortBinaryNumeralTerm tokenCount), (#3 : ArithmeticSemiterm Nat 4),
              (#2 : ArithmeticSemiterm Nat 4), (#1 : ArithmeticSemiterm Nat 4),
              (#0 : ArithmeticSemiterm Nat 4)]))))

private theorem compactAdditiveSyntaxTaskListConsRowsTailTerminal_free_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    Rewriting.free (compactAdditiveSyntaxTaskListConsRowsTailTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary) =
      compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal tokenTable width tokenCount
        sourceBoundary targetBoundary := by
  unfold compactAdditiveSyntaxTaskListConsRowsTailTerminal
  unfold compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal
  simp [closedShift, ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

private def localExplicitBoundedWitnessFormulaFour
    (bound : ValuationTerm) (body : ArithmeticSemiformula Nat 4) :
    ValuationFormula :=
  ((((body.bexsLTSucc (closedShift 3 bound)).bexsLTSucc
      (closedShift 2 bound)).bexsLTSucc
    (closedShift 1 bound)).bexsLTSucc bound)

private theorem localExplicitBoundedWitnessFormulaFour_eq_explicit
    (bound : ValuationTerm) (body : ArithmeticSemiformula Nat 4) :
    localExplicitBoundedWitnessFormulaFour bound body =
      explicitBoundedWitnessFormula bound 4 body := by
  rfl

private theorem compactAdditiveSyntaxTaskListConsRowsTailBody_free_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    Rewriting.free (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
      sourceBoundary targetBoundary) =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm tokenCount) 4
        (compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal tokenTable width tokenCount
          sourceBoundary targetBoundary) := by
  calc
    Rewriting.free (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary) =
      localExplicitBoundedWitnessFormulaFour (shortBinaryNumeralTerm tokenCount)
        (compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal tokenTable width tokenCount
          sourceBoundary targetBoundary) := by
      unfold compactAdditiveSyntaxTaskListConsRowsTailBody
      unfold localExplicitBoundedWitnessFormulaFour
      simp [Rew.q_free, closedShift,
        compactAdditiveSyntaxTaskListConsRowsTailTerminal_free_alignment]
    _ = explicitBoundedWitnessFormula (shortBinaryNumeralTerm tokenCount) 4
        (compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal tokenTable width tokenCount
          sourceBoundary targetBoundary) :=
      localExplicitBoundedWitnessFormulaFour_eq_explicit _ _

theorem compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal_substitution_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary sourceLeft sourceRight
      targetLeft targetRight : Nat) :
    (compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary) ⇜
        ![shortBinaryNumeralTerm targetRight, shortBinaryNumeralTerm targetLeft,
          shortBinaryNumeralTerm sourceRight, shortBinaryNumeralTerm sourceLeft] =
      (compactFixedWidthEntryAtValuationFormula (shortBinaryNumeralTerm sourceBoundary)
          (shortBinaryNumeralTerm tokenCount) (&0 : ValuationTerm)
          (shortBinaryNumeralTerm sourceLeft) ⋏
        (compactFixedWidthEntryAtValuationFormula (shortBinaryNumeralTerm sourceBoundary)
            (shortBinaryNumeralTerm tokenCount) (‘&0 + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm sourceRight) ⋏
          (compactFixedWidthEntryAtValuationFormula (shortBinaryNumeralTerm targetBoundary)
              (shortBinaryNumeralTerm tokenCount) (‘&0 + 1’ : ValuationTerm)
              (shortBinaryNumeralTerm targetLeft) ⋏
            (compactFixedWidthEntryAtValuationFormula (shortBinaryNumeralTerm targetBoundary)
                (shortBinaryNumeralTerm tokenCount) (‘&0 + 2’ : ValuationTerm)
                (shortBinaryNumeralTerm targetRight) ⋏
              ((Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
                ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
                  shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm sourceLeft,
                  shortBinaryNumeralTerm sourceRight, shortBinaryNumeralTerm targetLeft,
                  shortBinaryNumeralTerm targetRight]))))) := by
  unfold compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal
  unfold compactFixedWidthEntryAtValuationFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
    · intro coordinate
      exact Empty.elim coordinate

private theorem arithmeticAddTerm_eq_func {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd (valuation : Nat -> Nat)
    (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := termValue_one valuation ![]

private theorem termValue_arithmeticTwo (valuation : Nat -> Nat) :
    termValue valuation (‘2’ : ValuationTerm) = 2 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

noncomputable def countEqualityCertificate (sourceCount targetCount : Nat)
    (hcount : targetCount = sourceCount + 1) : HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm targetCount) =
        !!(shortBinaryNumeralTerm sourceCount) + 1” := by
  let rightTerm : ValuationTerm := ‘!!(shortBinaryNumeralTerm sourceCount) + 1’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic zeroValuation
    Language.Eq.eq ![shortBinaryNumeralTerm targetCount, rightTerm] (by
      change termValue zeroValuation (shortBinaryNumeralTerm targetCount) =
        termValue zeroValuation rightTerm
      simp [rightTerm, termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
        termValue_arithmeticOne]
      exact hcount)
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

structure CompactAdditiveSyntaxTaskListConsHeadData
    (tokenTable width tokenCount targetBoundary headKind headBinderArity headRepeatCount : Nat) where
  targetLeft : Nat
  targetRight : Nat
  targetLeft_le : targetLeft ≤ tokenCount
  targetRight_le : targetRight ≤ tokenCount
  targetLeft_entry : CompactFixedWidthEntry targetBoundary tokenCount 0 targetLeft
  targetRight_entry : CompactFixedWidthEntry targetBoundary tokenCount 1 targetRight
  layout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount targetLeft targetRight
    (headKind, headBinderArity, headRepeatCount)

structure CompactAdditiveSyntaxTaskListConsTailRowData
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat) where
  sourceLeft : Nat
  sourceRight : Nat
  targetLeft : Nat
  targetRight : Nat
  sourceLeft_le : sourceLeft ≤ tokenCount
  sourceRight_le : sourceRight ≤ tokenCount
  targetLeft_le : targetLeft ≤ tokenCount
  targetRight_le : targetRight ≤ tokenCount
  sourceLeft_entry : CompactFixedWidthEntry sourceBoundary tokenCount index sourceLeft
  sourceRight_entry : CompactFixedWidthEntry sourceBoundary tokenCount (index + 1) sourceRight
  targetLeft_entry : CompactFixedWidthEntry targetBoundary tokenCount (index + 1) targetLeft
  targetRight_entry : CompactFixedWidthEntry targetBoundary tokenCount (index + 2) targetRight
  row_eq : CompactAdditiveSyntaxTaskRowEq tokenTable width tokenCount
    sourceLeft sourceRight targetLeft targetRight

noncomputable def compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate
    (tokenTable width tokenCount targetBoundary headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (hheadKindValue : ∀ valuation, termValue valuation headKindTerm = headKind)
    (hheadBinderArityValue : ∀ valuation,
      termValue valuation headBinderArityTerm = headBinderArity)
    (hheadRepeatCountValue : ∀ valuation,
      termValue valuation headRepeatCountTerm = headRepeatCount)
    (data : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width tokenCount targetBoundary
      headKind headBinderArity headRepeatCount) : HybridCertificate zeroValuation
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody tokenTable width tokenCount
        targetBoundary headKindTerm headBinderArityTerm headRepeatCountTerm) := by
  let values : Fin 2 -> Nat := ![data.targetRight, data.targetLeft]
  have hvalueTerms : (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
      ![shortBinaryNumeralTerm data.targetRight, shortBinaryNumeralTerm data.targetLeft] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminalParts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactFixedWidthEntryAtValuationExplicitHybridCertificate zeroValuation
      (shortBinaryNumeralTerm targetBoundary) (shortBinaryNumeralTerm tokenCount)
      (unaryNumeralTerm 0) (shortBinaryNumeralTerm data.targetLeft) (by
        simpa [termValue_shortBinaryNumeralTerm, termValue_unaryNumeralTerm]
          using data.targetLeft_entry))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate zeroValuation
        (shortBinaryNumeralTerm targetBoundary) (shortBinaryNumeralTerm tokenCount)
        (unaryNumeralTerm 1) (shortBinaryNumeralTerm data.targetRight) (by
          simpa [termValue_shortBinaryNumeralTerm, termValue_unaryNumeralTerm]
            using data.targetRight_entry))
      (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout tokenTable
        width tokenCount data.targetLeft data.targetRight headKind headBinderArity
          headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm
            hheadKindValue hheadBinderArityValue hheadRepeatCountValue data.layout))
  let terminal : HybridCertificate zeroValuation
      ((compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal tokenTable width tokenCount
        targetBoundary headKindTerm headBinderArityTerm headRepeatCountTerm) ⇜
          fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_substitution_alignment
          tokenTable width tokenCount targetBoundary data.targetLeft data.targetRight
            headKindTerm headBinderArityTerm headRepeatCountTerm).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal tokenTable width tokenCount
      targetBoundary headKindTerm headBinderArityTerm headRepeatCountTerm) values (by
        intro coordinate
        fin_cases coordinate
        · exact data.targetRight_le
        · exact data.targetLeft_le) terminal
  exact .cast (by rfl) installed

noncomputable def compactAdditiveSyntaxTaskListConsRowsHeadCertificate
    (tokenTable width tokenCount targetBoundary headKind headBinderArity headRepeatCount : Nat)
    (data : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width tokenCount targetBoundary
      headKind headBinderArity headRepeatCount) : HybridCertificate zeroValuation
      (compactAdditiveSyntaxTaskListConsRowsHeadBody tokenTable width tokenCount targetBoundary
        headKind headBinderArity headRepeatCount) := by
  simpa [compactAdditiveSyntaxTaskListConsRowsHeadBody] using
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate tokenTable width
      tokenCount targetBoundary headKind headBinderArity headRepeatCount
        (shortBinaryNumeralTerm headKind) (shortBinaryNumeralTerm headBinderArity)
          (shortBinaryNumeralTerm headRepeatCount)
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm]) data

noncomputable def compactAdditiveSyntaxTaskListConsRowsTailBranchCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width tokenCount sourceBoundary
      targetBoundary index) : HybridCertificate (extendValuation index zeroValuation)
      (Rewriting.free (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary)) := by
  let valuation := extendValuation index zeroValuation
  let values : Fin 4 -> Nat := ![data.targetRight, data.targetLeft, data.sourceRight, data.sourceLeft]
  have hvalueTerms : (fun coordinate : Fin 4 => shortBinaryNumeralTerm (values coordinate)) =
      ![shortBinaryNumeralTerm data.targetRight, shortBinaryNumeralTerm data.targetLeft,
        shortBinaryNumeralTerm data.sourceRight, shortBinaryNumeralTerm data.sourceLeft] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminalParts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm sourceBoundary) (shortBinaryNumeralTerm tokenCount)
      (&0 : ValuationTerm) (shortBinaryNumeralTerm data.sourceLeft) (by
        simpa [valuation, zeroValuation, termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.sourceLeft_entry))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
        (shortBinaryNumeralTerm sourceBoundary) (shortBinaryNumeralTerm tokenCount)
        (‘&0 + 1’ : ValuationTerm) (shortBinaryNumeralTerm data.sourceRight) (by
          simpa [valuation, zeroValuation, termValue_shortBinaryNumeralTerm,
            termValue_arithmeticAdd, termValue_arithmeticOne,
            FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
            using data.sourceRight_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          (shortBinaryNumeralTerm targetBoundary) (shortBinaryNumeralTerm tokenCount)
          (‘&0 + 1’ : ValuationTerm) (shortBinaryNumeralTerm data.targetLeft) (by
            simpa [valuation, zeroValuation, termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne,
              FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
              using data.targetLeft_entry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
            (shortBinaryNumeralTerm targetBoundary) (shortBinaryNumeralTerm tokenCount)
            (‘&0 + 2’ : ValuationTerm) (shortBinaryNumeralTerm data.targetRight) (by
              simpa [valuation, zeroValuation, termValue_shortBinaryNumeralTerm,
                termValue_arithmeticAdd, termValue_arithmeticTwo,
                FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
                using data.targetRight_entry))
          (compactAdditiveSyntaxTaskRowEqExplicitHybridCertificateOfGraph valuation tokenTable width
            tokenCount data.sourceLeft data.sourceRight data.targetLeft data.targetRight data.row_eq))))
  let terminal : HybridCertificate valuation
      ((compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal tokenTable width tokenCount
        sourceBoundary targetBoundary) ⇜ fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact (compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal_substitution_alignment
        tokenTable width tokenCount sourceBoundary targetBoundary data.sourceLeft data.sourceRight
        data.targetLeft data.targetRight).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
    (compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary) values (by
        intro coordinate
        fin_cases coordinate
        · exact data.targetRight_le
        · exact data.targetLeft_le
        · exact data.sourceRight_le
        · exact data.sourceLeft_le) terminal
  exact .cast (compactAdditiveSyntaxTaskListConsRowsTailBody_free_alignment tokenTable width tokenCount
    sourceBoundary targetBoundary).symm installed

noncomputable def compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranchesAtCount
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) -> CompactAdditiveSyntaxTaskListConsTailRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    CheckedHybridValuationUniversalBranches zeroValuation
      (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary) sourceCount :=
  buildExplicitHybridUniversalBranches sourceCount (fun index hindex =>
    compactAdditiveSyntaxTaskListConsRowsTailBranchCertificate tokenTable width tokenCount
      sourceBoundary targetBoundary index (rows ⟨index, hindex⟩))

theorem compactAdditiveSyntaxTaskListConsRowsShortNumeralBound_eq_sourceCount
    (sourceCount : Nat) :
    termValue zeroValuation (shortBinaryNumeralTerm sourceCount) = sourceCount := by
  exact termValue_shortBinaryNumeralTerm zeroValuation sourceCount

noncomputable def compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranches
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) -> CompactAdditiveSyntaxTaskListConsTailRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    CheckedHybridValuationUniversalBranches zeroValuation
      (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary)
      (termValue zeroValuation (shortBinaryNumeralTerm sourceCount)) :=
  (compactAdditiveSyntaxTaskListConsRowsShortNumeralBound_eq_sourceCount
    sourceCount).symm ▸
      compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranchesAtCount
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows

noncomputable def compactAdditiveSyntaxTaskListConsRowsTailUniversalCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) -> CompactAdditiveSyntaxTaskListConsTailRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    HybridCertificate zeroValuation
      ((compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary).ballLT (shortBinaryNumeralTerm sourceCount)) := by
  let body := compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let branches := compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranches
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  let direct := CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
    (shortBinaryNumeralTerm sourceCount) body branches
  exact .cast (by
    change (∀⁰ termBoundedUniversalBody (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body) =
      body.ballLT (shortBinaryNumeralTerm sourceCount)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

noncomputable def
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataExplicitHybridCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (hheadKindValue : ∀ valuation, termValue valuation headKindTerm = headKind)
    (hheadBinderArityValue : ∀ valuation,
      termValue valuation headBinderArityTerm = headBinderArity)
    (hheadRepeatCountValue : ∀ valuation,
      termValue valuation headRepeatCountTerm = headRepeatCount)
    (hcount : targetCount = sourceCount + 1)
    (headData : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width tokenCount targetBoundary
      headKind headBinderArity headRepeatCount)
    (tailRows : (index : Fin sourceCount) -> CompactAdditiveSyntaxTaskListConsTailRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    HybridCertificate zeroValuation
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount headKindTerm headBinderArityTerm
          headRepeatCountTerm) := by
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (countEqualityCertificate sourceCount targetCount hcount)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate tokenTable width
        tokenCount targetBoundary headKind headBinderArity headRepeatCount headKindTerm
          headBinderArityTerm headRepeatCountTerm hheadKindValue hheadBinderArityValue
            hheadRepeatCountValue headData)
      (compactAdditiveSyntaxTaskListConsRowsTailUniversalCertificate tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary tailRows))
  exact .cast
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula_alignment tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary targetCount headKindTerm
        headBinderArityTerm headRepeatCountTerm).symm parts

noncomputable def compactAdditiveSyntaxTaskListConsRowsFromDataExplicitHybridCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      headKind headBinderArity headRepeatCount : Nat)
    (hcount : targetCount = sourceCount + 1)
    (headData : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width tokenCount targetBoundary
      headKind headBinderArity headRepeatCount)
    (tailRows : (index : Fin sourceCount) -> CompactAdditiveSyntaxTaskListConsTailRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    HybridCertificate zeroValuation
      (compactAdditiveSyntaxTaskListConsRowsClosedFormula tokenTable width tokenCount sourceBoundary
        sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount) := by
  simpa [compactAdditiveSyntaxTaskListConsRowsClosedFormula] using
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataExplicitHybridCertificate
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount headKind
        headBinderArity headRepeatCount (shortBinaryNumeralTerm headKind)
          (shortBinaryNumeralTerm headBinderArity) (shortBinaryNumeralTerm headRepeatCount)
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm]) hcount headData tailRows

noncomputable def compactAdditiveSyntaxTaskListConsRowsHeadDataOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount) :
    CompactAdditiveSyntaxTaskListConsHeadData tokenTable width tokenCount targetBoundary
      headKind headBinderArity headRepeatCount := by
  let targetLeftExists := hgraph.2.1
  let targetLeft := Classical.choose targetLeftExists
  have htargetLeft := Classical.choose_spec targetLeftExists
  let targetRightExists := htargetLeft.2
  let targetRight := Classical.choose targetRightExists
  have htargetRight := Classical.choose_spec targetRightExists
  exact
    { targetLeft := targetLeft
      targetRight := targetRight
      targetLeft_le := htargetLeft.1
      targetRight_le := htargetRight.1
      targetLeft_entry := htargetRight.2.1
      targetRight_entry := htargetRight.2.2.1
      layout := htargetRight.2.2.2 }

noncomputable def compactAdditiveSyntaxTaskListConsRowsTailRowDataOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount)
    (index : Fin sourceCount) :
    CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index := by
  let sourceLeftExists := hgraph.2.2 index index.isLt
  let sourceLeft := Classical.choose sourceLeftExists
  have hsourceLeft := Classical.choose_spec sourceLeftExists
  let sourceRightExists := hsourceLeft.2
  let sourceRight := Classical.choose sourceRightExists
  have hsourceRight := Classical.choose_spec sourceRightExists
  let targetLeftExists := hsourceRight.2
  let targetLeft := Classical.choose targetLeftExists
  have htargetLeft := Classical.choose_spec targetLeftExists
  let targetRightExists := htargetLeft.2
  let targetRight := Classical.choose targetRightExists
  have htargetRight := Classical.choose_spec targetRightExists
  exact
    { sourceLeft := sourceLeft
      sourceRight := sourceRight
      targetLeft := targetLeft
      targetRight := targetRight
      sourceLeft_le := hsourceLeft.1
      sourceRight_le := hsourceRight.1
      targetLeft_le := htargetLeft.1
      targetRight_le := htargetRight.1
      sourceLeft_entry := htargetRight.2.1
      sourceRight_entry := htargetRight.2.2.1
      targetLeft_entry := htargetRight.2.2.2.1
      targetRight_entry := htargetRight.2.2.2.2.1
      row_eq := htargetRight.2.2.2.2.2 }

noncomputable def
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (hheadKindValue : ∀ valuation, termValue valuation headKindTerm = headKind)
    (hheadBinderArityValue : ∀ valuation,
      termValue valuation headBinderArityTerm = headBinderArity)
    (hheadRepeatCountValue : ∀ valuation,
      termValue valuation headRepeatCountTerm = headRepeatCount)
    (hgraph : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount) :
    HybridCertificate zeroValuation
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount headKindTerm headBinderArityTerm
          headRepeatCountTerm) :=
  compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataExplicitHybridCertificate tokenTable
    width tokenCount sourceBoundary sourceCount targetBoundary targetCount headKind headBinderArity
      headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm hheadKindValue
        hheadBinderArityValue hheadRepeatCountValue hgraph.1
    (compactAdditiveSyntaxTaskListConsRowsHeadDataOfGraph tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount headKind headBinderArity
      headRepeatCount hgraph)
    (compactAdditiveSyntaxTaskListConsRowsTailRowDataOfGraph tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount headKind headBinderArity
      headRepeatCount hgraph)

noncomputable def compactAdditiveSyntaxTaskListConsRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount) :
    HybridCertificate zeroValuation
      (compactAdditiveSyntaxTaskListConsRowsClosedFormula tokenTable width tokenCount sourceBoundary
        sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount) := by
  simpa [compactAdditiveSyntaxTaskListConsRowsClosedFormula] using
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount headKind
        headBinderArity headRepeatCount (shortBinaryNumeralTerm headKind)
          (shortBinaryNumeralTerm headBinderArity) (shortBinaryNumeralTerm headRepeatCount)
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm]) hgraph

noncomputable def compileCompactAdditiveSyntaxTaskListConsRowsExplicitHybridContext
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount) :
    CertifiedPAContextProof
      (valuationContext
        (compactAdditiveSyntaxTaskListConsRowsClosedFormula tokenTable width tokenCount sourceBoundary
          sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount).freeVariables
        zeroValuation)
      (compactAdditiveSyntaxTaskListConsRowsClosedFormula tokenTable width tokenCount sourceBoundary
        sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount) :=
  (compactAdditiveSyntaxTaskListConsRowsExplicitHybridCertificateOfGraph tokenTable width tokenCount
    sourceBoundary sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount hgraph).compile

noncomputable def compactAdditiveSyntaxTaskListConsRowsExplicitStructuralResource
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactAdditiveSyntaxTaskListConsRowsExplicitHybridCertificateOfGraph tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount hgraph)

theorem compileCompactAdditiveSyntaxTaskListConsRowsExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount) :
    (compileCompactAdditiveSyntaxTaskListConsRowsExplicitHybridContext tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount
        hgraph).payloadLength ≤
      compactAdditiveSyntaxTaskListConsRowsExplicitStructuralResource tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount
          hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactAdditiveSyntaxTaskListConsRowsExplicitHybridCertificateOfGraph tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount headKind headBinderArity headRepeatCount hgraph)

#print axioms compactAdditiveSyntaxTaskListConsRowsClosedFormula_alignment
#print axioms compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula_alignment
#print axioms
  compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
#print axioms compactAdditiveSyntaxTaskListConsRowsExplicitHybridCertificateOfGraph
#print axioms compileCompactAdditiveSyntaxTaskListConsRowsExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
