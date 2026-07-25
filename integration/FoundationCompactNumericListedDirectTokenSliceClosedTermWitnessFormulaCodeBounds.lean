import integration.FoundationCompactNumericListedDirectTokenSliceClosedTermLeafFixedBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds
import integration.FoundationCompactPAFreeFormulaVariableTransport

/-!
# Formula-code bounds for the closed-term token-slice witness shell

The witness body is exhibited as a uniform rewriting of one fixed eight-place
formula.  This gives direct code bounds for the body and its existential
closure without treating either formula length as an input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceClosedTermWitnessFormulaCodeBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactPAFreeFormulaVariableTransport
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate

def tokenSliceClosedTermWitnessFormulaSeed :
    LO.FirstOrder.ArithmeticSemiformula Nat 8 :=
  “#0 < #3 + 1 ∧
    #5 = #4 + #0 ∧
    #7 = #6 + #0 ∧
    #5 ≤ #3 ∧
    #7 ≤ #3 ∧
    ∀ offset < #0,
      ∀ bitIndex < #3,
        (!bitDef (((#6 + offset) * #4 + bitIndex)) #3 ↔
          !bitDef (((#8 + offset) * #4 + bitIndex)) #3)”

private theorem tokenSliceClosedTerm_rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      rewriting.comp
          ((Rew.subst terms).comp
            (Rew.emb : Rew ℒₒᵣ Empty predicateArity sourceVariables
              predicateArity)) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity targetVariables
            predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity sourceVariables
            predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity targetVariables
            predicateArity)) ▹ formula := by
      exact congrArg (fun candidate => candidate ▹ formula) hcomposition
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem tokenSliceClosedTerm_rewriting_formulaOperator
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
  exact tokenSliceClosedTerm_rewriting_embeddedFormulaSubstitution
    rewriting operator.sentence terms

private theorem tokenSliceClosedTerm_rewriting_ballLT
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
  rw [Rewriting.smul_ball,
    tokenSliceClosedTerm_rewriting_formulaOperator, hguardTerms]

private def tokenSliceClosedTermBodyTerms
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    Fin 8 -> LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
    Rew.bShift tokenTableTerm, Rew.bShift widthTerm,
    Rew.bShift tokenCountTerm, Rew.bShift sourceStartTerm,
    Rew.bShift sourceFinishTerm, Rew.bShift targetStartTerm,
    Rew.bShift targetFinishTerm]

private def tokenSliceClosedTermOffsetTerms
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    Fin 9 -> LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2), #1,
    Rew.bShift (Rew.bShift tokenTableTerm),
    Rew.bShift (Rew.bShift widthTerm),
    Rew.bShift (Rew.bShift tokenCountTerm),
    Rew.bShift (Rew.bShift sourceStartTerm),
    Rew.bShift (Rew.bShift sourceFinishTerm),
    Rew.bShift (Rew.bShift targetStartTerm),
    Rew.bShift (Rew.bShift targetFinishTerm)]

private def tokenSliceClosedTermBitTerms
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    Fin 10 -> LO.FirstOrder.ArithmeticSemiterm Nat 3 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 3), #1, #2,
    Rew.bShift (Rew.bShift (Rew.bShift tokenTableTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift widthTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift tokenCountTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift sourceStartTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift sourceFinishTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift targetStartTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift targetFinishTerm))]

private def tokenSliceClosedTermBodyRewriting
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    Rew ℒₒᵣ Nat 8 Nat 1 :=
  Rew.bind
    (tokenSliceClosedTermBodyTerms tokenTableTerm widthTerm tokenCountTerm
      sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm)
    (fun index => &index)

private theorem tokenSliceClosedTermBodyRewriting_q_eq
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    (tokenSliceClosedTermBodyRewriting tokenTableTerm widthTerm tokenCountTerm
      sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm).q =
      Rew.bind
        (tokenSliceClosedTermOffsetTerms tokenTableTerm widthTerm tokenCountTerm
          sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm)
        (fun index => &index) := by
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        simp [tokenSliceClosedTermBodyRewriting,
          tokenSliceClosedTermBodyTerms, tokenSliceClosedTermOffsetTerms,
          Rew.q_bvar_zero]
    | succ coordinate =>
        simp only [Rew.q_bvar_succ, Rew.bind_bvar]
        fin_cases coordinate <;> rfl
  · simp [tokenSliceClosedTermBodyRewriting]

private theorem tokenSliceClosedTermBodyRewriting_qq_eq
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    (tokenSliceClosedTermBodyRewriting tokenTableTerm widthTerm tokenCountTerm
      sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm).q.q =
      Rew.bind
        (tokenSliceClosedTermBitTerms tokenTableTerm widthTerm tokenCountTerm
          sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm)
        (fun index => &index) := by
  rw [tokenSliceClosedTermBodyRewriting_q_eq]
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        simp [tokenSliceClosedTermOffsetTerms, tokenSliceClosedTermBitTerms,
          Rew.q_bvar_zero]
    | succ coordinate =>
        simp only [Rew.q_bvar_succ, Rew.bind_bvar]
        fin_cases coordinate <;> rfl
  · simp

theorem tokenSliceClosedTermWitnessFormulaSeed_rewrite
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    tokenSliceClosedTermBodyRewriting tokenTableTerm widthTerm tokenCountTerm
        sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm ▹
        tokenSliceClosedTermWitnessFormulaSeed =
      tokenSliceAtValuationWitnessBody tokenTableTerm widthTerm tokenCountTerm
        sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm := by
  unfold tokenSliceClosedTermWitnessFormulaSeed
    tokenSliceAtValuationWitnessBody
  simp only [LogicalConnective.HomClass.map_and,
    tokenSliceClosedTerm_rewriting_ballLT]
  rw [tokenSliceClosedTermBodyRewriting_qq_eq,
    tokenSliceClosedTermBodyRewriting_q_eq]
  simp [tokenSliceClosedTermBodyRewriting, tokenSliceClosedTermBodyTerms,
    tokenSliceClosedTermOffsetTerms, tokenSliceClosedTermBitTerms,
    tokenSliceClosedTerm_rewriting_embeddedFormulaSubstitution]

def tokenSliceClosedTermWitnessImageCodePolynomial (termCode : Nat) : Nat :=
  3 * termCode +
    (binaryTermCode (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length + 1

private theorem tokenSliceClosedTerm_bShift_code_le
    (term : ValuationTerm) (termCode : Nat)
    (hterm : (binaryTermCode term).length <= termCode) :
    (binaryTermCode
      (Rew.bShift term : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <=
      tokenSliceClosedTermWitnessImageCodePolynomial termCode := by
  have hshift := binaryTermCode_bShift_length_le_add_symbols term
  have hsymbols := termSymbolCount_le_binaryTermCode_length term
  unfold tokenSliceClosedTermWitnessImageCodePolynomial
  omega

private theorem tokenSliceClosedTermBodyRewriting_imageCodeBound
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (termCode : Nat)
    (htable : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidth : (binaryTermCode widthTerm).length <= termCode)
    (htokenCount : (binaryTermCode tokenCountTerm).length <= termCode)
    (hsourceStart : (binaryTermCode sourceStartTerm).length <= termCode)
    (hsourceFinish : (binaryTermCode sourceFinishTerm).length <= termCode)
    (htargetStart : (binaryTermCode targetStartTerm).length <= termCode)
    (htargetFinish : (binaryTermCode targetFinishTerm).length <= termCode) :
    RewritingImageCodeBound
      (tokenSliceClosedTermBodyRewriting tokenTableTerm widthTerm tokenCountTerm
        sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm)
      (tokenSliceClosedTermWitnessImageCodePolynomial termCode) := by
  constructor
  · intro coordinate
    fin_cases coordinate
    · change
        (binaryTermCode
          (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <= _
      unfold tokenSliceClosedTermWitnessImageCodePolynomial
      omega
    · simpa [tokenSliceClosedTermBodyRewriting,
        tokenSliceClosedTermBodyTerms] using
        tokenSliceClosedTerm_bShift_code_le tokenTableTerm termCode htable
    · simpa [tokenSliceClosedTermBodyRewriting,
        tokenSliceClosedTermBodyTerms] using
        tokenSliceClosedTerm_bShift_code_le widthTerm termCode hwidth
    · simpa [tokenSliceClosedTermBodyRewriting,
        tokenSliceClosedTermBodyTerms] using
        tokenSliceClosedTerm_bShift_code_le tokenCountTerm termCode htokenCount
    · simpa [tokenSliceClosedTermBodyRewriting,
        tokenSliceClosedTermBodyTerms] using
        tokenSliceClosedTerm_bShift_code_le sourceStartTerm termCode hsourceStart
    · simpa [tokenSliceClosedTermBodyRewriting,
        tokenSliceClosedTermBodyTerms] using
        tokenSliceClosedTerm_bShift_code_le sourceFinishTerm termCode
          hsourceFinish
    · simpa [tokenSliceClosedTermBodyRewriting,
        tokenSliceClosedTermBodyTerms] using
        tokenSliceClosedTerm_bShift_code_le targetStartTerm termCode htargetStart
    · simpa [tokenSliceClosedTermBodyRewriting,
        tokenSliceClosedTermBodyTerms] using
        tokenSliceClosedTerm_bShift_code_le targetFinishTerm termCode
          htargetFinish
  · intro coordinate
    simp [tokenSliceClosedTermBodyRewriting]

def tokenSliceClosedTermWitnessBodyCodePolynomial (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (tokenSliceClosedTermWitnessImageCodePolynomial termCode)
    (binaryFormulaCode tokenSliceClosedTermWitnessFormulaSeed).length

theorem tokenSliceAtValuationWitnessBody_code_length_le_closedFixed
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (termCode : Nat)
    (htable : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidth : (binaryTermCode widthTerm).length <= termCode)
    (htokenCount : (binaryTermCode tokenCountTerm).length <= termCode)
    (hsourceStart : (binaryTermCode sourceStartTerm).length <= termCode)
    (hsourceFinish : (binaryTermCode sourceFinishTerm).length <= termCode)
    (htargetStart : (binaryTermCode targetStartTerm).length <= termCode)
    (htargetFinish : (binaryTermCode targetFinishTerm).length <= termCode) :
    (binaryFormulaCode
      (tokenSliceAtValuationWitnessBody tokenTableTerm widthTerm tokenCountTerm
        sourceStartTerm sourceFinishTerm targetStartTerm
        targetFinishTerm)).length <=
      tokenSliceClosedTermWitnessBodyCodePolynomial termCode := by
  have hraw := binaryFormulaCode_rewriting_length_le_uniform
    (tokenSliceClosedTermBodyRewriting tokenTableTerm widthTerm tokenCountTerm
      sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm)
    (tokenSliceClosedTermWitnessImageCodePolynomial termCode)
    (tokenSliceClosedTermBodyRewriting_imageCodeBound tokenTableTerm widthTerm
      tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm termCode htable hwidth htokenCount hsourceStart
      hsourceFinish htargetStart htargetFinish)
    tokenSliceClosedTermWitnessFormulaSeed
  rw [tokenSliceClosedTermWitnessFormulaSeed_rewrite] at hraw
  exact hraw

def tokenSliceClosedTermExistentialFormulaCodePolynomial
    (termCode : Nat) : Nat :=
  tokenSliceClosedTermWitnessBodyCodePolynomial termCode + 8

theorem tokenSliceAtValuationExistentialFormula_code_length_le_closedFixed
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (termCode : Nat)
    (htable : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidth : (binaryTermCode widthTerm).length <= termCode)
    (htokenCount : (binaryTermCode tokenCountTerm).length <= termCode)
    (hsourceStart : (binaryTermCode sourceStartTerm).length <= termCode)
    (hsourceFinish : (binaryTermCode sourceFinishTerm).length <= termCode)
    (htargetStart : (binaryTermCode targetStartTerm).length <= termCode)
    (htargetFinish : (binaryTermCode targetFinishTerm).length <= termCode) :
    (binaryFormulaCode
      (∃⁰ tokenSliceAtValuationWitnessBody tokenTableTerm widthTerm
        tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
        targetFinishTerm : ValuationFormula)).length <=
      tokenSliceClosedTermExistentialFormulaCodePolynomial termCode := by
  have hbody := tokenSliceAtValuationWitnessBody_code_length_le_closedFixed
    tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
    targetStartTerm targetFinishTerm termCode htable hwidth htokenCount
    hsourceStart hsourceFinish htargetStart htargetFinish
  have hexists := binaryFormulaCode_exs_length_le
    (tokenSliceAtValuationWitnessBody tokenTableTerm widthTerm tokenCountTerm
      sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm)
  unfold tokenSliceClosedTermExistentialFormulaCodePolynomial
  omega

def tokenSliceClosedTermPostWitnessFormulaCodePolynomial
    (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (tokenSliceClosedTermWitnessBodyCodePolynomial termCode)

private theorem tokenSliceClosedTermWitnessSubstitution_imageCodeBound
    (count termCode : Nat)
    (hcount :
      (binaryTermCode (shortBinaryNumeralTerm count)).length <= termCode) :
    RewritingImageCodeBound (Rew.subst ![shortBinaryNumeralTerm count])
      termCode := by
  constructor
  · intro coordinate
    fin_cases coordinate
    change
      (binaryTermCode (shortBinaryNumeralTerm count)).length <= termCode
    exact hcount
  · intro coordinate
    simp

theorem tokenSliceAtValuationPostWitnessFormula_code_length_le_closedFixed
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count termCode : Nat)
    (htable : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidth : (binaryTermCode widthTerm).length <= termCode)
    (htokenCount : (binaryTermCode tokenCountTerm).length <= termCode)
    (hsourceStart : (binaryTermCode sourceStartTerm).length <= termCode)
    (hsourceFinish : (binaryTermCode sourceFinishTerm).length <= termCode)
    (htargetStart : (binaryTermCode targetStartTerm).length <= termCode)
    (htargetFinish : (binaryTermCode targetFinishTerm).length <= termCode)
    (hcount :
      (binaryTermCode (shortBinaryNumeralTerm count)).length <= termCode) :
    (binaryFormulaCode
      (tokenSliceAtValuationPostWitnessFormula tokenTableTerm widthTerm
        tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
        targetFinishTerm count)).length <=
      tokenSliceClosedTermPostWitnessFormulaCodePolynomial termCode := by
  let body := tokenSliceAtValuationWitnessBody tokenTableTerm widthTerm
    tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
    targetFinishTerm
  have hbody := tokenSliceAtValuationWitnessBody_code_length_le_closedFixed
    tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
    targetStartTerm targetFinishTerm termCode htable hwidth htokenCount
    hsourceStart hsourceFinish htargetStart htargetFinish
  have hraw := binaryFormulaCode_rewriting_length_le_uniform
    (Rew.subst ![shortBinaryNumeralTerm count]) termCode
    (tokenSliceClosedTermWitnessSubstitution_imageCodeBound count termCode
      hcount) body
  have hmono :=
    uniformRewritingFormulaCodeEnvelope_mono_formula termCode hbody
  unfold tokenSliceAtValuationPostWitnessFormula
    tokenSliceClosedTermPostWitnessFormulaCodePolynomial
  simpa only [body] using hraw.trans hmono

#print axioms tokenSliceClosedTermWitnessFormulaSeed_rewrite
#print axioms tokenSliceAtValuationWitnessBody_code_length_le_closedFixed
#print axioms
  tokenSliceAtValuationExistentialFormula_code_length_le_closedFixed
#print axioms
  tokenSliceAtValuationPostWitnessFormula_code_length_le_closedFixed

end FoundationCompactNumericListedDirectTokenSliceClosedTermWitnessFormulaCodeBounds
