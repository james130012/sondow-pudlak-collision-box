import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for a quantified syntax-formula transition

The task head keeps the original native kind/repeat numerals and the original
`binderArity + 1` term.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left : ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
      ArithmeticSemiformula targetVariables targetArity) = Rewriting.app right := by
  cases h
  rfl

def nativeNumeralTerm (value : Nat) : ValuationTerm :=
  (Semiterm.Operator.numeral ℒₒᵣ value : Semiterm.Const ℒₒᵣ)

@[simp] theorem termValue_nativeNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (nativeNumeralTerm value) = value := by
  unfold termValue nativeNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘ (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) =
        (![] : Fin 0 -> Nat) by
      funext index
      exact Fin.elim0 index]
  simp

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 :=
  termValue_one valuation ![]

def binderSuccessorTerm (binderArity : Nat) : ValuationTerm :=
  ‘!!(shortBinaryNumeralTerm binderArity) + 1’

@[simp] theorem termValue_binderSuccessorTerm
    (valuation : Nat -> Nat) (binderArity : Nat) :
    termValue valuation (binderSuccessorTerm binderArity) = binderArity + 1 := by
  simp [binderSuccessorTerm, termValue_arithmeticAdd, termValue_arithmeticOne,
    termValue_shortBinaryNumeralTerm]

def compactUnifiedParserSyntaxFormulaQuantifierClosedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserSyntaxFormulaQuantifierRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm current.start,
      shortBinaryNumeralTerm current.finish, shortBinaryNumeralTerm current.tokensFinish,
      shortBinaryNumeralTerm current.tasksFinish,
      shortBinaryNumeralTerm current.tokensBoundary,
      shortBinaryNumeralTerm current.tokensCount,
      shortBinaryNumeralTerm current.tasksBoundary,
      shortBinaryNumeralTerm current.tasksCount, shortBinaryNumeralTerm next.start,
      shortBinaryNumeralTerm next.finish, shortBinaryNumeralTerm next.tokensFinish,
      shortBinaryNumeralTerm next.tasksFinish,
      shortBinaryNumeralTerm next.tokensBoundary,
      shortBinaryNumeralTerm next.tokensCount,
      shortBinaryNumeralTerm next.tasksBoundary,
      shortBinaryNumeralTerm next.tasksCount,
      shortBinaryNumeralTerm tailBoundary, shortBinaryNumeralTerm tailCount,
      shortBinaryNumeralTerm binderArity]

def compactUnifiedParserSyntaxFormulaQuantifierExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) : ValuationFormula :=
  compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
      next.tasksFinish next.finish ⋏
    (FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveNatListDropFixedNumeralRowsClosedFormula
        tokenTable width tokenCount current.tokensBoundary current.tokensCount next.tokensBoundary
          next.tokensCount 1 ⋏
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable width tokenCount
        tailBoundary tailCount next.tasksBoundary next.tasksCount (nativeNumeralTerm 1)
          (binderSuccessorTerm binderArity) (nativeNumeralTerm 0))

theorem compactUnifiedParserSyntaxFormulaQuantifierClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) :
    compactUnifiedParserSyntaxFormulaQuantifierClosedFormula tokenTable width tokenCount current next
        tailBoundary tailCount binderArity =
      compactUnifiedParserSyntaxFormulaQuantifierExplicitFormula tokenTable width tokenCount current
        next tailBoundary tailCount binderArity := by
  unfold compactUnifiedParserSyntaxFormulaQuantifierClosedFormula
  unfold compactUnifiedParserSyntaxFormulaQuantifierExplicitFormula
  unfold compactUnifiedParserSyntaxFormulaQuantifierRowsDef
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  unfold FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveNatListDropFixedNumeralRowsClosedFormula
  unfold compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
  unfold binderSuccessorTerm
  simp [nativeNumeralTerm,
    FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
    ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
  all_goals
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

noncomputable def
    compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable width tokenCount current next
      tailBoundary tailCount binderArity) :
    HybridCertificate
      (compactUnifiedParserSyntaxFormulaQuantifierClosedFormula tokenTable width tokenCount current
        next tailBoundary tailCount binderArity) := by
  rcases hgraph with ⟨hrunning, htokens, htasks⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph tokenTable width tokenCount
      next.tasksFinish next.finish hrunning)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.tokensBoundary current.tokensCount next.tokensBoundary
          next.tokensCount 1 htokens)
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary next.tasksCount
          1 (binderArity + 1) 0 (nativeNumeralTerm 1) (binderSuccessorTerm binderArity)
            (nativeNumeralTerm 0) (fun valuation => by simp)
              (fun valuation => by simp) (fun valuation => by simp) htasks))
  exact .cast
    (compactUnifiedParserSyntaxFormulaQuantifierClosedFormula_alignment tokenTable width tokenCount
      current next tailBoundary tailCount binderArity).symm parts

noncomputable def compileCompactUnifiedParserSyntaxFormulaQuantifierExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable width tokenCount current next
      tailBoundary tailCount binderArity) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserSyntaxFormulaQuantifierClosedFormula tokenTable width tokenCount current
          next tailBoundary tailCount binderArity).freeVariables zeroValuation)
      (compactUnifiedParserSyntaxFormulaQuantifierClosedFormula tokenTable width tokenCount current
        next tailBoundary tailCount binderArity) :=
  (compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph tokenTable width
    tokenCount current next tailBoundary tailCount binderArity hgraph).compile

noncomputable def compactUnifiedParserSyntaxFormulaQuantifierExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable width tokenCount current next
      tailBoundary tailCount binderArity) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph tokenTable width
      tokenCount current next tailBoundary tailCount binderArity hgraph)

theorem compileCompactUnifiedParserSyntaxFormulaQuantifierExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable width tokenCount current next
      tailBoundary tailCount binderArity) :
    (compileCompactUnifiedParserSyntaxFormulaQuantifierExplicitHybridContext tokenTable width
      tokenCount current next tailBoundary tailCount binderArity hgraph).payloadLength ≤
      compactUnifiedParserSyntaxFormulaQuantifierExplicitStructuralResource tokenTable width
        tokenCount current next tailBoundary tailCount binderArity hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph tokenTable width
      tokenCount current next tailBoundary tailCount binderArity hgraph)

#print axioms compactUnifiedParserSyntaxFormulaQuantifierClosedFormula_alignment
#print axioms compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
#print axioms compileCompactUnifiedParserSyntaxFormulaQuantifierExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate
