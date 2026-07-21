import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for a binary syntax-formula transition

The original native numerals `0`, `1`, and `2` are retained in the exact
22-coordinate formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate

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
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate

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

def compactUnifiedParserSyntaxFormulaBinaryClosedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserSyntaxFormulaBinaryRowsDef.val) ⇜
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

def compactUnifiedParserSyntaxFormulaBinaryExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) : ValuationFormula :=
  compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
      next.tasksFinish next.finish ⋏
    (FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveNatListDropFixedNumeralRowsClosedFormula
        tokenTable width tokenCount current.tokensBoundary current.tokensCount next.tokensBoundary
          next.tokensCount 1 ⋏
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
          tokenTable width tokenCount next.tasksBoundary next.tasksCount tailBoundary tailCount 2 ⋏
        (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width tokenCount
            next.tasksBoundary next.tasksCount (nativeNumeralTerm 0) (nativeNumeralTerm 1)
              (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0) ⋏
          compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width tokenCount
            next.tasksBoundary next.tasksCount (nativeNumeralTerm 1) (nativeNumeralTerm 1)
              (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0))))

theorem compactUnifiedParserSyntaxFormulaBinaryClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) :
    compactUnifiedParserSyntaxFormulaBinaryClosedFormula tokenTable width tokenCount current next
        tailBoundary tailCount binderArity =
      compactUnifiedParserSyntaxFormulaBinaryExplicitFormula tokenTable width tokenCount current next
        tailBoundary tailCount binderArity := by
  unfold compactUnifiedParserSyntaxFormulaBinaryClosedFormula
  unfold compactUnifiedParserSyntaxFormulaBinaryExplicitFormula
  unfold compactUnifiedParserSyntaxFormulaBinaryRowsDef
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  unfold FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveNatListDropFixedNumeralRowsClosedFormula
  unfold FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula
  simp [nativeNumeralTerm,
    FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
    FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
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

noncomputable def compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable width tokenCount current next
      tailBoundary tailCount binderArity) :
    HybridCertificate
      (compactUnifiedParserSyntaxFormulaBinaryClosedFormula tokenTable width tokenCount current next
        tailBoundary tailCount binderArity) := by
  rcases hgraph with ⟨hrunning, htokens, hdrop, htaskZero, htaskOne⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph tokenTable width tokenCount
      next.tasksFinish next.finish hrunning)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.tokensBoundary current.tokensCount next.tokensBoundary
          next.tokensCount 1 htokens)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount next.tasksBoundary next.tasksCount tailBoundary tailCount 2 hdrop)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph
            tokenTable width tokenCount next.tasksBoundary next.tasksCount 0 1 binderArity 0
              (nativeNumeralTerm 0) (nativeNumeralTerm 1)
                (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0) (by simp)
                  (fun valuation => by simp) (fun valuation => by
                    simp [termValue_shortBinaryNumeralTerm]) (fun valuation => by simp) htaskZero)
          (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph
            tokenTable width tokenCount next.tasksBoundary next.tasksCount 1 1 binderArity 0
              (nativeNumeralTerm 1) (nativeNumeralTerm 1)
                (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0) (by simp)
                  (fun valuation => by simp) (fun valuation => by
                    simp [termValue_shortBinaryNumeralTerm]) (fun valuation => by simp) htaskOne))))
  exact .cast
    (compactUnifiedParserSyntaxFormulaBinaryClosedFormula_alignment tokenTable width tokenCount
      current next tailBoundary tailCount binderArity).symm parts

noncomputable def compileCompactUnifiedParserSyntaxFormulaBinaryExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable width tokenCount current next
      tailBoundary tailCount binderArity) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserSyntaxFormulaBinaryClosedFormula tokenTable width tokenCount current next
          tailBoundary tailCount binderArity).freeVariables zeroValuation)
      (compactUnifiedParserSyntaxFormulaBinaryClosedFormula tokenTable width tokenCount current next
        tailBoundary tailCount binderArity) :=
  (compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph tokenTable width tokenCount
    current next tailBoundary tailCount binderArity hgraph).compile

noncomputable def compactUnifiedParserSyntaxFormulaBinaryExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable width tokenCount current next
      tailBoundary tailCount binderArity) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph tokenTable width
      tokenCount current next tailBoundary tailCount binderArity hgraph)

theorem compileCompactUnifiedParserSyntaxFormulaBinaryExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable width tokenCount current next
      tailBoundary tailCount binderArity) :
    (compileCompactUnifiedParserSyntaxFormulaBinaryExplicitHybridContext tokenTable width tokenCount
      current next tailBoundary tailCount binderArity hgraph).payloadLength ≤
      compactUnifiedParserSyntaxFormulaBinaryExplicitStructuralResource tokenTable width tokenCount
        current next tailBoundary tailCount binderArity hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph tokenTable width
      tokenCount current next tailBoundary tailCount binderArity hgraph)

#print axioms compactUnifiedParserSyntaxFormulaBinaryClosedFormula_alignment
#print axioms compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph
#print axioms compileCompactUnifiedParserSyntaxFormulaBinaryExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
