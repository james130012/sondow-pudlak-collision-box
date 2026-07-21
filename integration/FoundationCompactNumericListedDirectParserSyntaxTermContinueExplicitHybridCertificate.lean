import integration.FoundationCompactNumericListedDirectParserSyntaxTermFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for continuing a syntax-term task

The consumed token count is kept as a native arithmetic numeral. This lets the
term and formula callers preserve their original `2` and `1` formula syntax.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate

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

def compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount consumed : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserSyntaxTermContinueRowsDef.val) ⇜
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
      fixedNumeralTerm consumed]

def compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount consumed : Nat) : ValuationFormula :=
  compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
      next.tasksFinish next.finish ⋏
    (compactAdditiveNatListDropFixedNumeralRowsClosedFormula tokenTable width tokenCount
        current.tokensBoundary current.tokensCount next.tokensBoundary next.tokensCount consumed ⋏
      compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width tokenCount
        tailBoundary tailCount next.tasksBoundary next.tasksCount)

theorem compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount consumed : Nat) :
    compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable width tokenCount
        current next tailBoundary tailCount consumed =
      compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitFormula tokenTable width tokenCount
        current next tailBoundary tailCount consumed := by
  unfold compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
  unfold compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitFormula
  unfold compactUnifiedParserSyntaxTermContinueRowsDef
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  unfold compactAdditiveNatListDropFixedNumeralRowsClosedFormula
  unfold compactAdditiveSyntaxTaskListSameRowsClosedFormula
  simp [fixedNumeralTerm, ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

noncomputable def
    compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateFromGraphData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount consumed : Nat)
    (hrunning : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListDropRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount consumed)
    (htasks : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      tailBoundary tailCount next.tasksBoundary next.tasksCount) :
    HybridCertificate
      (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable width tokenCount
        current next tailBoundary tailCount consumed) := by
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph tokenTable width tokenCount
      next.tasksFinish next.finish hrunning)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph tokenTable width
        tokenCount current.tokensBoundary current.tokensCount next.tokensBoundary next.tokensCount
          consumed htokens)
      (compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph tokenTable width
        tokenCount tailBoundary tailCount next.tasksBoundary next.tasksCount htasks))
  exact .cast
    (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula_alignment tokenTable width
      tokenCount current next tailBoundary tailCount consumed).symm parts

noncomputable def
    compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount consumed : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermContinueRows tokenTable width tokenCount current next
      tailBoundary tailCount consumed) :
    HybridCertificate
      (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable width tokenCount
        current next tailBoundary tailCount consumed) :=
  compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateFromGraphData
    tokenTable width tokenCount current next tailBoundary tailCount consumed
    hgraph.1 hgraph.2.1 hgraph.2.2

noncomputable def compileCompactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount consumed : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermContinueRows tokenTable width tokenCount current next
      tailBoundary tailCount consumed) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable width tokenCount
          current next tailBoundary tailCount consumed).freeVariables zeroValuation)
      (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable width tokenCount
        current next tailBoundary tailCount consumed) :=
  (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph tokenTable
    width tokenCount current next tailBoundary tailCount consumed hgraph).compile

noncomputable def
    compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount consumed : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermContinueRows tokenTable width tokenCount current next
      tailBoundary tailCount consumed) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current next tailBoundary tailCount consumed hgraph)

theorem
    compileCompactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount consumed : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermContinueRows tokenTable width tokenCount current next
      tailBoundary tailCount consumed) :
    (compileCompactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridContext tokenTable width
      tokenCount current next tailBoundary tailCount consumed hgraph).payloadLength ≤
      compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitStructuralResource tokenTable width
        tokenCount current next tailBoundary tailCount consumed hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current next tailBoundary tailCount consumed hgraph)

#print axioms compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula_alignment
#print axioms
  compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
#print axioms
  compileCompactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
