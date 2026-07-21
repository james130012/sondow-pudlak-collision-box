import integration.FoundationCompactNumericListedDirectParserSyntaxTermFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for a syntax-term function task

The token drop count and the task-head kind remain native arithmetic numerals,
matching the original 23-coordinate formula exactly.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate

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
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
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

def compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserSyntaxTermFunctionRowsDef.val) ⇜
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
      shortBinaryNumeralTerm binderArity, shortBinaryNumeralTerm functionArity]

def compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat) : ValuationFormula :=
  compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
      next.tasksFinish next.finish ⋏
    (compactAdditiveNatListDropFixedNumeralRowsClosedFormula tokenTable width tokenCount
        current.tokensBoundary current.tokensCount next.tokensBoundary next.tokensCount 3 ⋏
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable width tokenCount
        tailBoundary tailCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 2)
          (shortBinaryNumeralTerm binderArity) (shortBinaryNumeralTerm functionArity))

theorem compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat) :
    compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable width tokenCount
        current next tailBoundary tailCount binderArity functionArity =
      compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitFormula tokenTable width tokenCount
        current next tailBoundary tailCount binderArity functionArity := by
  unfold compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
  unfold compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitFormula
  unfold compactUnifiedParserSyntaxTermFunctionRowsDef
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  unfold compactAdditiveNatListDropFixedNumeralRowsClosedFormula
  unfold compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
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
    compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateFromGraphData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat)
    (hrunning : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListDropRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount 3)
    (htasks : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount next.tasksBoundary next.tasksCount 2 binderArity
      functionArity) :
    HybridCertificate
      (compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable width tokenCount
        current next tailBoundary tailCount binderArity functionArity) := by
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph tokenTable width tokenCount
      next.tasksFinish next.finish hrunning)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph tokenTable width
        tokenCount current.tokensBoundary current.tokensCount next.tokensBoundary next.tokensCount
          3 htokens)
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary next.tasksCount
          2 binderArity functionArity (fixedNumeralTerm 2)
            (shortBinaryNumeralTerm binderArity) (shortBinaryNumeralTerm functionArity)
          (fun valuation => by simp)
          (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
          (fun valuation => by simp [termValue_shortBinaryNumeralTerm]) htasks))
  exact .cast
    (compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula_alignment tokenTable width
      tokenCount current next tailBoundary tailCount binderArity functionArity).symm parts

noncomputable def
    compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width tokenCount current next
      tailBoundary tailCount binderArity functionArity) :
    HybridCertificate
      (compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable width tokenCount
        current next tailBoundary tailCount binderArity functionArity) :=
  compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateFromGraphData
    tokenTable width tokenCount current next tailBoundary tailCount binderArity
    functionArity hgraph.1 hgraph.2.1 hgraph.2.2

noncomputable def compileCompactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width tokenCount current next
      tailBoundary tailCount binderArity functionArity) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable width tokenCount
          current next tailBoundary tailCount binderArity functionArity).freeVariables zeroValuation)
      (compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable width tokenCount
        current next tailBoundary tailCount binderArity functionArity) :=
  (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph tokenTable
    width tokenCount current next tailBoundary tailCount binderArity functionArity hgraph).compile

noncomputable def
    compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width tokenCount current next
      tailBoundary tailCount binderArity functionArity) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current next tailBoundary tailCount binderArity functionArity hgraph)

theorem
    compileCompactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width tokenCount current next
      tailBoundary tailCount binderArity functionArity) :
    (compileCompactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridContext tokenTable width
      tokenCount current next tailBoundary tailCount binderArity functionArity hgraph).payloadLength ≤
      compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitStructuralResource tokenTable width
        tokenCount current next tailBoundary tailCount binderArity functionArity hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current next tailBoundary tailCount binderArity functionArity hgraph)

#print axioms compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula_alignment
#print axioms
  compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
#print axioms
  compileCompactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
