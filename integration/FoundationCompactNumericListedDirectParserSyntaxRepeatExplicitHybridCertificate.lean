import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for the repeated syntax-task branch

The original twenty-five-coordinate formula is assembled directly from the two
running-status slices, the unchanged token list, the exact task-list head, and
the zero/successor repeat branches. Native numerals `0`, `1`, and `2` are
preserved through the component formulas; no truth-to-certificate conversion is
used.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
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

@[simp] private theorem termValue_fixedNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (fixedNumeralTerm value) = value := by
  unfold termValue fixedNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘ (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) =
        (![] : Fin 0 -> Nat) by
      funext index
      exact Fin.elim0 index]
  simp

def nativeEqFormula (value expected : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) = !!(fixedNumeralTerm expected)”

def nativeSuccessorEqFormula (value predecessor : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) =
    !!(shortBinaryNumeralTerm predecessor) + !!(fixedNumeralTerm 1)”

noncomputable def nativeEqCertificate
    (value expected : Nat) (heq : value = expected) :
    HybridCertificate (nativeEqFormula value expected) := by
  unfold nativeEqFormula
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] (by
        change termValue zeroValuation (shortBinaryNumeralTerm value) =
          termValue zeroValuation (fixedNumeralTerm expected)
        simpa [termValue_shortBinaryNumeralTerm, termValue_fixedNumeralTerm] using heq)
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

noncomputable def nativeSuccessorEqCertificate
    (value predecessor : Nat) (heq : value = predecessor + 1) :
    HybridCertificate (nativeSuccessorEqFormula value predecessor) := by
  unfold nativeSuccessorEqFormula
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm predecessor) + !!(fixedNumeralTerm 1)’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq ![shortBinaryNumeralTerm value, rightTerm] (by
      change termValue zeroValuation (shortBinaryNumeralTerm value) =
        termValue zeroValuation rightTerm
      simpa [rightTerm, termValue_shortBinaryNumeralTerm, termValue_fixedNumeralTerm,
        termValue_arithmeticAdd] using heq)
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

def compactUnifiedParserSyntaxRepeatClosedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserSyntaxRepeatRowsDef.val) ⇜
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
      shortBinaryNumeralTerm binderArity, shortBinaryNumeralTerm repeatCount,
      shortBinaryNumeralTerm witness.tailBoundary,
      shortBinaryNumeralTerm witness.tailCount,
      shortBinaryNumeralTerm witness.tailBoundarySize,
      shortBinaryNumeralTerm witness.decrementedCount]

def compactUnifiedParserSyntaxRepeatBranchExplicitFormula
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) : ValuationFormula :=
  (nativeEqFormula repeatCount 0 ⋏
      compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width tokenCount
        witness.tailBoundary witness.tailCount next.tasksBoundary next.tasksCount) ⋎
    (nativeSuccessorEqFormula repeatCount witness.decrementedCount ⋏
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable width
          tokenCount next.tasksBoundary next.tasksCount witness.tailBoundary
            witness.tailCount 2 ⋏
        (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
            tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 0)
              (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
                (fixedNumeralTerm 0) ⋏
          compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
            tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 1)
              (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
                (shortBinaryNumeralTerm witness.decrementedCount))))

def compactUnifiedParserSyntaxRepeatExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) : ValuationFormula :=
  compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
      current.tasksFinish current.finish ⋏
    (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
        next.tasksFinish next.finish ⋏
      (compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
          current.tokensBoundary current.tokensCount next.tokensBoundary next.tokensCount ⋏
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula tokenTable width
            tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
              witness.tailCount witness.tailBoundarySize binderArity repeatCount
                (fixedNumeralTerm 2) ⋏
          compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width tokenCount next
            binderArity repeatCount witness)))

theorem compactUnifiedParserSyntaxRepeatClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) :
    compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount current next
        binderArity repeatCount witness =
      compactUnifiedParserSyntaxRepeatExplicitFormula tokenTable width tokenCount current next
        binderArity repeatCount witness := by
  unfold compactUnifiedParserSyntaxRepeatClosedFormula
  unfold compactUnifiedParserSyntaxRepeatExplicitFormula
  unfold compactUnifiedParserSyntaxRepeatBranchExplicitFormula
  unfold compactUnifiedParserSyntaxRepeatRowsDef
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  unfold compactAdditiveNatListSameRowsClosedFormula
  unfold compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula
  unfold compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
  unfold compactAdditiveSyntaxTaskListSameRowsClosedFormula
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula
  unfold nativeEqFormula nativeSuccessorEqFormula
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

inductive CompactSyntaxRepeatCheckedBranchData
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) : Type
  | zero
      (hrepeatZero : repeatCount = 0)
      (hsame : CompactAdditiveSyntaxTaskListSameRows tokenTable width
        tokenCount witness.tailBoundary witness.tailCount next.tasksBoundary
        next.tasksCount)
  | positive
      (hrepeatSuccessor : repeatCount = witness.decrementedCount + 1)
      (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
        next.tasksBoundary next.tasksCount witness.tailBoundary
        witness.tailCount 2)
      (htaskZero : CompactAdditiveSyntaxTaskListAtRows tokenTable width
        tokenCount next.tasksBoundary next.tasksCount 0 0 binderArity 0)
      (htaskOne : CompactAdditiveSyntaxTaskListAtRows tokenTable width
        tokenCount next.tasksBoundary next.tasksCount 1 2 binderArity
        witness.decrementedCount)

def compactSyntaxRepeatCheckedBranchDataOfGraph
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hbranch :
      (repeatCount = 0 ∧
        CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
          witness.tailBoundary witness.tailCount next.tasksBoundary
          next.tasksCount) ∨
      (repeatCount = witness.decrementedCount + 1 ∧
        CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
          next.tasksBoundary next.tasksCount witness.tailBoundary
          witness.tailCount 2 ∧
        CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
          next.tasksBoundary next.tasksCount 0 0 binderArity 0 ∧
        CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
          next.tasksBoundary next.tasksCount 1 2 binderArity
          witness.decrementedCount)) :
    CompactSyntaxRepeatCheckedBranchData tokenTable width tokenCount next
      binderArity repeatCount witness := by
  by_cases hrepeatZero : repeatCount = 0
  · have hzero := hbranch.resolve_right (by
      intro hpositive
      omega)
    exact .zero hrepeatZero hzero.2
  · have hpositive := hbranch.resolve_left (by
      intro hzero
      exact hrepeatZero hzero.1)
    exact .positive hpositive.1 hpositive.2.1 hpositive.2.2.1
      hpositive.2.2.2

noncomputable def compactUnifiedParserSyntaxRepeatExplicitHybridCertificateFromGraphData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hcurrent : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      current.tasksFinish current.finish)
    (hnext : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListSameRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount)
    (huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
      witness.tailCount witness.tailBoundarySize 2 binderArity repeatCount)
    (branchData : CompactSyntaxRepeatCheckedBranchData tokenTable width
      tokenCount next binderArity repeatCount witness) :
    HybridCertificate
      (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount current next
        binderArity repeatCount witness) := by
  let currentCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph tokenTable width tokenCount
      current.tasksFinish current.finish hcurrent
  let nextCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph tokenTable width tokenCount
      next.tasksFinish next.finish hnext
  let tokensCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary next.tokensCount htokens
  let unconsCertificate :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
        witness.tailCount witness.tailBoundarySize 2 binderArity repeatCount (fixedNumeralTerm 2)
          (fun valuation => by simp) huncons
  rcases branchData with ⟨hrepeatZero, hsame⟩ |
    ⟨hrepeatSuccessor, hdrop, htaskZero, htaskOne⟩
  ·
    let zeroBranch := CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqCertificate repeatCount 0 hrepeatZero)
      (compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph tokenTable width
        tokenCount witness.tailBoundary witness.tailCount next.tasksBoundary next.tasksCount hsame)
    let branch : HybridCertificate
        (compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width tokenCount next
          binderArity repeatCount witness) :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft zeroBranch
    let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction currentCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction nextCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction tokensCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction unconsCertificate branch)))
    exact .cast
      (compactUnifiedParserSyntaxRepeatClosedFormula_alignment tokenTable width tokenCount current
        next binderArity repeatCount witness).symm parts

  ·
    let dropCertificate :=
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph tokenTable
        width tokenCount next.tasksBoundary next.tasksCount witness.tailBoundary witness.tailCount
          2 hdrop
    let taskZeroCertificate :=
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph tokenTable
        width tokenCount next.tasksBoundary next.tasksCount 0 0 binderArity 0
          (fixedNumeralTerm 0) (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
            (fixedNumeralTerm 0)
          (by simp)
          (fun valuation => by simp)
          (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
          (fun valuation => by simp) htaskZero
    let taskOneCertificate :=
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph tokenTable
        width tokenCount next.tasksBoundary next.tasksCount 1 2 binderArity
          witness.decrementedCount (fixedNumeralTerm 1) (fixedNumeralTerm 2)
            (shortBinaryNumeralTerm binderArity)
              (shortBinaryNumeralTerm witness.decrementedCount)
          (by simp)
          (fun valuation => by simp)
          (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
          (fun valuation => by simp [termValue_shortBinaryNumeralTerm]) htaskOne
    let positiveBranch := CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeSuccessorEqCertificate repeatCount witness.decrementedCount hrepeatSuccessor)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction dropCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction taskZeroCertificate
          taskOneCertificate))
    let branch : HybridCertificate
        (compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width tokenCount next
          binderArity repeatCount witness) :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight positiveBranch
    let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction currentCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction nextCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction tokensCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction unconsCertificate branch)))
    exact .cast
      (compactUnifiedParserSyntaxRepeatClosedFormula_alignment tokenTable width tokenCount current
        next binderArity repeatCount witness).symm parts

noncomputable def compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount current next
      binderArity repeatCount witness) :
    HybridCertificate
      (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount current next
        binderArity repeatCount witness) :=
  compactUnifiedParserSyntaxRepeatExplicitHybridCertificateFromGraphData
    tokenTable width tokenCount current next binderArity repeatCount witness
    hgraph.1 hgraph.2.1 hgraph.2.2.1 hgraph.2.2.2.1
    (compactSyntaxRepeatCheckedBranchDataOfGraph tokenTable width tokenCount
      next binderArity repeatCount witness hgraph.2.2.2.2)

noncomputable def compileCompactUnifiedParserSyntaxRepeatExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount current next
      binderArity repeatCount witness) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount current next
          binderArity repeatCount witness).freeVariables zeroValuation)
      (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount current next
        binderArity repeatCount witness) :=
  (compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph tokenTable width tokenCount
    current next binderArity repeatCount witness hgraph).compile

noncomputable def compactUnifiedParserSyntaxRepeatExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount current next
      binderArity repeatCount witness) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph tokenTable width tokenCount
      current next binderArity repeatCount witness hgraph)

theorem compileCompactUnifiedParserSyntaxRepeatExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount current next
      binderArity repeatCount witness) :
    (compileCompactUnifiedParserSyntaxRepeatExplicitHybridContext tokenTable width tokenCount
      current next binderArity repeatCount witness hgraph).payloadLength ≤
      compactUnifiedParserSyntaxRepeatExplicitStructuralResource tokenTable width tokenCount
        current next binderArity repeatCount witness hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph tokenTable width tokenCount
      current next binderArity repeatCount witness hgraph)

#print axioms compactUnifiedParserSyntaxRepeatClosedFormula_alignment
#print axioms compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph
#print axioms compileCompactUnifiedParserSyntaxRepeatExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
