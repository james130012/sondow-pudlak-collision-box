import integration.FoundationCompactNumericListedDirectParserSyntaxTermFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for the complete syntax-term transition

This file keeps every native numeral in the original 26-coordinate formula
and certifies every semantic branch from the concrete row relation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactArithmeticSymbolCode
open FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate

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

def nativeEqFormula (value expected : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) = !!(fixedNumeralTerm expected)”

def nativeNeFormula (value expected : Nat) : ValuationFormula :=
  ∼nativeEqFormula value expected

def shortLtFormula (left right : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm left) < !!(shortBinaryNumeralTerm right)”

def termLeFormula (leftTerm rightTerm : ValuationTerm) : ValuationFormula :=
  “!!leftTerm ≤ !!rightTerm”

def shortLeFormula (left right : Nat) : ValuationFormula :=
  termLeFormula (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right)

def shortNativeLeFormula (left right : Nat) : ValuationFormula :=
  termLeFormula (shortBinaryNumeralTerm left) (fixedNumeralTerm right)

def nativeShortLeFormula (left right : Nat) : ValuationFormula :=
  termLeFormula (fixedNumeralTerm left) (shortBinaryNumeralTerm right)

noncomputable def nativeEqCertificate
    (value expected : Nat) (heq : value = expected) :
    HybridCertificate (nativeEqFormula value expected) := by
  unfold nativeEqFormula
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] (by
        change termValue zeroValuation (shortBinaryNumeralTerm value) =
          termValue zeroValuation (fixedNumeralTerm expected)
        simpa [termValue_shortBinaryNumeralTerm] using heq)
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

noncomputable def nativeNeCertificate
    (value expected : Nat) (hne : value ≠ expected) :
    HybridCertificate (nativeNeFormula value expected) := by
  unfold nativeNeFormula nativeEqFormula
  let direct := CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
    zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] (by
        change ¬termValue zeroValuation (shortBinaryNumeralTerm value) =
          termValue zeroValuation (fixedNumeralTerm expected)
        simpa [termValue_shortBinaryNumeralTerm] using hne)
  exact .cast
    (congrArg (fun formula : ValuationFormula => ∼formula)
      (Semiformula.Operator.eq_def _ _).symm) direct

noncomputable def shortLtCertificate
    (left right : Nat) (hlt : left < right) :
    HybridCertificate (shortLtFormula left right) := by
  unfold shortLtFormula
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
        change termValue zeroValuation (shortBinaryNumeralTerm left) <
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [termValue_shortBinaryNumeralTerm] using hlt)
  exact .cast (Semiformula.Operator.lt_def _ _).symm direct

noncomputable def termLeCertificate
    (left right : Nat) (leftTerm rightTerm : ValuationTerm)
    (hleft : termValue zeroValuation leftTerm = left)
    (hright : termValue zeroValuation rightTerm = right)
    (hle : left ≤ right) :
    HybridCertificate (termLeFormula leftTerm rightTerm) := by
  unfold termLeFormula
  if heq : left = right then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![leftTerm, rightTerm] (by
        change termValue zeroValuation leftTerm = termValue zeroValuation rightTerm
        simpa [hleft, hright] using heq)
    exact .cast (Semiformula.Operator.le_def _ _).symm (.disjunctionLeft equality)
  else
    have hlt : left < right := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] (by
        change termValue zeroValuation leftTerm < termValue zeroValuation rightTerm
        simpa [hleft, hright] using hlt)
    exact .cast (Semiformula.Operator.le_def _ _).symm (.disjunctionRight strict)

noncomputable def shortLeCertificate
    (left right : Nat) (hle : left ≤ right) :
    HybridCertificate (shortLeFormula left right) := by
  unfold shortLeFormula
  exact termLeCertificate left right (shortBinaryNumeralTerm left)
    (shortBinaryNumeralTerm right) (by simp [termValue_shortBinaryNumeralTerm])
      (by simp [termValue_shortBinaryNumeralTerm]) hle

noncomputable def shortNativeLeCertificate
    (left right : Nat) (hle : left ≤ right) :
    HybridCertificate (shortNativeLeFormula left right) := by
  unfold shortNativeLeFormula
  exact termLeCertificate left right (shortBinaryNumeralTerm left) (fixedNumeralTerm right)
    (by simp [termValue_shortBinaryNumeralTerm]) (by simp) hle

noncomputable def nativeShortLeCertificate
    (left right : Nat) (hle : left ≤ right) :
    HybridCertificate (nativeShortLeFormula left right) := by
  unfold nativeShortLeFormula
  exact termLeCertificate left right (fixedNumeralTerm left) (shortBinaryNumeralTerm right)
    (by simp) (by simp [termValue_shortBinaryNumeralTerm]) hle

def compactUnifiedParserSyntaxTermClosedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserSyntaxTermRowsDef.val) ⇜
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
      shortBinaryNumeralTerm next.tasksCount, shortBinaryNumeralTerm binderArity,
      shortBinaryNumeralTerm witness.tailBoundary,
      shortBinaryNumeralTerm witness.tailCount,
      shortBinaryNumeralTerm witness.tailBoundarySize,
      shortBinaryNumeralTerm witness.tag,
      shortBinaryNumeralTerm witness.argument,
      shortBinaryNumeralTerm witness.functionCode]

def compactUnifiedParserSyntaxTermDecisionExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : ValuationFormula :=
  let failureBranch := compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width tokenCount
    current next witness.tailBoundary witness.tailCount
  let continueBranch :=
    compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable width tokenCount
      current next witness.tailBoundary witness.tailCount 2
  let functionBranch :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable width tokenCount
      current next witness.tailBoundary witness.tailCount binderArity witness.argument
  let atFunction := compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width tokenCount
    current.tokensBoundary current.tokensCount witness.functionCode (fixedNumeralTerm 2)
  ((nativeEqFormula witness.tag 0 ⋏
      shortLtFormula witness.argument binderArity ⋏ continueBranch) ⋎
    (nativeEqFormula witness.tag 0 ⋏
      shortLeFormula binderArity witness.argument ⋏ failureBranch)) ⋎
   (nativeEqFormula witness.tag 1 ⋏ continueBranch) ⋎
   (nativeEqFormula witness.tag 2 ⋏
      ((shortNativeLeFormula current.tokensCount 2 ⋏ failureBranch) ⋎
       (nativeShortLeFormula 3 current.tokensCount ⋏
        atFunction ⋏
        ((compactAdditiveArithmeticFuncCodeValidClosedFormula witness.argument
            witness.functionCode ⋏ functionBranch) ⋎
         (compactAdditiveArithmeticFuncCodeInvalidClosedFormula witness.argument
            witness.functionCode ⋏ failureBranch))))) ⋎
   (nativeNeFormula witness.tag 0 ⋏
    nativeNeFormula witness.tag 1 ⋏
    nativeNeFormula witness.tag 2 ⋏ failureBranch)

def compactUnifiedParserSyntaxTermBranchExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : ValuationFormula :=
  let failureBranch := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
    witness.tailCount
  let atTag := compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable
    width tokenCount current.tokensBoundary current.tokensCount witness.tag
    (fixedNumeralTerm 0)
  let atArgument := compactAdditiveNatListAtRowsAtValuationIndexFormula
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    witness.argument (fixedNumeralTerm 1)
  (shortNativeLeFormula current.tokensCount 1 ⋏ failureBranch) ⋎
    (nativeShortLeFormula 2 current.tokensCount ⋏ atTag ⋏ atArgument ⋏
      compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness)

def compactUnifiedParserSyntaxTermExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : ValuationFormula :=
  compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
      current.tasksFinish current.finish ⋏
    (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula tokenTable width
        tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary witness.tailCount
          witness.tailBoundarySize (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
            (fixedNumeralTerm 0) ⋏
      compactUnifiedParserSyntaxTermBranchExplicitFormula tokenTable width tokenCount current next
        binderArity witness)

theorem compactUnifiedParserSyntaxTermClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) :
    compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount current next
        binderArity witness =
      compactUnifiedParserSyntaxTermExplicitFormula tokenTable width tokenCount current next
        binderArity witness := by
  unfold compactUnifiedParserSyntaxTermClosedFormula
  unfold compactUnifiedParserSyntaxTermExplicitFormula
  unfold compactUnifiedParserSyntaxTermBranchExplicitFormula
  unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
  unfold compactUnifiedParserSyntaxTermRowsDef
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  unfold compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
  unfold compactUnifiedParserSyntaxTermFailureClosedFormula
  unfold compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
  unfold compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
  rw [compactAdditiveNatListAtRowsAtValuationIndexFormula_eq_explicitSubstitution]
  rw [compactAdditiveNatListAtRowsAtValuationIndexFormula_eq_explicitSubstitution]
  rw [compactAdditiveNatListAtRowsAtValuationIndexFormula_eq_explicitSubstitution]
  unfold compactAdditiveArithmeticFuncCodeInvalidClosedFormula
  unfold compactAdditiveArithmeticFuncCodeValidClosedFormula
  unfold compactAdditiveArithmeticFuncCodeValidDef
  unfold nativeEqFormula nativeNeFormula shortLtFormula shortLeFormula
  unfold shortNativeLeFormula nativeShortLeFormula termLeFormula
  simp [fixedNumeralTerm,
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

private theorem compactUnifiedParserSyntaxTermBranchCertificate_nonempty
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount current next
      binderArity witness) :
    Nonempty
      (HybridCertificate
        (compactUnifiedParserSyntaxTermBranchExplicitFormula tokenTable width tokenCount current
          next binderArity witness)) := by
  unfold compactUnifiedParserSyntaxTermBranchExplicitFormula
  rcases hgraph.2.2 with hshort | henough
  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (shortNativeLeCertificate current.tokensCount 1 hshort.1)
        (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph tokenTable width
          tokenCount current next witness.tailBoundary witness.tailCount hshort.2))⟩
  · let enoughPrefix := CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeShortLeCertificate 2 current.tokensCount henough.1)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph tokenTable
          width tokenCount current.tokensBoundary current.tokensCount 0 witness.tag
            (fixedNumeralTerm 0) (by simp) henough.2.1)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph tokenTable
            width tokenCount current.tokensBoundary current.tokensCount 1 witness.argument
              (fixedNumeralTerm 1) (by simp) henough.2.2.1)
          (Classical.choice (show Nonempty (HybridCertificate
              (((nativeEqFormula witness.tag 0 ⋏
                  shortLtFormula witness.argument binderArity ⋏
                  compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable width
                    tokenCount current next witness.tailBoundary witness.tailCount 2) ⋎
                (nativeEqFormula witness.tag 0 ⋏
                  shortLeFormula binderArity witness.argument ⋏
                  compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width tokenCount
                    current next witness.tailBoundary witness.tailCount)) ⋎
               (nativeEqFormula witness.tag 1 ⋏
                  compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable width
                    tokenCount current next witness.tailBoundary witness.tailCount 2) ⋎
               (nativeEqFormula witness.tag 2 ⋏
                  ((shortNativeLeFormula current.tokensCount 2 ⋏
                      compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width tokenCount
                        current next witness.tailBoundary witness.tailCount) ⋎
                   (nativeShortLeFormula 3 current.tokensCount ⋏
                    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width tokenCount
                      current.tokensBoundary current.tokensCount witness.functionCode
                        (fixedNumeralTerm 2) ⋏
                    ((compactAdditiveArithmeticFuncCodeValidClosedFormula witness.argument
                        witness.functionCode ⋏
                        compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable
                          width tokenCount current next witness.tailBoundary witness.tailCount
                            binderArity witness.argument) ⋎
                     (compactAdditiveArithmeticFuncCodeInvalidClosedFormula witness.argument
                        witness.functionCode ⋏
                        compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width tokenCount
                          current next witness.tailBoundary witness.tailCount))))) ⋎
               (nativeNeFormula witness.tag 0 ⋏
                nativeNeFormula witness.tag 1 ⋏
                nativeNeFormula witness.tag 2 ⋏
                compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width tokenCount
                  current next witness.tailBoundary witness.tailCount))) from by
            rcases henough.2.2.2 with hzero | hrest
            · rcases hzero with hsuccess | hfailure
              · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                  (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                      (nativeEqCertificate witness.tag 0 hsuccess.1)
                      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                        (shortLtCertificate witness.argument binderArity hsuccess.2.1)
                        (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
                          tokenTable width tokenCount current next witness.tailBoundary
                            witness.tailCount 2 hsuccess.2.2))))⟩
              · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                  (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                      (nativeEqCertificate witness.tag 0 hfailure.1)
                      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                        (shortLeCertificate binderArity witness.argument hfailure.2.1)
                        (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                          tokenTable width tokenCount current next witness.tailBoundary
                            witness.tailCount hfailure.2.2))))⟩
            · rcases hrest with hone | hrest
              · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                  (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                      (nativeEqCertificate witness.tag 1 hone.1)
                      (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
                        tokenTable width tokenCount current next witness.tailBoundary
                          witness.tailCount 2 hone.2)))⟩
              · rcases hrest with htwo | hinvalidTag
                · rcases htwo.2 with htooShort | hfunction
                  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                            (nativeEqCertificate witness.tag 2 htwo.1)
                            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                                (shortNativeLeCertificate current.tokensCount 2 htooShort.1)
                                (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                                  tokenTable width tokenCount current next witness.tailBoundary
                                    witness.tailCount htooShort.2))))))⟩
                  · rcases hfunction.2.2 with hvalid | hinvalid
                    · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                              (nativeEqCertificate witness.tag 2 htwo.1)
                              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                                  (nativeShortLeCertificate 3 current.tokensCount hfunction.1)
                                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                                    (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                                      tokenTable width tokenCount current.tokensBoundary
                                        current.tokensCount 2 witness.functionCode
                                          (fixedNumeralTerm 2) (by simp) hfunction.2.1)
                                    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                                      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                                        (compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificateOfGraph
                                          witness.argument witness.functionCode hvalid.1)
                                        (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
                                          tokenTable width tokenCount current next witness.tailBoundary
                                            witness.tailCount binderArity witness.argument
                                              hvalid.2)))))))))⟩
                    · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                              (nativeEqCertificate witness.tag 2 htwo.1)
                              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                                  (nativeShortLeCertificate 3 current.tokensCount hfunction.1)
                                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                                    (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                                      tokenTable width tokenCount current.tokensBoundary
                                        current.tokensCount 2 witness.functionCode
                                          (fixedNumeralTerm 2) (by simp) hfunction.2.1)
                                    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                                      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                                        (compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificateOfGraph
                                          witness.argument witness.functionCode hinvalid.1)
                                        (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                                          tokenTable width tokenCount current next witness.tailBoundary
                                            witness.tailCount hinvalid.2)))))))))⟩
                · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                          (nativeNeCertificate witness.tag 0 hinvalidTag.1)
                          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                            (nativeNeCertificate witness.tag 1 hinvalidTag.2.1)
                            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                              (nativeNeCertificate witness.tag 2 hinvalidTag.2.2.1)
                              (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                                tokenTable width tokenCount current next witness.tailBoundary
                                  witness.tailCount hinvalidTag.2.2.2))))))⟩))))
    exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight enoughPrefix⟩

inductive CompactSyntaxTermCheckedBranchData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : Type where
  | short
      (hcount : current.tokensCount ≤ 1)
      (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)
  | zeroSuccess
      (hcount : 2 ≤ current.tokensCount)
      (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 0 witness.tag)
      (hatArgument : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 1 witness.argument)
      (htag : witness.tag = 0)
      (hargument : witness.argument < binderArity)
      (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount 2)
  | zeroFailure
      (hcount : 2 ≤ current.tokensCount)
      (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 0 witness.tag)
      (hatArgument : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 1 witness.argument)
      (htag : witness.tag = 0)
      (hargument : binderArity ≤ witness.argument)
      (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)
  | one
      (hcount : 2 ≤ current.tokensCount)
      (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 0 witness.tag)
      (hatArgument : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 1 witness.argument)
      (htag : witness.tag = 1)
      (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount 2)
  | twoShort
      (hcount : 2 ≤ current.tokensCount)
      (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 0 witness.tag)
      (hatArgument : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 1 witness.argument)
      (htag : witness.tag = 2)
      (htooShort : current.tokensCount ≤ 2)
      (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)
  | twoValid
      (hcount : 2 ≤ current.tokensCount)
      (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 0 witness.tag)
      (hatArgument : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 1 witness.argument)
      (htag : witness.tag = 2)
      (hthree : 3 ≤ current.tokensCount)
      (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 2 witness.functionCode)
      (hvalid : ArithmeticFuncCodeValid witness.argument witness.functionCode)
      (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount
        binderArity witness.argument)
  | twoInvalid
      (hcount : 2 ≤ current.tokensCount)
      (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 0 witness.tag)
      (hatArgument : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 1 witness.argument)
      (htag : witness.tag = 2)
      (hthree : 3 ≤ current.tokensCount)
      (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 2 witness.functionCode)
      (hinvalid : ¬ArithmeticFuncCodeValid witness.argument witness.functionCode)
      (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)
  | invalidTag
      (hcount : 2 ≤ current.tokensCount)
      (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 0 witness.tag)
      (hatArgument : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 1 witness.argument)
      (hne0 : witness.tag ≠ 0)
      (hne1 : witness.tag ≠ 1)
      (hne2 : witness.tag ≠ 2)
      (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)

theorem compactSyntaxTermCheckedBranchData_nonempty
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    Nonempty (CompactSyntaxTermCheckedBranchData tokenTable width tokenCount
      current next binderArity witness) := by
  rcases hgraph.2.2 with hshort | henough
  · exact ⟨.short hshort.1 hshort.2⟩
  · rcases henough.2.2.2 with hzero | hrest
    · rcases hzero with hsuccess | hfailure
      · exact ⟨.zeroSuccess henough.1 henough.2.1 henough.2.2.1
          hsuccess.1 hsuccess.2.1 hsuccess.2.2⟩
      · exact ⟨.zeroFailure henough.1 henough.2.1 henough.2.2.1
          hfailure.1 hfailure.2.1 hfailure.2.2⟩
    · rcases hrest with hone | hrest
      · exact ⟨.one henough.1 henough.2.1 henough.2.2.1 hone.1
          hone.2⟩
      · rcases hrest with htwo | hinvalidTag
        · rcases htwo.2 with htooShort | hfunction
          · exact ⟨.twoShort henough.1 henough.2.1 henough.2.2.1
              htwo.1 htooShort.1 htooShort.2⟩
          · rcases hfunction.2.2 with hvalid | hinvalid
            · exact ⟨.twoValid henough.1 henough.2.1 henough.2.2.1
                htwo.1 hfunction.1 hfunction.2.1 hvalid.1 hvalid.2⟩
            · exact ⟨.twoInvalid henough.1 henough.2.1 henough.2.2.1
                htwo.1 hfunction.1 hfunction.2.1 hinvalid.1 hinvalid.2⟩
        · exact ⟨.invalidTag henough.1 henough.2.1 henough.2.2.1
            hinvalidTag.1 hinvalidTag.2.1 hinvalidTag.2.2.1
            hinvalidTag.2.2.2⟩

noncomputable def compactSyntaxTermCheckedBranchDataOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    CompactSyntaxTermCheckedBranchData tokenTable width tokenCount current next
      binderArity witness :=
  Classical.choice (compactSyntaxTermCheckedBranchData_nonempty tokenTable
    width tokenCount current next binderArity witness hgraph)

noncomputable def compactSyntaxTermZeroSuccessDecisionCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 0)
    (hargument : witness.argument < binderArity)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 2) :
    HybridCertificate
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (nativeEqCertificate witness.tag 0 htag)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (shortLtCertificate witness.argument binderArity hargument)
      (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount 2 hcontinue))

noncomputable def compactSyntaxTermZeroFailureDecisionCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 0)
    (hargument : binderArity ≤ witness.argument)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    HybridCertificate
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (nativeEqCertificate witness.tag 0 htag)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (shortLeCertificate binderArity witness.argument hargument)
      (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount hfailure))

noncomputable def compactSyntaxTermOneDecisionCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 1)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 2) :
    HybridCertificate
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (nativeEqCertificate witness.tag 1 htag)
    (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount 2 hcontinue)

noncomputable def compactSyntaxTermTwoShortDecisionCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (htooShort : current.tokensCount ≤ 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    HybridCertificate
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (nativeEqCertificate witness.tag 2 htag)
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (shortNativeLeCertificate current.tokensCount 2 htooShort)
        (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount hfailure)))

noncomputable def compactSyntaxTermTwoValidDecisionCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (hthree : 3 ≤ current.tokensCount)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (hvalid : ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.argument) :
    HybridCertificate
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (nativeEqCertificate witness.tag 2 htag)
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeShortLeCertificate 3 current.tokensCount hthree)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 2 witness.functionCode (fixedNumeralTerm 2)
            (by simp) hatFunction)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificateOfGraph
                witness.argument witness.functionCode hvalid)
              (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current next witness.tailBoundary
                witness.tailCount binderArity witness.argument hfunction))))))

noncomputable def compactSyntaxTermTwoInvalidDecisionCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (hthree : 3 ≤ current.tokensCount)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (hinvalid : ¬ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    HybridCertificate
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (nativeEqCertificate witness.tag 2 htag)
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeShortLeCertificate 3 current.tokensCount hthree)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 2 witness.functionCode (fixedNumeralTerm 2)
            (by simp) hatFunction)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificateOfGraph
                witness.argument witness.functionCode hinvalid)
              (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current next witness.tailBoundary
                witness.tailCount hfailure))))))

noncomputable def compactSyntaxTermInvalidTagDecisionCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hne0 : witness.tag ≠ 0)
    (hne1 : witness.tag ≠ 1)
    (hne2 : witness.tag ≠ 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    HybridCertificate
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (nativeNeCertificate witness.tag 0 hne0)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeNeCertificate witness.tag 1 hne1)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeNeCertificate witness.tag 2 hne2)
        (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount hfailure)))

noncomputable def compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (data : CompactSyntaxTermCheckedBranchData tokenTable width tokenCount
      current next binderArity witness) :
    HybridCertificate
      (compactUnifiedParserSyntaxTermBranchExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxTermBranchExplicitFormula
  cases data with
  | short hcount hfailure =>
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (shortNativeLeCertificate current.tokensCount 1 hcount)
          (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount hfailure))
  | zeroSuccess hcount hatTag hatArgument htag hargument hcontinue =>
      let decision := compactSyntaxTermZeroSuccessDecisionCertificate tokenTable
        width tokenCount current next binderArity witness htag hargument
        hcontinue
      let enoughPrefix := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeShortLeCertificate 2 current.tokensCount hcount)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
            (by simp) hatTag)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current.tokensBoundary
              current.tokensCount 1 witness.argument (fixedNumeralTerm 1)
              (by simp) hatArgument)
            decision))
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        enoughPrefix
  | zeroFailure hcount hatTag hatArgument htag hargument hfailure =>
      let decision := compactSyntaxTermZeroFailureDecisionCertificate tokenTable
        width tokenCount current next binderArity witness htag hargument
        hfailure
      let enoughPrefix := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeShortLeCertificate 2 current.tokensCount hcount)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
            (by simp) hatTag)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current.tokensBoundary
              current.tokensCount 1 witness.argument (fixedNumeralTerm 1)
              (by simp) hatArgument)
            decision))
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        enoughPrefix
  | one hcount hatTag hatArgument htag hcontinue =>
      let decision := compactSyntaxTermOneDecisionCertificate tokenTable width
        tokenCount current next binderArity witness htag hcontinue
      let enoughPrefix := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeShortLeCertificate 2 current.tokensCount hcount)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
            (by simp) hatTag)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current.tokensBoundary
              current.tokensCount 1 witness.argument (fixedNumeralTerm 1)
              (by simp) hatArgument)
            decision))
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        enoughPrefix
  | twoShort hcount hatTag hatArgument htag htooShort hfailure =>
      let decision := compactSyntaxTermTwoShortDecisionCertificate tokenTable
        width tokenCount current next binderArity witness htag htooShort
        hfailure
      let enoughPrefix := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeShortLeCertificate 2 current.tokensCount hcount)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
            (by simp) hatTag)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current.tokensBoundary
              current.tokensCount 1 witness.argument (fixedNumeralTerm 1)
              (by simp) hatArgument)
            decision))
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        enoughPrefix
  | twoValid hcount hatTag hatArgument htag hthree hatFunction hvalid hfunction =>
      let decision := compactSyntaxTermTwoValidDecisionCertificate tokenTable
        width tokenCount current next binderArity witness htag hthree
        hatFunction hvalid hfunction
      let enoughPrefix := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeShortLeCertificate 2 current.tokensCount hcount)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
            (by simp) hatTag)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current.tokensBoundary
              current.tokensCount 1 witness.argument (fixedNumeralTerm 1)
              (by simp) hatArgument)
            decision))
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        enoughPrefix
  | twoInvalid hcount hatTag hatArgument htag hthree hatFunction hinvalid hfailure =>
      let decision := compactSyntaxTermTwoInvalidDecisionCertificate tokenTable
        width tokenCount current next binderArity witness htag hthree
        hatFunction hinvalid hfailure
      let enoughPrefix := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeShortLeCertificate 2 current.tokensCount hcount)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
            (by simp) hatTag)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current.tokensBoundary
              current.tokensCount 1 witness.argument (fixedNumeralTerm 1)
              (by simp) hatArgument)
            decision))
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        enoughPrefix
  | invalidTag hcount hatTag hatArgument hne0 hne1 hne2 hfailure =>
      let decision := compactSyntaxTermInvalidTagDecisionCertificate tokenTable
        width tokenCount current next binderArity witness hne0 hne1 hne2
        hfailure
      let enoughPrefix := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeShortLeCertificate 2 current.tokensCount hcount)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
            (by simp) hatTag)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current.tokensBoundary
              current.tokensCount 1 witness.argument (fixedNumeralTerm 1)
              (by simp) hatArgument)
            decision))
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        enoughPrefix

noncomputable def compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount current next
      binderArity witness) :
    HybridCertificate
      (compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount current next
        binderArity witness) := by
  let branchData := compactSyntaxTermCheckedBranchDataOfGraph tokenTable width
    tokenCount current next binderArity witness hgraph
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph tokenTable width tokenCount
      current.tasksFinish current.finish hgraph.1)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
          witness.tailCount witness.tailBoundarySize 0 binderArity 0 (fixedNumeralTerm 0)
            (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0) (fun valuation => by simp)
              (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
                (fun valuation => by simp) hgraph.2.1)
      (compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData
        tokenTable width tokenCount current next binderArity witness branchData))
  exact .cast
    (compactUnifiedParserSyntaxTermClosedFormula_alignment tokenTable width tokenCount current next
      binderArity witness).symm parts

noncomputable def compileCompactUnifiedParserSyntaxTermExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount current next
      binderArity witness) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount current next
          binderArity witness).freeVariables zeroValuation)
      (compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount current next
        binderArity witness) :=
  (compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph tokenTable width tokenCount current
    next binderArity witness hgraph).compile

noncomputable def compactUnifiedParserSyntaxTermExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount current next
      binderArity witness) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph tokenTable width tokenCount
      current next binderArity witness hgraph)

theorem compileCompactUnifiedParserSyntaxTermExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount current next
      binderArity witness) :
    (compileCompactUnifiedParserSyntaxTermExplicitHybridContext tokenTable width tokenCount current
      next binderArity witness hgraph).payloadLength ≤
      compactUnifiedParserSyntaxTermExplicitStructuralResource tokenTable width tokenCount current
        next binderArity witness hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph tokenTable width tokenCount
      current next binderArity witness hgraph)

#print axioms compactUnifiedParserSyntaxTermClosedFormula_alignment
#print axioms compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph
#print axioms compileCompactUnifiedParserSyntaxTermExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
