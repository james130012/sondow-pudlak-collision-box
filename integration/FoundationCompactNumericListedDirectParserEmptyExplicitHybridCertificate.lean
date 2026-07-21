import integration.FoundationCompactNumericListedDirectParserEmptyFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for the parser empty-task branch

The constructor follows the nine conjuncts of the original twenty-two
coordinate graph.  Every non-atomic conjunct is supplied by an existing
explicit certificate; no Sigma-zero truth conversion is used.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectCompletedOutputSameRows
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      Rewriting.app right := by
  cases h
  rfl

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left * !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Mul.mul ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left * !!right’ =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul valuation ![left, right]

private theorem termValue_arithmeticZero (valuation : Nat -> Nat) :
    termValue valuation (‘0’ : ValuationTerm) = 0 := by
  exact termValue_zero valuation ![]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

noncomputable def closedEqZeroCertificate
    (value : Nat) (heq : value = 0) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm value) = 0” := by
  exact .positiveAtomic zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, (‘0’ : ValuationTerm)] (by
      change termValue zeroValuation (shortBinaryNumeralTerm value) =
        termValue zeroValuation (‘0’ : ValuationTerm)
      simpa [termValue_shortBinaryNumeralTerm,
        termValue_arithmeticZero] using heq)

noncomputable def valuationLeCertificate
    (leftTerm rightTerm : ValuationTerm)
    (hle : termValue zeroValuation leftTerm ≤
      termValue zeroValuation rightTerm) :
    HybridCertificate “!!leftTerm ≤ !!rightTerm” := by
  if heq : termValue zeroValuation leftTerm =
      termValue zeroValuation rightTerm then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![leftTerm, rightTerm] heq
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : termValue zeroValuation leftTerm <
        termValue zeroValuation rightTerm := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hlt
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

noncomputable def outputBoundaryAreaCertificate
    (tokenCount sourceCount outputBoundarySize : Nat)
    (hbound : outputBoundarySize ≤ (sourceCount + 1) * tokenCount) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
        (!!(shortBinaryNumeralTerm sourceCount) + 1) *
          !!(shortBinaryNumeralTerm tokenCount)” := by
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm sourceCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  exact valuationLeCertificate
    (shortBinaryNumeralTerm outputBoundarySize) rightTerm (by
      simpa [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticMul,
        termValue_arithmeticOne] using hbound)

def compactUnifiedParserEmptyClosedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserEmptyGraphRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm current.start,
      shortBinaryNumeralTerm current.finish,
      shortBinaryNumeralTerm current.tokensFinish,
      shortBinaryNumeralTerm current.tasksFinish,
      shortBinaryNumeralTerm current.tokensBoundary,
      shortBinaryNumeralTerm current.tokensCount,
      shortBinaryNumeralTerm current.tasksBoundary,
      shortBinaryNumeralTerm current.tasksCount,
      shortBinaryNumeralTerm next.start,
      shortBinaryNumeralTerm next.finish,
      shortBinaryNumeralTerm next.tokensFinish,
      shortBinaryNumeralTerm next.tasksFinish,
      shortBinaryNumeralTerm next.tokensBoundary,
      shortBinaryNumeralTerm next.tokensCount,
      shortBinaryNumeralTerm next.tasksBoundary,
      shortBinaryNumeralTerm next.tasksCount,
      shortBinaryNumeralTerm witness.targetOutputStart,
      shortBinaryNumeralTerm witness.targetOutputBoundary,
      shortBinaryNumeralTerm witness.targetOutputBoundarySize]

def compactUnifiedParserEmptyExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm current.tasksCount) = 0” ⋏
    (“!!(shortBinaryNumeralTerm next.tasksCount) = 0” ⋏
      (compactBinaryNatRunningStatusSliceClosedFormula
          tokenTable width tokenCount current.tasksFinish current.finish ⋏
        (compactAdditiveNatListSameRowsClosedFormula
            tokenTable width tokenCount
            current.tokensBoundary current.tokensCount
            next.tokensBoundary next.tokensCount ⋏
          (compactBinaryNatCompletedStatusPrefixClosedFormula
              tokenTable width tokenCount next.tasksFinish
                witness.targetOutputStart ⋏
            (compactAdditiveStructuredListLayoutClosedFormula
                tokenTable width tokenCount witness.targetOutputStart
                current.tokensCount next.finish
                witness.targetOutputBoundary ⋏
              (compactAdditiveNatListSameRowsClosedFormula
                  tokenTable width tokenCount
                  current.tokensBoundary current.tokensCount
                  witness.targetOutputBoundary current.tokensCount ⋏
                (compactNatSizeClosedFormula
                    witness.targetOutputBoundarySize
                    witness.targetOutputBoundary ⋏
                  “!!(shortBinaryNumeralTerm
                        witness.targetOutputBoundarySize) ≤
                    (!!(shortBinaryNumeralTerm current.tokensCount) + 1) *
                      !!(shortBinaryNumeralTerm tokenCount)”)))))))

theorem compactUnifiedParserEmptyClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates) :
    compactUnifiedParserEmptyClosedFormula
        tokenTable width tokenCount current next witness =
      compactUnifiedParserEmptyExplicitFormula
        tokenTable width tokenCount current next witness := by
  unfold compactUnifiedParserEmptyClosedFormula
  unfold compactUnifiedParserEmptyExplicitFormula
  unfold compactUnifiedParserEmptyGraphRowsDef
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  unfold compactAdditiveNatListSameRowsClosedFormula
  unfold compactBinaryNatCompletedStatusPrefixClosedFormula
  unfold compactAdditiveStructuredListLayoutClosedFormula
  unfold compactNatSizeClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

noncomputable def compactUnifiedParserEmptyExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates)
    (hgraph : CompactUnifiedParserEmptyGraphRows
      tokenTable width tokenCount current next witness) :
    HybridCertificate
      (compactUnifiedParserEmptyClosedFormula
        tokenTable width tokenCount current next witness) := by
  rcases hgraph with
    ⟨hcurrentCount, hnextCount, hrunning, htokenRows, hcompleted⟩
  rcases hcompleted with
    ⟨⟨hprefix, hlayout, houtputRows⟩, hsize, harea⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedEqZeroCertificate current.tasksCount hcurrentCount)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (closedEqZeroCertificate next.tasksCount hnextCount)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tasksFinish current.finish
            hrunning)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
            tokenTable width tokenCount
            current.tokensBoundary current.tokensCount
            next.tokensBoundary next.tokensCount htokenRows)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
              tokenTable width tokenCount next.tasksFinish
                witness.targetOutputStart hprefix)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
                tokenTable width tokenCount witness.targetOutputStart
                  current.tokensCount next.finish
                  witness.targetOutputBoundary hlayout)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount
                    current.tokensBoundary current.tokensCount
                    witness.targetOutputBoundary current.tokensCount
                      houtputRows)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (compactNatSizeExplicitHybridCertificateOfEq
                    witness.targetOutputBoundarySize
                    witness.targetOutputBoundary hsize)
                  (outputBoundaryAreaCertificate tokenCount
                    current.tokensCount witness.targetOutputBoundarySize
                      harea))))))))
  exact .cast
    (compactUnifiedParserEmptyClosedFormula_alignment
      tokenTable width tokenCount current next witness).symm parts

noncomputable def compileCompactUnifiedParserEmptyExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates)
    (hgraph : CompactUnifiedParserEmptyGraphRows
      tokenTable width tokenCount current next witness) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserEmptyClosedFormula
          tokenTable width tokenCount current next witness).freeVariables
        zeroValuation)
      (compactUnifiedParserEmptyClosedFormula
        tokenTable width tokenCount current next witness) :=
  (compactUnifiedParserEmptyExplicitHybridCertificateOfGraph
    tokenTable width tokenCount current next witness hgraph).compile

noncomputable def compactUnifiedParserEmptyExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates)
    (hgraph : CompactUnifiedParserEmptyGraphRows
      tokenTable width tokenCount current next witness) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactUnifiedParserEmptyExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness hgraph)

theorem compileCompactUnifiedParserEmptyExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates)
    (hgraph : CompactUnifiedParserEmptyGraphRows
      tokenTable width tokenCount current next witness) :
    (compileCompactUnifiedParserEmptyExplicitHybridContext
      tokenTable width tokenCount current next witness hgraph).payloadLength ≤
      compactUnifiedParserEmptyExplicitStructuralResource
        tokenTable width tokenCount current next witness hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactUnifiedParserEmptyExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness hgraph)

#print axioms compactUnifiedParserEmptyClosedFormula_alignment
#print axioms compactUnifiedParserEmptyExplicitHybridCertificateOfGraph
#print axioms
  compileCompactUnifiedParserEmptyExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
