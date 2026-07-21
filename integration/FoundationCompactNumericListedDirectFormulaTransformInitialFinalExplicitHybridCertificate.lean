import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificate for formula-transform endpoints

The seven conjuncts of the genuine initial/final relation are compiled in their
source-formula order.  Both selected transform states, both parser endpoint
relations, and the emitted-output comparison retain their original checked
graphs; only the two elementary closed equalities are discharged directly.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialFormula
open FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate

private def zeroValuation : Nat -> Nat := fun _ => 0

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

def compactFormulaTransformInitialFinalRowsClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactFormulaTransformInitialFinalRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      shortBinaryNumeralTerm fuel,
      shortBinaryNumeralTerm inputBoundary,
      shortBinaryNumeralTerm inputCount,
      shortBinaryNumeralTerm expectedOutputBoundary,
      shortBinaryNumeralTerm expectedOutputCount,
      shortBinaryNumeralTerm expectedSuffixBoundary,
      shortBinaryNumeralTerm expectedSuffixCount,
      shortBinaryNumeralTerm binderArity,
      shortBinaryNumeralTerm witness.initialCoordinates.start,
      shortBinaryNumeralTerm witness.initialCoordinates.finish,
      shortBinaryNumeralTerm witness.initialCoordinates.parserFinish,
      shortBinaryNumeralTerm witness.initialCoordinates.parserTokensFinish,
      shortBinaryNumeralTerm witness.initialCoordinates.parserTasksFinish,
      shortBinaryNumeralTerm witness.initialCoordinates.parserTokensBoundary,
      shortBinaryNumeralTerm witness.initialCoordinates.parserTokensCount,
      shortBinaryNumeralTerm witness.initialCoordinates.parserTasksBoundary,
      shortBinaryNumeralTerm witness.initialCoordinates.parserTasksCount,
      shortBinaryNumeralTerm witness.initialCoordinates.outputBoundary,
      shortBinaryNumeralTerm witness.initialCoordinates.outputCount,
      shortBinaryNumeralTerm witness.initialSizeWitness.parserTokensBoundarySize,
      shortBinaryNumeralTerm witness.initialSizeWitness.parserTasksBoundarySize,
      shortBinaryNumeralTerm witness.initialSizeWitness.outputBoundarySize,
      shortBinaryNumeralTerm witness.finalCoordinates.start,
      shortBinaryNumeralTerm witness.finalCoordinates.finish,
      shortBinaryNumeralTerm witness.finalCoordinates.parserFinish,
      shortBinaryNumeralTerm witness.finalCoordinates.parserTokensFinish,
      shortBinaryNumeralTerm witness.finalCoordinates.parserTasksFinish,
      shortBinaryNumeralTerm witness.finalCoordinates.parserTokensBoundary,
      shortBinaryNumeralTerm witness.finalCoordinates.parserTokensCount,
      shortBinaryNumeralTerm witness.finalCoordinates.parserTasksBoundary,
      shortBinaryNumeralTerm witness.finalCoordinates.parserTasksCount,
      shortBinaryNumeralTerm witness.finalCoordinates.outputBoundary,
      shortBinaryNumeralTerm witness.finalCoordinates.outputCount,
      shortBinaryNumeralTerm witness.finalSizeWitness.parserTokensBoundarySize,
      shortBinaryNumeralTerm witness.finalSizeWitness.parserTasksBoundarySize,
      shortBinaryNumeralTerm witness.finalSizeWitness.outputBoundarySize,
      shortBinaryNumeralTerm witness.finalParserOutputStart,
      shortBinaryNumeralTerm witness.finalParserOutputBoundary,
      shortBinaryNumeralTerm witness.finalParserOutputBoundarySize]

private def compactFormulaTransformInitialParserSourceFormula
    (tokenTable width tokenCount inputBoundary inputCount binderArity : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserInitialStateRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.parserFinish,
      shortBinaryNumeralTerm coordinates.parserTokensFinish,
      shortBinaryNumeralTerm coordinates.parserTasksFinish,
      shortBinaryNumeralTerm coordinates.parserTokensBoundary,
      shortBinaryNumeralTerm coordinates.parserTokensCount,
      shortBinaryNumeralTerm coordinates.parserTasksBoundary,
      shortBinaryNumeralTerm coordinates.parserTasksCount,
      shortBinaryNumeralTerm inputBoundary,
      shortBinaryNumeralTerm inputCount,
      (‘1’ : ValuationTerm),
      shortBinaryNumeralTerm binderArity,
      (‘0’ : ValuationTerm)]

private def compactFormulaTransformInitialParserSourceExplicitFormula
    (tokenTable width tokenCount inputBoundary inputCount binderArity : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates) :
    ValuationFormula :=
  compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
      inputBoundary inputCount coordinates.parserTokensBoundary
        coordinates.parserTokensCount ⋏
    (“!!(shortBinaryNumeralTerm coordinates.parserTasksCount) = 1” ⋏
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula
          tokenTable width tokenCount coordinates.parserTasksBoundary
          coordinates.parserTasksCount (‘0’ : ValuationTerm)
          (‘1’ : ValuationTerm) (shortBinaryNumeralTerm binderArity)
          (‘0’ : ValuationTerm) ⋏
        compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
          tokenCount coordinates.parserTasksFinish coordinates.parserFinish))

private theorem compactFormulaTransformInitialParserSourceFormula_alignment
    (tokenTable width tokenCount inputBoundary inputCount binderArity : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates) :
    compactFormulaTransformInitialParserSourceFormula tokenTable width
        tokenCount inputBoundary inputCount binderArity coordinates =
      compactFormulaTransformInitialParserSourceExplicitFormula tokenTable width
        tokenCount inputBoundary inputCount binderArity coordinates := by
  unfold compactFormulaTransformInitialParserSourceFormula
  unfold compactFormulaTransformInitialParserSourceExplicitFormula
  unfold compactUnifiedParserInitialStateRowsDef
  unfold compactAdditiveNatListSameRowsClosedFormula
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula
  unfold compactBinaryNatRunningStatusSliceClosedFormula
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

def compactFormulaTransformInitialFinalRowsExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm stateCount) =
      !!(shortBinaryNumeralTerm fuel) + 1” ⋏
    (compactFormulaTransformStateAtRowsClosedFormula
        tokenTable width tokenCount stateBoundary stateCount 0
        witness.initialCoordinates witness.initialSizeWitness ⋏
      (compactFormulaTransformInitialParserSourceFormula
          tokenTable width tokenCount inputBoundary inputCount binderArity
          witness.initialCoordinates ⋏
        (“!!(shortBinaryNumeralTerm witness.initialCoordinates.outputCount) = 0” ⋏
          (compactFormulaTransformStateAtRowsClosedFormula
              tokenTable width tokenCount stateBoundary stateCount fuel
              witness.finalCoordinates witness.finalSizeWitness ⋏
            (compactUnifiedParserFinalStateRowsClosedFormula
                tokenTable width tokenCount witness.finalCoordinates.parser
                expectedSuffixBoundary expectedSuffixCount
                witness.finalParserOutputStart witness.finalParserOutputBoundary
                witness.finalParserOutputBoundarySize ⋏
              compactAdditiveNatListSameRowsClosedFormula
                tokenTable width tokenCount
                expectedOutputBoundary expectedOutputCount
                witness.finalCoordinates.outputBoundary
                witness.finalCoordinates.outputCount)))))

theorem compactFormulaTransformInitialFinalRowsClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    compactFormulaTransformInitialFinalRowsClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity witness =
      compactFormulaTransformInitialFinalRowsExplicitFormula
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity witness := by
  unfold compactFormulaTransformInitialFinalRowsClosedFormula
  unfold compactFormulaTransformInitialFinalRowsExplicitFormula
  unfold compactFormulaTransformInitialFinalRowsDef
  unfold compactFormulaTransformStateAtRowsClosedFormula
  unfold compactFormulaTransformInitialParserSourceFormula
  unfold compactUnifiedParserFinalStateRowsClosedFormula
  unfold compactAdditiveNatListSameRowsClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, shortBinaryNumeralTerm,
          CompactFormulaTransformStateRowCoordinates.parser,
          arithmeticZeroTerm, Semiterm.Operator.operator,
          Semiterm.Operator.numeral_zero,
          Semiterm.Operator.numeral_one, Semiterm.Operator.Zero.term_eq,
          Semiterm.Operator.One.term_eq, Rew.func, Matrix.empty_eq]
    · intro coordinate
      exact Empty.elim coordinate

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem termValue_arithmeticZero (valuation : Nat -> Nat) :
    termValue valuation (‘0’ : ValuationTerm) = 0 := by
  exact termValue_zero valuation ![]

private noncomputable def stateCountCertificate
    (stateCount fuel : Nat) (hcount : stateCount = fuel + 1) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm stateCount) =
        !!(shortBinaryNumeralTerm fuel) + 1” := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm fuel) + 1’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm stateCount, rightTerm] (by
      change termValue zeroValuation (shortBinaryNumeralTerm stateCount) =
        termValue zeroValuation rightTerm
      simpa [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticOne] using hcount)
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

private noncomputable def outputCountZeroCertificate
    (outputCount : Nat) (hcount : outputCount = 0) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm outputCount) = 0” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm outputCount, (‘0’ : ValuationTerm)] (by
      change termValue zeroValuation (shortBinaryNumeralTerm outputCount) =
        termValue zeroValuation (‘0’ : ValuationTerm)
      simpa [termValue_shortBinaryNumeralTerm,
        termValue_arithmeticZero] using hcount)
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

private noncomputable def unaryOneEqualityCertificate
    (value : Nat) (hvalue : value = 1) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm value) = 1” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, (‘1’ : ValuationTerm)] (by
      change termValue zeroValuation (shortBinaryNumeralTerm value) =
        termValue zeroValuation (‘1’ : ValuationTerm)
      simpa [termValue_shortBinaryNumeralTerm,
        termValue_arithmeticOne] using hvalue)
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

private noncomputable def
    compactFormulaTransformInitialParserSourceCertificateOfGraph
    (tokenTable width tokenCount inputBoundary inputCount binderArity : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (hgraph : CompactUnifiedParserInitialStateRows tokenTable width tokenCount
      coordinates.parser inputBoundary inputCount 1 binderArity 0) :
    HybridCertificate
      (compactFormulaTransformInitialParserSourceFormula tokenTable width
        tokenCount inputBoundary inputCount binderArity coordinates) := by
  rcases hgraph with ⟨hsame, htaskCount, htask, hrunning⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount inputBoundary inputCount
      coordinates.parserTokensBoundary coordinates.parserTokensCount hsame)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (unaryOneEqualityCertificate coordinates.parserTasksCount htaskCount)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount coordinates.parserTasksBoundary
          coordinates.parserTasksCount 0 1 binderArity 0
          (‘0’ : ValuationTerm) (‘1’ : ValuationTerm)
          (shortBinaryNumeralTerm binderArity) (‘0’ : ValuationTerm)
          (by exact termValue_arithmeticZero _)
          (fun valuation => termValue_arithmeticOne valuation)
          (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
          (fun valuation => termValue_arithmeticZero valuation) htask)
        (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount coordinates.parserTasksFinish
          coordinates.parserFinish hrunning)))
  exact .cast
    (compactFormulaTransformInitialParserSourceFormula_alignment tokenTable
      width tokenCount inputBoundary inputCount binderArity coordinates).symm
    parts

noncomputable def
    compactFormulaTransformInitialFinalRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates)
    (hgraph : CompactFormulaTransformInitialFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity witness) :
    HybridCertificate
      (compactFormulaTransformInitialFinalRowsClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity witness) := by
  rcases hgraph with
    ⟨hcount, hinitialAt, hinitialParser, hinitialOutputCount,
      hfinalAt, hfinalParser, hfinalOutput⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (stateCountCertificate stateCount fuel hcount)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFormulaTransformStateAtRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount stateBoundary stateCount 0
        witness.initialCoordinates witness.initialSizeWitness hinitialAt)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFormulaTransformInitialParserSourceCertificateOfGraph
          tokenTable width tokenCount inputBoundary inputCount binderArity
          witness.initialCoordinates hinitialParser)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (outputCountZeroCertificate
            witness.initialCoordinates.outputCount hinitialOutputCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactFormulaTransformStateAtRowsExplicitHybridCertificateOfGraph
              tokenTable width tokenCount stateBoundary stateCount fuel
              witness.finalCoordinates witness.finalSizeWitness hfinalAt)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactUnifiedParserFinalStateRowsExplicitHybridCertificateOfGraph
                tokenTable width tokenCount witness.finalCoordinates.parser
                expectedSuffixBoundary expectedSuffixCount
                witness.finalParserOutputStart
                witness.finalParserOutputBoundary
                witness.finalParserOutputBoundarySize hfinalParser)
              (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
                tokenTable width tokenCount expectedOutputBoundary
                expectedOutputCount witness.finalCoordinates.outputBoundary
                witness.finalCoordinates.outputCount hfinalOutput))))))
  exact .cast
    (compactFormulaTransformInitialFinalRowsClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity witness).symm parts

#print axioms compactFormulaTransformInitialFinalRowsClosedFormula_alignment
#print axioms
  compactFormulaTransformInitialFinalRowsExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalExplicitHybridCertificate
