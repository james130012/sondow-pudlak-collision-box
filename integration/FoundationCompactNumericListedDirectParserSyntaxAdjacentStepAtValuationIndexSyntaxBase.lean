import integration.FoundationCompactNumericListedDirectParserStateAtRowsValuationFullyUniformDirectFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFullyFixedBounds

/-! # Source components for an adjacent syntax step at an open index -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexSyntaxBase

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase
open FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula

def compactParserSyntaxAdjacentStepAtValuationIndexTerms
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (row : CompactParserSyntaxAdjacentStepRow) :
    Fin 33 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    shortBinaryNumeralTerm stateCount,
    indexTerm,
    shortBinaryNumeralTerm row.currentCoordinates.start,
    shortBinaryNumeralTerm row.currentCoordinates.finish,
    shortBinaryNumeralTerm row.currentCoordinates.tokensFinish,
    shortBinaryNumeralTerm row.currentCoordinates.tasksFinish,
    shortBinaryNumeralTerm row.currentCoordinates.tokensBoundary,
    shortBinaryNumeralTerm row.currentCoordinates.tokensCount,
    shortBinaryNumeralTerm row.currentCoordinates.tasksBoundary,
    shortBinaryNumeralTerm row.currentCoordinates.tasksCount,
    shortBinaryNumeralTerm row.currentSize.tokensBoundarySize,
    shortBinaryNumeralTerm row.currentSize.tasksBoundarySize,
    shortBinaryNumeralTerm row.nextCoordinates.start,
    shortBinaryNumeralTerm row.nextCoordinates.finish,
    shortBinaryNumeralTerm row.nextCoordinates.tokensFinish,
    shortBinaryNumeralTerm row.nextCoordinates.tasksFinish,
    shortBinaryNumeralTerm row.nextCoordinates.tokensBoundary,
    shortBinaryNumeralTerm row.nextCoordinates.tokensCount,
    shortBinaryNumeralTerm row.nextCoordinates.tasksBoundary,
    shortBinaryNumeralTerm row.nextCoordinates.tasksCount,
    shortBinaryNumeralTerm row.nextSize.tokensBoundarySize,
    shortBinaryNumeralTerm row.nextSize.tasksBoundarySize,
    shortBinaryNumeralTerm row.stepWitness.slot0,
    shortBinaryNumeralTerm row.stepWitness.slot1,
    shortBinaryNumeralTerm row.stepWitness.slot2,
    shortBinaryNumeralTerm row.stepWitness.slot3,
    shortBinaryNumeralTerm row.stepWitness.slot4,
    shortBinaryNumeralTerm row.stepWitness.slot5,
    shortBinaryNumeralTerm row.stepWitness.slot6]

def compactParserSyntaxAdjacentStepSourceCurrentFormula :
    ArithmeticSemiformula Nat 33 :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserStateAtRowsDef.val) ⇜
    ![(#0 : ArithmeticSemiterm Nat 33), #1, #2, #3, #4, #5, #6, #7,
      #8, #9, #10, #11, #12, #13, #14, #15]

def compactParserSyntaxAdjacentStepSourceNextFormula :
    ArithmeticSemiformula Nat 33 :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserStateAtRowsDef.val) ⇜
    ![(#0 : ArithmeticSemiterm Nat 33), #1, #2, #3, #4,
      (‘#5 + 1’ : ArithmeticSemiterm Nat 33), #16, #17, #18, #19, #20,
      #21, #22, #23, #24, #25]

def compactParserSyntaxAdjacentStepSourceStepFormula :
    ArithmeticSemiformula Nat 33 :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserSyntaxStepRowsDef.val) ⇜
    ![(#0 : ArithmeticSemiterm Nat 33), #1, #2,
      #6, #7, #8, #9, #10, #11, #12, #13,
      #16, #17, #18, #19, #20, #21, #22, #23,
      #26, #27, #28, #29, #30, #31, #32]

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right :
      Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left : ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
      ArithmeticSemiformula targetVariables targetArity) =
        Rewriting.app right := by
  cases h
  rfl

theorem compactParserSyntaxAdjacentStepRowDef_emb_decomposition :
    Rewriting.emb (ξ := Nat) compactParserSyntaxAdjacentStepRowDef.val =
      compactParserSyntaxAdjacentStepSourceCurrentFormula ⋏
        (compactParserSyntaxAdjacentStepSourceNextFormula ⋏
          compactParserSyntaxAdjacentStepSourceStepFormula) := by
  unfold compactParserSyntaxAdjacentStepRowDef
  unfold compactParserSyntaxAdjacentStepSourceCurrentFormula
  unfold compactParserSyntaxAdjacentStepSourceNextFormula
  unfold compactParserSyntaxAdjacentStepSourceStepFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

def compactParserSyntaxAdjacentStepRowAtValuationIndexFormula
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (row : CompactParserSyntaxAdjacentStepRow) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactParserSyntaxAdjacentStepRowDef.val) ⇜
    compactParserSyntaxAdjacentStepAtValuationIndexTerms tokenTable width
      tokenCount stateBoundary stateCount indexTerm row

def compactParserSyntaxAdjacentStepRowAtValuationIndexExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (row : CompactParserSyntaxAdjacentStepRow) : ValuationFormula :=
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount indexTerm row.currentCoordinates
        row.currentSize ⋏
    (compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
        tokenCount stateBoundary stateCount nextIndexTerm row.nextCoordinates
          row.nextSize ⋏
      compactUnifiedParserSyntaxStepClosedFormula tokenTable width tokenCount
        row.currentCoordinates row.nextCoordinates row.stepWitness)

theorem parserSyntaxAdjacentIndexAdd_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables
  ext candidate
  simp [LO.FirstOrder.Semiterm.freeVariables_func]

theorem parserSyntaxAdjacentIndexOne_freeVariables :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

theorem parserSyntaxAdjacentIndexAdd_termValue
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  exact termValue_add valuation ![left, right]

theorem parserSyntaxAdjacentIndexOne_termValue (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

def compactParserSyntaxAdjacentStepAtValuationIndexCurrentResource
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
    indexTerm numericBound bitBound

def compactParserSyntaxAdjacentStepAtValuationIndexNextResource
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
    (‘!!indexTerm + 1’ : ValuationTerm) numericBound bitBound

def compactParserSyntaxAdjacentStepAtValuationIndexSyntaxResource
    (indexTerm : ValuationTerm)
    (tokenCount numericBound bitBound : Nat) : Nat :=
  let currentResource :=
    compactParserSyntaxAdjacentStepAtValuationIndexCurrentResource indexTerm
      numericBound bitBound
  let nextResource :=
    compactParserSyntaxAdjacentStepAtValuationIndexNextResource indexTerm
      numericBound bitBound
  let stepResource :=
    syntaxStepAllBranchesClosedFixedResource tokenCount numericBound bitBound
  valuationContextFormulaCodeSumEnvelope 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length +
    currentResource + nextResource + stepResource +
    2 * (binaryNatCode 4).length + 1

def compactParserSyntaxAdjacentStepAtValuationIndexFullyFixedPayloadPolynomial
    (indexTerm : ValuationTerm)
    (tokenCount numericBound bitBound : Nat) : Nat :=
  directThreeConjunctionGeneralPayloadEnvelope
    (compactParserSyntaxAdjacentStepAtValuationIndexSyntaxResource indexTerm
      tokenCount numericBound bitBound)
    (compactParserSyntaxAdjacentStepAtValuationIndexCurrentResource indexTerm
      numericBound bitBound)
    (compactParserSyntaxAdjacentStepAtValuationIndexNextResource indexTerm
      numericBound bitBound)
    (syntaxStepAllBranchesClosedFixedResource tokenCount numericBound bitBound)

#print axioms compactParserSyntaxAdjacentStepRowDef_emb_decomposition

end FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexSyntaxBase
