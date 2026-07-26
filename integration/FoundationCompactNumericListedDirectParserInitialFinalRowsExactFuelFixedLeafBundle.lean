import integration.FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBundle
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Five parser endpoint leaves at the exact composite fuel term

Three endpoint leaves are independent of the syntactic presentation of fuel
and are reused unchanged.  The state-count equality and final state-row leaf
are rebuilt with the original composite parser fuel term.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserFinalStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsCoordinateBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBundle
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality

private theorem exactFuelAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_exactFuelAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [exactFuelAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_exactFuelOne
    (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem exactFuelAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (Semiterm.func Language.Add.add ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  ext candidate
  constructor
  · intro hcandidate
    rw [Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem exactFuelOneTerm_freeVariables :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.numeral_one,
    Semiterm.Operator.One.term_eq]

def compactParserInitialFinalExactFuelCountFormula
    (stateCount inputCount : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm stateCount) =
    !!(compactParserSyntaxExactFuelTerm inputCount) + 1”

def compactParserInitialFinalExactFuelCountResource
    (inputCount : Nat) : Nat :=
  compileTermValueEqualityPayloadResource (fun _ => 0)
    (‘!!(compactParserSyntaxExactFuelTerm inputCount) + 1’ : ValuationTerm)

noncomputable def parserInitialFinalExactFuelCountClosedDirectBound
    (stateCount inputCount : Nat)
    (hcount :
      stateCount = compactParserSyntaxExactFuel inputCount + 1) :
    ParserInitialFinalClosedDirectBound
      (compactParserInitialFinalExactFuelCountFormula stateCount inputCount)
      (compactParserInitialFinalExactFuelCountResource inputCount) := by
  let rightTerm : ValuationTerm :=
    ‘!!(compactParserSyntaxExactFuelTerm inputCount) + 1’
  let raw := compileTermValueEquality (fun _ => 0) rightTerm
  have hvalue :
      termValue (fun _ => 0) rightTerm = stateCount := by
    dsimp only [rightTerm]
    rw [termValue_exactFuelAdd,
      compactParserSyntaxExactFuelTerm_value,
      termValue_exactFuelOne]
    exact hcount.symm
  have hformula :
      (“!!(shortBinaryNumeralTerm
          (termValue (fun _ => 0) rightTerm)) =
        !!rightTerm” : ValuationFormula) =
      compactParserInitialFinalExactFuelCountFormula stateCount inputCount := by
    rw [hvalue]
    rfl
  let aligned := CertifiedPAContextProof.cast hformula raw
  have hrightClosed : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    rw [exactFuelAddTerm_freeVariables,
      compactParserSyntaxExactFuelTerm_freeVariables_eq_empty,
      exactFuelOneTerm_freeVariables]
    simp
  have hcontext :
      valuationContext rightTerm.freeVariables (fun _ => 0) = ∅ := by
    rw [hrightClosed]
    simp [valuationContext]
  let proof := CertifiedPAContextProof.castContext hcontext aligned
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _
    (CertifiedPAContextProof.cast _ raw)).payloadLength <= _
  rw [CertifiedPAContextProof.castContext_payloadLength,
    CertifiedPAContextProof.cast_payloadLength]
  exact compileTermValueEquality_payloadLength_le_resource
    (fun _ => 0) rightTerm

def compactParserInitialFinalExactFuelFinalAtFormula
    (tokenTable width tokenCount stateBoundary stateCount inputCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness) :
    ValuationFormula :=
  compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
    tokenCount stateBoundary stateCount
      (compactParserSyntaxExactFuelTerm inputCount) coordinates sizeWitness

noncomputable def parserInitialFinalExactFuelFinalAtClosedDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount inputCount
      numericBound bitBound : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateAtRows tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
        coordinates sizeWitness)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hcoordinatesValue :
      CompactUnifiedParserStateCoordinateValueBound coordinates numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hcoordinatesSize :
      CompactUnifiedParserStateCoordinateSizeBound coordinates bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ParserInitialFinalClosedDirectBound
      (compactParserInitialFinalExactFuelFinalAtFormula tokenTable width
        tokenCount stateBoundary stateCount inputCount coordinates sizeWitness)
      (compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
        (compactParserSyntaxExactFuelTerm inputCount)
          numericBound bitBound) := by
  let indexTerm := compactParserSyntaxExactFuelTerm inputCount
  have hindexVariables : indexTerm.freeVariables ⊆ {0} := by
    rw [show indexTerm.freeVariables = ∅ by
      exact compactParserSyntaxExactFuelTerm_freeVariables_eq_empty inputCount]
    simp
  have hgraphAtTerm : CompactUnifiedParserStateAtRows tokenTable width
      tokenCount stateBoundary stateCount
      (termValue compactParserStateAtRowsZeroValuation indexTerm)
        coordinates sizeWitness := by
    change CompactUnifiedParserStateAtRows tokenTable width tokenCount
      stateBoundary stateCount
      (termValue (fun _ => 0)
        (compactParserSyntaxExactFuelTerm inputCount))
      coordinates sizeWitness
    rw [compactParserSyntaxExactFuelTerm_value]
    exact hgraph
  let bound :=
    compactUnifiedParserStateAtRowsAtValuationIndexFullyUniformDirectFixedBound
      tokenTable width tokenCount stateBoundary stateCount indexTerm
      coordinates sizeWitness numericBound bitBound hindexVariables
      hgraphAtTerm hwidth htokenCount hstateCount hcoordinatesValue
      htokenTableSize hstateBoundarySize hcoordinatesSize hnumericSize
  have hclosed :
      (compactParserInitialFinalExactFuelFinalAtFormula tokenTable width
        tokenCount stateBoundary stateCount inputCount coordinates
          sizeWitness).freeVariables = ∅ := by
    unfold compactParserInitialFinalExactFuelFinalAtFormula
      compactUnifiedParserStateAtRowsAtValuationIndexFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    intro coordinate
    fin_cases coordinate <;>
      first
      | exact compactParserSyntaxExactFuelTerm_freeVariables_eq_empty inputCount
      | exact shortBinaryNumeralTerm_freeVariables_eq_empty _
  let proof : CertifiedPAContextProof ∅
      (compactParserInitialFinalExactFuelFinalAtFormula tokenTable width
        tokenCount stateBoundary stateCount inputCount coordinates
          sizeWitness) :=
    CertifiedPAContextProof.castContext (by
      have hboundClosed :
          (compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable
            width tokenCount stateBoundary stateCount indexTerm coordinates
              sizeWitness).freeVariables = ∅ := by
        simpa only [indexTerm,
          compactParserInitialFinalExactFuelFinalAtFormula] using hclosed
      rw [hboundClosed]
      simp [valuationContext]) bound.proof
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _ bound.proof).payloadLength <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  simpa only [indexTerm] using bound.payloadLength_le

structure ParserInitialFinalExactFuelFiveLeafBounds
    (tokenTable width tokenCount stateBoundary stateCount inputCount
      inputBoundary expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount numericBound bitBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) where
  count :
    ParserInitialFinalClosedDirectBound
      (compactParserInitialFinalExactFuelCountFormula stateCount inputCount)
      (compactParserInitialFinalExactFuelCountResource inputCount)
  initialAt :
    ParserInitialFinalClosedDirectBound
      (compactUnifiedParserStateAtRowsClosedFormula tokenTable width tokenCount
        stateBoundary stateCount 0 witness.initialCoordinates
        witness.initialSizeWitness)
      (compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
        (shortBinaryNumeralTerm 0) numericBound bitBound)
  initial :
    ParserInitialFinalClosedDirectBound
      (compactUnifiedParserInitialStateRowsClosedFormula tokenTable width
        tokenCount witness.initialCoordinates inputBoundary inputCount taskKind
        taskBinderArity taskRepeatCount)
      (parserInitialStateFullyFixedPayloadPolynomial numericBound bitBound)
  finalAt :
    ParserInitialFinalClosedDirectBound
      (compactParserInitialFinalExactFuelFinalAtFormula tokenTable width
        tokenCount stateBoundary stateCount inputCount
          witness.finalCoordinates witness.finalSizeWitness)
      (compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
        (compactParserSyntaxExactFuelTerm inputCount) numericBound bitBound)
  final :
    ParserInitialFinalClosedDirectBound
      (compactUnifiedParserFinalStateRowsClosedFormula tokenTable width
        tokenCount witness.finalCoordinates expectedBoundary expectedCount
        witness.outputStart witness.outputBoundary witness.outputBoundarySize)
      (parserFinalStateFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound)

noncomputable def parserInitialFinalExactFuelFiveLeafBoundsOfGraph
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount numericBound bitBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates)
    (hgraph : CompactUnifiedParserInitialFinalRows tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount witness)
    (hvalue : ParserInitialFinalRowsValueBound tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount numericBound witness)
    (hsize : ParserInitialFinalRowsSizeBound tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount bitBound witness)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ParserInitialFinalExactFuelFiveLeafBounds tokenTable width tokenCount
      stateBoundary stateCount inputCount inputBoundary expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount numericBound
      bitBound witness := by
  let oldLeaves := parserInitialFinalFiveLeafBoundsOfGraph tokenTable width
    tokenCount stateBoundary stateCount
    (compactParserSyntaxExactFuel inputCount) inputBoundary inputCount
    expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
    numericBound bitBound witness hgraph hvalue hsize hnumericSize hbitPositive
  rcases hgraph with
    ⟨hcount, _hinitialAt, _hinitial, hfinalAt, _hfinal⟩
  have hwidthValue : width <= numericBound := by
    simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 1
  have htokenCountValue : tokenCount <= numericBound := by
    simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 2
  have hstateCountValue : stateCount <= numericBound := by
    simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 4
  have hfinalCoordinatesValue :=
    finalCoordinatesValueBound_of_combined tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
      taskBinderArity taskRepeatCount numericBound witness hvalue
  have htokenTableSize : Nat.size tokenTable <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 0
  have hstateBoundarySize : Nat.size stateBoundary <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 3
  have hfinalCoordinatesSize :=
    finalCoordinatesSizeBound_of_combined tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
      taskBinderArity taskRepeatCount bitBound witness hsize
  let count := parserInitialFinalExactFuelCountClosedDirectBound stateCount
    inputCount hcount
  let finalAt :=
    parserInitialFinalExactFuelFinalAtClosedDirectBoundOfGraph tokenTable width
      tokenCount stateBoundary stateCount inputCount numericBound bitBound
      witness.finalCoordinates witness.finalSizeWitness hfinalAt hwidthValue
      htokenCountValue hstateCountValue hfinalCoordinatesValue
      htokenTableSize hstateBoundarySize hfinalCoordinatesSize hnumericSize
  exact
    { count := count
      initialAt := oldLeaves.initialAt
      initial := oldLeaves.initial
      finalAt := finalAt
      final := oldLeaves.final }

#print axioms parserInitialFinalExactFuelCountClosedDirectBound
#print axioms parserInitialFinalExactFuelFinalAtClosedDirectBoundOfGraph
#print axioms parserInitialFinalExactFuelFiveLeafBoundsOfGraph

end FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle
