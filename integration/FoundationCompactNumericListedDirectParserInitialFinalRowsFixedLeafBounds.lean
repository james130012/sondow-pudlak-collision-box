import integration.FoundationCompactNumericListedDirectParserInitialStateFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserFinalStateFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectFreeVariables
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds

/-! # Fixed direct leaf bounds for the combined parser endpoints -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserInitialFormula
open FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserFinalFormula
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserFinalStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectFreeVariables

def parserInitialFinalZeroValuation : Nat -> Nat := fun _ => 0

structure ParserInitialFinalClosedDirectBound
    (formula : ValuationFormula) (resource : Nat) where
  proof : CertifiedPAContextProof ∅ formula
  payloadLength_le : proof.payloadLength <= resource

private theorem arithmeticAddTerm_freeVariables_initialFinalLeaf
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem arithmeticOneTerm_freeVariables_initialFinalLeaf :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticAddTerm_eq_func_initialFinalLeaf
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd_initialFinalLeaf
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_initialFinalLeaf]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_initialFinalLeaf
    (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

def parserInitialFinalStateCountTermCodeBound
    (stateCount fuel : Nat) : Nat :=
  max
    (binaryTermCode (shortBinaryNumeralTerm stateCount : ValuationTerm)).length
    (binaryTermCode
      (‘!!(shortBinaryNumeralTerm fuel) + 1’ : ValuationTerm)).length

def parserInitialFinalStateCountPayloadPolynomial
    (stateCount fuel numericBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial numericBound
    (parserInitialFinalStateCountTermCodeBound stateCount fuel)

noncomputable def parserInitialFinalStateCountClosedDirectBound
    (stateCount fuel numericBound : Nat)
    (hcount : stateCount = fuel + 1) :
    ParserInitialFinalClosedDirectBound
      “!!(shortBinaryNumeralTerm stateCount) =
        !!(shortBinaryNumeralTerm fuel) + 1”
      (parserInitialFinalStateCountPayloadPolynomial stateCount fuel
        numericBound) := by
  let leftTerm : ValuationTerm := shortBinaryNumeralTerm stateCount
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm fuel) + 1’
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      parserInitialFinalZeroValuation Language.Eq.eq ![leftTerm, rightTerm]
      (by
        change termValue parserInitialFinalZeroValuation leftTerm =
          termValue parserInitialFinalZeroValuation rightTerm
        simpa only [leftTerm, rightTerm, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd_initialFinalLeaf,
          termValue_arithmeticOne_initialFinalLeaf] using hcount)
  let certificate :
      CheckedHybridValuationBoundedFormulaCertificate
        parserInitialFinalZeroValuation
        “!!(shortBinaryNumeralTerm stateCount) =
          !!(shortBinaryNumeralTerm fuel) + 1” :=
    .cast (Semiformula.Operator.eq_def _ _).symm direct
  have hleftClosed : leftTerm.freeVariables = ∅ := by
    simp [leftTerm, shortBinaryNumeralTerm_freeVariables_eq_empty]
  have hrightClosed : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    rw [arithmeticAddTerm_freeVariables_initialFinalLeaf,
      arithmeticOneTerm_freeVariables_initialFinalLeaf,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hleftCode :
      (binaryTermCode leftTerm).length <=
        parserInitialFinalStateCountTermCodeBound stateCount fuel := by
    exact le_max_left _ _
  have hrightCode :
      (binaryTermCode rightTerm).length <=
        parserInitialFinalStateCountTermCodeBound stateCount fuel := by
    exact le_max_right _ _
  have hresource :
      hybridFormulaStructuralPayloadBound certificate <=
        parserInitialFinalStateCountPayloadPolynomial stateCount fuel
          numericBound := by
    have hfixed :=
      compilePositiveRelationPayloadResource_le_fixed_of_closed
        parserInitialFinalZeroValuation Language.Eq.eq leftTerm rightTerm
        numericBound
        (parserInitialFinalStateCountTermCodeBound stateCount fuel)
        hleftClosed hrightClosed hleftCode hrightCode
    simpa only [certificate, direct, hybridFormulaStructuralPayloadBound,
      parserInitialFinalStateCountPayloadPolynomial] using hfixed
  have hclosed :
      (“!!(shortBinaryNumeralTerm stateCount) =
        !!(shortBinaryNumeralTerm fuel) + 1” :
          ValuationFormula).freeVariables = ∅ := by
    simpa only [leftTerm, rightTerm] using
      (show
        (“!!leftTerm = !!rightTerm” : ValuationFormula).freeVariables = ∅ by
          change
            (Semiformula.rel Language.Eq.eq
              ![leftTerm, rightTerm]).freeVariables = ∅
          rw [LO.FirstOrder.Semiformula.freeVariables_rel]
          ext candidate
          constructor
          · intro hcandidate
            rcases Finset.mem_biUnion.mp hcandidate with
              ⟨coordinate, _, hcoordinate⟩
            cases coordinate using Fin.cases with
            | zero =>
                change candidate ∈ leftTerm.freeVariables at hcoordinate
                rw [hleftClosed] at hcoordinate
                simp at hcoordinate
            | succ coordinate =>
                cases coordinate using Fin.cases with
                | zero =>
                    change candidate ∈ rightTerm.freeVariables at hcoordinate
                    rw [hrightClosed] at hcoordinate
                    simp at hcoordinate
                | succ coordinate => exact Fin.elim0 coordinate
          · intro hcandidate
            simp at hcandidate)
  let proof : CertifiedPAContextProof ∅
      “!!(shortBinaryNumeralTerm stateCount) =
        !!(shortBinaryNumeralTerm fuel) + 1” :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed]
      simp [valuationContext]) certificate.compile
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _ certificate.compile).payloadLength
      <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact
    (compile_payloadLength_le_structuralPayloadBound certificate).trans
      hresource

noncomputable def parserInitialFinalStateAtRowsClosedDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserStateAtRows tokenTable width tokenCount
      stateBoundary stateCount index coordinates sizeWitness)
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
      (compactUnifiedParserStateAtRowsClosedFormula tokenTable width tokenCount
        stateBoundary stateCount index coordinates sizeWitness)
      (compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
        (shortBinaryNumeralTerm index) numericBound bitBound) := by
  let indexTerm : ValuationTerm := shortBinaryNumeralTerm index
  have hindexVariables : indexTerm.freeVariables ⊆ {0} := by
    rw [show indexTerm.freeVariables = ∅ by
      simp [indexTerm, shortBinaryNumeralTerm_freeVariables_eq_empty]]
    simp
  have hgraphAtTerm : CompactUnifiedParserStateAtRows tokenTable width
      tokenCount stateBoundary stateCount
      (termValue compactParserStateAtRowsZeroValuation indexTerm)
      coordinates sizeWitness := by
    simpa only [indexTerm, termValue_shortBinaryNumeralTerm] using hgraph
  let bound :=
    compactUnifiedParserStateAtRowsAtValuationIndexFullyUniformDirectFixedBound
      tokenTable width tokenCount stateBoundary stateCount indexTerm
      coordinates sizeWitness numericBound bitBound hindexVariables
      hgraphAtTerm hwidth htokenCount hstateCount hcoordinatesValue
      htokenTableSize hstateBoundarySize hcoordinatesSize hnumericSize
  have hformula :
      compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
          tokenCount stateBoundary stateCount indexTerm coordinates
            sizeWitness =
        compactUnifiedParserStateAtRowsClosedFormula tokenTable width
          tokenCount stateBoundary stateCount index coordinates
            sizeWitness := by
    rfl
  let contextualProof :=
    castValuationContextProof hformula bound.proof
  have hrowClosed :
      (compactUnifiedParserStateAtRowsClosedFormula tokenTable width
        tokenCount stateBoundary stateCount index coordinates
          sizeWitness).freeVariables = ∅ := by
    unfold compactUnifiedParserStateAtRowsClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    intro coordinate
    fin_cases coordinate <;>
      exact shortBinaryNumeralTerm_freeVariables_eq_empty _
  let proof : CertifiedPAContextProof ∅
      (compactUnifiedParserStateAtRowsClosedFormula tokenTable width tokenCount
        stateBoundary stateCount index coordinates sizeWitness) :=
    CertifiedPAContextProof.castContext (by
      rw [hrowClosed]
      simp [valuationContext]) contextualProof
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _ contextualProof).payloadLength
      <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  change (castValuationContextProof hformula bound.proof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  simpa only [indexTerm] using bound.payloadLength_le

noncomputable def parserInitialStateClosedDirectBoundOfGraph
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount taskKind taskBinderArity taskRepeatCount
      numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserInitialStateRows tokenTable width tokenCount
      coordinates sourceBoundary sourceCount taskKind taskBinderArity
        taskRepeatCount)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hsourceCountValue : sourceCount <= numericBound)
    (htasksCountValue : coordinates.tasksCount <= numericBound)
    (htasksFinishValue : coordinates.tasksFinish <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size coordinates.start <= bitBound)
    (hfinishSize : Nat.size coordinates.finish <= bitBound)
    (htokensFinishSize : Nat.size coordinates.tokensFinish <= bitBound)
    (htasksFinishSize : Nat.size coordinates.tasksFinish <= bitBound)
    (htokensBoundarySize : Nat.size coordinates.tokensBoundary <= bitBound)
    (htokensCountSize : Nat.size coordinates.tokensCount <= bitBound)
    (htasksBoundarySize : Nat.size coordinates.tasksBoundary <= bitBound)
    (htasksCountSize : Nat.size coordinates.tasksCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (htaskKindSize : Nat.size taskKind <= bitBound)
    (htaskBinderAritySize : Nat.size taskBinderArity <= bitBound)
    (htaskRepeatCountSize : Nat.size taskRepeatCount <= bitBound)
    (hnumericBoundSize : Nat.size numericBound <= bitBound) :
    ParserInitialFinalClosedDirectBound
      (compactUnifiedParserInitialStateRowsClosedFormula tokenTable width
        tokenCount coordinates sourceBoundary sourceCount taskKind
          taskBinderArity taskRepeatCount)
      (parserInitialStateFullyFixedPayloadPolynomial numericBound bitBound) := by
  let certificate :=
    compactUnifiedParserInitialStateRowsFixedCertificateOfGraph tokenTable
      width tokenCount coordinates sourceBoundary sourceCount taskKind
      taskBinderArity taskRepeatCount hgraph
  have hresource :
      hybridFormulaStructuralPayloadBound certificate <=
        parserInitialStateFullyFixedPayloadPolynomial numericBound bitBound := by
    exact
      compactUnifiedParserInitialStateRowsFixedCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount coordinates sourceBoundary sourceCount
        taskKind taskBinderArity taskRepeatCount numericBound bitBound hgraph
        hwidthValue htokenCountValue hsourceCountValue htasksCountValue
        htasksFinishValue htokenTableSize hwidthSize htokenCountSize
        hstartSize hfinishSize htokensFinishSize htasksFinishSize
        htokensBoundarySize htokensCountSize htasksBoundarySize htasksCountSize
        hsourceBoundarySize hsourceCountSize htaskKindSize
        htaskBinderAritySize htaskRepeatCountSize hnumericBoundSize
  have hclosed :=
    compactUnifiedParserInitialStateRowsClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount coordinates sourceBoundary sourceCount
      taskKind taskBinderArity taskRepeatCount
  let proof : CertifiedPAContextProof ∅
      (compactUnifiedParserInitialStateRowsClosedFormula tokenTable width
        tokenCount coordinates sourceBoundary sourceCount taskKind
          taskBinderArity taskRepeatCount) :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed]
      simp [valuationContext]) certificate.compile
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _ certificate.compile).payloadLength
      <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact
    (compile_payloadLength_le_structuralPayloadBound certificate).trans
      hresource

noncomputable def parserFinalStateClosedDirectBoundOfGraph
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount outputStart outputBoundary outputBoundarySize
      numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserFinalStateRows tokenTable width tokenCount
      coordinates sourceBoundary sourceCount outputStart outputBoundary
        outputBoundarySize)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hsourceCountValue : sourceCount <= numericBound)
    (htasksFinishValue : coordinates.tasksFinish <= numericBound)
    (htasksFinishSuccValue : coordinates.tasksFinish + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size coordinates.start <= bitBound)
    (hfinishSize : Nat.size coordinates.finish <= bitBound)
    (htokensFinishSize : Nat.size coordinates.tokensFinish <= bitBound)
    (htasksFinishSize : Nat.size coordinates.tasksFinish <= bitBound)
    (htokensBoundarySize : Nat.size coordinates.tokensBoundary <= bitBound)
    (htokensCountSize : Nat.size coordinates.tokensCount <= bitBound)
    (htasksBoundarySize : Nat.size coordinates.tasksBoundary <= bitBound)
    (htasksCountSize : Nat.size coordinates.tasksCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (houtputStartSize : Nat.size outputStart <= bitBound)
    (houtputBoundarySize : Nat.size outputBoundary <= bitBound)
    (houtputBoundarySizeSize : Nat.size outputBoundarySize <= bitBound)
    (htasksFinishSuccSize :
      Nat.size (coordinates.tasksFinish + 1) <= bitBound)
    (hnumericBoundSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ParserInitialFinalClosedDirectBound
      (compactUnifiedParserFinalStateRowsClosedFormula tokenTable width
        tokenCount coordinates sourceBoundary sourceCount outputStart
          outputBoundary outputBoundarySize)
      (parserFinalStateFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound) := by
  let bound :=
    compactUnifiedParserFinalStateRowsClosedDirectBoundOfGraph tokenTable width
      tokenCount coordinates sourceBoundary sourceCount outputStart
      outputBoundary outputBoundarySize numericBound bitBound hgraph
      hwidthValue htokenCountValue hsourceCountValue htasksFinishValue
      htasksFinishSuccValue htokenTableSize hwidthSize htokenCountSize
      hstartSize hfinishSize htokensFinishSize htasksFinishSize
      htokensBoundarySize htokensCountSize htasksBoundarySize htasksCountSize
      hsourceBoundarySize hsourceCountSize houtputStartSize
      houtputBoundarySize houtputBoundarySizeSize htasksFinishSuccSize
      hnumericBoundSize hbitPositive
  exact { proof := bound.proof, payloadLength_le := bound.payloadLength_le }

#print axioms parserInitialFinalStateCountClosedDirectBound
#print axioms parserInitialFinalStateAtRowsClosedDirectBoundOfGraph
#print axioms parserInitialStateClosedDirectBoundOfGraph
#print axioms parserFinalStateClosedDirectBoundOfGraph

end FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
