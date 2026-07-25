import integration.FoundationCompactNumericListedDirectParserFinalStatePrefixDirectBound
import integration.FoundationCompactNumericListedDirectParserFinalStateLayoutDirectBound
import integration.FoundationCompactNumericListedDirectParserFinalStateSameDirectBound
import integration.FoundationCompactNumericListedDirectParserFinalStateSizeAreaPairDirectBound
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-! # Fully fixed direct proof for the exact parser final-state formula -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserFinalStateFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserFinalFormula
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserFinalStateSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserFinalStatePrefixDirectBound
open FoundationCompactNumericListedDirectParserFinalStateLayoutDirectBound
open FoundationCompactNumericListedDirectParserFinalStateSameDirectBound
open FoundationCompactNumericListedDirectParserFinalStateSizeAreaPairDirectBound
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds

private theorem binaryFormulaCode_and_left_le_final
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem binaryFormulaCode_and_right_le_final
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem conjunction_left_closed_of_closed_final
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    left.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).1

private theorem conjunction_right_closed_of_closed_final
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    right.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).2

structure ParserFinalStateClosedDirectBound
    (formula : ValuationFormula) (resource : Nat) where
  proof : CertifiedPAContextProof ∅ formula
  payloadLength_le : proof.payloadLength <= resource

def parserFinalStateFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  let syntaxResource := parserFinalStateSyntaxResource bitBound
  let pairResource :=
    parserFinalSizeAreaPairPayloadPolynomial tokenCount numericBound bitBound
  hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
      bitBound)
    (hybridThreeConjunctionGeneralPayloadEnvelope syntaxResource
      (compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
        numericBound bitBound)
      (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      pairResource)

noncomputable def compactUnifiedParserFinalStateRowsClosedDirectBoundOfGraph
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
    ParserFinalStateClosedDirectBound
      (compactUnifiedParserFinalStateRowsClosedFormula tokenTable width
        tokenCount coordinates sourceBoundary sourceCount outputStart
          outputBoundary outputBoundarySize)
      (parserFinalStateFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound) := by
  rcases hgraph with ⟨⟨hprefix, hlayout, hsame⟩, hsize, harea⟩
  let prefixFormula := parserFinalPrefixFormula tokenTable width tokenCount
    coordinates.tasksFinish outputStart
  let layoutFormula := parserFinalLayoutFormula tokenTable width tokenCount
    outputStart sourceCount coordinates.finish outputBoundary
  let sameFormula := parserFinalSameFormula tokenTable width tokenCount
    sourceBoundary sourceCount outputBoundary
  let sizeFormula := parserFinalSizeFormula outputBoundarySize outputBoundary
  let areaFormula :=
    parserFinalAreaFormula outputBoundarySize sourceCount tokenCount
  let pairFormula := sizeFormula ⋏ areaFormula
  let prefixBound := parserFinalPrefixDirectBoundOfGraph tokenTable width
    tokenCount coordinates.tasksFinish outputStart numericBound bitBound hprefix
    hwidthValue htasksFinishValue htasksFinishSuccValue htokenTableSize
    hwidthSize htokenCountSize htasksFinishSize houtputStartSize
    htasksFinishSuccSize hbitPositive
  let layoutBound := parserFinalLayoutDirectBoundOfGraph tokenTable width
    tokenCount outputStart sourceCount coordinates.finish outputBoundary
    numericBound bitBound hlayout hwidthValue htokenCountValue
    hsourceCountValue htokenTableSize houtputBoundarySize hnumericBoundSize
  let sameBound := parserFinalSameDirectBoundOfGraph tokenTable width tokenCount
    sourceBoundary sourceCount outputBoundary numericBound bitBound hsame
    hwidthValue htokenCountValue hsourceCountValue htokenTableSize
    hsourceBoundarySize houtputBoundarySize hnumericBoundSize
  let pairBound := parserFinalSizeAreaPairDirectBound tokenCount outputBoundary
    sourceCount outputBoundarySize numericBound bitBound hsize harea
    htokenCountValue hsourceCountValue houtputBoundarySize hnumericBoundSize
  let prefixResource :=
    binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound bitBound
  let layoutResource :=
    compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let sameResource :=
    sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound
  let pairResource :=
    parserFinalSizeAreaPairPayloadPolynomial tokenCount numericBound bitBound
  let syntaxResource := parserFinalStateSyntaxResource bitBound
  have hfullCode :
      (binaryFormulaCode
        (prefixFormula ⋏
          (layoutFormula ⋏ (sameFormula ⋏ pairFormula)))).length <=
        syntaxResource := by
    have hcode :=
      compactUnifiedParserFinalStateRowsClosedFormula_code_length_le_fixed
        tokenTable width tokenCount coordinates sourceBoundary sourceCount
        outputStart outputBoundary outputBoundarySize bitBound htokenTableSize
        hwidthSize htokenCountSize hstartSize hfinishSize htokensFinishSize
        htasksFinishSize htokensBoundarySize htokensCountSize
        htasksBoundarySize htasksCountSize hsourceBoundarySize hsourceCountSize
        houtputStartSize houtputBoundarySize houtputBoundarySizeSize
    rw [compactUnifiedParserFinalStateRowsClosedFormula_alignment] at hcode
    simpa only [compactUnifiedParserFinalStateRowsExplicitFormula,
      parserFinalPrefixFormula, parserFinalLayoutFormula,
      parserFinalSameFormula, parserFinalSizeFormula, parserFinalAreaFormula,
      prefixFormula, layoutFormula, sameFormula, sizeFormula, areaFormula,
      pairFormula] using hcode
  have hfullClosed :
      (prefixFormula ⋏
        (layoutFormula ⋏ (sameFormula ⋏ pairFormula))).freeVariables = ∅ := by
    have hclosed :=
      compactUnifiedParserFinalStateRowsClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount coordinates sourceBoundary sourceCount
        outputStart outputBoundary outputBoundarySize
    rw [compactUnifiedParserFinalStateRowsClosedFormula_alignment] at hclosed
    simpa only [compactUnifiedParserFinalStateRowsExplicitFormula,
      parserFinalPrefixFormula, parserFinalLayoutFormula,
      parserFinalSameFormula, parserFinalSizeFormula, parserFinalAreaFormula,
      prefixFormula, layoutFormula, sameFormula, sizeFormula, areaFormula,
      pairFormula] using hclosed
  let innerFormula := layoutFormula ⋏ (sameFormula ⋏ pairFormula)
  have hprefixClosed : prefixFormula.freeVariables = ∅ :=
    conjunction_left_closed_of_closed_final prefixFormula innerFormula (by
      simpa only [innerFormula] using hfullClosed)
  have hinnerClosed : innerFormula.freeVariables = ∅ :=
    conjunction_right_closed_of_closed_final prefixFormula innerFormula (by
      simpa only [innerFormula] using hfullClosed)
  have hprefixCode :
      (binaryFormulaCode prefixFormula).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_final prefixFormula innerFormula).trans
      (by simpa only [innerFormula] using hfullCode)
  have hinnerCode :
      (binaryFormulaCode innerFormula).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_final prefixFormula innerFormula).trans
      (by simpa only [innerFormula] using hfullCode)
  let samePair := compileDirectConjunction sameBound.proof pairBound.proof
  have hsamePair :=
    compileDirectConjunction_payloadLength_le sameBound.proof pairBound.proof
      sameResource pairResource sameBound.payloadLength_le
      pairBound.payloadLength_le
  let layoutTail := compileDirectConjunction layoutBound.proof samePair
  have hlayoutTail :=
    compileDirectConjunction_payloadLength_le layoutBound.proof samePair
      layoutResource
      (transparentHybridConjunctionPayloadEnvelope parserFinalZeroValuation
        sameFormula pairFormula sameResource pairResource)
      layoutBound.payloadLength_le (by simpa only [samePair] using hsamePair)
  have hinnerGeneral :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      parserFinalZeroValuation layoutFormula sameFormula pairFormula
      layoutResource sameResource pairResource syntaxResource
      (by simp [syntaxResource, parserFinalStateSyntaxResource])
      (by simpa only [innerFormula] using hinnerClosed)
      (by simpa only [innerFormula] using hinnerCode)
  have hlayoutTailFixed :
      layoutTail.payloadLength <=
        hybridThreeConjunctionGeneralPayloadEnvelope syntaxResource
          layoutResource sameResource pairResource :=
    hlayoutTail.trans hinnerGeneral
  let assembled := compileDirectConjunction prefixBound.proof layoutTail
  have hassembled :=
    compileDirectConjunction_payloadLength_le prefixBound.proof layoutTail
      prefixResource
      (hybridThreeConjunctionGeneralPayloadEnvelope syntaxResource
        layoutResource sameResource pairResource)
      prefixBound.payloadLength_le hlayoutTailFixed
  have houterGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      parserFinalZeroValuation prefixFormula innerFormula prefixResource
      (hybridThreeConjunctionGeneralPayloadEnvelope syntaxResource
        layoutResource sameResource pairResource)
      syntaxResource
      (by simp [syntaxResource, parserFinalStateSyntaxResource])
      hprefixClosed hinnerClosed hprefixCode hinnerCode
      (by simpa only [innerFormula] using hfullCode)
  let atClosedFormula :=
    CertifiedPAContextProof.cast
      (compactUnifiedParserFinalStateRowsClosedFormula_alignment tokenTable
        width tokenCount coordinates sourceBoundary sourceCount outputStart
        outputBoundary outputBoundarySize).symm assembled
  let proof : CertifiedPAContextProof ∅
      (compactUnifiedParserFinalStateRowsClosedFormula tokenTable width
        tokenCount coordinates sourceBoundary sourceCount outputStart
          outputBoundary outputBoundarySize) :=
    CertifiedPAContextProof.castContext (by
      rw [hfullClosed]
      simp [valuationContext]) atClosedFormula
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _ atClosedFormula).payloadLength
      <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  change (CertifiedPAContextProof.cast _ assembled).payloadLength <= _
  rw [CertifiedPAContextProof.cast_payloadLength]
  unfold parserFinalStateFullyFixedPayloadPolynomial
  simpa only [prefixResource, layoutResource, sameResource, pairResource,
    syntaxResource] using hassembled.trans houterGeneral

#print axioms compactUnifiedParserFinalStateRowsClosedDirectBoundOfGraph

end FoundationCompactNumericListedDirectParserFinalStateFullyFixedBounds
