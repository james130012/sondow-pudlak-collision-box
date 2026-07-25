import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBundle
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Fully fixed direct proof for the combined parser endpoints -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserInitialFinalRowsFullyFixedDirectBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserFinalStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectFreeVariables
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsCoordinateBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedSyntaxBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBundle

noncomputable def compactUnifiedParserInitialFinalRowsClosedDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount numericBound bitBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates)
    (hgraph : CompactUnifiedParserInitialFinalRows tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount witness)
    (hvalue : ParserInitialFinalRowsValueBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount numericBound
      witness)
    (hsize : ParserInitialFinalRowsSizeBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount bitBound witness)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ParserInitialFinalClosedDirectBound
      (compactUnifiedParserInitialFinalRowsClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness)
      (parserInitialFinalRowsFullyFixedPayloadPolynomial stateCount fuel
        tokenCount numericBound bitBound) := by
  let leaves :=
    parserInitialFinalFiveLeafBoundsOfGraph tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount numericBound
      bitBound witness hgraph hvalue hsize hnumericSize hbitPositive
  let formula1 : ValuationFormula :=
    “!!(shortBinaryNumeralTerm stateCount) =
      !!(shortBinaryNumeralTerm fuel) + 1”
  let formula2 :=
    compactUnifiedParserStateAtRowsClosedFormula tokenTable width tokenCount
      stateBoundary stateCount 0 witness.initialCoordinates
      witness.initialSizeWitness
  let formula3 :=
    compactUnifiedParserInitialStateRowsClosedFormula tokenTable width
      tokenCount witness.initialCoordinates inputBoundary inputCount taskKind
      taskBinderArity taskRepeatCount
  let formula4 :=
    compactUnifiedParserStateAtRowsClosedFormula tokenTable width tokenCount
      stateBoundary stateCount fuel witness.finalCoordinates
      witness.finalSizeWitness
  let formula5 :=
    compactUnifiedParserFinalStateRowsClosedFormula tokenTable width tokenCount
      witness.finalCoordinates expectedBoundary expectedCount
      witness.outputStart witness.outputBoundary witness.outputBoundarySize
  let resource1 :=
    parserInitialFinalStateCountPayloadPolynomial stateCount fuel numericBound
  let resource2 :=
    compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (shortBinaryNumeralTerm 0) numericBound bitBound
  let resource3 :=
    parserInitialStateFullyFixedPayloadPolynomial numericBound bitBound
  let resource4 :=
    compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (shortBinaryNumeralTerm fuel) numericBound bitBound
  let resource5 :=
    parserFinalStateFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound
  let syntaxResource :=
    parserInitialFinalRowsAssemblySyntaxResource stateCount fuel tokenCount
      numericBound bitBound
  have hcode1 : (binaryFormulaCode formula1).length <= resource1 := by
    exact
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        leaves.count.proof).trans leaves.count.payloadLength_le
  have hcode2 : (binaryFormulaCode formula2).length <= resource2 := by
    exact
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        leaves.initialAt.proof).trans leaves.initialAt.payloadLength_le
  have hcode3 : (binaryFormulaCode formula3).length <= resource3 := by
    exact
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        leaves.initial.proof).trans leaves.initial.payloadLength_le
  have hcode4 : (binaryFormulaCode formula4).length <= resource4 := by
    exact
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        leaves.finalAt.proof).trans leaves.finalAt.payloadLength_le
  have hcode5 : (binaryFormulaCode formula5).length <= resource5 := by
    exact
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        leaves.final.proof).trans leaves.final.payloadLength_le
  have hfullCode :
      (binaryFormulaCode
        (formula1 ⋏
          (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5))))).length <=
        syntaxResource := by
    simp only [binaryFormulaCode, List.length_append]
    unfold syntaxResource parserInitialFinalRowsAssemblySyntaxResource
    omega
  have hfullClosed :
      (formula1 ⋏
        (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5)))).freeVariables =
        ∅ := by
    have hclosed :=
      compactUnifiedParserInitialFinalRowsClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness
    rw [compactUnifiedParserInitialFinalRowsClosedFormula_alignment] at hclosed
    simpa only [compactUnifiedParserInitialFinalRowsExplicitFormula,
      formula1, formula2, formula3, formula4, formula5] using hclosed
  have hsplit1 :
      formula1.freeVariables = ∅ ∧
        (formula2 ⋏
          (formula3 ⋏ (formula4 ⋏ formula5))).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hfullClosed
    exact Finset.union_eq_empty.mp hfullClosed
  have hsplit2 :
      formula2.freeVariables = ∅ ∧
        (formula3 ⋏ (formula4 ⋏ formula5)).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hsplit1
    exact Finset.union_eq_empty.mp hsplit1.2
  have hsplit3 :
      formula3.freeVariables = ∅ ∧
        (formula4 ⋏ formula5).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hsplit2
    exact Finset.union_eq_empty.mp hsplit2.2
  have hsplit4 :
      formula4.freeVariables = ∅ ∧ formula5.freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hsplit3
    exact Finset.union_eq_empty.mp hsplit3.2
  let proof1 : CertifiedPAContextProof
      (valuationContext formula1.freeVariables
        parserInitialFinalZeroValuation) formula1 :=
    CertifiedPAContextProof.castContext (by
      rw [hsplit1.1]
      simp [valuationContext]) leaves.count.proof
  let proof2 : CertifiedPAContextProof
      (valuationContext formula2.freeVariables
        parserInitialFinalZeroValuation) formula2 :=
    CertifiedPAContextProof.castContext (by
      rw [hsplit2.1]
      simp [valuationContext]) leaves.initialAt.proof
  let proof3 : CertifiedPAContextProof
      (valuationContext formula3.freeVariables
        parserInitialFinalZeroValuation) formula3 :=
    CertifiedPAContextProof.castContext (by
      rw [hsplit3.1]
      simp [valuationContext]) leaves.initial.proof
  let proof4 : CertifiedPAContextProof
      (valuationContext formula4.freeVariables
        parserInitialFinalZeroValuation) formula4 :=
    CertifiedPAContextProof.castContext (by
      rw [hsplit4.1]
      simp [valuationContext]) leaves.finalAt.proof
  let proof5 : CertifiedPAContextProof
      (valuationContext formula5.freeVariables
        parserInitialFinalZeroValuation) formula5 :=
    CertifiedPAContextProof.castContext (by
      rw [hsplit4.2]
      simp [valuationContext]) leaves.final.proof
  have hproof1 : proof1.payloadLength <= resource1 := by
    rw [show proof1.payloadLength = leaves.count.proof.payloadLength by
      exact CertifiedPAContextProof.castContext_payloadLength _ _]
    exact leaves.count.payloadLength_le
  have hproof2 : proof2.payloadLength <= resource2 := by
    rw [show proof2.payloadLength = leaves.initialAt.proof.payloadLength by
      exact CertifiedPAContextProof.castContext_payloadLength _ _]
    exact leaves.initialAt.payloadLength_le
  have hproof3 : proof3.payloadLength <= resource3 := by
    rw [show proof3.payloadLength = leaves.initial.proof.payloadLength by
      exact CertifiedPAContextProof.castContext_payloadLength _ _]
    exact leaves.initial.payloadLength_le
  have hproof4 : proof4.payloadLength <= resource4 := by
    rw [show proof4.payloadLength = leaves.finalAt.proof.payloadLength by
      exact CertifiedPAContextProof.castContext_payloadLength _ _]
    exact leaves.finalAt.payloadLength_le
  have hproof5 : proof5.payloadLength <= resource5 := by
    rw [show proof5.payloadLength = leaves.final.proof.payloadLength by
      exact CertifiedPAContextProof.castContext_payloadLength _ _]
    exact leaves.final.payloadLength_le
  let proof45 :=
    compileDirectConjunction proof4 proof5
  have hproof45 :=
    compileDirectConjunction_payloadLength_le proof4 proof5 resource4
      resource5 hproof4 hproof5
  let proof345 := compileDirectConjunction proof3 proof45
  have hproof345 :=
    compileDirectConjunction_payloadLength_le proof3 proof45 resource3
      (transparentHybridConjunctionPayloadEnvelope
        parserInitialFinalZeroValuation formula4 formula5 resource4 resource5)
      hproof3 (by simpa only [proof45] using hproof45)
  let proof2345 := compileDirectConjunction proof2 proof345
  have hproof2345 :=
    compileDirectConjunction_payloadLength_le proof2 proof345 resource2
      (transparentHybridConjunctionPayloadEnvelope
        parserInitialFinalZeroValuation formula3 (formula4 ⋏ formula5)
        resource3
        (transparentHybridConjunctionPayloadEnvelope
          parserInitialFinalZeroValuation formula4 formula5 resource4
          resource5))
      hproof2 (by simpa only [proof345] using hproof345)
  let assembled := compileDirectConjunction proof1 proof2345
  have hassembled :=
    compileDirectConjunction_payloadLength_le proof1 proof2345 resource1
      (transparentHybridConjunctionPayloadEnvelope
        parserInitialFinalZeroValuation formula2
        (formula3 ⋏ (formula4 ⋏ formula5)) resource2
        (transparentHybridConjunctionPayloadEnvelope
          parserInitialFinalZeroValuation formula3 (formula4 ⋏ formula5)
          resource3
          (transparentHybridConjunctionPayloadEnvelope
            parserInitialFinalZeroValuation formula4 formula5 resource4
            resource5)))
      hproof1 (by simpa only [proof2345] using hproof2345)
  have hgeneral :=
    transparentHybridFiveConjunctionPayloadEnvelope_le_closedGeneral
      parserInitialFinalZeroValuation formula1 formula2 formula3 formula4
      formula5 resource1 resource2 resource3 resource4 resource5
      syntaxResource
      (by
        unfold syntaxResource
          parserInitialFinalRowsAssemblySyntaxResource
        omega)
      hfullClosed hfullCode
  let atClosedFormula :=
    CertifiedPAContextProof.cast
      (compactUnifiedParserInitialFinalRowsClosedFormula_alignment tokenTable
        width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness).symm assembled
  let proof : CertifiedPAContextProof ∅
      (compactUnifiedParserInitialFinalRowsClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness) :=
    CertifiedPAContextProof.castContext (by
      rw [hfullClosed]
      simp [valuationContext]) atClosedFormula
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _ atClosedFormula).payloadLength
      <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  change (CertifiedPAContextProof.cast _ assembled).payloadLength <= _
  rw [CertifiedPAContextProof.cast_payloadLength]
  unfold parserInitialFinalRowsFullyFixedPayloadPolynomial
  simpa only [formula1, formula2, formula3, formula4, formula5, resource1,
    resource2, resource3, resource4, resource5, syntaxResource] using
      hassembled.trans hgeneral

#print axioms
  compactUnifiedParserInitialFinalRowsClosedDirectBoundOfGraph

end FoundationCompactNumericListedDirectParserInitialFinalRowsFullyFixedDirectBound
