import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBundle
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedSyntaxBounds
import integration.FoundationCompactPASevenConjunctionClosedDirectBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Fully fixed direct proof for formula-transform initial/final rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFullyFixedDirectBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPASevenConjunctionClosedDirectBounds
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsDirectSyntax
open FoundationCompactNumericListedDirectFormulaTransformInitialParserSourceFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsCoordinateBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBundleTypes
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBundle
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedSyntaxBounds
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserFinalStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds

noncomputable def compactFormulaTransformInitialFinalRowsClosedDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity numericBound
      bitBound : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates)
    (hgraph : CompactFormulaTransformInitialFinalRows tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity witness)
    (hvalue : FormulaTransformInitialFinalRowsValueBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity numericBound witness)
    (hsize : FormulaTransformInitialFinalRowsSizeBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity bitBound witness)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound)
    (hfinalTasksFinishSuccValue :
      witness.finalCoordinates.parserTasksFinish + 1 <= numericBound)
    (hbitPositive : 1 <= bitBound) :
    ParserInitialFinalClosedDirectBound
      (compactFormulaTransformInitialFinalRowsClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity witness)
      (formulaTransformInitialFinalRowsFullyFixedPayloadPolynomial stateCount
        fuel tokenCount numericBound bitBound) := by
  let leaves := formulaTransformInitialFinalSevenLeafBoundsOfGraph tokenTable
    width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
    expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
    expectedSuffixCount binderArity numericBound bitBound witness hgraph hvalue
    hsize hnumericSize hnumericBit hfinalTasksFinishSuccValue hbitPositive
  let formula1 : ValuationFormula :=
    “!!(shortBinaryNumeralTerm stateCount) =
      !!(shortBinaryNumeralTerm fuel) + 1”
  let formula2 := compactFormulaTransformStateAtRowsClosedFormula tokenTable
    width tokenCount stateBoundary stateCount 0 witness.initialCoordinates
      witness.initialSizeWitness
  let formula3 := compactFormulaTransformInitialParserSourcePublicFormula
    tokenTable width tokenCount inputBoundary inputCount binderArity
      witness.initialCoordinates
  let formula4 : ValuationFormula :=
    “!!(shortBinaryNumeralTerm witness.initialCoordinates.outputCount) = 0”
  let formula5 := compactFormulaTransformStateAtRowsClosedFormula tokenTable
    width tokenCount stateBoundary stateCount fuel witness.finalCoordinates
      witness.finalSizeWitness
  let formula6 := compactUnifiedParserFinalStateRowsClosedFormula tokenTable
    width tokenCount witness.finalCoordinates.parser expectedSuffixBoundary
    expectedSuffixCount witness.finalParserOutputStart
    witness.finalParserOutputBoundary witness.finalParserOutputBoundarySize
  let formula7 := compactAdditiveNatListSameRowsClosedFormula tokenTable width
    tokenCount expectedOutputBoundary expectedOutputCount
    witness.finalCoordinates.outputBoundary
    witness.finalCoordinates.outputCount
  let resource1 :=
    parserInitialFinalStateCountPayloadPolynomial stateCount fuel numericBound
  let resource2 :=
    compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (shortBinaryNumeralTerm 0) numericBound bitBound
  let resource3 :=
    compactFormulaTransformInitialParserSourceFullyFixedPayloadPolynomial
      numericBound bitBound
  let resource4 :=
    formulaTransformInitialOutputCountZeroPayloadPolynomial numericBound
      bitBound
  let resource5 :=
    compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (shortBinaryNumeralTerm fuel) numericBound bitBound
  let resource6 := parserFinalStateFullyFixedPayloadPolynomial tokenCount
    numericBound bitBound
  let resource7 :=
    sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound
  let syntaxResource :=
    formulaTransformInitialFinalRowsAssemblySyntaxResource stateCount fuel
      tokenCount numericBound bitBound
  have hcode6 : (binaryFormulaCode formula6).length <= syntaxResource :=
    ((CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      leaves.finalParser.proof).trans leaves.finalParser.payloadLength_le).trans
      (by
        dsimp only [syntaxResource, resource6]
        unfold formulaTransformInitialFinalRowsAssemblySyntaxResource
        omega)
  have hcode7 : (binaryFormulaCode formula7).length <= syntaxResource :=
    ((CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      leaves.finalOutput.proof).trans leaves.finalOutput.payloadLength_le).trans
      (by
        dsimp only [syntaxResource, resource7]
        unfold formulaTransformInitialFinalRowsAssemblySyntaxResource
        omega)
  have hcode67 :
      (binaryFormulaCode (formula6 ⋏ formula7)).length <= syntaxResource := by
    have hraw6 : (binaryFormulaCode formula6).length <= resource6 :=
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        leaves.finalParser.proof).trans leaves.finalParser.payloadLength_le
    have hraw7 : (binaryFormulaCode formula7).length <= resource7 :=
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        leaves.finalOutput.proof).trans leaves.finalOutput.payloadLength_le
    have htag : 1 <= (binaryNatCode 4).length := by decide
    simp only [binaryFormulaCode, List.length_append]
    unfold syntaxResource
      formulaTransformInitialFinalRowsAssemblySyntaxResource
    omega
  have hfullCode :
      (binaryFormulaCode
        (formula1 ⋏
          (formula2 ⋏
            (formula3 ⋏
              (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7))))))).length <=
        syntaxResource := by
    have h1 : (binaryFormulaCode formula1).length <= resource1 :=
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        leaves.count.proof).trans leaves.count.payloadLength_le
    have h2 : (binaryFormulaCode formula2).length <= resource2 :=
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        leaves.initialAt.proof).trans leaves.initialAt.payloadLength_le
    have h3 : (binaryFormulaCode formula3).length <= resource3 :=
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        leaves.initialParser.proof).trans leaves.initialParser.payloadLength_le
    have h4 : (binaryFormulaCode formula4).length <= resource4 :=
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        leaves.initialOutputCount.proof).trans
          leaves.initialOutputCount.payloadLength_le
    have h5 : (binaryFormulaCode formula5).length <= resource5 :=
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        leaves.finalAt.proof).trans leaves.finalAt.payloadLength_le
    have h6 : (binaryFormulaCode formula6).length <= resource6 :=
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        leaves.finalParser.proof).trans leaves.finalParser.payloadLength_le
    have h7 : (binaryFormulaCode formula7).length <= resource7 :=
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        leaves.finalOutput.proof).trans leaves.finalOutput.payloadLength_le
    have htag : 1 <= (binaryNatCode 4).length := by decide
    simp only [binaryFormulaCode, List.length_append]
    unfold syntaxResource
      formulaTransformInitialFinalRowsAssemblySyntaxResource
    omega
  have hfullClosed :
      (formula1 ⋏
        (formula2 ⋏
          (formula3 ⋏
            (formula4 ⋏
              (formula5 ⋏ (formula6 ⋏ formula7)))))).freeVariables = ∅ := by
    have hclosed :=
      compactFormulaTransformInitialFinalRowsPublicExplicitFormula_freeVariables_eq_empty
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity witness
    simpa only [compactFormulaTransformInitialFinalRowsPublicExplicitFormula,
      formula1, formula2, formula3, formula4, formula5, formula6, formula7]
      using hclosed
  have hsplit1 : formula1.freeVariables = ∅ ∧
      (formula2 ⋏
        (formula3 ⋏
          (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7))))).freeVariables =
        ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hfullClosed
    exact Finset.union_eq_empty.mp hfullClosed
  have hsplit2 : formula2.freeVariables = ∅ ∧
      (formula3 ⋏
        (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7)))).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hsplit1
    exact Finset.union_eq_empty.mp hsplit1.2
  have hsplit3 : formula3.freeVariables = ∅ ∧
      (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7))).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hsplit2
    exact Finset.union_eq_empty.mp hsplit2.2
  have hsplit4 : formula4.freeVariables = ∅ ∧
      (formula5 ⋏ (formula6 ⋏ formula7)).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hsplit3
    exact Finset.union_eq_empty.mp hsplit3.2
  have hsplit5 : formula5.freeVariables = ∅ ∧
      (formula6 ⋏ formula7).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hsplit4
    exact Finset.union_eq_empty.mp hsplit4.2
  have hsplit6 : formula6.freeVariables = ∅ ∧ formula7.freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hsplit5
    exact Finset.union_eq_empty.mp hsplit5.2
  let assembled := sevenConjunctionClosedDirectBound
    formulaTransformInitialFinalZeroValuation formula1 formula2 formula3
    formula4 formula5 formula6 formula7 resource1 resource2 resource3
    resource4 resource5 resource6 resource7 syntaxResource leaves.count.proof
    leaves.initialAt.proof leaves.initialParser.proof
    leaves.initialOutputCount.proof leaves.finalAt.proof
    leaves.finalParser.proof leaves.finalOutput.proof
    leaves.count.payloadLength_le leaves.initialAt.payloadLength_le
    leaves.initialParser.payloadLength_le
    leaves.initialOutputCount.payloadLength_le leaves.finalAt.payloadLength_le
    leaves.finalParser.payloadLength_le leaves.finalOutput.payloadLength_le
    hsplit1.1 hsplit2.1 hsplit3.1 hsplit4.1 hsplit5.1 hsplit6.1 hsplit6.2
    hcode6 hcode7 hcode67 hfullCode
    (by
      unfold syntaxResource
        formulaTransformInitialFinalRowsAssemblySyntaxResource
      omega)
  let atClosedFormula := CertifiedPAContextProof.cast
    (compactFormulaTransformInitialFinalRowsClosedFormula_alignment_public
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity witness).symm
    assembled.proof
  let proof : CertifiedPAContextProof ∅
      (compactFormulaTransformInitialFinalRowsClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity witness) :=
    CertifiedPAContextProof.castContext (by
      rw [hfullClosed]
      simp [valuationContext]) atClosedFormula
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _ atClosedFormula).payloadLength
      <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  change (CertifiedPAContextProof.cast _ assembled.proof).payloadLength <= _
  rw [CertifiedPAContextProof.cast_payloadLength]
  have hbound := assembled.payloadLength_le
  unfold formulaTransformInitialFinalRowsFullyFixedPayloadPolynomial
  unfold sevenConjunctionClosedDirectPayloadEnvelope at hbound
  simpa only [formula1, formula2, formula3, formula4, formula5, formula6,
    formula7, resource1, resource2, resource3, resource4, resource5,
    resource6, resource7, syntaxResource, assembled] using hbound

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFullyFixedDirectBound
