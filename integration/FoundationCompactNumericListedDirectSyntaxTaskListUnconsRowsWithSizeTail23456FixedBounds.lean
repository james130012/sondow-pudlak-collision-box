import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail23456Certificate
import integration.FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-!
# Fixed `DropOne ∧ Tail3456` uncons tail
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail23456FixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsFullyFixedBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridUniversalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail3456Certificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail3456FixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail23456Certificate

theorem unconsRowsWithSizeTail23456Certificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount
      numericBound bitBound : Nat)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount 1)
    (htriple : CompactAdditiveTripleBoundaryRows tokenCount tailCount
      tailBoundary)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount headKind
      headBinderArity headRepeatCount)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (unconsRowsWithSizeTail23456Certificate tokenTable width tokenCount
          sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
          headKind headBinderArity headRepeatCount hdrop htriple hcons hsize
          harea) <=
      hybridConjunctionGeneralPayloadEnvelope
        (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
          bitBound)
        (taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound)
        (hybridConjunctionGeneralPayloadEnvelope
          (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
            bitBound)
          (tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
            bitBound)
          (hybridConjunctionGeneralPayloadEnvelope
            (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
              bitBound)
            (taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
              bitBound)
            (hybridConjunctionGeneralPayloadEnvelope
              (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
                bitBound)
              (compactNatSizeFixedPayloadPolynomial bitBound)
              (parserAreaFixedPayloadPolynomial bitBound)))) := by
  let dropFormula :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable
      width tokenCount sourceBoundary sourceCount tailBoundary tailCount 1
  let tailFormula : ValuationFormula :=
    compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount
        tailBoundary ⋏
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
          tokenTable width tokenCount tailBoundary tailCount sourceBoundary
          sourceCount (shortBinaryNumeralTerm headKind)
          (shortBinaryNumeralTerm headBinderArity)
          (shortBinaryNumeralTerm headRepeatCount) ⋏
        (compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
          (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
            (!!(shortBinaryNumeralTerm tailCount) + 1) *
              !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula)))
  let dropCertificate :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hdrop
  have hdropResource :
      hybridFormulaStructuralPayloadBound dropCertificate <=
        taskDropOneCompleteFullyFixedPayloadPolynomial numericBound
          bitBound :=
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hdrop).trans
    (compactAdditiveSyntaxTaskListDropOneRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount numericBound bitBound hdrop hwidth htokenCount hsourceCount
      htokenTableSize hsourceBoundarySize htailBoundarySize hnumericSize)
  have htailResource :=
    unconsRowsWithSizeTail3456Certificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize headKind headBinderArity headRepeatCount
      numericBound bitBound htriple hcons hsize harea hwidth htokenCount
      hsourceCount htailCount htokenTableSize hsourceBoundarySize
      htailBoundarySize hnumericSize
  have htransparent : hybridFormulaStructuralPayloadBound
      (unconsRowsWithSizeTail23456Certificate tokenTable width tokenCount
        sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
        headKind headBinderArity headRepeatCount hdrop htriple hcons hsize
        harea) <=
      transparentHybridConjunctionPayloadEnvelope
        FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
        dropFormula tailFormula
        (taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound)
        (hybridConjunctionGeneralPayloadEnvelope
          (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
            bitBound)
          (tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
            bitBound)
          (hybridConjunctionGeneralPayloadEnvelope
            (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
              bitBound)
            (taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
              bitBound)
            (hybridConjunctionGeneralPayloadEnvelope
              (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
                bitBound)
              (compactNatSizeFixedPayloadPolynomial bitBound)
              (parserAreaFixedPayloadPolynomial bitBound)))) := by
    unfold unconsRowsWithSizeTail23456Certificate
    rw [hybridFormulaStructuralPayloadBound_conjunction_eq_transparent]
    exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _
      hdropResource htailResource
  have hdropClosed : dropFormula.freeVariables = ∅ := by
    simpa only [dropFormula] using
      compactAdditiveSyntaxTaskListDropOneRowsClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount
  have htailClosed : tailFormula.freeVariables = ∅ := by
    dsimp only [tailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectCompiler.compactAdditiveTripleBoundaryRowsClosedFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      taskConsGenericFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      natSizeClosedFormula_freeVariables_eq_empty,
      parserAreaFormula_freeVariables_eq_empty]
    simp
  have hdropCode :
      (binaryFormulaCode dropFormula).length <=
        taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound := by
    simpa only [dropFormula, dropCertificate] using
      (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        dropCertificate).trans hdropResource
  have htailCode :
      (binaryFormulaCode tailFormula).length <=
        tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
            bitBound +
          taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
            bitBound +
          compactNatSizeFixedPayloadPolynomial bitBound +
          parserAreaFixedPayloadPolynomial bitBound +
          3 * (binaryNatCode 4).length := by
    simpa only [tailFormula] using
      unconsRowsWithSizeTail3456Formula_code_length_le_tight tokenTable width
        tokenCount tailBoundary tailCount sourceBoundary sourceCount
        tailBoundarySize headKind headBinderArity headRepeatCount numericBound
        bitBound htriple hcons hsize harea hwidth htokenCount hsourceCount
        htailCount htokenTableSize hsourceBoundarySize htailBoundarySize
        hnumericSize
  let syntaxResource :=
    unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound bitBound
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold unconsRowsWithSizeFormulaCodePolynomial
    omega
  have hdropCodeGlobal :
      (binaryFormulaCode dropFormula).length <= syntaxResource :=
    hdropCode.trans (by
      dsimp only [syntaxResource]
      unfold unconsRowsWithSizeFormulaCodePolynomial
      omega)
  have htailCodeGlobal :
      (binaryFormulaCode tailFormula).length <= syntaxResource :=
    htailCode.trans (by
      dsimp only [syntaxResource]
      unfold unconsRowsWithSizeFormulaCodePolynomial
      omega)
  have htotalCode :
      (binaryFormulaCode (dropFormula ⋏ tailFormula)).length <=
        syntaxResource := by
    simp only [binaryFormulaCode, List.length_append]
    dsimp only [syntaxResource]
    unfold unconsRowsWithSizeFormulaCodePolynomial
    omega
  have henvelope :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      dropFormula tailFormula
      (taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource
        (tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
          bitBound)
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource
          (taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
            bitBound)
          (hybridConjunctionGeneralPayloadEnvelope syntaxResource
            (compactNatSizeFixedPayloadPolynomial bitBound)
            (parserAreaFixedPayloadPolynomial bitBound))))
      syntaxResource hpositive hdropClosed htailClosed hdropCodeGlobal
      htailCodeGlobal htotalCode
  exact htransparent.trans (by
    simpa only [syntaxResource] using henvelope)

theorem unconsRowsWithSizeDropFormula_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount numericBound bitBound : Nat)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount 1)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount 1)).length <=
      taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound := by
  let certificate :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hdrop
  have hresource : hybridFormulaStructuralPayloadBound certificate <=
      taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound :=
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hdrop).trans
    (compactAdditiveSyntaxTaskListDropOneRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount numericBound bitBound hdrop hwidth htokenCount hsourceCount
      htokenTableSize hsourceBoundarySize htailBoundarySize hnumericSize)
  exact
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      certificate).trans hresource

theorem unconsRowsWithSizeTail23456Formula_code_length_le_tight
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount
      numericBound bitBound : Nat)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount 1)
    (htriple : CompactAdditiveTripleBoundaryRows tokenCount tailCount
      tailBoundary)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount headKind
      headBinderArity headRepeatCount)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
          tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
          tailCount 1 ⋏
        (compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount
            tailBoundary ⋏
          (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
              tokenTable width tokenCount tailBoundary tailCount
              sourceBoundary sourceCount (shortBinaryNumeralTerm headKind)
              (shortBinaryNumeralTerm headBinderArity)
              (shortBinaryNumeralTerm headRepeatCount) ⋏
            (compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
              (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
                (!!(shortBinaryNumeralTerm tailCount) + 1) *
                  !!(shortBinaryNumeralTerm tokenCount)” :
                ValuationFormula)))))).length <=
      taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound +
        tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
          bitBound +
        taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
          bitBound +
        compactNatSizeFixedPayloadPolynomial bitBound +
        parserAreaFixedPayloadPolynomial bitBound +
        4 * (binaryNatCode 4).length := by
  have hdropCode :=
    unconsRowsWithSizeDropFormula_code_length_le_fixed tokenTable width
      tokenCount sourceBoundary sourceCount tailBoundary tailCount numericBound
      bitBound hdrop hwidth htokenCount hsourceCount htokenTableSize
      hsourceBoundarySize htailBoundarySize hnumericSize
  have htailCode :=
    unconsRowsWithSizeTail3456Formula_code_length_le_tight tokenTable width
      tokenCount tailBoundary tailCount sourceBoundary sourceCount
      tailBoundarySize headKind headBinderArity headRepeatCount numericBound
      bitBound htriple hcons hsize harea hwidth htokenCount hsourceCount
      htailCount htokenTableSize hsourceBoundarySize htailBoundarySize
      hnumericSize
  simp only [binaryFormulaCode, List.length_append] at htailCode ⊢
  omega

end FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail23456FixedBounds
