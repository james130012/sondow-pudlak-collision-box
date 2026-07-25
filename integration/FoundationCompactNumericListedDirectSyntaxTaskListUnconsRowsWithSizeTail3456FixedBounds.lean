import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail3456Certificate
import integration.FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-!
# Fixed `TripleBoundary ∧ Tail456` uncons tail
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail3456FixedBounds

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
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridUniversalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail456Certificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail456FixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail3456Certificate

theorem unconsRowsWithSizeTail3456Certificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize headKind headBinderArity headRepeatCount
      numericBound bitBound : Nat)
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
        (unconsRowsWithSizeTail3456Certificate tokenTable width tokenCount
          tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
          headKind headBinderArity headRepeatCount htriple hcons hsize
          harea) <=
      hybridConjunctionGeneralPayloadEnvelope
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
            (parserAreaFixedPayloadPolynomial bitBound))) := by
  let tripleFormula :=
    compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount
      tailBoundary
  let tailFormula : ValuationFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
        tokenTable width tokenCount tailBoundary tailCount sourceBoundary
        sourceCount (shortBinaryNumeralTerm headKind)
        (shortBinaryNumeralTerm headBinderArity)
        (shortBinaryNumeralTerm headRepeatCount) ⋏
      (compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
        (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
          (!!(shortBinaryNumeralTerm tailCount) + 1) *
            !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula))
  let tripleCertificate :=
    compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph
      tokenCount tailCount tailBoundary htriple
  have htripleResource :
      hybridFormulaStructuralPayloadBound tripleCertificate <=
        tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
          bitBound :=
    (compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenCount tailCount tailBoundary htriple).trans
    (compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope_le_fullyFixed
      tokenCount tailCount tailBoundary numericBound bitBound htriple
      htokenCount htailCount htailBoundarySize hnumericSize)
  have htailResource :=
    unconsRowsWithSizeTail456Certificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize headKind headBinderArity headRepeatCount
      numericBound bitBound hcons hsize harea hwidth htokenCount hsourceCount
      htailCount htokenTableSize hsourceBoundarySize htailBoundarySize
      hnumericSize
  have htransparent : hybridFormulaStructuralPayloadBound
      (unconsRowsWithSizeTail3456Certificate tokenTable width tokenCount
        tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
        headKind headBinderArity headRepeatCount htriple hcons hsize harea) <=
      transparentHybridConjunctionPayloadEnvelope
        FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
        tripleFormula tailFormula
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
            (parserAreaFixedPayloadPolynomial bitBound))) := by
    unfold unconsRowsWithSizeTail3456Certificate
    rw [hybridFormulaStructuralPayloadBound_conjunction_eq_transparent]
    exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _
      htripleResource htailResource
  have htripleClosed : tripleFormula.freeVariables = ∅ := by
    simpa only [tripleFormula] using
      compactAdditiveTripleBoundaryRowsClosedFormula_freeVariables_eq_empty
        tokenCount tailCount tailBoundary
  have htailClosed : tailFormula.freeVariables = ∅ := by
    dsimp only [tailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      taskConsGenericFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      natSizeClosedFormula_freeVariables_eq_empty,
      parserAreaFormula_freeVariables_eq_empty]
    simp
  have htripleCode :
      (binaryFormulaCode tripleFormula).length <=
        tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
          bitBound := by
    simpa only [tripleFormula, tripleCertificate] using
      (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        tripleCertificate).trans htripleResource
  have htailCode :
      (binaryFormulaCode tailFormula).length <=
        taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
            bitBound +
          compactNatSizeFixedPayloadPolynomial bitBound +
          parserAreaFixedPayloadPolynomial bitBound +
          2 * (binaryNatCode 4).length := by
    simpa only [tailFormula] using
      unconsRowsWithSizeTail456Formula_code_length_le_tight tokenTable width
        tokenCount tailBoundary tailCount sourceBoundary sourceCount
        tailBoundarySize headKind headBinderArity headRepeatCount numericBound
        bitBound hcons hsize harea hwidth htokenCount hsourceCount htailCount
        htokenTableSize hsourceBoundarySize htailBoundarySize hnumericSize
  let syntaxResource :=
    unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound bitBound
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold unconsRowsWithSizeFormulaCodePolynomial
    omega
  have htripleCodeGlobal :
      (binaryFormulaCode tripleFormula).length <= syntaxResource :=
    htripleCode.trans (by
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
      (binaryFormulaCode (tripleFormula ⋏ tailFormula)).length <=
        syntaxResource := by
    simp only [binaryFormulaCode, List.length_append]
    dsimp only [syntaxResource]
    unfold unconsRowsWithSizeFormulaCodePolynomial
    omega
  have henvelope :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      tripleFormula tailFormula
      (tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
        bitBound)
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource
        (taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
          bitBound)
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource
          (compactNatSizeFixedPayloadPolynomial bitBound)
          (parserAreaFixedPayloadPolynomial bitBound)))
      syntaxResource hpositive htripleClosed htailClosed htripleCodeGlobal
      htailCodeGlobal htotalCode
  exact htransparent.trans (by
    simpa only [syntaxResource] using henvelope)

theorem unconsRowsWithSizeTripleFormula_code_length_le_fixed
    (tokenCount tailCount tailBoundary numericBound bitBound : Nat)
    (htriple : CompactAdditiveTripleBoundaryRows tokenCount tailCount
      tailBoundary)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount
        tailBoundary)).length <=
      tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
        bitBound := by
  let certificate :=
    compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph
      tokenCount tailCount tailBoundary htriple
  have hresource : hybridFormulaStructuralPayloadBound certificate <=
      tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
        bitBound :=
    (compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenCount tailCount tailBoundary htriple).trans
    (compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope_le_fullyFixed
      tokenCount tailCount tailBoundary numericBound bitBound htriple
      htokenCount htailCount htailBoundarySize hnumericSize)
  exact
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      certificate).trans hresource

theorem unconsRowsWithSizeTail3456Formula_code_length_le_tight
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize headKind headBinderArity headRepeatCount
      numericBound bitBound : Nat)
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
      (compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount
          tailBoundary ⋏
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
            tokenTable width tokenCount tailBoundary tailCount sourceBoundary
            sourceCount (shortBinaryNumeralTerm headKind)
            (shortBinaryNumeralTerm headBinderArity)
            (shortBinaryNumeralTerm headRepeatCount) ⋏
          (compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
            (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
              (!!(shortBinaryNumeralTerm tailCount) + 1) *
                !!(shortBinaryNumeralTerm tokenCount)” :
              ValuationFormula))))).length <=
      tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
          bitBound +
        taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
          bitBound +
        compactNatSizeFixedPayloadPolynomial bitBound +
        parserAreaFixedPayloadPolynomial bitBound +
        3 * (binaryNatCode 4).length := by
  have htripleCode :=
    unconsRowsWithSizeTripleFormula_code_length_le_fixed tokenCount tailCount
      tailBoundary numericBound bitBound htriple htokenCount htailCount
      htailBoundarySize hnumericSize
  have htailCode :=
    unconsRowsWithSizeTail456Formula_code_length_le_tight tokenTable width
      tokenCount tailBoundary tailCount sourceBoundary sourceCount
      tailBoundarySize headKind headBinderArity headRepeatCount numericBound
      bitBound hcons hsize harea hwidth htokenCount hsourceCount htailCount
      htokenTableSize hsourceBoundarySize htailBoundarySize hnumericSize
  simp only [binaryFormulaCode, List.length_append] at htailCode ⊢
  omega

end FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail3456FixedBounds
