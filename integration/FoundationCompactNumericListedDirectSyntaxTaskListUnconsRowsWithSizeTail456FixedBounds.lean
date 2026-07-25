import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail456Certificate
import integration.FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-!
# Fixed `ConsRows ∧ (NatSize ∧ area)` uncons tail
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail456FixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactListedLocalCostPrimitives
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
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56Certificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56FixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail456Certificate

theorem unconsRowsWithSizeTail456Certificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize headKind headBinderArity headRepeatCount
      numericBound bitBound : Nat)
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
        (unconsRowsWithSizeTail456Certificate tokenTable width tokenCount
          tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
          headKind headBinderArity headRepeatCount hcons hsize harea) <=
      hybridConjunctionGeneralPayloadEnvelope
        (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
          bitBound)
        (taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
          bitBound)
        (hybridConjunctionGeneralPayloadEnvelope
          (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
            bitBound)
          (compactNatSizeFixedPayloadPolynomial bitBound)
          (parserAreaFixedPayloadPolynomial bitBound)) := by
  let consFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable
      width tokenCount tailBoundary tailCount sourceBoundary sourceCount
      (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)
  let tailFormula : ValuationFormula :=
    compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
      (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
        (!!(shortBinaryNumeralTerm tailCount) + 1) *
          !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula)
  let consCertificate :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount headKind headBinderArity headRepeatCount
      (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)
      (termValue_shortBinaryNumeralTerm · headKind)
      (termValue_shortBinaryNumeralTerm · headBinderArity)
      (termValue_shortBinaryNumeralTerm · headRepeatCount) hcons
  have hconsResource :
      hybridFormulaStructuralPayloadBound consCertificate <=
        taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
          bitBound := by
    simpa only [consCertificate,
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph]
      using
      (taskConsGenericCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount tailBoundary tailCount sourceBoundary
        sourceCount headKind headBinderArity headRepeatCount numericBound
        bitBound hwidth htokenCount hsourceCount htokenTableSize
        htailBoundarySize hsourceBoundarySize hnumericSize hcons.1
        (compactAdditiveSyntaxTaskListConsRowsHeadDataOfGraph tokenTable width
          tokenCount tailBoundary tailCount sourceBoundary sourceCount
          headKind headBinderArity headRepeatCount hcons)
        (compactAdditiveSyntaxTaskListConsRowsTailRowDataOfGraph tokenTable
          width tokenCount tailBoundary tailCount sourceBoundary sourceCount
          headKind headBinderArity headRepeatCount hcons))
  have htailResource :=
    unconsRowsWithSizeTail56Certificate_structuralPayloadBound_le_fixed
      tokenCount tailBoundary tailCount tailBoundarySize numericBound bitBound
      hsize harea htokenCount htailCount htailBoundarySize hnumericSize
  have htransparent : hybridFormulaStructuralPayloadBound
      (unconsRowsWithSizeTail456Certificate tokenTable width tokenCount
        tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
        headKind headBinderArity headRepeatCount hcons hsize harea) <=
      transparentHybridConjunctionPayloadEnvelope
        FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
        consFormula tailFormula
        (taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
          bitBound)
        (hybridConjunctionGeneralPayloadEnvelope
          (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
            bitBound)
          (compactNatSizeFixedPayloadPolynomial bitBound)
          (parserAreaFixedPayloadPolynomial bitBound)) := by
    unfold unconsRowsWithSizeTail456Certificate
    rw [hybridFormulaStructuralPayloadBound_conjunction_eq_transparent]
    exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _
      hconsResource htailResource
  have hconsClosed : consFormula.freeVariables = ∅ := by
    simpa only [consFormula] using
      taskConsGenericFormula_freeVariables_eq_empty tokenTable width tokenCount
        tailBoundary tailCount sourceBoundary sourceCount headKind
        headBinderArity headRepeatCount
  have htailClosed : tailFormula.freeVariables = ∅ := by
    dsimp only [tailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      natSizeClosedFormula_freeVariables_eq_empty,
      parserAreaFormula_freeVariables_eq_empty]
    simp
  have hconsCode :
      (binaryFormulaCode consFormula).length <=
        taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
          bitBound := by
    simpa only [consFormula, consCertificate] using
      (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        consCertificate).trans hconsResource
  have htailCode :
      (binaryFormulaCode tailFormula).length <=
        compactNatSizeFixedPayloadPolynomial bitBound +
          parserAreaFixedPayloadPolynomial bitBound +
          (binaryNatCode 4).length := by
    simpa only [tailFormula] using
      unconsRowsWithSizeTail56Formula_code_length_le_tight tokenCount
        tailBoundary tailCount tailBoundarySize numericBound bitBound hsize
        harea htokenCount htailCount htailBoundarySize hnumericSize
  let syntaxResource :=
    unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound bitBound
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold unconsRowsWithSizeFormulaCodePolynomial
    omega
  have hconsCodeGlobal :
      (binaryFormulaCode consFormula).length <= syntaxResource :=
    hconsCode.trans (by
      dsimp only [syntaxResource]
      unfold unconsRowsWithSizeFormulaCodePolynomial
      omega)
  have htailCodeGlobal :
      (binaryFormulaCode tailFormula).length <= syntaxResource := by
    exact htailCode.trans (by
      dsimp only [syntaxResource]
      unfold unconsRowsWithSizeFormulaCodePolynomial
      omega)
  have htotalCode :
      (binaryFormulaCode (consFormula ⋏ tailFormula)).length <=
        syntaxResource := by
    simp only [binaryFormulaCode, List.length_append]
    dsimp only [syntaxResource]
    unfold unconsRowsWithSizeFormulaCodePolynomial
    omega
  have henvelope :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      consFormula tailFormula
      (taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound)
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource
        (compactNatSizeFixedPayloadPolynomial bitBound)
        (parserAreaFixedPayloadPolynomial bitBound))
      syntaxResource hpositive hconsClosed htailClosed hconsCodeGlobal
      htailCodeGlobal htotalCode
  exact htransparent.trans (by
    simpa only [syntaxResource] using henvelope)

theorem unconsRowsWithSizeConsFormula_code_length_le_fixed
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount headKind headBinderArity headRepeatCount numericBound
      bitBound : Nat)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount headKind
      headBinderArity headRepeatCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
        tokenTable width tokenCount tailBoundary tailCount sourceBoundary
        sourceCount (shortBinaryNumeralTerm headKind)
        (shortBinaryNumeralTerm headBinderArity)
        (shortBinaryNumeralTerm headRepeatCount))).length <=
      taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound := by
  let certificate :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount headKind headBinderArity headRepeatCount
      (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)
      (termValue_shortBinaryNumeralTerm · headKind)
      (termValue_shortBinaryNumeralTerm · headBinderArity)
      (termValue_shortBinaryNumeralTerm · headRepeatCount) hcons
  have hresource : hybridFormulaStructuralPayloadBound certificate <=
      taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound := by
    simpa only [certificate,
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph]
      using
      (taskConsGenericCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount tailBoundary tailCount sourceBoundary
        sourceCount headKind headBinderArity headRepeatCount numericBound
        bitBound hwidth htokenCount hsourceCount htokenTableSize
        htailBoundarySize hsourceBoundarySize hnumericSize hcons.1
        (compactAdditiveSyntaxTaskListConsRowsHeadDataOfGraph tokenTable width
          tokenCount tailBoundary tailCount sourceBoundary sourceCount
          headKind headBinderArity headRepeatCount hcons)
        (compactAdditiveSyntaxTaskListConsRowsTailRowDataOfGraph tokenTable
          width tokenCount tailBoundary tailCount sourceBoundary sourceCount
          headKind headBinderArity headRepeatCount hcons))
  exact
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      certificate).trans hresource

theorem unconsRowsWithSizeTail456Formula_code_length_le_tight
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize headKind headBinderArity headRepeatCount
      numericBound bitBound : Nat)
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
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
          tokenTable width tokenCount tailBoundary tailCount sourceBoundary
          sourceCount (shortBinaryNumeralTerm headKind)
          (shortBinaryNumeralTerm headBinderArity)
          (shortBinaryNumeralTerm headRepeatCount) ⋏
        (compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
          (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
            (!!(shortBinaryNumeralTerm tailCount) + 1) *
              !!(shortBinaryNumeralTerm tokenCount)” :
            ValuationFormula)))).length <=
      taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
          bitBound +
        compactNatSizeFixedPayloadPolynomial bitBound +
        parserAreaFixedPayloadPolynomial bitBound +
        2 * (binaryNatCode 4).length := by
  have hconsCode :=
    unconsRowsWithSizeConsFormula_code_length_le_fixed tokenTable width
      tokenCount tailBoundary tailCount sourceBoundary sourceCount headKind
      headBinderArity headRepeatCount numericBound bitBound hcons hwidth
      htokenCount hsourceCount htokenTableSize hsourceBoundarySize
      htailBoundarySize hnumericSize
  have htailCode :=
    unconsRowsWithSizeTail56Formula_code_length_le_tight tokenCount
      tailBoundary tailCount tailBoundarySize numericBound bitBound hsize
      harea htokenCount htailCount htailBoundarySize hnumericSize
  simp only [binaryFormulaCode, List.length_append] at htailCode ⊢
  omega

end FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail456FixedBounds
