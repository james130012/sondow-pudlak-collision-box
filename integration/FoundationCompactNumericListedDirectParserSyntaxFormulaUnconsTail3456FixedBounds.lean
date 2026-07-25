import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail3456Certificate
import integration.FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Fixed resources for the exact parser `TripleBoundary ∧ Tail456` certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail3456FixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridUniversalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456Certificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456FixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail3456Certificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds

theorem parserSyntaxFormulaUnconsTail3456Certificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize binderArity numericBound bitBound : Nat)
    (htriple : CompactAdditiveTripleBoundaryRows tokenCount tailCount
      tailBoundary)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount 1 binderArity 0)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (parserSyntaxFormulaUnconsTail3456Certificate tokenTable width tokenCount
          tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
          binderArity htriple hcons hsize harea) <=
      hybridConjunctionGeneralPayloadEnvelope
        (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
          bitBound)
        (tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
          bitBound)
        (hybridConjunctionGeneralPayloadEnvelope
          (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
            bitBound)
          (taskConsParserFullyFixedPayloadEnvelope numericBound bitBound)
          (hybridConjunctionGeneralPayloadEnvelope
            (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
              bitBound)
            (compactNatSizeFixedPayloadPolynomial bitBound)
            (parserAreaFixedPayloadPolynomial bitBound))) := by
  let tripleFormula :=
    compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount
      tailBoundary
  let tailFormula : ValuationFormula :=
    parserSyntaxFormulaUnconsTail456ConsFormula tokenTable width tokenCount
        tailBoundary tailCount sourceBoundary sourceCount binderArity ⋏
      parserSyntaxFormulaUnconsTail56Formula tailBoundarySize tailBoundary
        tailCount tokenCount
  let tripleCertificate :=
    compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph
      tokenCount tailCount tailBoundary htriple
  let tailCertificate :=
    parserSyntaxFormulaUnconsTail456Certificate tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
      binderArity hcons hsize harea
  have htripleResource :
      hybridFormulaStructuralPayloadBound tripleCertificate <=
        tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
          bitBound :=
    (compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenCount tailCount tailBoundary htriple).trans
    (compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope_le_fullyFixed
      tokenCount tailCount tailBoundary numericBound bitBound htriple
      htokenCount htailCount htailBoundarySize hnumericSize)
  have htailResource :
      hybridFormulaStructuralPayloadBound tailCertificate <=
        hybridConjunctionGeneralPayloadEnvelope
          (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
            bitBound)
          (taskConsParserFullyFixedPayloadEnvelope numericBound bitBound)
          (hybridConjunctionGeneralPayloadEnvelope
            (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
              bitBound)
            (compactNatSizeFixedPayloadPolynomial bitBound)
            (parserAreaFixedPayloadPolynomial bitBound)) := by
    exact
      parserSyntaxFormulaUnconsTail456Certificate_structuralPayloadBound_le_fixed
        tokenTable width tokenCount tailBoundary tailCount sourceBoundary
        sourceCount tailBoundarySize binderArity numericBound bitBound hcons
        hsize harea hwidth htokenCount hsourceCount htailCount htokenTableSize
        hsourceBoundarySize htailBoundarySize hbinderSize hnumericSize
  have htransparent :
      hybridFormulaStructuralPayloadBound
          (parserSyntaxFormulaUnconsTail3456Certificate tokenTable width
            tokenCount tailBoundary tailCount sourceBoundary sourceCount
            tailBoundarySize binderArity htriple hcons hsize harea) <=
        transparentHybridConjunctionPayloadEnvelope
          FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
          tripleFormula tailFormula
          (tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
            bitBound)
          (hybridConjunctionGeneralPayloadEnvelope
            (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount
              numericBound bitBound)
            (taskConsParserFullyFixedPayloadEnvelope numericBound bitBound)
            (hybridConjunctionGeneralPayloadEnvelope
              (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
                bitBound)
              (compactNatSizeFixedPayloadPolynomial bitBound)
              (parserAreaFixedPayloadPolynomial bitBound))) := by
    change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          tripleCertificate tailCertificate) <= _
    exact transparentHybridConjunctionPayloadBound_le tripleCertificate
      tailCertificate _ _ htripleResource htailResource
  have htripleClosed : tripleFormula.freeVariables = ∅ := by
    simpa only [tripleFormula] using
      compactAdditiveTripleBoundaryRowsClosedFormula_freeVariables_eq_empty
        tokenCount tailCount tailBoundary
  have htailClosed : tailFormula.freeVariables = ∅ := by
    have hconsClosed :
        (parserSyntaxFormulaUnconsTail456ConsFormula tokenTable width tokenCount
          tailBoundary tailCount sourceBoundary sourceCount
          binderArity).freeVariables = ∅ := by
      simpa only [parserSyntaxFormulaUnconsTail456ConsFormula] using
        (taskConsParserFormula_freeVariables_eq_empty tokenTable width
          tokenCount tailBoundary tailCount sourceBoundary sourceCount
          binderArity)
    have htail56Closed :
        (parserSyntaxFormulaUnconsTail56Formula tailBoundarySize tailBoundary
          tailCount tokenCount).freeVariables = ∅ := by
      unfold parserSyntaxFormulaUnconsTail56Formula
      rw [LO.FirstOrder.Semiformula.freeVariables_and,
        natSizeClosedFormula_freeVariables_eq_empty,
        parserAreaFormula_freeVariables_eq_empty]
      simp
    dsimp only [tailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hconsClosed,
      htail56Closed]
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
        taskConsParserFullyFixedPayloadEnvelope numericBound bitBound +
          compactNatSizeFixedPayloadPolynomial bitBound +
          parserAreaFixedPayloadPolynomial bitBound +
          2 * (binaryNatCode 4).length := by
    simpa only [tailFormula] using
      parserSyntaxFormulaUnconsTail456Formula_code_length_le_tight tokenTable
        width tokenCount tailBoundary tailCount sourceBoundary sourceCount
        tailBoundarySize binderArity numericBound bitBound hcons hsize harea
        hwidth htokenCount hsourceCount htailCount htokenTableSize
        hsourceBoundarySize htailBoundarySize hbinderSize hnumericSize
  have hpositive :
      1 <= parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
        bitBound := by
    unfold parserSyntaxFormulaUnconsFormulaCodePolynomial
      unconsRowsWithSizeFormulaCodePolynomial
    omega
  have htripleCodeGlobal :
      (binaryFormulaCode tripleFormula).length <=
        parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
          bitBound :=
    htripleCode.trans (by
      unfold parserSyntaxFormulaUnconsFormulaCodePolynomial
        unconsRowsWithSizeFormulaCodePolynomial
      omega)
  have htailCodeGlobal :
      (binaryFormulaCode tailFormula).length <=
        parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
          bitBound :=
    htailCode.trans (by
      unfold parserSyntaxFormulaUnconsFormulaCodePolynomial
        unconsRowsWithSizeFormulaCodePolynomial
      omega)
  have htotalCode :
      (binaryFormulaCode (tripleFormula ⋏ tailFormula)).length <=
        parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
          bitBound := by
    simp only [binaryFormulaCode, List.length_append]
    unfold parserSyntaxFormulaUnconsFormulaCodePolynomial
      unconsRowsWithSizeFormulaCodePolynomial
    omega
  have henvelope :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      tripleFormula tailFormula
      (tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
        bitBound)
      (hybridConjunctionGeneralPayloadEnvelope
        (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
          bitBound)
        (taskConsParserFullyFixedPayloadEnvelope numericBound bitBound)
        (hybridConjunctionGeneralPayloadEnvelope
          (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
            bitBound)
          (compactNatSizeFixedPayloadPolynomial bitBound)
          (parserAreaFixedPayloadPolynomial bitBound)))
      (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
        bitBound)
      hpositive htripleClosed htailClosed htripleCodeGlobal htailCodeGlobal
      htotalCode
  exact Nat.le_trans htransparent henvelope

theorem parserSyntaxFormulaUnconsTail3456Formula_code_length_le_tight
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize binderArity numericBound bitBound : Nat)
    (htriple : CompactAdditiveTripleBoundaryRows tokenCount tailCount
      tailBoundary)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount 1 binderArity 0)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (parserSyntaxFormulaUnconsTail3456Formula tokenTable width tokenCount
        tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
        binderArity)).length <=
      tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
          bitBound +
        taskConsParserFullyFixedPayloadEnvelope numericBound bitBound +
        compactNatSizeFixedPayloadPolynomial bitBound +
        parserAreaFixedPayloadPolynomial bitBound +
        3 * (binaryNatCode 4).length := by
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
  have htripleCode :
      (binaryFormulaCode
        (compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount
          tailBoundary)).length <=
        tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
          bitBound := by
    simpa only [tripleCertificate] using
      (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        tripleCertificate).trans htripleResource
  have htailCode :=
    parserSyntaxFormulaUnconsTail456Formula_code_length_le_tight tokenTable
      width tokenCount tailBoundary tailCount sourceBoundary sourceCount
      tailBoundarySize binderArity numericBound bitBound hcons hsize harea
      hwidth htokenCount hsourceCount htailCount htokenTableSize
      hsourceBoundarySize htailBoundarySize hbinderSize hnumericSize
  unfold parserSyntaxFormulaUnconsTail3456Formula
  simp only [binaryFormulaCode, List.length_append] at htailCode ⊢
  omega

end FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail3456FixedBounds
