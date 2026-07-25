import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail23456Certificate
import integration.FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Fixed resources for the exact parser `DropOne ∧ Tail3456` certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail23456FixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsFullyFixedBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridUniversalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456Certificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail3456Certificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail3456FixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail23456Certificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds

theorem parserSyntaxFormulaUnconsTail23456Certificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity numericBound bitBound : Nat)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount 1)
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
        (parserSyntaxFormulaUnconsTail23456Certificate tokenTable width
          tokenCount sourceBoundary sourceCount tailBoundary tailCount
          tailBoundarySize binderArity hdrop htriple hcons hsize harea) <=
      hybridConjunctionGeneralPayloadEnvelope
        (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
          bitBound)
        (taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound)
        (hybridConjunctionGeneralPayloadEnvelope
          (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
            bitBound)
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
              (parserAreaFixedPayloadPolynomial bitBound)))) := by
  let dropFormula :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable
      width tokenCount sourceBoundary sourceCount tailBoundary tailCount 1
  let tailFormula :=
    parserSyntaxFormulaUnconsTail3456Formula tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
      binderArity
  let dropCertificate :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hdrop
  let tailCertificate :=
    parserSyntaxFormulaUnconsTail3456Certificate tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
      binderArity htriple hcons hsize harea
  have hdropResource :
      hybridFormulaStructuralPayloadBound dropCertificate <=
        taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound :=
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hdrop).trans
    (compactAdditiveSyntaxTaskListDropOneRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount numericBound bitBound hdrop hwidth htokenCount hsourceCount
      htokenTableSize hsourceBoundarySize htailBoundarySize hnumericSize)
  have htailResource :
      hybridFormulaStructuralPayloadBound tailCertificate <=
        hybridConjunctionGeneralPayloadEnvelope
          (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
            bitBound)
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
    exact
      parserSyntaxFormulaUnconsTail3456Certificate_structuralPayloadBound_le_fixed
        tokenTable width tokenCount tailBoundary tailCount sourceBoundary
        sourceCount tailBoundarySize binderArity numericBound bitBound htriple
        hcons hsize harea hwidth htokenCount hsourceCount htailCount
        htokenTableSize hsourceBoundarySize htailBoundarySize hbinderSize
        hnumericSize
  have htransparent :
      hybridFormulaStructuralPayloadBound
          (parserSyntaxFormulaUnconsTail23456Certificate tokenTable width
            tokenCount sourceBoundary sourceCount tailBoundary tailCount
            tailBoundarySize binderArity hdrop htriple hcons hsize harea) <=
        transparentHybridConjunctionPayloadEnvelope
          FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
          dropFormula tailFormula
          (taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound)
          (hybridConjunctionGeneralPayloadEnvelope
            (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount
              numericBound bitBound)
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
                (parserAreaFixedPayloadPolynomial bitBound)))) := by
    change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          dropCertificate tailCertificate) <= _
    exact transparentHybridConjunctionPayloadBound_le dropCertificate
      tailCertificate _ _ hdropResource htailResource
  have hdropClosed : dropFormula.freeVariables = ∅ := by
    simpa only [dropFormula] using
      compactAdditiveSyntaxTaskListDropOneRowsClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount
  have htailClosed : tailFormula.freeVariables = ∅ := by
    have htripleClosed :
        (compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount
          tailBoundary).freeVariables = ∅ :=
      compactAdditiveTripleBoundaryRowsClosedFormula_freeVariables_eq_empty
        tokenCount tailCount tailBoundary
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
    unfold parserSyntaxFormulaUnconsTail3456Formula
    rw [LO.FirstOrder.Semiformula.freeVariables_and, htripleClosed,
      LO.FirstOrder.Semiformula.freeVariables_and, hconsClosed, htail56Closed]
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
          taskConsParserFullyFixedPayloadEnvelope numericBound bitBound +
          compactNatSizeFixedPayloadPolynomial bitBound +
          parserAreaFixedPayloadPolynomial bitBound +
          3 * (binaryNatCode 4).length := by
    simpa only [tailFormula] using
      parserSyntaxFormulaUnconsTail3456Formula_code_length_le_tight tokenTable
        width tokenCount tailBoundary tailCount sourceBoundary sourceCount
        tailBoundarySize binderArity numericBound bitBound htriple hcons hsize
        harea hwidth htokenCount hsourceCount htailCount htokenTableSize
        hsourceBoundarySize htailBoundarySize hbinderSize hnumericSize
  have hpositive :
      1 <= parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
        bitBound := by
    unfold parserSyntaxFormulaUnconsFormulaCodePolynomial
      unconsRowsWithSizeFormulaCodePolynomial
    omega
  have hdropCodeGlobal :
      (binaryFormulaCode dropFormula).length <=
        parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
          bitBound :=
    hdropCode.trans (by
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
      (binaryFormulaCode (dropFormula ⋏ tailFormula)).length <=
        parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
          bitBound := by
    simp only [binaryFormulaCode, List.length_append]
    unfold parserSyntaxFormulaUnconsFormulaCodePolynomial
      unconsRowsWithSizeFormulaCodePolynomial
    omega
  have henvelope :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      dropFormula tailFormula
      (taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (hybridConjunctionGeneralPayloadEnvelope
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
            (parserAreaFixedPayloadPolynomial bitBound))))
      (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
        bitBound)
      hpositive hdropClosed htailClosed hdropCodeGlobal htailCodeGlobal
      htotalCode
  exact Nat.le_trans htransparent henvelope

theorem parserSyntaxFormulaUnconsTail23456Formula_code_length_le_tight
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity numericBound bitBound : Nat)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount 1)
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
      (parserSyntaxFormulaUnconsTail23456Formula tokenTable width tokenCount
        sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
        binderArity)).length <=
      taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound +
        tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
          bitBound +
        taskConsParserFullyFixedPayloadEnvelope numericBound bitBound +
        compactNatSizeFixedPayloadPolynomial bitBound +
        parserAreaFixedPayloadPolynomial bitBound +
        4 * (binaryNatCode 4).length := by
  let dropCertificate :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hdrop
  have hdropResource :
      hybridFormulaStructuralPayloadBound dropCertificate <=
        taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound :=
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hdrop).trans
    (compactAdditiveSyntaxTaskListDropOneRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount numericBound bitBound hdrop hwidth htokenCount hsourceCount
      htokenTableSize hsourceBoundarySize htailBoundarySize hnumericSize)
  have hdropCode :
      (binaryFormulaCode
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
          tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
          tailCount 1)).length <=
        taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound := by
    simpa only [dropCertificate] using
      (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        dropCertificate).trans hdropResource
  have htailCode :=
    parserSyntaxFormulaUnconsTail3456Formula_code_length_le_tight tokenTable
      width tokenCount tailBoundary tailCount sourceBoundary sourceCount
      tailBoundarySize binderArity numericBound bitBound htriple hcons hsize
      harea hwidth htokenCount hsourceCount htailCount htokenTableSize
      hsourceBoundarySize htailBoundarySize hbinderSize hnumericSize
  unfold parserSyntaxFormulaUnconsTail23456Formula
  simp only [binaryFormulaCode, List.length_append] at htailCode ⊢
  omega

end FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail23456FixedBounds
