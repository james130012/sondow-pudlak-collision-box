import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail456Certificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionGraphFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56FixedBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-! # Fully fixed Repeat uncons tail: function ConsRows and size-area -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail456FixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionGraphFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56Certificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56FixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail456Certificate

def parserSyntaxRepeatUnconsTail456SyntaxPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  taskConsFunctionFullyFixedPayloadEnvelope tokenCount numericBound bitBound +
    hybridConjunctionGeneralPayloadEnvelope
      (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound bitBound)
      (compactNatSizeFixedPayloadPolynomial bitBound)
      (parserAreaFixedPayloadPolynomial bitBound) +
    (binaryNatCode 4).length + 1

def parserSyntaxRepeatUnconsTail456PayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (parserSyntaxRepeatUnconsTail456SyntaxPolynomial tokenCount numericBound
      bitBound)
    (taskConsFunctionFullyFixedPayloadEnvelope tokenCount numericBound
      bitBound)
    (hybridConjunctionGeneralPayloadEnvelope
      (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound bitBound)
      (compactNatSizeFixedPayloadPolynomial bitBound)
      (parserAreaFixedPayloadPolynomial bitBound))

theorem
    parserSyntaxRepeatUnconsTail456Certificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize binderArity repeatCount numericBound
      bitBound : Nat)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount 2 binderArity
      repeatCount)
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
    (hrepeatSize : Nat.size repeatCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (parserSyntaxRepeatUnconsTail456Certificate tokenTable width tokenCount
          tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
          binderArity repeatCount hcons hsize harea) <=
      parserSyntaxRepeatUnconsTail456PayloadPolynomial tokenCount numericBound
        bitBound := by
  let consCertificate :=
    parserSyntaxRepeatConsCertificate tokenTable width tokenCount tailBoundary
      tailCount sourceBoundary sourceCount binderArity repeatCount hcons
  let tailCertificate :=
    unconsRowsWithSizeTail56Certificate tailBoundarySize tailBoundary
      tailCount tokenCount hsize harea
  let consFormula :=
    parserSyntaxRepeatUnconsTail456ConsFormula tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount binderArity
      repeatCount
  let tailFormula :=
    parserSyntaxRepeatUnconsTail56Formula tailBoundarySize tailBoundary
      tailCount tokenCount
  let consResource :=
    taskConsFunctionFullyFixedPayloadEnvelope tokenCount numericBound bitBound
  let tailResource :=
    hybridConjunctionGeneralPayloadEnvelope
      (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound bitBound)
      (compactNatSizeFixedPayloadPolynomial bitBound)
      (parserAreaFixedPayloadPolynomial bitBound)
  let syntaxResource :=
    parserSyntaxRepeatUnconsTail456SyntaxPolynomial tokenCount numericBound
      bitBound
  have hconsResource :
      hybridFormulaStructuralPayloadBound consCertificate <= consResource := by
    change hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionGraphCertificate.functionConsCertificateOfGraph
          tokenTable width tokenCount tailBoundary tailCount sourceBoundary
          sourceCount binderArity repeatCount hcons) <=
      taskConsFunctionFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound
    exact
      taskConsFunctionGraphCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount tailBoundary tailCount sourceBoundary
        sourceCount binderArity repeatCount numericBound bitBound hcons hwidth
        htokenCount hsourceCount htokenTableSize htailBoundarySize
        hsourceBoundarySize hbinderSize hrepeatSize hnumericSize
  have htailResource :
      hybridFormulaStructuralPayloadBound tailCertificate <= tailResource := by
    simpa only [tailCertificate, tailResource] using
      unconsRowsWithSizeTail56Certificate_structuralPayloadBound_le_fixed
        tokenCount tailBoundary tailCount tailBoundarySize numericBound
        bitBound hsize harea htokenCount htailCount htailBoundarySize
        hnumericSize
  have htransparent :=
    transparentHybridConjunctionPayloadBound_le consCertificate
      tailCertificate consResource tailResource hconsResource htailResource
  have hconsClosed : consFormula.freeVariables = ∅ := by
    simpa only [consFormula,
      parserSyntaxRepeatUnconsTail456ConsFormula] using
      taskConsFunctionFormula_freeVariables_eq_empty tokenTable width
        tokenCount tailBoundary tailCount sourceBoundary sourceCount
        binderArity repeatCount
  have htailClosed : tailFormula.freeVariables = ∅ := by
    unfold tailFormula parserSyntaxRepeatUnconsTail56Formula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      natSizeClosedFormula_freeVariables_eq_empty,
      parserAreaFormula_freeVariables_eq_empty]
    simp
  have hconsCodeResource :
      (binaryFormulaCode consFormula).length <= consResource := by
    have hraw :=
      FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        consCertificate
    simpa only [consFormula, consCertificate] using
      hraw.trans hconsResource
  have htailCodeResource :
      (binaryFormulaCode tailFormula).length <= tailResource := by
    change
      (binaryFormulaCode
        (compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
          (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
            (!!(shortBinaryNumeralTerm tailCount) + 1) *
              !!(shortBinaryNumeralTerm tokenCount)” :
            ValuationFormula))).length <= tailResource
    have hraw :=
      FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        tailCertificate
    exact hraw.trans htailResource
  have hconsCode :
      (binaryFormulaCode consFormula).length <= syntaxResource :=
    hconsCodeResource.trans (by
      unfold syntaxResource
        parserSyntaxRepeatUnconsTail456SyntaxPolynomial
      omega)
  have htailCode :
      (binaryFormulaCode tailFormula).length <= syntaxResource :=
    htailCodeResource.trans (by
      unfold syntaxResource
        parserSyntaxRepeatUnconsTail456SyntaxPolynomial
      omega)
  have htotalCode :
      (binaryFormulaCode (consFormula ⋏ tailFormula)).length <=
        syntaxResource := by
    simp only [binaryFormulaCode, List.length_append]
    unfold syntaxResource parserSyntaxRepeatUnconsTail456SyntaxPolynomial
    omega
  have hclosed :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      consFormula tailFormula consResource tailResource syntaxResource
      (by
        unfold syntaxResource
          parserSyntaxRepeatUnconsTail456SyntaxPolynomial
        omega)
      hconsClosed htailClosed hconsCode htailCode htotalCode
  unfold parserSyntaxRepeatUnconsTail456Certificate
    parserSyntaxRepeatUnconsTail456PayloadPolynomial
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        consCertificate tailCertificate) <=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource consResource
      tailResource
  exact htransparent.trans hclosed

end FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail456FixedBounds
