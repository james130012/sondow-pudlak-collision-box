import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBoundsDefinitions
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456Certificate
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456TransparentFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaConsCertificateFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56FixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserGraphFullyFixedBounds
import integration.FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Fixed parser `ConsRows ∧ (NatSize ∧ area)` Uncons tail -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456FixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserGraphFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56Certificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56FixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456Certificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456TransparentFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaConsCertificateFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate

private abbrev parserFixedNumeralTerm (value : Nat) : ValuationTerm :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
    value

private theorem termValue_parserFixedNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (parserFixedNumeralTerm value) = value := by
  simp [parserFixedNumeralTerm,
    FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
    termValue]

theorem
    parserSyntaxFormulaUnconsTail456Certificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize binderArity numericBound bitBound : Nat)
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
        (parserSyntaxFormulaUnconsTail456Certificate tokenTable width tokenCount
          tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
          binderArity hcons hsize harea) <=
      hybridConjunctionGeneralPayloadEnvelope
        (FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBoundsDefinitions.parserSyntaxFormulaUnconsFormulaCodePolynomial
          tokenCount numericBound bitBound)
        (taskConsParserFullyFixedPayloadEnvelope numericBound bitBound)
        (hybridConjunctionGeneralPayloadEnvelope
          (FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions.unconsRowsWithSizeFormulaCodePolynomial
            tokenCount numericBound bitBound)
          (compactNatSizeFixedPayloadPolynomial bitBound)
          (parserAreaFixedPayloadPolynomial bitBound)) := by
  let consFormula :=
    parserSyntaxFormulaUnconsTail456ConsFormula tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount binderArity
  let tailFormula :=
    parserSyntaxFormulaUnconsTail56Formula tailBoundarySize tailBoundary
      tailCount tokenCount
  let consCertificate :=
    parserSyntaxFormulaConsCertificate tokenTable width tokenCount tailBoundary
      tailCount sourceBoundary sourceCount binderArity hcons
  have hconsResource :
      hybridFormulaStructuralPayloadBound consCertificate <=
        taskConsParserFullyFixedPayloadEnvelope numericBound bitBound := by
    exact
      parserSyntaxFormulaConsCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount tailBoundary tailCount sourceBoundary
        sourceCount binderArity numericBound bitBound hcons hwidth htokenCount
        hsourceCount htokenTableSize hsourceBoundarySize htailBoundarySize
        hbinderSize hnumericSize
  have htransparent :=
    parserSyntaxFormulaUnconsTail456Certificate_structuralPayloadBound_le_transparentFixed
      tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize binderArity numericBound bitBound hcons
      hsize harea hwidth htokenCount hsourceCount htailCount htokenTableSize
      hsourceBoundarySize htailBoundarySize hbinderSize hnumericSize
  have hconsClosed : consFormula.freeVariables = ∅ := by
    simpa only [consFormula,
      parserSyntaxFormulaUnconsTail456ConsFormula] using
      (taskConsParserFormula_freeVariables_eq_empty tokenTable width
        tokenCount tailBoundary tailCount sourceBoundary sourceCount binderArity)
  have htailClosed : tailFormula.freeVariables = ∅ := by
    dsimp only [tailFormula, parserSyntaxFormulaUnconsTail56Formula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      natSizeClosedFormula_freeVariables_eq_empty,
      parserAreaFormula_freeVariables_eq_empty]
    simp
  have hconsCode :
      (binaryFormulaCode consFormula).length <=
        taskConsParserFullyFixedPayloadEnvelope numericBound bitBound := by
    simpa only [consFormula, consCertificate] using
      (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        consCertificate).trans hconsResource
  have htailCode :
      (binaryFormulaCode tailFormula).length <=
        compactNatSizeFixedPayloadPolynomial bitBound +
          parserAreaFixedPayloadPolynomial bitBound +
          (binaryNatCode 4).length := by
    simpa only [tailFormula, parserSyntaxFormulaUnconsTail56Formula] using
      unconsRowsWithSizeTail56Formula_code_length_le_tight tokenCount
        tailBoundary tailCount tailBoundarySize numericBound bitBound hsize
        harea htokenCount htailCount htailBoundarySize hnumericSize
  have hpositive :
      1 <=
        FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBoundsDefinitions.parserSyntaxFormulaUnconsFormulaCodePolynomial
          tokenCount numericBound bitBound := by
    unfold parserSyntaxFormulaUnconsFormulaCodePolynomial
    unfold FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions.unconsRowsWithSizeFormulaCodePolynomial
    omega
  have hconsCodeGlobal :
      (binaryFormulaCode consFormula).length <=
        FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBoundsDefinitions.parserSyntaxFormulaUnconsFormulaCodePolynomial
          tokenCount numericBound bitBound :=
    hconsCode.trans (by
      unfold parserSyntaxFormulaUnconsFormulaCodePolynomial
      unfold FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions.unconsRowsWithSizeFormulaCodePolynomial
      omega)
  have htailCodeGlobal :
      (binaryFormulaCode tailFormula).length <=
        FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBoundsDefinitions.parserSyntaxFormulaUnconsFormulaCodePolynomial
          tokenCount numericBound bitBound :=
    htailCode.trans (by
      unfold parserSyntaxFormulaUnconsFormulaCodePolynomial
      unfold FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions.unconsRowsWithSizeFormulaCodePolynomial
      omega)
  have htotalCode :
      (binaryFormulaCode (consFormula ⋏ tailFormula)).length <=
        FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBoundsDefinitions.parserSyntaxFormulaUnconsFormulaCodePolynomial
          tokenCount numericBound bitBound := by
    simp only [binaryFormulaCode, List.length_append]
    unfold parserSyntaxFormulaUnconsFormulaCodePolynomial
    unfold FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions.unconsRowsWithSizeFormulaCodePolynomial
    omega
  have henvelopeEq :
      parserSyntaxFormulaUnconsTail456TransparentFixedEnvelope tokenTable width
          tokenCount tailBoundary tailCount sourceBoundary sourceCount
          tailBoundarySize binderArity numericBound bitBound =
        transparentHybridConjunctionPayloadEnvelope
          FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
          consFormula tailFormula
          (taskConsParserFullyFixedPayloadEnvelope numericBound bitBound)
          (hybridConjunctionGeneralPayloadEnvelope
            (FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions.unconsRowsWithSizeFormulaCodePolynomial
              tokenCount numericBound bitBound)
            (compactNatSizeFixedPayloadPolynomial bitBound)
            (parserAreaFixedPayloadPolynomial bitBound)) := rfl
  rw [henvelopeEq] at htransparent
  have henvelope :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      consFormula tailFormula
      (taskConsParserFullyFixedPayloadEnvelope numericBound bitBound)
      (hybridConjunctionGeneralPayloadEnvelope
        (FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions.unconsRowsWithSizeFormulaCodePolynomial
          tokenCount numericBound bitBound)
        (compactNatSizeFixedPayloadPolynomial bitBound)
        (parserAreaFixedPayloadPolynomial bitBound))
      (FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBoundsDefinitions.parserSyntaxFormulaUnconsFormulaCodePolynomial
        tokenCount numericBound bitBound)
      hpositive hconsClosed htailClosed hconsCodeGlobal htailCodeGlobal
      htotalCode
  exact Nat.le_trans htransparent henvelope

theorem parserSyntaxFormulaUnconsTail456Formula_code_length_le_tight
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize binderArity numericBound bitBound : Nat)
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
      (parserSyntaxFormulaUnconsTail456ConsFormula tokenTable width tokenCount
          tailBoundary tailCount sourceBoundary sourceCount binderArity ⋏
        parserSyntaxFormulaUnconsTail56Formula tailBoundarySize tailBoundary
          tailCount tokenCount)).length <=
      taskConsParserFullyFixedPayloadEnvelope numericBound bitBound +
        compactNatSizeFixedPayloadPolynomial bitBound +
        parserAreaFixedPayloadPolynomial bitBound +
        2 * (binaryNatCode 4).length := by
  let consCertificate :=
    parserSyntaxFormulaConsCertificate tokenTable width tokenCount tailBoundary
      tailCount sourceBoundary sourceCount binderArity hcons
  have hconsResource :
      hybridFormulaStructuralPayloadBound consCertificate <=
        taskConsParserFullyFixedPayloadEnvelope numericBound bitBound := by
    exact
      parserSyntaxFormulaConsCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount tailBoundary tailCount sourceBoundary
        sourceCount binderArity numericBound bitBound hcons hwidth htokenCount
        hsourceCount htokenTableSize hsourceBoundarySize htailBoundarySize
        hbinderSize hnumericSize
  have hconsCode :
      (binaryFormulaCode
        (parserSyntaxFormulaUnconsTail456ConsFormula tokenTable width tokenCount
          tailBoundary tailCount sourceBoundary sourceCount binderArity)).length <=
        taskConsParserFullyFixedPayloadEnvelope numericBound bitBound := by
    simpa only [consCertificate] using
      (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        consCertificate).trans hconsResource
  have htailCode :
      (binaryFormulaCode
        (parserSyntaxFormulaUnconsTail56Formula tailBoundarySize tailBoundary
          tailCount tokenCount)).length <=
        compactNatSizeFixedPayloadPolynomial bitBound +
          parserAreaFixedPayloadPolynomial bitBound +
          (binaryNatCode 4).length := by
    simpa only [parserSyntaxFormulaUnconsTail56Formula] using
      unconsRowsWithSizeTail56Formula_code_length_le_tight tokenCount
        tailBoundary tailCount tailBoundarySize numericBound bitBound hsize
        harea htokenCount htailCount htailBoundarySize hnumericSize
  simp only [binaryFormulaCode, List.length_append] at htailCode ⊢
  omega

end FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456FixedBounds
