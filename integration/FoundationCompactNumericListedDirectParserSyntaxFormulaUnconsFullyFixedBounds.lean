import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullPartsCertificate
import integration.FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Fully fixed six-leaf certificate for the exact parser Uncons formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsAtomicFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsFullyFixedBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridUniversalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456Certificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail3456Certificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail23456Certificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail23456FixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullPartsCertificate
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds

theorem
    parserSyntaxFormulaUnconsFullPartsCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity numericBound bitBound : Nat)
    (hpositive : 0 < sourceCount)
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
        (parserSyntaxFormulaUnconsFullPartsCertificate tokenTable width
          tokenCount sourceBoundary sourceCount tailBoundary tailCount
          tailBoundarySize binderArity hpositive hdrop htriple hcons hsize
          harea) <=
      parserSyntaxFormulaUnconsFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound := by
  let positiveFormula : ValuationFormula :=
    “0 < !!(shortBinaryNumeralTerm sourceCount)”
  let tailFormula :=
    parserSyntaxFormulaUnconsTail23456Formula tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      binderArity
  let positiveCertificate := closedPositiveCertificate sourceCount hpositive
  let tailCertificate :=
    parserSyntaxFormulaUnconsTail23456Certificate tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      binderArity hdrop htriple hcons hsize harea
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCount).trans hnumericSize
  have hpositiveResource :
      hybridFormulaStructuralPayloadBound positiveCertificate <=
        unconsPositiveFullyFixedPayloadPolynomial bitBound :=
    (closedPositiveCertificate_structuralPayloadBound_le_public sourceCount
      hpositive).trans
    (compactAdditiveSyntaxTaskListUnconsRowsPositivePayloadPolynomial_le_fullyFixed
      sourceCount bitBound hsourceCountSize)
  have htailResource :
      hybridFormulaStructuralPayloadBound tailCertificate <=
        hybridConjunctionGeneralPayloadEnvelope
          (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
            bitBound)
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
    exact
      parserSyntaxFormulaUnconsTail23456Certificate_structuralPayloadBound_le_fixed
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount tailBoundarySize binderArity numericBound bitBound hdrop
        htriple hcons hsize harea hwidth htokenCount hsourceCount htailCount
        htokenTableSize hsourceBoundarySize htailBoundarySize hbinderSize
        hnumericSize
  have htransparent :
      hybridFormulaStructuralPayloadBound
          (parserSyntaxFormulaUnconsFullPartsCertificate tokenTable width
            tokenCount sourceBoundary sourceCount tailBoundary tailCount
            tailBoundarySize binderArity hpositive hdrop htriple hcons hsize
            harea) <=
        transparentHybridConjunctionPayloadEnvelope
          FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
          positiveFormula tailFormula
          (unconsPositiveFullyFixedPayloadPolynomial bitBound)
          (hybridConjunctionGeneralPayloadEnvelope
            (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount
              numericBound bitBound)
            (taskDropOneCompleteFullyFixedPayloadPolynomial numericBound
              bitBound)
            (hybridConjunctionGeneralPayloadEnvelope
              (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount
                numericBound bitBound)
              (tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial
                numericBound bitBound)
              (hybridConjunctionGeneralPayloadEnvelope
                (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount
                  numericBound bitBound)
                (taskConsParserFullyFixedPayloadEnvelope numericBound bitBound)
                (hybridConjunctionGeneralPayloadEnvelope
                  (unconsRowsWithSizeFormulaCodePolynomial tokenCount
                    numericBound bitBound)
                  (compactNatSizeFixedPayloadPolynomial bitBound)
                  (parserAreaFixedPayloadPolynomial bitBound))))) := by
    change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          positiveCertificate tailCertificate) <= _
    exact transparentHybridConjunctionPayloadBound_le positiveCertificate
      tailCertificate _ _ hpositiveResource htailResource
  have hpositiveClosed : positiveFormula.freeVariables = ∅ := by
    simp [positiveFormula, shortBinaryNumeralTerm_freeVariables_eq_empty,
      LO.FirstOrder.Semiterm.Operator.operator]
  have htailClosed : tailFormula.freeVariables = ∅ := by
    have hdropClosed :
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
          tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
          tailCount 1).freeVariables = ∅ :=
      compactAdditiveSyntaxTaskListDropOneRowsClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount
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
    unfold parserSyntaxFormulaUnconsTail23456Formula
      parserSyntaxFormulaUnconsTail3456Formula
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hdropClosed,
      LO.FirstOrder.Semiformula.freeVariables_and, htripleClosed,
      LO.FirstOrder.Semiformula.freeVariables_and, hconsClosed, htail56Closed]
    simp
  have hpositiveCode :
      (binaryFormulaCode positiveFormula).length <=
        unconsPositiveFullyFixedPayloadPolynomial bitBound := by
    simpa only [positiveFormula, positiveCertificate] using
      (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        positiveCertificate).trans hpositiveResource
  have htailCode :
      (binaryFormulaCode tailFormula).length <=
        taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound +
          tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
            bitBound +
          taskConsParserFullyFixedPayloadEnvelope numericBound bitBound +
          compactNatSizeFixedPayloadPolynomial bitBound +
          parserAreaFixedPayloadPolynomial bitBound +
          4 * (binaryNatCode 4).length := by
    simpa only [tailFormula] using
      parserSyntaxFormulaUnconsTail23456Formula_code_length_le_tight tokenTable
        width tokenCount sourceBoundary sourceCount tailBoundary tailCount
        tailBoundarySize binderArity numericBound bitBound hdrop htriple hcons
        hsize harea hwidth htokenCount hsourceCount htailCount htokenTableSize
        hsourceBoundarySize htailBoundarySize hbinderSize hnumericSize
  have hpositiveSyntax :
      1 <= parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
        bitBound := by
    unfold parserSyntaxFormulaUnconsFormulaCodePolynomial
      unconsRowsWithSizeFormulaCodePolynomial
    omega
  have hpositiveCodeGlobal :
      (binaryFormulaCode positiveFormula).length <=
        parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
          bitBound :=
    hpositiveCode.trans (by
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
      (binaryFormulaCode (positiveFormula ⋏ tailFormula)).length <=
        parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
          bitBound := by
    simp only [binaryFormulaCode, List.length_append]
    unfold parserSyntaxFormulaUnconsFormulaCodePolynomial
      unconsRowsWithSizeFormulaCodePolynomial
    omega
  have henvelope :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      positiveFormula tailFormula
      (unconsPositiveFullyFixedPayloadPolynomial bitBound)
      (hybridConjunctionGeneralPayloadEnvelope
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
              (parserAreaFixedPayloadPolynomial bitBound)))))
      (parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
        bitBound)
      hpositiveSyntax hpositiveClosed htailClosed hpositiveCodeGlobal
      htailCodeGlobal htotalCode
  unfold parserSyntaxFormulaUnconsFullyFixedPayloadPolynomial
  exact Nat.le_trans htransparent henvelope

theorem parserSyntaxFormulaUnconsFullFormula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity : Nat) :
    (parserSyntaxFormulaUnconsFullFormula tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      binderArity).freeVariables = ∅ := by
  have hpositiveClosed :
      ((“0 < !!(shortBinaryNumeralTerm sourceCount)” :
        ValuationFormula)).freeVariables = ∅ := by
    simp [shortBinaryNumeralTerm_freeVariables_eq_empty,
      LO.FirstOrder.Semiterm.Operator.operator]
  have hdropClosed :
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable
        width tokenCount sourceBoundary sourceCount tailBoundary tailCount
        1).freeVariables = ∅ :=
    compactAdditiveSyntaxTaskListDropOneRowsClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount
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
      (taskConsParserFormula_freeVariables_eq_empty tokenTable width tokenCount
        tailBoundary tailCount sourceBoundary sourceCount binderArity)
  have htail56Closed :
      (parserSyntaxFormulaUnconsTail56Formula tailBoundarySize tailBoundary
        tailCount tokenCount).freeVariables = ∅ := by
    unfold parserSyntaxFormulaUnconsTail56Formula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      natSizeClosedFormula_freeVariables_eq_empty,
      parserAreaFormula_freeVariables_eq_empty]
    simp
  unfold parserSyntaxFormulaUnconsFullFormula
    parserSyntaxFormulaUnconsTail23456Formula
    parserSyntaxFormulaUnconsTail3456Formula
  rw [LO.FirstOrder.Semiformula.freeVariables_and, hpositiveClosed,
    LO.FirstOrder.Semiformula.freeVariables_and, hdropClosed,
    LO.FirstOrder.Semiformula.freeVariables_and, htripleClosed,
    LO.FirstOrder.Semiformula.freeVariables_and, hconsClosed, htail56Closed]
  simp

theorem parserSyntaxFormulaUnconsGraphFormula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity : Nat) :
    (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        1)
      (shortBinaryNumeralTerm binderArity)
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        0)).freeVariables = ∅ := by
  rw [compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula_alignment]
  change
    (parserSyntaxFormulaUnconsFullFormula tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      binderArity).freeVariables = ∅
  exact parserSyntaxFormulaUnconsFullFormula_freeVariables_eq_empty tokenTable
    width tokenCount sourceBoundary sourceCount tailBoundary tailCount
    tailBoundarySize binderArity

theorem
    parserSyntaxFormulaUnconsGraphCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity numericBound bitBound : Nat)
    (hgraph :
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows.CompactAdditiveSyntaxTaskListUnconsRowsWithSize
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount tailBoundarySize 1 binderArity 0)
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
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
          tailCount tailBoundarySize 1 binderArity 0
          (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
            1)
          (shortBinaryNumeralTerm binderArity)
          (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
            0)
          (fun valuation => by simp)
          (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
          (fun valuation => by simp) hgraph) <=
      parserSyntaxFormulaUnconsFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound := by
  rcases hgraph with
    ⟨hpositive, hdrop, htriple, hcons, hsize, harea⟩
  have hparts :=
    parserSyntaxFormulaUnconsFullPartsCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity numericBound bitBound hpositive
      hdrop htriple hcons hsize harea hwidth htokenCount hsourceCount
      htailCount htokenTableSize hsourceBoundarySize htailBoundarySize
      hbinderSize hnumericSize
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula_alignment
          tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
          tailCount tailBoundarySize
          (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
            1)
          (shortBinaryNumeralTerm binderArity)
          (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
            0)).symm
        (parserSyntaxFormulaUnconsFullPartsCertificate tokenTable width
          tokenCount sourceBoundary sourceCount tailBoundary tailCount
          tailBoundarySize binderArity hpositive hdrop htriple hcons hsize
          harea)) <= _
  exact hparts

end FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBounds
