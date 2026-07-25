import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullPartsCertificate
import integration.FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-!
# Fully fixed syntax-task-list uncons certificate

The original six leaves are assembled along their native right-associated
formula tree.  Each compiled layer is imported opaquely, so elaboration does
not rebuild the heterogeneous proof tree.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBounds

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
open FoundationCompactPAHybridSixConjunctionClosedGeneralBounds
open FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsFullyFixedBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridUniversalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsAtomicFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail23456FixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullPartsCertificate

theorem unconsRowsWithSizeFullPartsCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount
      numericBound bitBound : Nat)
    (hpositive : 0 < sourceCount)
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
        (unconsRowsWithSizeFullPartsCertificate tokenTable width tokenCount
          sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
          headKind headBinderArity headRepeatCount hpositive hdrop htriple
          hcons hsize harea) <=
      unconsRowsWithSizeFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
  let positiveFormula : ValuationFormula :=
    “0 < !!(shortBinaryNumeralTerm sourceCount)”
  let tailFormula : ValuationFormula :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount 1 ⋏
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
                !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula))))
  let positiveCertificate := closedPositiveCertificate sourceCount hpositive
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCount).trans hnumericSize
  have hpositiveResource :
      hybridFormulaStructuralPayloadBound positiveCertificate <=
        unconsPositiveFullyFixedPayloadPolynomial bitBound :=
    (closedPositiveCertificate_structuralPayloadBound_le_public sourceCount
      hpositive).trans
    (compactAdditiveSyntaxTaskListUnconsRowsPositivePayloadPolynomial_le_fullyFixed
      sourceCount bitBound hsourceCountSize)
  have htailResource :=
    unconsRowsWithSizeTail23456Certificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount
      numericBound bitBound hdrop htriple hcons hsize harea hwidth htokenCount
      hsourceCount htailCount htokenTableSize hsourceBoundarySize
      htailBoundarySize hnumericSize
  have htransparent : hybridFormulaStructuralPayloadBound
      (unconsRowsWithSizeFullPartsCertificate tokenTable width tokenCount
        sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
        headKind headBinderArity headRepeatCount hpositive hdrop htriple
        hcons hsize harea) <=
      transparentHybridConjunctionPayloadEnvelope
        FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
        positiveFormula tailFormula
        (unconsPositiveFullyFixedPayloadPolynomial bitBound)
        (hybridConjunctionGeneralPayloadEnvelope
          (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
            bitBound)
          (taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound)
          (hybridConjunctionGeneralPayloadEnvelope
            (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
              bitBound)
            (tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial
              numericBound bitBound)
            (hybridConjunctionGeneralPayloadEnvelope
              (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
                bitBound)
              (taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
                bitBound)
              (hybridConjunctionGeneralPayloadEnvelope
                (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
                  bitBound)
                (compactNatSizeFixedPayloadPolynomial bitBound)
                (parserAreaFixedPayloadPolynomial bitBound))))) := by
    unfold unconsRowsWithSizeFullPartsCertificate
    rw [hybridFormulaStructuralPayloadBound_conjunction_eq_transparent]
    exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _
      hpositiveResource htailResource
  have hpositiveClosed : positiveFormula.freeVariables = ∅ := by
    simp [positiveFormula, shortBinaryNumeralTerm_freeVariables_eq_empty,
      LO.FirstOrder.Semiterm.Operator.operator]
  have htailClosed : tailFormula.freeVariables = ∅ := by
    dsimp only [tailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      compactAdditiveSyntaxTaskListDropOneRowsClosedFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      compactAdditiveTripleBoundaryRowsClosedFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      taskConsGenericFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      natSizeClosedFormula_freeVariables_eq_empty,
      parserAreaFormula_freeVariables_eq_empty]
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
          taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
            bitBound +
          compactNatSizeFixedPayloadPolynomial bitBound +
          parserAreaFixedPayloadPolynomial bitBound +
          4 * (binaryNatCode 4).length := by
    simpa only [tailFormula] using
      unconsRowsWithSizeTail23456Formula_code_length_le_tight tokenTable width
        tokenCount sourceBoundary sourceCount tailBoundary tailCount
        tailBoundarySize headKind headBinderArity headRepeatCount numericBound
        bitBound hdrop htriple hcons hsize harea hwidth htokenCount
        hsourceCount htailCount htokenTableSize hsourceBoundarySize
        htailBoundarySize hnumericSize
  let syntaxResource :=
    unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound bitBound
  have hpositiveSyntax : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold unconsRowsWithSizeFormulaCodePolynomial
    omega
  have hpositiveCodeGlobal :
      (binaryFormulaCode positiveFormula).length <= syntaxResource :=
    hpositiveCode.trans (by
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
      (binaryFormulaCode (positiveFormula ⋏ tailFormula)).length <=
        syntaxResource := by
    simp only [binaryFormulaCode, List.length_append]
    dsimp only [syntaxResource]
    unfold unconsRowsWithSizeFormulaCodePolynomial
    omega
  have henvelope :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      positiveFormula tailFormula
      (unconsPositiveFullyFixedPayloadPolynomial bitBound)
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource
        (taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound)
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource
          (tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
            bitBound)
          (hybridConjunctionGeneralPayloadEnvelope syntaxResource
            (taskConsGenericFullyFixedPayloadEnvelope tokenCount numericBound
              bitBound)
            (hybridConjunctionGeneralPayloadEnvelope syntaxResource
              (compactNatSizeFixedPayloadPolynomial bitBound)
              (parserAreaFixedPayloadPolynomial bitBound)))))
      syntaxResource hpositiveSyntax hpositiveClosed htailClosed
      hpositiveCodeGlobal htailCodeGlobal htotalCode
  exact htransparent.trans (by
    unfold unconsRowsWithSizeFullyFixedPayloadPolynomial
      hybridSixConjunctionGeneralPayloadEnvelope
    simpa only [syntaxResource] using henvelope)

theorem
    unconsRowsWithSizeCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount
      numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
          tailCount tailBoundarySize headKind headBinderArity headRepeatCount
          (shortBinaryNumeralTerm headKind)
          (shortBinaryNumeralTerm headBinderArity)
          (shortBinaryNumeralTerm headRepeatCount)
          (termValue_shortBinaryNumeralTerm · headKind)
          (termValue_shortBinaryNumeralTerm · headBinderArity)
          (termValue_shortBinaryNumeralTerm · headRepeatCount) hgraph) <=
      unconsRowsWithSizeFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
  rcases hgraph with
    ⟨hpositive, hdrop, htriple, hcons, hsize, harea⟩
  have hparts :=
    unconsRowsWithSizeFullPartsCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount
      numericBound bitBound hpositive hdrop htriple hcons hsize harea hwidth
      htokenCount hsourceCount htailCount htokenTableSize hsourceBoundarySize
      htailBoundarySize hnumericSize
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula_alignment
          tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
          tailCount tailBoundarySize (shortBinaryNumeralTerm headKind)
          (shortBinaryNumeralTerm headBinderArity)
          (shortBinaryNumeralTerm headRepeatCount)).symm
        (unconsRowsWithSizeFullPartsCertificate tokenTable width tokenCount
          sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
          headKind headBinderArity headRepeatCount hpositive hdrop htriple
          hcons hsize harea)) <= _
  exact hparts

end FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBounds
