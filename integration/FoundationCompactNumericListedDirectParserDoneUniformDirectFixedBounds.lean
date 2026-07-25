import integration.FoundationCompactNumericListedDirectParserDoneUniformDirectCompiler
import integration.FoundationCompactPADirectNineConjunctionClosedGeneralBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectCompletedStatusSameRowsPublicBounds
import integration.FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Fixed bound for the direct completed-status same-rows proof -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserDoneUniformDirectFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectNineConjunctionCompiler
open FoundationCompactPADirectNineConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectCompletedStatusSameRowsPublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserDoneUniformDirectCompiler

private abbrev doneFixedZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate.zeroValuation

def completedSameRowsUniformDirectFormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  2 * binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
      bitBound +
    2 * compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound +
    sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound +
    2 * compactNatSizeFixedPayloadPolynomial bitBound +
    2 * completedAreaFixedPayloadPolynomial bitBound +
    20 * (binaryNatCode 4).length + 100

def completedSameRowsUniformDirectFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  directNineConjunctionGeneralPayloadEnvelope
    (completedSameRowsUniformDirectFormulaCodePolynomial numericBound bitBound)
    (binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
      bitBound)
    (compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound)
    (binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
      bitBound)
    (compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound)
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    (compactNatSizeFixedPayloadPolynomial bitBound)
    (completedAreaFixedPayloadPolynomial bitBound)
    (compactNatSizeFixedPayloadPolynomial bitBound)
    (completedAreaFixedPayloadPolynomial bitBound)

private theorem compiledCompletedPrefix_payloadLength_le_fixed
    (tokenTable width tokenCount start outputStart numericBound bitBound : Nat)
    (hgraph : CompactBinaryNatCompletedStatusPrefix tokenTable width tokenCount
      start outputStart)
    (hwidth : width <= numericBound)
    (hstart : start <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount start outputStart hgraph).compile.payloadLength
        <= binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
          bitBound := by
  rcases hgraph with ⟨innerStart, hinnerLe, hfirstCell, hsecondCell⟩
  have hinnerEq : innerStart = start + 1 := hfirstCell.2.1
  have hinnerValue : start + 1 <= numericBound := by
    rw [← hinnerEq]
    exact hinnerLe.trans htokenCount
  have houtputStartValue : outputStart <= numericBound := by
    have houtputEq : outputStart = innerStart + 1 := hsecondCell.2.1
    rw [houtputEq]
    exact (Nat.succ_le_of_lt hsecondCell.1).trans htokenCount
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hinnerSize : Nat.size (start + 1) <= bitBound :=
    (Nat.size_le_size hinnerValue).trans hnumericSize
  have houtputStartSize : Nat.size outputStart <= bitBound :=
    (Nat.size_le_size houtputStartValue).trans hnumericSize
  exact
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound _ |>.trans
      (compactBinaryNatCompletedStatusPrefixExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount start outputStart numericBound bitBound
        hwidth hstart hinnerValue htokenTableSize hwidthSize htokenCountSize
        hstartSize houtputStartSize hinnerSize hbitPositive
        ⟨innerStart, hinnerLe, hfirstCell, hsecondCell⟩)

private theorem compiledCompletedArea_payloadLength_le_fixed
    (tokenCount outputCount boundary boundarySize numericBound bitBound : Nat)
    (harea : boundarySize <= (outputCount + 1) * tokenCount)
    (hsize : boundarySize = Nat.size boundary)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : outputCount <= numericBound)
    (hboundarySize : Nat.size boundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (boundaryAreaCertificate tokenCount outputCount boundarySize
      harea).compile.payloadLength <=
        completedAreaFixedPayloadPolynomial bitBound := by
  exact
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound _ |>.trans
      ((boundaryAreaCertificate_structuralPayloadBound_le_public tokenCount
        outputCount boundarySize harea).trans
        (completedAreaStructuralPayloadPolynomial_le_fixed tokenCount
          outputCount boundary boundarySize numericBound bitBound hsize
          htokenCount houtputCount hboundarySize hnumericSize))

theorem
    compileCompactBinaryNatCompletedStatusSameRowsUniformDirect_payloadLength_le_fixed
    (tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount numericBound bitBound : Nat)
    (hgraph : CompactBinaryNatCompletedStatusSameRowsWithSize
      tokenTable width tokenCount
        sourceStatusStart sourceStatusFinish
        targetStatusStart targetStatusFinish
        sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
        targetOutputStart targetOutputBoundary targetOutputBoundarySize
        outputCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : outputCount <= numericBound)
    (hsourceStart : sourceStatusStart <= numericBound)
    (htargetStart : targetStatusStart <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceStartSize : Nat.size sourceStatusStart <= bitBound)
    (htargetStartSize : Nat.size targetStatusStart <= bitBound)
    (hsourceBoundarySize : Nat.size sourceOutputBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactBinaryNatCompletedStatusSameRowsUniformDirect tokenTable
      width tokenCount sourceStatusStart sourceStatusFinish targetStatusStart
      targetStatusFinish sourceOutputStart sourceOutputBoundary
      sourceOutputBoundarySize targetOutputStart targetOutputBoundary
      targetOutputBoundarySize outputCount numericBound bitBound hgraph
      htokenCount houtputCount hsourceBoundarySize htargetBoundarySize
      hnumericSize).payloadLength <=
        completedSameRowsUniformDirectFixedPayloadPolynomial numericBound
          bitBound := by
  rcases hgraph with
    ⟨⟨hsourcePrefix, hsourceLayout, htargetPrefix, htargetLayout, hsame⟩,
      hsourceSize, hsourceArea, htargetSize, htargetArea⟩
  let sourceLayoutData :=
    compactAdditiveStructuredListLayoutDataOfLayout tokenTable width tokenCount
      sourceOutputStart outputCount sourceStatusFinish sourceOutputBoundary
      hsourceLayout
  let targetLayoutData :=
    compactAdditiveStructuredListLayoutDataOfLayout tokenTable width tokenCount
      targetOutputStart outputCount targetStatusFinish targetOutputBoundary
      htargetLayout
  let formula1 := compactBinaryNatCompletedStatusPrefixClosedFormula tokenTable
    width tokenCount sourceStatusStart sourceOutputStart
  let formula2 := compactAdditiveStructuredListLayoutClosedFormula tokenTable
    width tokenCount sourceOutputStart outputCount sourceStatusFinish
    sourceOutputBoundary
  let formula3 := compactBinaryNatCompletedStatusPrefixClosedFormula tokenTable
    width tokenCount targetStatusStart targetOutputStart
  let formula4 := compactAdditiveStructuredListLayoutClosedFormula tokenTable
    width tokenCount targetOutputStart outputCount targetStatusFinish
    targetOutputBoundary
  let formula5 := compactAdditiveNatListSameRowsClosedFormula tokenTable width
    tokenCount sourceOutputBoundary outputCount targetOutputBoundary outputCount
  let formula6 := compactNatSizeClosedFormula sourceOutputBoundarySize
    sourceOutputBoundary
  let formula7 : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sourceOutputBoundarySize) ≤
      (!!(shortBinaryNumeralTerm outputCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let formula8 := compactNatSizeClosedFormula targetOutputBoundarySize
    targetOutputBoundary
  let formula9 : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetOutputBoundarySize) ≤
      (!!(shortBinaryNumeralTerm outputCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let certificate1 :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceStatusStart sourceOutputStart
      hsourcePrefix
  let sourceLayoutRaw :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount sourceOutputStart outputCount
      sourceStatusFinish sourceOutputBoundary sourceLayoutData.bodyStart
      numericBound bitBound sourceLayoutData.bodyStart_le_tokenCount
      sourceLayoutData.header sourceLayoutData.boundaryFinish_le_tokenCount
      sourceLayoutData.boundaryStartEntry sourceLayoutData.boundaryFinishEntry
      sourceLayoutData.rows htokenCount houtputCount hsourceBoundarySize
      hnumericSize
  have hsourceLayoutContext :
      (∅ : Finset ValuationFormula) =
        valuationContext formula2.freeVariables doneFixedZeroValuation := by
    rw [show formula2.freeVariables = ∅ by
      simpa only [formula2] using
        compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
          tokenTable width tokenCount sourceOutputStart outputCount
          sourceStatusFinish sourceOutputBoundary]
    simp [valuationContext]
  let proof2 := CertifiedPAContextProof.castContext hsourceLayoutContext
    sourceLayoutRaw
  let certificate3 :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount targetStatusStart targetOutputStart
      htargetPrefix
  let targetLayoutRaw :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount targetOutputStart outputCount
      targetStatusFinish targetOutputBoundary targetLayoutData.bodyStart
      numericBound bitBound targetLayoutData.bodyStart_le_tokenCount
      targetLayoutData.header targetLayoutData.boundaryFinish_le_tokenCount
      targetLayoutData.boundaryStartEntry targetLayoutData.boundaryFinishEntry
      targetLayoutData.rows htokenCount houtputCount htargetBoundarySize
      hnumericSize
  have htargetLayoutContext :
      (∅ : Finset ValuationFormula) =
        valuationContext formula4.freeVariables doneFixedZeroValuation := by
    rw [show formula4.freeVariables = ∅ by
      simpa only [formula4] using
        compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
          tokenTable width tokenCount targetOutputStart outputCount
          targetStatusFinish targetOutputBoundary]
    simp [valuationContext]
  let proof4 := CertifiedPAContextProof.castContext htargetLayoutContext
    targetLayoutRaw
  let certificate5 :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount sourceOutputBoundary outputCount targetOutputBoundary
      outputCount hsame
  let certificate6 := compactNatSizeExplicitHybridCertificateOfEq
    sourceOutputBoundarySize sourceOutputBoundary hsourceSize
  let certificate7 := boundaryAreaCertificate tokenCount outputCount
    sourceOutputBoundarySize hsourceArea
  let certificate8 := compactNatSizeExplicitHybridCertificateOfEq
    targetOutputBoundarySize targetOutputBoundary htargetSize
  let certificate9 := boundaryAreaCertificate tokenCount outputCount
    targetOutputBoundarySize htargetArea
  have hresource1 := compiledCompletedPrefix_payloadLength_le_fixed tokenTable
    width tokenCount sourceStatusStart sourceOutputStart numericBound bitBound
    hsourcePrefix hwidth hsourceStart htokenCount htokenTableSize
    hsourceStartSize hnumericSize hbitPositive
  have hresource2 :
      proof2.payloadLength <=
        compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
          numericBound bitBound := by
    dsimp only [proof2]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact
      compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le_fixed
        tokenTable width tokenCount sourceOutputStart outputCount
        sourceStatusFinish sourceOutputBoundary sourceLayoutData.bodyStart
        numericBound bitBound sourceLayoutData.bodyStart_le_tokenCount
        sourceLayoutData.header sourceLayoutData.boundaryFinish_le_tokenCount
        sourceLayoutData.boundaryStartEntry
        sourceLayoutData.boundaryFinishEntry sourceLayoutData.rows hwidth
        htokenCount houtputCount htokenTableSize hsourceBoundarySize
        hnumericSize
  have hresource3 := compiledCompletedPrefix_payloadLength_le_fixed tokenTable
    width tokenCount targetStatusStart targetOutputStart numericBound bitBound
    htargetPrefix hwidth htargetStart htokenCount htokenTableSize
    htargetStartSize hnumericSize hbitPositive
  have hresource4 :
      proof4.payloadLength <=
        compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
          numericBound bitBound := by
    dsimp only [proof4]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact
      compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le_fixed
        tokenTable width tokenCount targetOutputStart outputCount
        targetStatusFinish targetOutputBoundary targetLayoutData.bodyStart
        numericBound bitBound targetLayoutData.bodyStart_le_tokenCount
        targetLayoutData.header targetLayoutData.boundaryFinish_le_tokenCount
        targetLayoutData.boundaryStartEntry
        targetLayoutData.boundaryFinishEntry targetLayoutData.rows hwidth
        htokenCount houtputCount htokenTableSize htargetBoundarySize
        hnumericSize
  have hresource5 :
      certificate5.compile.payloadLength <=
        sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound :=
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate5 |>.trans
      ((compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
        tokenTable width tokenCount sourceOutputBoundary outputCount
        targetOutputBoundary outputCount hsame).trans
        (compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed
          tokenTable width tokenCount sourceOutputBoundary outputCount
          targetOutputBoundary outputCount numericBound bitBound hsame hwidth
          htokenCount houtputCount htokenTableSize hsourceBoundarySize
          htargetBoundarySize hnumericSize))
  have hresource6 :
      certificate6.compile.payloadLength <=
        compactNatSizeFixedPayloadPolynomial bitBound :=
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate6 |>.trans
      ((compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
        sourceOutputBoundarySize sourceOutputBoundary hsourceSize).trans
        (compactNatSizeStructuralPayloadPolynomial_le_fixed
          sourceOutputBoundarySize sourceOutputBoundary bitBound hsourceSize
          hsourceBoundarySize))
  have hresource7 := compiledCompletedArea_payloadLength_le_fixed tokenCount
    outputCount sourceOutputBoundary sourceOutputBoundarySize numericBound
    bitBound hsourceArea hsourceSize htokenCount houtputCount
    hsourceBoundarySize hnumericSize
  have hresource8 :
      certificate8.compile.payloadLength <=
        compactNatSizeFixedPayloadPolynomial bitBound :=
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate8 |>.trans
      ((compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
        targetOutputBoundarySize targetOutputBoundary htargetSize).trans
        (compactNatSizeStructuralPayloadPolynomial_le_fixed
          targetOutputBoundarySize targetOutputBoundary bitBound htargetSize
          htargetBoundarySize))
  have hresource9 := compiledCompletedArea_payloadLength_le_fixed tokenCount
    outputCount targetOutputBoundary targetOutputBoundarySize numericBound
    bitBound htargetArea htargetSize htokenCount houtputCount
    htargetBoundarySize hnumericSize
  have hclosed1 :
      formula1.freeVariables = ∅ := by
    simpa only [formula1] using
      compactBinaryNatCompletedStatusPrefixClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount sourceStatusStart sourceOutputStart
  have hclosed2 :
      formula2.freeVariables = ∅ := by
    simpa only [formula2] using
      compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount sourceOutputStart outputCount
        sourceStatusFinish sourceOutputBoundary
  have hclosed3 :
      formula3.freeVariables = ∅ := by
    simpa only [formula3] using
      compactBinaryNatCompletedStatusPrefixClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount targetStatusStart targetOutputStart
  have hclosed4 :
      formula4.freeVariables = ∅ := by
    simpa only [formula4] using
      compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount targetOutputStart outputCount
        targetStatusFinish targetOutputBoundary
  have hclosed5 :
      formula5.freeVariables = ∅ := by
    simpa only [formula5] using
      compactAdditiveNatListSameRowsClosedFormula_freeVariables_eq_empty_fullyFixed
        tokenTable width tokenCount sourceOutputBoundary outputCount
        targetOutputBoundary outputCount
  have hclosed6 :
      formula6.freeVariables = ∅ := by
    simpa only [formula6] using
      natSizeClosedFormula_freeVariables_eq_empty sourceOutputBoundarySize
        sourceOutputBoundary
  have hclosed7 :
      formula7.freeVariables = ∅ := by
    simpa only [formula7] using
      parserAreaFormula_freeVariables_eq_empty sourceOutputBoundarySize
        outputCount tokenCount
  have hclosed8 :
      formula8.freeVariables = ∅ := by
    simpa only [formula8] using
      natSizeClosedFormula_freeVariables_eq_empty targetOutputBoundarySize
        targetOutputBoundary
  have hclosed9 :
      formula9.freeVariables = ∅ := by
    simpa only [formula9] using
      parserAreaFormula_freeVariables_eq_empty targetOutputBoundarySize
        outputCount tokenCount
  have hcode1 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      certificate1.compile).trans hresource1
  have hcode2 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      proof2).trans hresource2
  have hcode3 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      certificate3.compile).trans hresource3
  have hcode4 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      proof4).trans hresource4
  have hcode5 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      certificate5.compile).trans hresource5
  have hcode6 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      certificate6.compile).trans hresource6
  have hcode7 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      certificate7.compile).trans hresource7
  have hcode8 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      certificate8.compile).trans hresource8
  have hcode9 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      certificate9.compile).trans hresource9
  have hcodeFormula1 :
      (binaryFormulaCode formula1).length <=
        binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
          bitBound := by
    simpa only [formula1] using hcode1
  have hcodeFormula2 :
      (binaryFormulaCode formula2).length <=
        compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
          numericBound bitBound := by
    simpa only [formula2] using hcode2
  have hcodeFormula3 :
      (binaryFormulaCode formula3).length <=
        binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
          bitBound := by
    simpa only [formula3] using hcode3
  have hcodeFormula4 :
      (binaryFormulaCode formula4).length <=
        compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
          numericBound bitBound := by
    simpa only [formula4] using hcode4
  have hcodeFormula5 :
      (binaryFormulaCode formula5).length <=
        sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound := by
    simpa only [formula5] using hcode5
  have hcodeFormula6 :
      (binaryFormulaCode formula6).length <=
        compactNatSizeFixedPayloadPolynomial bitBound := by
    simpa only [formula6] using hcode6
  have hcodeFormula7 :
      (binaryFormulaCode formula7).length <=
        completedAreaFixedPayloadPolynomial bitBound := by
    simpa only [formula7] using hcode7
  have hcodeFormula8 :
      (binaryFormulaCode formula8).length <=
        compactNatSizeFixedPayloadPolynomial bitBound := by
    simpa only [formula8] using hcode8
  have hcodeFormula9 :
      (binaryFormulaCode formula9).length <=
        completedAreaFixedPayloadPolynomial bitBound := by
    simpa only [formula9] using hcode9
  have hcode :
      (binaryFormulaCode
        (formula1 ⋏
          (formula2 ⋏
            (formula3 ⋏
              (formula4 ⋏
                (formula5 ⋏
                  (formula6 ⋏
                    (formula7 ⋏ (formula8 ⋏ formula9))))))))).length <=
        completedSameRowsUniformDirectFormulaCodePolynomial numericBound
          bitBound := by
    simp only [binaryFormulaCode, List.length_append]
    unfold completedSameRowsUniformDirectFormulaCodePolynomial
    omega
  have hgeneral :=
    compileDirectNineConjunction_payloadLength_le_closedGeneral
      certificate1.compile proof2 certificate3.compile proof4
      certificate5.compile certificate6.compile certificate7.compile
      certificate8.compile certificate9.compile
      (binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
        bitBound)
      (compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
        numericBound bitBound)
      (binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
        bitBound)
      (compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
        numericBound bitBound)
      (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (compactNatSizeFixedPayloadPolynomial bitBound)
      (completedAreaFixedPayloadPolynomial bitBound)
      (compactNatSizeFixedPayloadPolynomial bitBound)
      (completedAreaFixedPayloadPolynomial bitBound)
      (completedSameRowsUniformDirectFormulaCodePolynomial numericBound
        bitBound)
      hresource1 hresource2 hresource3 hresource4 hresource5 hresource6
      hresource7 hresource8 hresource9 (by
        unfold completedSameRowsUniformDirectFormulaCodePolynomial
        omega)
      hclosed1 hclosed2 hclosed3 hclosed4 hclosed5 hclosed6 hclosed7 hclosed8
      hclosed9 hcode
  unfold completedSameRowsUniformDirectFixedPayloadPolynomial
  unfold compileCompactBinaryNatCompletedStatusSameRowsUniformDirect
  dsimp only [sourceLayoutData, targetLayoutData, formula1, formula2, formula3,
    formula4, formula5, formula6, formula7, formula8, formula9, certificate1,
    sourceLayoutRaw, proof2, certificate3, targetLayoutRaw, proof4,
    certificate5, certificate6, certificate7, certificate8, certificate9]
  exact hgeneral

end FoundationCompactNumericListedDirectParserDoneUniformDirectFixedBounds
