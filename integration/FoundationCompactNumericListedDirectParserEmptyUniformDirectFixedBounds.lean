import integration.FoundationCompactNumericListedDirectParserEmptyUniformDirectAlignment
import integration.FoundationCompactNumericListedDirectParserEmptyAtomicFixedBounds
import integration.FoundationCompactPADirectNineConjunctionClosedGeneralBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Fixed resource bound for the uniform direct empty parser proof -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserEmptyUniformDirectFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPADirectNineConjunctionCompiler
open FoundationCompactPADirectNineConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyAtomicFixedBounds
open FoundationCompactNumericListedDirectParserEmptyUniformDirectCompiler
open FoundationCompactNumericListedDirectParserEmptyUniformDirectAlignment
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

private abbrev emptyFixedZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate.zeroValuation

def parserEmptyUniformDirectFormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  2 * parserEmptyClosedEqZeroFixedPayloadPolynomial +
    compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound +
    2 * sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound +
    binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
      bitBound +
    compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound +
    compactNatSizeFixedPayloadPolynomial bitBound +
    completedAreaFixedPayloadPolynomial bitBound +
    20 * (binaryNatCode 4).length + 100

def parserEmptyUniformDirectFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  directNineConjunctionGeneralPayloadEnvelope
    (parserEmptyUniformDirectFormulaCodePolynomial numericBound bitBound)
    parserEmptyClosedEqZeroFixedPayloadPolynomial
    parserEmptyClosedEqZeroFixedPayloadPolynomial
    (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound)
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    (binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
      bitBound)
    (compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound)
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    (compactNatSizeFixedPayloadPolynomial bitBound)
    (completedAreaFixedPayloadPolynomial bitBound)

theorem compileCompactUnifiedParserEmptyUniformDirectContext_payloadLength_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserEmptyGraphRows
      tokenTable width tokenCount current next witness)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (houtputBoundarySize :
      Nat.size witness.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactUnifiedParserEmptyUniformDirectContext tokenTable width
      tokenCount current next witness numericBound bitBound hgraph htokenCount
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          hcurrentValue (5 : Fin 8))
      houtputBoundarySize hnumericSize).payloadLength <=
      parserEmptyUniformDirectFixedPayloadPolynomial numericBound bitBound := by
  have hgraphRaw := hgraph
  rcases hgraph with
    ⟨hcurrentCount, hnextCount, hrunning, htokenRows, hcompleted⟩
  rcases hcompleted with
    ⟨⟨hprefix, hlayout, houtputRows⟩, hsize, harea⟩
  have hprefixRaw := hprefix
  let layoutData :=
    compactAdditiveStructuredListLayoutDataOfLayout tokenTable width tokenCount
      witness.targetOutputStart current.tokensCount next.finish
      witness.targetOutputBoundary hlayout
  let formula1 : ValuationFormula :=
    “!!(shortBinaryNumeralTerm current.tasksCount) = 0”
  let formula2 : ValuationFormula :=
    “!!(shortBinaryNumeralTerm next.tasksCount) = 0”
  let formula3 := compactBinaryNatRunningStatusSliceClosedFormula tokenTable
    width tokenCount current.tasksFinish current.finish
  let formula4 := compactAdditiveNatListSameRowsClosedFormula tokenTable width
    tokenCount current.tokensBoundary current.tokensCount next.tokensBoundary
    next.tokensCount
  let formula5 := compactBinaryNatCompletedStatusPrefixClosedFormula tokenTable
    width tokenCount next.tasksFinish witness.targetOutputStart
  let formula6 := compactAdditiveStructuredListLayoutClosedFormula tokenTable
    width tokenCount witness.targetOutputStart current.tokensCount next.finish
    witness.targetOutputBoundary
  let formula7 := compactAdditiveNatListSameRowsClosedFormula tokenTable width
    tokenCount current.tokensBoundary current.tokensCount
    witness.targetOutputBoundary current.tokensCount
  let formula8 := compactNatSizeClosedFormula witness.targetOutputBoundarySize
    witness.targetOutputBoundary
  let formula9 : ValuationFormula :=
    “!!(shortBinaryNumeralTerm witness.targetOutputBoundarySize) ≤
      (!!(shortBinaryNumeralTerm current.tokensCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let certificate1 := closedEqZeroCertificate current.tasksCount hcurrentCount
  let certificate2 := closedEqZeroCertificate next.tasksCount hnextCount
  let certificate3 :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksFinish current.finish hrunning
  let certificate4 :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokenRows
  let certificate5 :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksFinish witness.targetOutputStart
      hprefixRaw
  let layoutProof :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount witness.targetOutputStart current.tokensCount
      next.finish witness.targetOutputBoundary layoutData.bodyStart numericBound
      bitBound layoutData.bodyStart_le_tokenCount layoutData.header
      layoutData.boundaryFinish_le_tokenCount layoutData.boundaryStartEntry
      layoutData.boundaryFinishEntry layoutData.rows htokenCount
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          hcurrentValue (5 : Fin 8))
      houtputBoundarySize hnumericSize
  have hlayoutContext :
      (∅ : Finset ValuationFormula) =
        valuationContext formula6.freeVariables emptyFixedZeroValuation := by
    rw [show formula6.freeVariables = ∅ by
      simpa only [formula6] using
        compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
          tokenTable width tokenCount witness.targetOutputStart
          current.tokensCount next.finish witness.targetOutputBoundary]
    simp [valuationContext]
  let proof6 := CertifiedPAContextProof.castContext hlayoutContext layoutProof
  let certificate7 :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      witness.targetOutputBoundary current.tokensCount houtputRows
  let certificate8 := compactNatSizeExplicitHybridCertificateOfEq
    witness.targetOutputBoundarySize witness.targetOutputBoundary hsize
  let certificate9 := outputBoundaryAreaCertificate tokenCount
    current.tokensCount witness.targetOutputBoundarySize harea
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hcurrentTasksFinish : current.tasksFinish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (3 : Fin 8)
  have hcurrentTokensCount : current.tokensCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (5 : Fin 8)
  have hnextTasksFinish : next.tasksFinish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextValue (3 : Fin 8)
  have hcurrentFinishSize : Nat.size current.finish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (1 : Fin 8)
  have hcurrentTasksFinishSize :
      Nat.size current.tasksFinish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (3 : Fin 8)
  have hcurrentTokensBoundarySize :
      Nat.size current.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (4 : Fin 8)
  have hnextTokensBoundarySize :
      Nat.size next.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (4 : Fin 8)
  have hnextTasksFinishSize : Nat.size next.tasksFinish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (3 : Fin 8)
  rcases hprefix with ⟨innerStart, hinnerLe, hfirstCell, hsecondCell⟩
  have hinnerEq : innerStart = next.tasksFinish + 1 := by
    exact hfirstCell.2.1
  have hinnerValue : next.tasksFinish + 1 <= numericBound := by
    rw [← hinnerEq]
    exact hinnerLe.trans htokenCount
  have houtputStartValue : witness.targetOutputStart <= numericBound := by
    have houtputEq : witness.targetOutputStart = innerStart + 1 :=
      hsecondCell.2.1
    rw [houtputEq]
    exact (Nat.succ_le_of_lt hsecondCell.1).trans htokenCount
  have hinnerSize : Nat.size (next.tasksFinish + 1) <= bitBound :=
    (Nat.size_le_size hinnerValue).trans hnumericSize
  have houtputStartSize :
      Nat.size witness.targetOutputStart <= bitBound :=
    (Nat.size_le_size houtputStartValue).trans hnumericSize
  have hresource1 :
      certificate1.compile.payloadLength <=
        parserEmptyClosedEqZeroFixedPayloadPolynomial :=
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate1 |>.trans
      (closedEqZeroCertificate_structuralPayloadBound_le_fixed
        current.tasksCount hcurrentCount)
  have hresource2 :
      certificate2.compile.payloadLength <=
        parserEmptyClosedEqZeroFixedPayloadPolynomial :=
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate2 |>.trans
      (closedEqZeroCertificate_structuralPayloadBound_le_fixed
        next.tasksCount hnextCount)
  have hresource3 :
      certificate3.compile.payloadLength <=
        compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
          numericBound bitBound :=
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate3 |>.trans
      (compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount current.tasksFinish current.finish
        numericBound bitBound hwidth hcurrentTasksFinish htokenTableSize
        hwidthSize htokenCountSize hcurrentTasksFinishSize hcurrentFinishSize
        hrunning)
  have hresource4 :
      certificate4.compile.payloadLength <=
        sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound :=
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate4 |>.trans
      ((compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
        tokenTable width tokenCount current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount htokenRows).trans
        (compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount next.tokensBoundary next.tokensCount numericBound
          bitBound htokenRows hwidth htokenCount hcurrentTokensCount
          htokenTableSize hcurrentTokensBoundarySize hnextTokensBoundarySize
          hnumericSize))
  have hresource5 :
      certificate5.compile.payloadLength <=
        binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
          bitBound :=
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate5 |>.trans
      (compactBinaryNatCompletedStatusPrefixExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount next.tasksFinish
        witness.targetOutputStart numericBound bitBound hwidth
        hnextTasksFinish hinnerValue htokenTableSize hwidthSize
        htokenCountSize hnextTasksFinishSize houtputStartSize hinnerSize
        hbitPositive hprefixRaw)
  have hresource6 :
      proof6.payloadLength <=
        compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
          numericBound bitBound := by
    dsimp only [proof6]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact
      compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le_fixed
        tokenTable width tokenCount witness.targetOutputStart
        current.tokensCount next.finish witness.targetOutputBoundary
        layoutData.bodyStart numericBound bitBound
        layoutData.bodyStart_le_tokenCount layoutData.header
        layoutData.boundaryFinish_le_tokenCount layoutData.boundaryStartEntry
        layoutData.boundaryFinishEntry layoutData.rows hwidth htokenCount
        hcurrentTokensCount htokenTableSize houtputBoundarySize hnumericSize
  have hresource7 :
      certificate7.compile.payloadLength <=
        sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound :=
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate7 |>.trans
      ((compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
        tokenTable width tokenCount current.tokensBoundary current.tokensCount
        witness.targetOutputBoundary current.tokensCount houtputRows).trans
        (compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount witness.targetOutputBoundary current.tokensCount
          numericBound bitBound houtputRows hwidth htokenCount
          hcurrentTokensCount htokenTableSize hcurrentTokensBoundarySize
          houtputBoundarySize hnumericSize))
  have hresource8 :
      certificate8.compile.payloadLength <=
        compactNatSizeFixedPayloadPolynomial bitBound :=
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate8 |>.trans
      ((compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
        witness.targetOutputBoundarySize witness.targetOutputBoundary
        hsize).trans
        (compactNatSizeStructuralPayloadPolynomial_le_fixed
          witness.targetOutputBoundarySize witness.targetOutputBoundary
          bitBound hsize houtputBoundarySize))
  have hresource9 :
      certificate9.compile.payloadLength <=
        completedAreaFixedPayloadPolynomial bitBound :=
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate9 |>.trans
      (outputBoundaryAreaCertificate_structuralPayloadBound_le_fixed tokenCount
        current.tokensCount witness.targetOutputBoundary
        witness.targetOutputBoundarySize numericBound bitBound harea hsize
        htokenCount hcurrentTokensCount houtputBoundarySize hnumericSize)
  have htotalClosed :
      (formula1 ⋏
        (formula2 ⋏
          (formula3 ⋏
            (formula4 ⋏
              (formula5 ⋏
                (formula6 ⋏
                  (formula7 ⋏ (formula8 ⋏ formula9)))))))).freeVariables =
        ∅ := by
    have hclosed :
        (compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount
          current next witness).freeVariables = ∅ := by
      unfold compactUnifiedParserEmptyClosedFormula
      apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
      intro coordinate
      fin_cases coordinate <;>
        apply shortBinaryNumeralTerm_freeVariables_eq_empty
    rw [compactUnifiedParserEmptyClosedFormula_alignment tokenTable width
      tokenCount current next witness] at hclosed
    simpa only [compactUnifiedParserEmptyExplicitFormula, formula1, formula2,
      formula3, formula4, formula5, formula6, formula7, formula8, formula9]
      using hclosed
  have hclosedParts :
      formula1.freeVariables = ∅ ∧ formula2.freeVariables = ∅ ∧
      formula3.freeVariables = ∅ ∧ formula4.freeVariables = ∅ ∧
      formula5.freeVariables = ∅ ∧ formula6.freeVariables = ∅ ∧
      formula7.freeVariables = ∅ ∧ formula8.freeVariables = ∅ ∧
      formula9.freeVariables = ∅ := by
    simpa only [LO.FirstOrder.Semiformula.freeVariables_and,
      Finset.union_eq_empty] using htotalClosed
  have hcode1 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      certificate1.compile).trans hresource1
  have hcode2 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      certificate2.compile).trans hresource2
  have hcode3 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      certificate3.compile).trans hresource3
  have hcode4 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      certificate4.compile).trans hresource4
  have hcode5 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      certificate5.compile).trans hresource5
  have hcode6 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      proof6).trans hresource6
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
        parserEmptyClosedEqZeroFixedPayloadPolynomial := by
    simpa only [formula1] using hcode1
  have hcodeFormula2 :
      (binaryFormulaCode formula2).length <=
        parserEmptyClosedEqZeroFixedPayloadPolynomial := by
    simpa only [formula2] using hcode2
  have hcodeFormula3 :
      (binaryFormulaCode formula3).length <=
        compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
          numericBound bitBound := by
    simpa only [formula3] using hcode3
  have hcodeFormula4 :
      (binaryFormulaCode formula4).length <=
        sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound := by
    simpa only [formula4] using hcode4
  have hcodeFormula5 :
      (binaryFormulaCode formula5).length <=
        binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
          bitBound := by
    simpa only [formula5] using hcode5
  have hcodeFormula6 :
      (binaryFormulaCode formula6).length <=
        compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
          numericBound bitBound := by
    simpa only [formula6] using hcode6
  have hcodeFormula7 :
      (binaryFormulaCode formula7).length <=
        sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound := by
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
        parserEmptyUniformDirectFormulaCodePolynomial numericBound bitBound := by
    simp only [binaryFormulaCode, List.length_append]
    unfold parserEmptyUniformDirectFormulaCodePolynomial
    omega
  have hgeneral :=
    compileDirectNineConjunction_payloadLength_le_closedGeneral
      certificate1.compile certificate2.compile certificate3.compile
      certificate4.compile certificate5.compile proof6 certificate7.compile
      certificate8.compile certificate9.compile
      parserEmptyClosedEqZeroFixedPayloadPolynomial
      parserEmptyClosedEqZeroFixedPayloadPolynomial
      (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound)
      (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
        bitBound)
      (compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
        numericBound bitBound)
      (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (compactNatSizeFixedPayloadPolynomial bitBound)
      (completedAreaFixedPayloadPolynomial bitBound)
      (parserEmptyUniformDirectFormulaCodePolynomial numericBound bitBound)
      hresource1 hresource2 hresource3 hresource4 hresource5 hresource6
      hresource7 hresource8 hresource9 (by
        unfold parserEmptyUniformDirectFormulaCodePolynomial
        omega)
      hclosedParts.1 hclosedParts.2.1 hclosedParts.2.2.1
      hclosedParts.2.2.2.1 hclosedParts.2.2.2.2.1
      hclosedParts.2.2.2.2.2.1 hclosedParts.2.2.2.2.2.2.1
      hclosedParts.2.2.2.2.2.2.2.1 hclosedParts.2.2.2.2.2.2.2.2 hcode
  unfold parserEmptyUniformDirectFixedPayloadPolynomial
  unfold compileCompactUnifiedParserEmptyUniformDirectContext
  dsimp only [layoutData, formula1, formula2, formula3, formula4, formula5,
    formula6, formula7, formula8, formula9, certificate1, certificate2,
    certificate3, certificate4, certificate5, layoutProof, proof6,
    certificate7, certificate8, certificate9]
  exact hgeneral

#print axioms
  compileCompactUnifiedParserEmptyUniformDirectContext_payloadLength_le_fixed

end FoundationCompactNumericListedDirectParserEmptyUniformDirectFixedBounds
