import integration.FoundationCompactNumericListedDirectNatListListRowsDirectBranchUniformResources
import integration.FoundationCompactPADirectConnectiveTransparentBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompiler

/-! # Direct row-independent proof for one additive natural-list-list row -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectNatListListRowsDirectBranchUniformBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationContextSingletonCodeBound
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFullyFixedProof
open FoundationCompactNumericListedDirectNatListSliceUniformDirectBound
open FoundationCompactNumericListedDirectNatListListRowsDirectBranchUniformResources

private abbrev listRowsZeroValuation : Nat -> Nat :=
  FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation

private noncomputable def explicitDirectConjunctionWithUniformSyntax
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    {leftResource rightResource syntaxResource : Nat}
    (leftBound : ExplicitDirectFormulaBound valuation left leftResource)
    (rightBound : ExplicitDirectFormulaBound valuation right rightResource)
    (hpositive : 1 <= syntaxResource)
    (hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
      (valuationContext (left ⋏ right).freeVariables valuation) <=
        syntaxResource)
    (hleft : (binaryFormulaCode left).length <= syntaxResource)
    (hright : (binaryFormulaCode right).length <= syntaxResource)
    (hconjunction : (binaryFormulaCode (left ⋏ right)).length <=
      syntaxResource) :
    ExplicitDirectFormulaBound valuation (left ⋏ right)
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
        rightResource) := by
  let proof := compileDirectConjunction leftBound.proof rightBound.proof
  have hraw := compileDirectConjunction_payloadLength_le leftBound.proof
    rightBound.proof leftResource rightResource leftBound.payloadLength_le
    rightBound.payloadLength_le
  have henvelope :
      transparentHybridConjunctionPayloadEnvelope valuation left right
          leftResource rightResource <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
          rightResource := by
    change hybridConjunctionStructuralPayloadEnvelope valuation left right
      leftResource rightResource <= _
    exact hybridConjunctionStructuralPayloadEnvelope_le_general valuation left
      right leftResource rightResource syntaxResource hpositive hcontext hleft
      hright hconjunction
  exact { proof := proof, payloadLength_le := hraw.trans henvelope }

noncomputable def compactAdditiveNatListListRowsTerminalUniformBoundOfData
    (tokenTable width tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveNatListListRowData tokenTable width tokenCount
      boundaryTable index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound (extendValuation index listRowsZeroValuation)
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount) (&0 : ValuationTerm)
          (shortBinaryNumeralTerm data.left) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (‘&0 + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm data.right) ⋏
          compactAdditiveNatListSliceClosedFormula tokenTable width tokenCount
            data.left data.innerCount data.right))
      (compactAdditiveNatListListRowsTerminalPayloadResource numericBound
        bitBound) := by
  let valuation := extendValuation index listRowsZeroValuation
  let leftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount) (&0 : ValuationTerm)
    (shortBinaryNumeralTerm data.left)
  let rightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount) (‘&0 + 1’ : ValuationTerm)
    (shortBinaryNumeralTerm data.right)
  let sliceFormula := compactAdditiveNatListSliceClosedFormula tokenTable width
    tokenCount data.left data.innerCount data.right
  let entryResource := compactAdditiveNatListListRowsEntryPayloadResource
    numericBound bitBound
  let sliceResource := compactAdditiveNatListListRowsSlicePayloadResource
    numericBound bitBound
  let syntaxResource := compactAdditiveNatListListRowsTerminalSyntaxResource
    numericBound bitBound
  have hindex : index <= numericBound := by omega
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hindexSize : Nat.size index <= bitBound :=
    (Nat.size_le_size hindex).trans hnumericSize
  have hindexSuccessorSize : Nat.size (index + 1) <= bitBound :=
    (Nat.size_le_size hindexSuccessor).trans hnumericSize
  have hleftBound : data.left <= numericBound :=
    data.left_le.trans htokenCount
  have hrightBound : data.right <= numericBound :=
    data.right_le.trans htokenCount
  have hinnerCountBound : data.innerCount <= numericBound :=
    data.innerCount_le.trans htokenCount
  have hleftSize : Nat.size data.left <= bitBound :=
    (Nat.size_le_size hleftBound).trans hnumericSize
  have hrightSize : Nat.size data.right <= bitBound :=
    (Nat.size_le_size hrightBound).trans hnumericSize
  have hinnerCountSize : Nat.size data.innerCount <= bitBound :=
    (Nat.size_le_size hinnerCountBound).trans hnumericSize
  have hvaluation : valuation 0 <= numericBound := by
    simpa only [valuation, listRowsZeroValuation, extendValuation_zero] using
      hindex
  have hleftEvaluation : termValue valuation (&0 : ValuationTerm) = index := by
    simpa only [valuation, listRowsZeroValuation] using
      termValue_indexTerm_bvarZero_under_extendValuation index
  have hrightEvaluation :
      termValue valuation (‘&0 + 1’ : ValuationTerm) = index + 1 := by
    simpa only [valuation, listRowsZeroValuation] using
      termValue_indexTerm_bvarZeroAddOne_under_extendValuation index
  have hleftIndexVariables : (&0 : ValuationTerm).freeVariables ⊆ {0} := by
    simp
  have hrightIndexVariables :
      (‘&0 + 1’ : ValuationTerm).freeVariables ⊆ {0} := by
    rw [FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds.arithmeticAddTerm_freeVariables_eq_union]
    simp
  have hleftIndexCode : (binaryTermCode (&0 : ValuationTerm)).length <=
      compactAdditiveNatListListRowsIndexCodeBound := by
    unfold compactAdditiveNatListListRowsIndexCodeBound
    omega
  have hrightIndexCode :
      (binaryTermCode (‘&0 + 1’ : ValuationTerm)).length <=
        compactAdditiveNatListListRowsIndexCodeBound := by
    unfold compactAdditiveNatListListRowsIndexCodeBound
    omega
  let leftBound :=
    compactSequentFormulaStepFixedWidthEntryAtOpenIndexFullyFixedBound valuation
      boundaryTable tokenCount data.left (&0 : ValuationTerm) numericBound
      bitBound compactAdditiveNatListListRowsIndexCodeBound htokenCount
      (by simpa only [hleftEvaluation] using hindex) hvaluation hboundarySize
      htokenCountSize (by simpa only [hleftEvaluation] using hindexSize)
      hleftSize hleftIndexCode hleftIndexVariables (by
        simpa only [hleftEvaluation] using data.left_entry)
  let rightBound :=
    compactSequentFormulaStepFixedWidthEntryAtOpenIndexFullyFixedBound valuation
      boundaryTable tokenCount data.right (‘&0 + 1’ : ValuationTerm)
      numericBound bitBound compactAdditiveNatListListRowsIndexCodeBound
      htokenCount (by simpa only [hrightEvaluation] using hindexSuccessor)
      hvaluation hboundarySize htokenCountSize
      (by simpa only [hrightEvaluation] using hindexSuccessorSize) hrightSize
      hrightIndexCode hrightIndexVariables (by
        simpa only [hrightEvaluation] using data.right_entry)
  have hsliceData := compactAdditiveNatListSlice_explicitData data.slice
  have hbodyStartBound : data.left + 1 <= numericBound :=
    hsliceData.1.trans htokenCount
  have hbodyStartSize : Nat.size (data.left + 1) <= bitBound :=
    (Nat.size_le_size hbodyStartBound).trans hnumericSize
  let sliceFixed := compactAdditiveNatListSliceUniformDirectBound tokenTable
    width tokenCount data.left data.innerCount data.right (data.left + 1)
    numericBound bitBound hsliceData.1 hsliceData.2.1 hsliceData.2.2
    htokenCount hwidth hleftBound htableSize hwidthSize htokenCountSize
    hleftSize hinnerCountSize hrightSize hbodyStartSize
  let sliceProof : CertifiedPAContextProof
      (valuationContext sliceFormula.freeVariables valuation) sliceFormula :=
    CertifiedPAContextProof.castContext (by
      rw [sliceFixed.closed]
      simp [valuationContext]) sliceFixed.proof
  let sliceBound : ExplicitDirectFormulaBound valuation sliceFormula
      sliceResource :=
    { proof := sliceProof
      payloadLength_le := by
        dsimp only [sliceProof]
        rw [CertifiedPAContextProof.castContext_payloadLength]
        simpa only [sliceResource,
          compactAdditiveNatListListRowsSlicePayloadResource] using
          sliceFixed.payloadLength_le }
  have hleftCode : (binaryFormulaCode leftFormula).length <= entryResource :=
    (FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      leftBound.proof).trans leftBound.payloadLength_le
  have hrightCode : (binaryFormulaCode rightFormula).length <= entryResource :=
    (FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      rightBound.proof).trans rightBound.payloadLength_le
  have hsliceCode : (binaryFormulaCode sliceFormula).length <= sliceResource :=
    sliceFixed.codeLength_le
  have hrightVariables : rightFormula.freeVariables ⊆ {0} := by
    dsimp only [rightFormula]
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _) hrightIndexVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have hleftVariables : leftFormula.freeVariables ⊆ {0} := by
    dsimp only [leftFormula]
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _) hleftIndexVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have hsliceVariables : sliceFormula.freeVariables ⊆ {0} := by
    rw [sliceFixed.closed]
    simp
  have hinnerVariables : (rightFormula ⋏ sliceFormula).freeVariables ⊆
      {0} := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hrightVariables hsliceVariables
  have houterVariables :
      (leftFormula ⋏ (rightFormula ⋏ sliceFormula)).freeVariables ⊆ {0} := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hleftVariables hinnerVariables
  have hinnerCode :
      (binaryFormulaCode (rightFormula ⋏ sliceFormula)).length <=
        entryResource + sliceResource + (binaryNatCode 4).length := by
    simp only [binaryFormulaCode, List.length_append]
    omega
  let innerCodeResource :=
    entryResource + sliceResource + (binaryNatCode 4).length
  have houterCode :
      (binaryFormulaCode
        (leftFormula ⋏ (rightFormula ⋏ sliceFormula))).length <=
        entryResource + innerCodeResource + (binaryNatCode 4).length := by
    simp only [binaryFormulaCode, List.length_append]
    dsimp only [innerCodeResource]
    omega
  have hinnerContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
      (valuationContext (rightFormula ⋏ sliceFormula).freeVariables valuation) <=
        syntaxResource := by
    have hbase := valuationContext_formulaCodeSum_le_singleton
      (rightFormula ⋏ sliceFormula).freeVariables valuation numericBound
      hinnerVariables hvaluation
    exact hbase.trans (by
      unfold syntaxResource
        compactAdditiveNatListListRowsTerminalSyntaxResource
        compactAdditiveNatListListRowsContextCodeResource
      omega)
  have houterContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
      (valuationContext
        (leftFormula ⋏ (rightFormula ⋏ sliceFormula)).freeVariables valuation) <=
        syntaxResource := by
    have hbase := valuationContext_formulaCodeSum_le_singleton
      (leftFormula ⋏ (rightFormula ⋏ sliceFormula)).freeVariables valuation
      numericBound houterVariables hvaluation
    exact hbase.trans (by
      unfold syntaxResource
        compactAdditiveNatListListRowsTerminalSyntaxResource
        compactAdditiveNatListListRowsContextCodeResource
      omega)
  have hpositive : 1 <= syntaxResource := by
    unfold syntaxResource compactAdditiveNatListListRowsTerminalSyntaxResource
    omega
  have hentrySyntax : entryResource <= syntaxResource := by
    unfold syntaxResource compactAdditiveNatListListRowsTerminalSyntaxResource
      entryResource compactAdditiveNatListListRowsEntryPayloadResource
    omega
  have hsliceSyntax : sliceResource <= syntaxResource := by
    unfold syntaxResource compactAdditiveNatListListRowsTerminalSyntaxResource
      sliceResource compactAdditiveNatListListRowsSlicePayloadResource
    omega
  have hinnerSyntax : innerCodeResource <= syntaxResource := by
    unfold syntaxResource compactAdditiveNatListListRowsTerminalSyntaxResource
      innerCodeResource entryResource sliceResource
      compactAdditiveNatListListRowsEntryPayloadResource
      compactAdditiveNatListListRowsSlicePayloadResource
    omega
  have houterSyntax :
      entryResource + innerCodeResource + (binaryNatCode 4).length <=
        syntaxResource := by
    unfold syntaxResource compactAdditiveNatListListRowsTerminalSyntaxResource
      innerCodeResource entryResource sliceResource
      compactAdditiveNatListListRowsEntryPayloadResource
      compactAdditiveNatListListRowsSlicePayloadResource
    omega
  let innerBound := explicitDirectConjunctionWithUniformSyntax rightBound
    sliceBound hpositive hinnerContext (hrightCode.trans hentrySyntax)
    (hsliceCode.trans hsliceSyntax) (hinnerCode.trans hinnerSyntax)
  let outerBound := explicitDirectConjunctionWithUniformSyntax leftBound
    innerBound hpositive houterContext (hleftCode.trans hentrySyntax)
    (hinnerCode.trans hinnerSyntax)
    (houterCode.trans houterSyntax)
  simpa only [valuation, leftFormula, rightFormula, sliceFormula, outerBound,
    compactAdditiveNatListListRowsTerminalPayloadResource,
    compactAdditiveNatListListRowsTerminalInnerPayloadResource,
    compactAdditiveNatListListRowsEntryPayloadResource,
    syntaxResource, entryResource, sliceResource] using outerBound

noncomputable def compactAdditiveNatListListRowsDirectUniformBranchBoundOfData
    (tokenTable width tokenCount boundaryTable count index numericBound
      bitBound : Nat)
    (data : CompactAdditiveNatListListRowData tokenTable width tokenCount
      boundaryTable index)
    (hindex : index < count)
    (hcount : count <= numericBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound (extendValuation index listRowsZeroValuation)
      (Rewriting.free
        (compactAdditiveNatListListRowsBody tokenTable width tokenCount
          boundaryTable))
      (compactAdditiveNatListListRowsBranchPayloadResource tokenTable width
        tokenCount boundaryTable numericBound bitBound) := by
  let valuation := extendValuation index listRowsZeroValuation
  let body := compactAdditiveNatListListRowsBranchTerminal tokenTable width
    tokenCount boundaryTable
  let values : Fin 3 -> Nat := ![data.innerCount, data.right, data.left]
  have hindexSuccessor : index + 1 <= numericBound := by omega
  let terminalBound := compactAdditiveNatListListRowsTerminalUniformBoundOfData
    tokenTable width tokenCount boundaryTable index numericBound bitBound data
    hwidth htokenCount hindexSuccessor htableSize hboundarySize hnumericSize
  have hvalueTerms :
      (fun coordinate : Fin 3 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.innerCount,
          shortBinaryNumeralTerm data.right,
          shortBinaryNumeralTerm data.left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hterminalFormula :
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount) (&0 : ValuationTerm)
          (shortBinaryNumeralTerm data.left) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (‘&0 + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm data.right) ⋏
          compactAdditiveNatListSliceClosedFormula tokenTable width tokenCount
            data.left data.innerCount data.right)) =
        body ⇜ fun coordinate => shortBinaryNumeralTerm (values coordinate) := by
    rw [hvalueTerms]
    exact (compactAdditiveNatListListRowsBranchTerminal_substitution_alignment
      tokenTable width tokenCount boundaryTable data.left data.right
      data.innerCount).symm
  let terminal := castValuationContextProof hterminalFormula terminalBound.proof
  have hterminal : terminal.payloadLength <=
      compactAdditiveNatListListRowsTerminalPayloadResource numericBound
        bitBound := by
    dsimp only [terminal]
    rw [castValuationContextProof_payloadLength_eq]
    exact terminalBound.payloadLength_le
  have hvalues : forall coordinate, values coordinate <= tokenCount := by
    intro coordinate
    fin_cases coordinate
    · exact data.innerCount_le
    · exact data.right_le
    · exact data.left_le
  have hbody : (binaryFormulaCode body).length <=
      (binaryFormulaCode body).length := Nat.le_refl _
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
      (valuationContext body.freeVariables valuation) <=
        compactAdditiveNatListListRowsContextCodeResource numericBound := by
    exact compactAdditiveNatListListRowsBranchTerminal_context_le tokenTable
      width tokenCount boundaryTable index numericBound (by omega)
  let compilation := compileExplicitBoundedWitnessDirectPublicWithUniformResource
    (compactAdditiveNatListListRowsContextCodeResource numericBound) tokenCount
    numericBound (binaryFormulaCode body).length htokenCount body values hvalues
    hbody hcontext
    (compactAdditiveNatListListRowsTerminalPayloadResource numericBound bitBound)
    terminal hterminal
  have hcoordinates :
      compilation.formula = explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm tokenCount) 3 body ∧
        compilation.payloadResource =
          explicitBoundedWitnessDirectPublicPayloadEnvelope 3
            (compactAdditiveNatListListRowsContextCodeResource numericBound)
            numericBound (binaryFormulaCode body).length
            (compactAdditiveNatListListRowsTerminalPayloadResource numericBound
              bitBound) := by
    constructor <;> rfl
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm tokenCount) 3 body
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula = Rewriting.free
      (compactAdditiveNatListListRowsBody tokenTable width tokenCount
        boundaryTable) := by
    exact (compactAdditiveNatListListRowsBody_free_alignment tokenTable width
      tokenCount boundaryTable).symm
  let proof := castValuationContextProof hformula rawProof
  refine { proof := proof, payloadLength_le := ?_ }
  dsimp only [proof]
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [compactAdditiveNatListListRowsBranchPayloadResource, body] using
    hcoordinates.2

#print axioms compactAdditiveNatListListRowsTerminalUniformBoundOfData
#print axioms compactAdditiveNatListListRowsDirectUniformBranchBoundOfData

end FoundationCompactNumericListedDirectNatListListRowsDirectBranchUniformBound
