import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFullyUniformDirectCompiler
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Fixed payload bound for the fully uniform completed binary-Nat status

The five checked leaves are charged to one numeric and one bit-width
coordinate.  Formula-code bounds are read from the already constructed child
proofs, so no large source predicate is unfolded during the final four
conjunction assemblies.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectBinaryNatCompletedStatusFullyUniformDirectFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds

private abbrev completedFixedZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation

private theorem completedFixedBinaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem completedFixedBinaryRelationFormula_freeVariables
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiformula.rel relationSymbol ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiformula.freeVariables_rel] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiformula.freeVariables_rel]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem completedFixedArithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

def compactBinaryNatCompletedStatusFullyUniformDirectAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound bitBound +
    compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound +
    unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound +
    compactNatSizeFixedPayloadPolynomial bitBound +
    completedAreaFixedPayloadPolynomial bitBound +
    4 * (binaryNatCode 4).length + 1

def compactBinaryNatCompletedStatusFullyUniformDirectFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactBinaryNatCompletedStatusFullyUniformDirectAssemblySyntaxPolynomial
      numericBound bitBound
  binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound bitBound +
    compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound +
    unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound +
    compactNatSizeFixedPayloadPolynomial bitBound +
    completedAreaFixedPayloadPolynomial bitBound +
    12 * generalContextAssemblyEnvelope syntaxResource

theorem
    compileCompactBinaryNatCompletedStatusFullyUniformDirect_payloadLength_le_fixed
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount numericBound bitBound : Nat)
    (hcompleted : CompactBinaryNatCompletedStatusValidRows tokenTable width
      tokenCount start finish
        (compactBinaryNatStatusValidityWitnessOf outputStart outputBoundary
          outputBoundarySize outputCount))
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : outputCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hboundaryTableSize : Nat.size outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactBinaryNatCompletedStatusFullyUniformDirect tokenTable width
      tokenCount start finish outputStart outputBoundary outputBoundarySize
      outputCount numericBound bitBound hcompleted htokenCount houtputCount
      hboundaryTableSize hnumericSize).payloadLength <=
      compactBinaryNatCompletedStatusFullyUniformDirectFixedPayloadPolynomial
        numericBound bitBound := by
  let prefixFormula := compactBinaryNatCompletedStatusPrefixClosedFormula
    tokenTable width tokenCount start outputStart
  let layoutData := compactAdditiveStructuredListLayoutDataOfLayout tokenTable
    width tokenCount outputStart outputCount finish outputBoundary
    hcompleted.2.1
  let layoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount outputStart outputCount finish outputBoundary
  let unitFormula := compactAdditiveUnitBoundaryRowsClosedFormula tokenCount
    outputCount outputBoundary
  let sizeFormula := compactNatSizeClosedFormula outputBoundarySize
    outputBoundary
  let areaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
      (!!(shortBinaryNumeralTerm outputCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let sizeAreaFormula := sizeFormula ⋏ areaFormula
  let unitTailFormula := unitFormula ⋏ sizeAreaFormula
  let layoutTailFormula := layoutFormula ⋏ unitTailFormula
  let completedFormula := prefixFormula ⋏ layoutTailFormula
  let prefixCertificate :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount start outputStart hcompleted.1
  let layoutRaw :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
      layoutData.bodyStart numericBound bitBound
      layoutData.bodyStart_le_tokenCount layoutData.header
      layoutData.boundaryFinish_le_tokenCount layoutData.boundaryStartEntry
      layoutData.boundaryFinishEntry layoutData.rows htokenCount houtputCount
      hboundaryTableSize hnumericSize
  have hlayoutContext : (∅ : Finset ValuationFormula) =
      valuationContext layoutFormula.freeVariables completedFixedZeroValuation := by
    rw [show layoutFormula.freeVariables = ∅ by
      simpa only [layoutFormula] using
        compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
          tokenTable width tokenCount outputStart outputCount finish
          outputBoundary]
    simp [valuationContext]
  let layoutProof := CertifiedPAContextProof.castContext hlayoutContext
    layoutRaw
  let unitRaw :=
    compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph
      tokenCount outputCount outputBoundary numericBound bitBound
      hcompleted.2.2.1 htokenCount houtputCount hboundaryTableSize hnumericSize
  have hunitContext : (∅ : Finset ValuationFormula) =
      valuationContext unitFormula.freeVariables completedFixedZeroValuation := by
    rw [show unitFormula.freeVariables = ∅ by
      simpa only [unitFormula] using
        compactAdditiveUnitBoundaryRowsClosedFormula_freeVariables_eq_empty
          tokenCount outputCount outputBoundary]
    simp [valuationContext]
  let unitProof := CertifiedPAContextProof.castContext hunitContext unitRaw
  let sizeCertificate := compactNatSizeExplicitHybridCertificateOfEq
    outputBoundarySize outputBoundary hcompleted.2.2.2.1
  let areaCertificate := completedAreaCertificate tokenCount outputCount
    outputBoundarySize hcompleted.2.2.2.2
  let prefixResource :=
    binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound bitBound
  let layoutResource :=
    compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let unitResource :=
    unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound bitBound
  let sizeResource := compactNatSizeFixedPayloadPolynomial bitBound
  let areaResource := completedAreaFixedPayloadPolynomial bitBound
  let syntaxResource :=
    compactBinaryNatCompletedStatusFullyUniformDirectAssemblySyntaxPolynomial
      numericBound bitBound
  let sizeAreaGeneral := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    sizeResource areaResource
  let unitTailGeneral := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    unitResource sizeAreaGeneral
  let layoutTailGeneral := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    layoutResource unitTailGeneral
  let completedGeneral := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    prefixResource layoutTailGeneral
  have hprefixWitness :=
    compactBinaryNatCompletedStatusPrefix_deterministicWitness tokenTable width
      tokenCount start outputStart hcompleted.1
  have hstartBound : start <= numericBound := by
    exact (Nat.le_of_lt hprefixWitness.2.1.1).trans htokenCount
  have hinnerBound : start + 1 <= numericBound :=
    hprefixWitness.1.trans htokenCount
  have houtputStartToken : outputStart <= tokenCount := by
    have hinnerLt : start + 1 < tokenCount := hprefixWitness.2.2.1
    have houtputEq : outputStart = (start + 1) + 1 :=
      hprefixWitness.2.2.2.1
    omega
  have houtputStartBound : outputStart <= numericBound :=
    houtputStartToken.trans htokenCount
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidthBound).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hstartSize : Nat.size start <= bitBound :=
    (Nat.size_le_size hstartBound).trans hnumericSize
  have hinnerSize : Nat.size (start + 1) <= bitBound :=
    (Nat.size_le_size hinnerBound).trans hnumericSize
  have houtputStartSize : Nat.size outputStart <= bitBound :=
    (Nat.size_le_size houtputStartBound).trans hnumericSize
  have hprefix : prefixCertificate.compile.payloadLength <= prefixResource := by
    exact (compile_payloadLength_le_structuralPayloadBound
      prefixCertificate).trans
        (compactBinaryNatCompletedStatusPrefixExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
          tokenTable width tokenCount start outputStart numericBound bitBound
          hwidthBound hstartBound hinnerBound htokenTableSize hwidthSize
          htokenCountSize hstartSize houtputStartSize hinnerSize hbitPositive
          hcompleted.1)
  have hlayoutRaw : layoutRaw.payloadLength <= layoutResource := by
    exact
      compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le_fixed
        tokenTable width tokenCount outputStart outputCount finish outputBoundary
        layoutData.bodyStart numericBound bitBound
        layoutData.bodyStart_le_tokenCount layoutData.header
        layoutData.boundaryFinish_le_tokenCount layoutData.boundaryStartEntry
        layoutData.boundaryFinishEntry layoutData.rows hwidthBound htokenCount
        houtputCount htokenTableSize hboundaryTableSize hnumericSize
  have hlayout : layoutProof.payloadLength <= layoutResource := by
    dsimp only [layoutProof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hlayoutRaw
  have hunitRaw : unitRaw.payloadLength <= unitResource := by
    exact
      (compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph_payloadLength_le
        tokenCount outputCount outputBoundary numericBound bitBound
        hcompleted.2.2.1 htokenCount houtputCount hboundaryTableSize
        hnumericSize).trans
      (compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource_le_fixed
        tokenCount outputCount outputBoundary numericBound bitBound htokenCount
        houtputCount hboundaryTableSize hnumericSize)
  have hunit : unitProof.payloadLength <= unitResource := by
    dsimp only [unitProof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hunitRaw
  have hsize : sizeCertificate.compile.payloadLength <= sizeResource := by
    exact (compile_payloadLength_le_structuralPayloadBound
      sizeCertificate).trans
      ((compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
        outputBoundarySize outputBoundary hcompleted.2.2.2.1).trans
        (compactNatSizeStructuralPayloadPolynomial_le_fixed outputBoundarySize
          outputBoundary bitBound hcompleted.2.2.2.1 hboundaryTableSize))
  have harea : areaCertificate.compile.payloadLength <= areaResource := by
    exact (compile_payloadLength_le_structuralPayloadBound
      areaCertificate).trans
      ((completedAreaCertificate_structuralPayloadBound_le_public tokenCount
        outputCount outputBoundarySize hcompleted.2.2.2.2).trans
        (completedAreaStructuralPayloadPolynomial_le_fixed tokenCount outputCount
          outputBoundary outputBoundarySize numericBound bitBound
          hcompleted.2.2.2.1 htokenCount houtputCount hboundaryTableSize
          hnumericSize))
  have hprefixClosed : prefixFormula.freeVariables = ∅ := by
    simpa only [prefixFormula] using
      compactBinaryNatCompletedStatusPrefixClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount start outputStart
  have hlayoutClosed : layoutFormula.freeVariables = ∅ := by
    simpa only [layoutFormula] using
      compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount outputStart outputCount finish outputBoundary
  have hunitClosed : unitFormula.freeVariables = ∅ := by
    simpa only [unitFormula] using
      compactAdditiveUnitBoundaryRowsClosedFormula_freeVariables_eq_empty
        tokenCount outputCount outputBoundary
  have hsizeClosed : sizeFormula.freeVariables = ∅ := by
    dsimp only [sizeFormula]
    unfold compactNatSizeClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      apply shortBinaryNumeralTerm_freeVariables_eq_empty
  have hareaClosed : areaFormula.freeVariables = ∅ := by
    let leftTerm := shortBinaryNumeralTerm outputBoundarySize
    let outputTerm := shortBinaryNumeralTerm outputCount
    let oneTerm : ValuationTerm := ‘1’
    let sumTerm : ValuationTerm := ‘!!outputTerm + !!oneTerm’
    let tokenTerm := shortBinaryNumeralTerm tokenCount
    let rightTerm : ValuationTerm := ‘!!sumTerm * !!tokenTerm’
    have hleft : leftTerm.freeVariables = ∅ :=
      shortBinaryNumeralTerm_freeVariables_eq_empty outputBoundarySize
    have houtput : outputTerm.freeVariables = ∅ :=
      shortBinaryNumeralTerm_freeVariables_eq_empty outputCount
    have hone : oneTerm.freeVariables = ∅ := by
      simpa only [oneTerm] using
        completedFixedArithmeticOneTerm_freeVariables_eq_empty
    have hsum : sumTerm.freeVariables = ∅ := by
      change
        (LO.FirstOrder.Semiterm.func Language.Add.add
          ![outputTerm, oneTerm]).freeVariables = ∅
      rw [completedFixedBinaryFunctionTerm_freeVariables, houtput, hone]
      simp
    have htoken : tokenTerm.freeVariables = ∅ :=
      shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
    have hright : rightTerm.freeVariables = ∅ := by
      change
        (LO.FirstOrder.Semiterm.func Language.Mul.mul
          ![sumTerm, tokenTerm]).freeVariables = ∅
      rw [completedFixedBinaryFunctionTerm_freeVariables, hsum, htoken]
      simp
    change
      (LO.FirstOrder.Semiformula.rel Language.Eq.eq ![leftTerm, rightTerm] ⋎
        LO.FirstOrder.Semiformula.rel Language.LT.lt
          ![leftTerm, rightTerm]).freeVariables = ∅
    rw [LO.FirstOrder.Semiformula.freeVariables_or,
      completedFixedBinaryRelationFormula_freeVariables,
      completedFixedBinaryRelationFormula_freeVariables, hleft, hright]
    simp
  have hsizeAreaClosed : sizeAreaFormula.freeVariables = ∅ := by
    dsimp only [sizeAreaFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hsizeClosed, hareaClosed]
    simp
  have hunitTailClosed : unitTailFormula.freeVariables = ∅ := by
    dsimp only [unitTailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hunitClosed,
      hsizeAreaClosed]
    simp
  have hlayoutTailClosed : layoutTailFormula.freeVariables = ∅ := by
    dsimp only [layoutTailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hlayoutClosed,
      hunitTailClosed]
    simp
  have hcompletedClosed : completedFormula.freeVariables = ∅ := by
    dsimp only [completedFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hprefixClosed,
      hlayoutTailClosed]
    simp
  have hprefixCode : (binaryFormulaCode prefixFormula).length <=
      prefixResource := by
    exact
      (FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        prefixCertificate.compile).trans hprefix
  have hlayoutCode : (binaryFormulaCode layoutFormula).length <=
      layoutResource := by
    exact
      (FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        layoutProof).trans hlayout
  have hunitCode : (binaryFormulaCode unitFormula).length <= unitResource := by
    exact
      (FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        unitProof).trans hunit
  have hsizeCode : (binaryFormulaCode sizeFormula).length <= sizeResource := by
    exact
      (FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        sizeCertificate.compile).trans hsize
  have hareaCode : (binaryFormulaCode areaFormula).length <= areaResource := by
    exact
      (FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        areaCertificate.compile).trans harea
  have hsizeAreaCode : (binaryFormulaCode sizeAreaFormula).length <=
      sizeResource + areaResource + (binaryNatCode 4).length := by
    dsimp only [sizeAreaFormula]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hunitTailCode : (binaryFormulaCode unitTailFormula).length <=
      unitResource + sizeResource + areaResource +
        2 * (binaryNatCode 4).length := by
    dsimp only [unitTailFormula]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hlayoutTailCode : (binaryFormulaCode layoutTailFormula).length <=
      layoutResource + unitResource + sizeResource + areaResource +
        3 * (binaryNatCode 4).length := by
    dsimp only [layoutTailFormula]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hcompletedCode : (binaryFormulaCode completedFormula).length <=
      prefixResource + layoutResource + unitResource + sizeResource +
        areaResource + 4 * (binaryNatCode 4).length := by
    dsimp only [completedFormula]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold compactBinaryNatCompletedStatusFullyUniformDirectAssemblySyntaxPolynomial
    exact Nat.le_add_left 1 _
  have hprefixSyntax : (binaryFormulaCode prefixFormula).length <=
      syntaxResource := hprefixCode.trans (by
    dsimp only [syntaxResource, prefixResource]
    unfold compactBinaryNatCompletedStatusFullyUniformDirectAssemblySyntaxPolynomial
    omega)
  have hlayoutSyntax : (binaryFormulaCode layoutFormula).length <=
      syntaxResource := hlayoutCode.trans (by
    dsimp only [syntaxResource, layoutResource]
    unfold compactBinaryNatCompletedStatusFullyUniformDirectAssemblySyntaxPolynomial
    omega)
  have hunitSyntax : (binaryFormulaCode unitFormula).length <= syntaxResource :=
    hunitCode.trans (by
      dsimp only [syntaxResource, unitResource]
      unfold compactBinaryNatCompletedStatusFullyUniformDirectAssemblySyntaxPolynomial
      omega)
  have hsizeSyntax : (binaryFormulaCode sizeFormula).length <= syntaxResource :=
    hsizeCode.trans (by
      dsimp only [syntaxResource, sizeResource]
      unfold compactBinaryNatCompletedStatusFullyUniformDirectAssemblySyntaxPolynomial
      omega)
  have hareaSyntax : (binaryFormulaCode areaFormula).length <= syntaxResource :=
    hareaCode.trans (by
      dsimp only [syntaxResource, areaResource]
      unfold compactBinaryNatCompletedStatusFullyUniformDirectAssemblySyntaxPolynomial
      omega)
  have hsizeAreaSyntax : (binaryFormulaCode sizeAreaFormula).length <=
      syntaxResource := hsizeAreaCode.trans (by
    dsimp only [syntaxResource, sizeResource, areaResource]
    unfold compactBinaryNatCompletedStatusFullyUniformDirectAssemblySyntaxPolynomial
    omega)
  have hunitTailSyntax : (binaryFormulaCode unitTailFormula).length <=
      syntaxResource := hunitTailCode.trans (by
    dsimp only [syntaxResource, unitResource, sizeResource, areaResource]
    unfold compactBinaryNatCompletedStatusFullyUniformDirectAssemblySyntaxPolynomial
    omega)
  have hlayoutTailSyntax : (binaryFormulaCode layoutTailFormula).length <=
      syntaxResource := hlayoutTailCode.trans (by
    dsimp only [syntaxResource, layoutResource, unitResource, sizeResource,
      areaResource]
    unfold compactBinaryNatCompletedStatusFullyUniformDirectAssemblySyntaxPolynomial
    omega)
  have hcompletedSyntax : (binaryFormulaCode completedFormula).length <=
      syntaxResource := hcompletedCode.trans (by
    dsimp only [syntaxResource, prefixResource, layoutResource, unitResource,
      sizeResource, areaResource]
    unfold compactBinaryNatCompletedStatusFullyUniformDirectAssemblySyntaxPolynomial
    omega)
  let sizeArea := compileDirectConjunction sizeCertificate.compile
    areaCertificate.compile
  have hsizeAreaRaw : sizeArea.payloadLength <=
      transparentHybridConjunctionPayloadEnvelope completedFixedZeroValuation
        sizeFormula areaFormula sizeResource areaResource :=
    compileDirectConjunction_payloadLength_le sizeCertificate.compile
      areaCertificate.compile sizeResource areaResource hsize harea
  have hsizeAreaEnvelope :=
    FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedFixedBounds.transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      completedFixedZeroValuation sizeFormula areaFormula sizeResource
      areaResource syntaxResource hpositive hsizeClosed hareaClosed hsizeSyntax
      hareaSyntax hsizeAreaSyntax
  have hsizeArea : sizeArea.payloadLength <= sizeAreaGeneral :=
    hsizeAreaRaw.trans hsizeAreaEnvelope
  let unitTail := compileDirectConjunction unitProof sizeArea
  have hunitTailRaw : unitTail.payloadLength <=
      transparentHybridConjunctionPayloadEnvelope completedFixedZeroValuation
        unitFormula sizeAreaFormula unitResource sizeAreaGeneral :=
    compileDirectConjunction_payloadLength_le unitProof sizeArea unitResource
      sizeAreaGeneral hunit hsizeArea
  have hunitTailEnvelope :=
    FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedFixedBounds.transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      completedFixedZeroValuation unitFormula sizeAreaFormula unitResource
      sizeAreaGeneral syntaxResource hpositive hunitClosed hsizeAreaClosed
      hunitSyntax hsizeAreaSyntax hunitTailSyntax
  have hunitTail : unitTail.payloadLength <= unitTailGeneral :=
    hunitTailRaw.trans hunitTailEnvelope
  let layoutTail := compileDirectConjunction layoutProof unitTail
  have hlayoutTailRaw : layoutTail.payloadLength <=
      transparentHybridConjunctionPayloadEnvelope completedFixedZeroValuation
        layoutFormula unitTailFormula layoutResource unitTailGeneral :=
    compileDirectConjunction_payloadLength_le layoutProof unitTail layoutResource
      unitTailGeneral hlayout hunitTail
  have hlayoutTailEnvelope :=
    FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedFixedBounds.transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      completedFixedZeroValuation layoutFormula unitTailFormula layoutResource
      unitTailGeneral syntaxResource hpositive hlayoutClosed hunitTailClosed
      hlayoutSyntax hunitTailSyntax hlayoutTailSyntax
  have hlayoutTail : layoutTail.payloadLength <= layoutTailGeneral :=
    hlayoutTailRaw.trans hlayoutTailEnvelope
  let completed := compileDirectConjunction prefixCertificate.compile layoutTail
  have hcompletedRaw : completed.payloadLength <=
      transparentHybridConjunctionPayloadEnvelope completedFixedZeroValuation
        prefixFormula layoutTailFormula prefixResource layoutTailGeneral :=
    compileDirectConjunction_payloadLength_le prefixCertificate.compile
      layoutTail prefixResource layoutTailGeneral hprefix hlayoutTail
  have hcompletedEnvelope :=
    FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedFixedBounds.transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      completedFixedZeroValuation prefixFormula layoutTailFormula prefixResource
      layoutTailGeneral syntaxResource hpositive hprefixClosed hlayoutTailClosed
      hprefixSyntax hlayoutTailSyntax hcompletedSyntax
  have hcompletedPayload : completed.payloadLength <= completedGeneral :=
    hcompletedRaw.trans hcompletedEnvelope
  change completed.payloadLength <= _
  have hfinal := hcompletedPayload
  dsimp only [completedGeneral, layoutTailGeneral, unitTailGeneral,
    sizeAreaGeneral, prefixResource, layoutResource, unitResource, sizeResource,
    areaResource, syntaxResource] at hfinal
  unfold hybridConjunctionGeneralPayloadEnvelope at hfinal
  exact hfinal.trans (by
    unfold
      compactBinaryNatCompletedStatusFullyUniformDirectFixedPayloadPolynomial
    dsimp only
    omega)

#print axioms
  compileCompactBinaryNatCompletedStatusFullyUniformDirect_payloadLength_le_fixed

end FoundationCompactNumericListedDirectBinaryNatCompletedStatusFullyUniformDirectFixedBounds
