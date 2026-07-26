import integration.FoundationCompactNumericListedDirectSequentFormulaStepFull21UniformResources

/-! # Uniform full-conjunction prefix from tail 09 through tail 05 -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectSequentFormulaStepFull21UniformTail05Bound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepTail10FullyFixedResources
open FoundationCompactNumericListedDirectSequentFormulaStepTail10UniformBound
open FoundationCompactNumericListedDirectSequentFormulaStepFull21FullyFixedResources
open FoundationCompactNumericListedDirectSequentFormulaStepFull21UniformResources
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound

noncomputable def compactSequentFormulaStepTail05UniformResultOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound numericBound bitBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound)
    (hrowIndex : rowIndex <= numericBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hsuffixBoundary : Nat.size suffixBoundary <= bitBound)
    (hvalueBoundary : Nat.size valueBoundary <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound) :
    CompactSequentFormulaStepAtValuationFixedResult
      (extendValuation rowIndex zeroValuation)
      (compactSequentFormulaStepTail05Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail05UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail05UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
  let valuation := extendValuation rowIndex zeroValuation
  let tail10 :=
    compactSequentFormulaStepDirectTail10AtValuationIndexUniformResultOfData
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound numericBound bitBound data hrowIndex
      htokenCount hsuffixBoundary hvalueBoundary hvalueBound
  let syntaxResource := compactSequentFormulaStepFull21UniformSyntaxPolynomial
    tokenTable width tokenCount suffixCount valueCount numericBound bitBound
    valueBound
  rcases data.graph with
    ⟨_, _, _, _, hnextFinish, hnextCount,
      hvalueStart, hvalueFinish, hvalueCount,
      _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hnextFinishSize : Nat.size data.row.next.finish <= bitBound :=
    (Nat.size_le_size hnextFinish).trans htokenCount
  have hnextCountSize : Nat.size data.row.next.count <= bitBound :=
    (Nat.size_le_size hnextCount).trans htokenCount
  have hvalueStartSize : Nat.size data.row.value.start <= bitBound :=
    (Nat.size_le_size hvalueStart).trans htokenCount
  have hvalueFinishSize : Nat.size data.row.value.finish <= bitBound :=
    (Nat.size_le_size hvalueFinish).trans htokenCount
  have hvalueCountSize : Nat.size data.row.value.count <= bitBound :=
    (Nat.size_le_size hvalueCount).trans htokenCount
  let leaf05 := compactSequentFormulaStepClosedLeFullyFixedResult valuation
    data.row.next.finish tokenCount bitBound hnextFinishSize htokenCount
    hnextFinish
  let leaf06 := compactSequentFormulaStepClosedLeFullyFixedResult valuation
    data.row.next.count tokenCount bitBound hnextCountSize htokenCount hnextCount
  let leaf07 := compactSequentFormulaStepClosedLeFullyFixedResult valuation
    data.row.value.start tokenCount bitBound hvalueStartSize htokenCount hvalueStart
  let leaf08 := compactSequentFormulaStepClosedLeFullyFixedResult valuation
    data.row.value.finish tokenCount bitBound hvalueFinishSize htokenCount
    hvalueFinish
  let leaf09 := compactSequentFormulaStepClosedLeFullyFixedResult valuation
    data.row.value.count tokenCount bitBound hvalueCountSize htokenCount hvalueCount
  have hvaluation : valuation 0 <= numericBound := by
    simpa only [valuation, extendValuation_zero] using hrowIndex
  have hpositive : 1 <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepFull21UniformSyntaxPolynomial
    omega
  have hcontextEnvelope :
      FoundationCompactPAValuationTermCompilerPublicBounds.valuationContextFormulaCodeSumEnvelope
          1 numericBound (binaryTermCode (&0 : ValuationTerm)).length <=
        syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepFull21UniformSyntaxPolynomial
      compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeEnvelope
    omega
  have hcode09 :
      compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
        compactSequentFormulaStepTail10UniformCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound +
        (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepFull21UniformSyntaxPolynomial
      compactSequentFormulaStepTail01UniformCodePolynomial
      compactSequentFormulaStepTail02UniformCodePolynomial
      compactSequentFormulaStepTail03UniformCodePolynomial
      compactSequentFormulaStepTail04UniformCodePolynomial
      compactSequentFormulaStepTail05UniformCodePolynomial
      compactSequentFormulaStepTail06UniformCodePolynomial
      compactSequentFormulaStepTail07UniformCodePolynomial
      compactSequentFormulaStepTail08UniformCodePolynomial
      compactSequentFormulaStepTail09UniformCodePolynomial
    omega
  let tail09Raw := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf09.bound tail10 leaf09.codeLength_le leaf09.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode09
  let tail09 : CompactSequentFormulaStepAtValuationFixedResult valuation
      (compactSequentFormulaStepTail09Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail09UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail09UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
    simpa only [compactSequentFormulaStepTail09Formula,
      compactSequentFormulaStepTail09UniformPayloadPolynomial,
      compactSequentFormulaStepTail09UniformCodePolynomial, syntaxResource]
      using tail09Raw
  have hcode08 :
      compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
        compactSequentFormulaStepTail09UniformCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound +
        (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepFull21UniformSyntaxPolynomial
      compactSequentFormulaStepTail01UniformCodePolynomial
      compactSequentFormulaStepTail02UniformCodePolynomial
      compactSequentFormulaStepTail03UniformCodePolynomial
      compactSequentFormulaStepTail04UniformCodePolynomial
      compactSequentFormulaStepTail05UniformCodePolynomial
      compactSequentFormulaStepTail06UniformCodePolynomial
      compactSequentFormulaStepTail07UniformCodePolynomial
      compactSequentFormulaStepTail08UniformCodePolynomial
    omega
  let tail08Raw := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf08.bound tail09 leaf08.codeLength_le leaf08.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode08
  let tail08 : CompactSequentFormulaStepAtValuationFixedResult valuation
      (compactSequentFormulaStepTail08Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail08UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail08UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
    simpa only [compactSequentFormulaStepTail08Formula,
      compactSequentFormulaStepTail08UniformPayloadPolynomial,
      compactSequentFormulaStepTail08UniformCodePolynomial, syntaxResource]
      using tail08Raw
  have hcode07 :
      compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
        compactSequentFormulaStepTail08UniformCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound +
        (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepFull21UniformSyntaxPolynomial
      compactSequentFormulaStepTail01UniformCodePolynomial
      compactSequentFormulaStepTail02UniformCodePolynomial
      compactSequentFormulaStepTail03UniformCodePolynomial
      compactSequentFormulaStepTail04UniformCodePolynomial
      compactSequentFormulaStepTail05UniformCodePolynomial
      compactSequentFormulaStepTail06UniformCodePolynomial
      compactSequentFormulaStepTail07UniformCodePolynomial
    omega
  let tail07Raw := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf07.bound tail08 leaf07.codeLength_le leaf07.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode07
  let tail07 : CompactSequentFormulaStepAtValuationFixedResult valuation
      (compactSequentFormulaStepTail07Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail07UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail07UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
    simpa only [compactSequentFormulaStepTail07Formula,
      compactSequentFormulaStepTail07UniformPayloadPolynomial,
      compactSequentFormulaStepTail07UniformCodePolynomial, syntaxResource]
      using tail07Raw
  have hcode06 :
      compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
        compactSequentFormulaStepTail07UniformCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound +
        (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepFull21UniformSyntaxPolynomial
      compactSequentFormulaStepTail01UniformCodePolynomial
      compactSequentFormulaStepTail02UniformCodePolynomial
      compactSequentFormulaStepTail03UniformCodePolynomial
      compactSequentFormulaStepTail04UniformCodePolynomial
      compactSequentFormulaStepTail05UniformCodePolynomial
      compactSequentFormulaStepTail06UniformCodePolynomial
    omega
  let tail06Raw := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf06.bound tail07 leaf06.codeLength_le leaf06.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode06
  let tail06 : CompactSequentFormulaStepAtValuationFixedResult valuation
      (compactSequentFormulaStepTail06Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail06UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail06UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
    simpa only [compactSequentFormulaStepTail06Formula,
      compactSequentFormulaStepTail06UniformPayloadPolynomial,
      compactSequentFormulaStepTail06UniformCodePolynomial, syntaxResource]
      using tail06Raw
  have hcode05 :
      compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
        compactSequentFormulaStepTail06UniformCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound +
        (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepFull21UniformSyntaxPolynomial
      compactSequentFormulaStepTail01UniformCodePolynomial
      compactSequentFormulaStepTail02UniformCodePolynomial
      compactSequentFormulaStepTail03UniformCodePolynomial
      compactSequentFormulaStepTail04UniformCodePolynomial
      compactSequentFormulaStepTail05UniformCodePolynomial
    omega
  let tail05Raw := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf05.bound tail06 leaf05.codeLength_le leaf05.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode05
  simpa only [compactSequentFormulaStepTail05Formula,
    compactSequentFormulaStepTail05UniformPayloadPolynomial,
    compactSequentFormulaStepTail05UniformCodePolynomial, syntaxResource]
    using tail05Raw

#print axioms compactSequentFormulaStepTail05UniformResultOfData

end FoundationCompactNumericListedDirectSequentFormulaStepFull21UniformTail05Bound
