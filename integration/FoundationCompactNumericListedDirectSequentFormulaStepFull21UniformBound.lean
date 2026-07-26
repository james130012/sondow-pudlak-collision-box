import integration.FoundationCompactNumericListedDirectSequentFormulaStepFull21UniformTail05Bound

/-! # Row-independent proof of all twenty-one open-index conjuncts -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectSequentFormulaStepFull21UniformBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexTerminalAlignment
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepTail10FullyFixedResources
open FoundationCompactNumericListedDirectSequentFormulaStepFull21FullyFixedResources
open FoundationCompactNumericListedDirectSequentFormulaStepFull21UniformResources
open FoundationCompactNumericListedDirectSequentFormulaStepFull21UniformTail05Bound
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound

noncomputable def compactSequentFormulaStepTail01UniformResultOfData
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
      (compactSequentFormulaStepTail01Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail01UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail01UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
  let valuation := extendValuation rowIndex zeroValuation
  let tail05 := compactSequentFormulaStepTail05UniformResultOfData tokenTable
    width tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
    valueBound numericBound bitBound data hrowIndex htokenCount hsuffixBoundary
    hvalueBoundary hvalueBound
  let syntaxResource := compactSequentFormulaStepFull21UniformSyntaxPolynomial
    tokenTable width tokenCount suffixCount valueCount numericBound bitBound
    valueBound
  rcases data.graph with
    ⟨hcurrentStart, hcurrentFinish, hcurrentCount, hnextStart,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hcurrentStartSize : Nat.size data.row.current.start <= bitBound :=
    (Nat.size_le_size hcurrentStart).trans htokenCount
  have hcurrentFinishSize : Nat.size data.row.current.finish <= bitBound :=
    (Nat.size_le_size hcurrentFinish).trans htokenCount
  have hcurrentCountSize : Nat.size data.row.current.count <= bitBound :=
    (Nat.size_le_size hcurrentCount).trans htokenCount
  have hnextStartSize : Nat.size data.row.next.start <= bitBound :=
    (Nat.size_le_size hnextStart).trans htokenCount
  let leaf01 := compactSequentFormulaStepClosedLeFullyFixedResult valuation
    data.row.current.start tokenCount bitBound hcurrentStartSize htokenCount
    hcurrentStart
  let leaf02 := compactSequentFormulaStepClosedLeFullyFixedResult valuation
    data.row.current.finish tokenCount bitBound hcurrentFinishSize htokenCount
    hcurrentFinish
  let leaf03 := compactSequentFormulaStepClosedLeFullyFixedResult valuation
    data.row.current.count tokenCount bitBound hcurrentCountSize htokenCount
    hcurrentCount
  let leaf04 := compactSequentFormulaStepClosedLeFullyFixedResult valuation
    data.row.next.start tokenCount bitBound hnextStartSize htokenCount hnextStart
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
  have hcode04 :
      compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
        compactSequentFormulaStepTail05UniformCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound +
        (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepFull21UniformSyntaxPolynomial
      compactSequentFormulaStepTail01UniformCodePolynomial
      compactSequentFormulaStepTail02UniformCodePolynomial
      compactSequentFormulaStepTail03UniformCodePolynomial
      compactSequentFormulaStepTail04UniformCodePolynomial
    omega
  let tail04Raw := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf04.bound tail05 leaf04.codeLength_le leaf04.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode04
  let tail04 : CompactSequentFormulaStepAtValuationFixedResult valuation
      (compactSequentFormulaStepTail04Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail04UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail04UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
    simpa only [compactSequentFormulaStepTail04Formula,
      compactSequentFormulaStepTail04UniformPayloadPolynomial,
      compactSequentFormulaStepTail04UniformCodePolynomial, syntaxResource]
      using tail04Raw
  have hcode03 :
      compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
        compactSequentFormulaStepTail04UniformCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound +
        (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepFull21UniformSyntaxPolynomial
      compactSequentFormulaStepTail01UniformCodePolynomial
      compactSequentFormulaStepTail02UniformCodePolynomial
      compactSequentFormulaStepTail03UniformCodePolynomial
    omega
  let tail03Raw := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf03.bound tail04 leaf03.codeLength_le leaf03.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode03
  let tail03 : CompactSequentFormulaStepAtValuationFixedResult valuation
      (compactSequentFormulaStepTail03Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail03UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail03UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
    simpa only [compactSequentFormulaStepTail03Formula,
      compactSequentFormulaStepTail03UniformPayloadPolynomial,
      compactSequentFormulaStepTail03UniformCodePolynomial, syntaxResource]
      using tail03Raw
  have hcode02 :
      compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
        compactSequentFormulaStepTail03UniformCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound +
        (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepFull21UniformSyntaxPolynomial
      compactSequentFormulaStepTail01UniformCodePolynomial
      compactSequentFormulaStepTail02UniformCodePolynomial
    omega
  let tail02Raw := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf02.bound tail03 leaf02.codeLength_le leaf02.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode02
  let tail02 : CompactSequentFormulaStepAtValuationFixedResult valuation
      (compactSequentFormulaStepTail02Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail02UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail02UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
    simpa only [compactSequentFormulaStepTail02Formula,
      compactSequentFormulaStepTail02UniformPayloadPolynomial,
      compactSequentFormulaStepTail02UniformCodePolynomial, syntaxResource]
      using tail02Raw
  have hcode01 :
      compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
        compactSequentFormulaStepTail02UniformCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound +
        (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepFull21UniformSyntaxPolynomial
      compactSequentFormulaStepTail01UniformCodePolynomial
    omega
  let tail01Raw := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf01.bound tail02 leaf01.codeLength_le leaf01.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode01
  simpa only [compactSequentFormulaStepTail01Formula,
    compactSequentFormulaStepTail01UniformPayloadPolynomial,
    compactSequentFormulaStepTail01UniformCodePolynomial, syntaxResource]
    using tail01Raw

noncomputable def
    compactSequentFormulaStepDirectFormulaAtValuationIndexUniformResultOfData
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
      (compactSequentFormulaStepDirectFormulaAtValuationIndex tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        (&0 : ValuationTerm) data.row)
      (compactSequentFormulaStepTail01UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail01UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
  simpa only [compactSequentFormulaStepTail01Formula_eq_directParts,
    compactSequentFormulaStepDirectFormulaAtValuationIndex_alignment] using
    compactSequentFormulaStepTail01UniformResultOfData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound numericBound bitBound data hrowIndex htokenCount
      hsuffixBoundary hvalueBoundary hvalueBound

#print axioms
  compactSequentFormulaStepDirectFormulaAtValuationIndexUniformResultOfData

end FoundationCompactNumericListedDirectSequentFormulaStepFull21UniformBound
