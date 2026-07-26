import integration.FoundationCompactNumericListedDirectSequentFormulaStepFull21FullyFixedResources

/-! # Fully fixed proof of all twenty-one open-index conjuncts -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectSequentFormulaStepFull21FullyFixedBound

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
open FoundationCompactNumericListedDirectSequentFormulaStepTail10FullyFixedBound
open FoundationCompactNumericListedDirectSequentFormulaStepFull21FullyFixedResources

noncomputable def compactSequentFormulaStepTail01FullyFixedResultOfData
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
      (compactSequentFormulaStepTail01FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row)
      (compactSequentFormulaStepTail01FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row) := by
  let valuation := extendValuation rowIndex zeroValuation
  let tail10 :=
    compactSequentFormulaStepDirectTail10AtValuationIndexFullyFixedResultOfData
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound numericBound bitBound data hrowIndex
      htokenCount hsuffixBoundary hvalueBoundary hvalueBound
  let syntaxResource :=
    compactSequentFormulaStepFull21FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound data.row
  rcases data.graph with
    ⟨hcurrentStart, hcurrentFinish, hcurrentCount,
      hnextStart, hnextFinish, hnextCount,
      hvalueStart, hvalueFinish, hvalueCount,
      _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hcurrentStartSize : Nat.size data.row.current.start <= bitBound :=
    (Nat.size_le_size hcurrentStart).trans htokenCount
  have hcurrentFinishSize : Nat.size data.row.current.finish <= bitBound :=
    (Nat.size_le_size hcurrentFinish).trans htokenCount
  have hcurrentCountSize : Nat.size data.row.current.count <= bitBound :=
    (Nat.size_le_size hcurrentCount).trans htokenCount
  have hnextStartSize : Nat.size data.row.next.start <= bitBound :=
    (Nat.size_le_size hnextStart).trans htokenCount
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
    unfold syntaxResource
      compactSequentFormulaStepFull21FullyFixedSyntaxPolynomial
    omega
  have hcontextEnvelope :
      FoundationCompactPAValuationTermCompilerPublicBounds.valuationContextFormulaCodeSumEnvelope
          1 numericBound (binaryTermCode (&0 : ValuationTerm)).length <=
        syntaxResource := by
    unfold syntaxResource
      compactSequentFormulaStepFull21FullyFixedSyntaxPolynomial
      FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound.compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeEnvelope
    omega
  have hcode01 :
      compactSequentFormulaStepTail01FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound
          data.row <= syntaxResource := by
    unfold syntaxResource
      compactSequentFormulaStepFull21FullyFixedSyntaxPolynomial
    omega
  have hcode02 :
      compactSequentFormulaStepTail02FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound
          data.row <= syntaxResource := by
    apply le_trans (b :=
      compactSequentFormulaStepTail01FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row)
    · unfold compactSequentFormulaStepTail01FullyFixedCodePolynomial
      omega
    · exact hcode01
  have hcode03 :
      compactSequentFormulaStepTail03FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound
          data.row <= syntaxResource := by
    apply le_trans (b :=
      compactSequentFormulaStepTail02FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row)
    · unfold compactSequentFormulaStepTail02FullyFixedCodePolynomial
      omega
    · exact hcode02
  have hcode04 :
      compactSequentFormulaStepTail04FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound
          data.row <= syntaxResource := by
    apply le_trans (b :=
      compactSequentFormulaStepTail03FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row)
    · unfold compactSequentFormulaStepTail03FullyFixedCodePolynomial
      omega
    · exact hcode03
  have hcode05 :
      compactSequentFormulaStepTail05FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound
          data.row <= syntaxResource := by
    apply le_trans (b :=
      compactSequentFormulaStepTail04FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row)
    · unfold compactSequentFormulaStepTail04FullyFixedCodePolynomial
      omega
    · exact hcode04
  have hcode06 :
      compactSequentFormulaStepTail06FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound
          data.row <= syntaxResource := by
    apply le_trans (b :=
      compactSequentFormulaStepTail05FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row)
    · unfold compactSequentFormulaStepTail05FullyFixedCodePolynomial
      omega
    · exact hcode05
  have hcode07 :
      compactSequentFormulaStepTail07FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound
          data.row <= syntaxResource := by
    apply le_trans (b :=
      compactSequentFormulaStepTail06FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row)
    · unfold compactSequentFormulaStepTail06FullyFixedCodePolynomial
      omega
    · exact hcode06
  have hcode08 :
      compactSequentFormulaStepTail08FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound
          data.row <= syntaxResource := by
    apply le_trans (b :=
      compactSequentFormulaStepTail07FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row)
    · unfold compactSequentFormulaStepTail07FullyFixedCodePolynomial
      omega
    · exact hcode07
  have hcode09 :
      compactSequentFormulaStepTail09FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound
          data.row <= syntaxResource := by
    apply le_trans (b :=
      compactSequentFormulaStepTail08FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row)
    · unfold compactSequentFormulaStepTail08FullyFixedCodePolynomial
      omega
    · exact hcode08
  let tail09 := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf09.bound tail10 leaf09.codeLength_le leaf09.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode09
  let tail08 := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf08.bound tail09 leaf08.codeLength_le leaf08.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode08
  let tail07 := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf07.bound tail08 leaf07.codeLength_le leaf07.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode07
  let tail06 := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf06.bound tail07 leaf06.codeLength_le leaf06.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode06
  let tail05 := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf05.bound tail06 leaf05.codeLength_le leaf05.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode05
  let tail04 := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf04.bound tail05 leaf04.codeLength_le leaf04.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode04
  let tail03 := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf03.bound tail04 leaf03.codeLength_le leaf03.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode03
  let tail02 := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf02.bound tail03 leaf02.codeLength_le leaf02.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode02
  let tail01 := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaf01.bound tail02 leaf01.codeLength_le leaf01.freeVariables_subset
    hvaluation hpositive hcontextEnvelope hcode01
  simpa only [compactSequentFormulaStepTail01Formula,
    compactSequentFormulaStepTail02Formula,
    compactSequentFormulaStepTail03Formula,
    compactSequentFormulaStepTail04Formula,
    compactSequentFormulaStepTail05Formula,
    compactSequentFormulaStepTail06Formula,
    compactSequentFormulaStepTail07Formula,
    compactSequentFormulaStepTail08Formula,
    compactSequentFormulaStepTail09Formula,
    compactSequentFormulaStepTail01FullyFixedPayloadPolynomial,
    compactSequentFormulaStepTail02FullyFixedPayloadPolynomial,
    compactSequentFormulaStepTail03FullyFixedPayloadPolynomial,
    compactSequentFormulaStepTail04FullyFixedPayloadPolynomial,
    compactSequentFormulaStepTail05FullyFixedPayloadPolynomial,
    compactSequentFormulaStepTail06FullyFixedPayloadPolynomial,
    compactSequentFormulaStepTail07FullyFixedPayloadPolynomial,
    compactSequentFormulaStepTail08FullyFixedPayloadPolynomial,
    compactSequentFormulaStepTail09FullyFixedPayloadPolynomial,
    compactSequentFormulaStepTail01FullyFixedCodePolynomial,
    compactSequentFormulaStepTail02FullyFixedCodePolynomial,
    compactSequentFormulaStepTail03FullyFixedCodePolynomial,
    compactSequentFormulaStepTail04FullyFixedCodePolynomial,
    compactSequentFormulaStepTail05FullyFixedCodePolynomial,
    compactSequentFormulaStepTail06FullyFixedCodePolynomial,
    compactSequentFormulaStepTail07FullyFixedCodePolynomial,
    compactSequentFormulaStepTail08FullyFixedCodePolynomial,
    compactSequentFormulaStepTail09FullyFixedCodePolynomial,
    compactSequentFormulaStepClosedLeFullyFixedCodePolynomial,
    syntaxResource] using tail01

noncomputable def
    compactSequentFormulaStepDirectFormulaAtValuationIndexFullyFixedResultOfData
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
      (compactSequentFormulaStepTail01FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row)
      (compactSequentFormulaStepTail01FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row) := by
  simpa only [compactSequentFormulaStepTail01Formula_eq_directParts,
    compactSequentFormulaStepDirectFormulaAtValuationIndex_alignment] using
    compactSequentFormulaStepTail01FullyFixedResultOfData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound numericBound bitBound data hrowIndex htokenCount
      hsuffixBoundary hvalueBoundary hvalueBound

#print axioms
  compactSequentFormulaStepDirectFormulaAtValuationIndexFullyFixedResultOfData

end FoundationCompactNumericListedDirectSequentFormulaStepFull21FullyFixedBound
