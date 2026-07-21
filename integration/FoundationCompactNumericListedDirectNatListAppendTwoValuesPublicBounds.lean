import integration.FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectTokenSlicePublicBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resources for appending two natural-list values

The public envelope charges both arithmetic equalities, the copied source
slice, and the two concrete value-term row lookups.  No certificate payload
resource is supplied by the caller.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListAppendTwoValuesPublicBounds

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListAppendTwoValues
open FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsPublicBounds

private abbrev appendTwoZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.zeroValuation

def appendTwoEqualityPayloadEnvelope
    (left right : ValuationTerm) : Nat :=
  compilePositiveRelationPayloadResource appendTwoZeroValuation
    Language.Eq.eq ![left, right]

theorem valuationEqCertificate_structuralPayloadBound_le_transparent
    (left right : ValuationTerm)
    (hequality : termValue appendTwoZeroValuation left =
      termValue appendTwoZeroValuation right) :
    hybridFormulaStructuralPayloadBound
        (valuationEqCertificate left right hequality) <=
      appendTwoEqualityPayloadEnvelope left right := by
  simp only [valuationEqCertificate, hybridFormulaStructuralPayloadBound,
    appendTwoEqualityPayloadEnvelope]
  exact le_rfl

noncomputable def
    compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second : Nat)
    (firstTerm secondTerm : ValuationTerm)
    (hgraph : CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount first second) : Nat :=
  let sliceCount := Classical.choose hgraph.2.2.1
  let finishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetFinish) =
      !!(addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm targetCount))”
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(addTerm (shortBinaryNumeralTerm sourceCount)
        (‘2’ : ValuationTerm))”
  let sliceFormula := compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (successorTerm (shortBinaryNumeralTerm sourceStart))
    (shortBinaryNumeralTerm sourceFinish)
    (successorTerm (shortBinaryNumeralTerm targetStart))
    (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
      (shortBinaryNumeralTerm sourceCount))
  let firstFormula := compactAdditiveNatListAtRowsAtValuationIndexValueFormula
    tokenTable width tokenCount targetBoundary targetCount
    (shortBinaryNumeralTerm sourceCount) firstTerm
  let secondFormula := compactAdditiveNatListAtRowsAtValuationIndexValueFormula
    tokenTable width tokenCount targetBoundary targetCount
    (successorTerm (shortBinaryNumeralTerm sourceCount)) secondTerm
  let finishResource := appendTwoEqualityPayloadEnvelope
    (shortBinaryNumeralTerm targetFinish)
    (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
      (shortBinaryNumeralTerm targetCount))
  let countResource := appendTwoEqualityPayloadEnvelope
    (shortBinaryNumeralTerm targetCount)
    (addTerm (shortBinaryNumeralTerm sourceCount) (‘2’ : ValuationTerm))
  let sliceResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope
      appendTwoZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm sourceFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm sourceCount)) sliceCount
  let firstResource :=
    compactAdditiveNatListAtRowsAtValuationIndexValueGraphPayloadEnvelope
      tokenTable width tokenCount targetBoundary targetCount sourceCount first
      (shortBinaryNumeralTerm sourceCount) firstTerm hgraph.2.2.2.1
  let secondResource :=
    compactAdditiveNatListAtRowsAtValuationIndexValueGraphPayloadEnvelope
      tokenTable width tokenCount targetBoundary targetCount (sourceCount + 1)
      second (successorTerm (shortBinaryNumeralTerm sourceCount)) secondTerm
      hgraph.2.2.2.2
  let rowsResource := transparentHybridConjunctionPayloadEnvelope
    appendTwoZeroValuation firstFormula secondFormula firstResource secondResource
  let sliceRowsResource := transparentHybridConjunctionPayloadEnvelope
    appendTwoZeroValuation sliceFormula (firstFormula ⋏ secondFormula)
    sliceResource rowsResource
  let countTailResource := transparentHybridConjunctionPayloadEnvelope
    appendTwoZeroValuation countFormula
    (sliceFormula ⋏ (firstFormula ⋏ secondFormula)) countResource
    sliceRowsResource
  transparentHybridConjunctionPayloadEnvelope appendTwoZeroValuation
    finishFormula
    (countFormula ⋏ (sliceFormula ⋏ (firstFormula ⋏ secondFormula)))
    finishResource countTailResource

theorem
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second : Nat)
    (firstTerm secondTerm : ValuationTerm)
    (hfirstClosed : firstTerm.freeVariables = ∅)
    (hsecondClosed : secondTerm.freeVariables = ∅)
    (hfirstValue : termValue appendTwoZeroValuation firstTerm = first)
    (hsecondValue : termValue appendTwoZeroValuation secondTerm = second)
    (hgraph : CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount first second) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceStart sourceFinish sourceCount
          targetStart targetFinish targetBoundary targetCount first second
          firstTerm secondTerm hfirstValue hsecondValue hgraph) <=
      compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount first second
        firstTerm secondTerm hgraph := by
  rcases hgraph with ⟨hfinish, hcount, hslice, hfirst, hsecond⟩
  let sliceCount := Classical.choose hslice
  have hsliceSpec :
      sliceCount <= tokenCount ∧
      sourceFinish = sourceStart + 1 + sliceCount ∧
      targetStart + 1 + sourceCount = targetStart + 1 + sliceCount ∧
      sourceFinish <= tokenCount ∧
      targetStart + 1 + sourceCount <= tokenCount ∧
      ∀ offset < sliceCount, ∀ bitIndex < width,
        tokenTable.testBit ((sourceStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + offset) * width + bitIndex) := by
    simpa [sliceCount, Nat.add_assoc] using Classical.choose_spec hslice
  have hsliceCountBound : sliceCount <= termValue appendTwoZeroValuation
      (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.1
  have hsourceEndpoint : termValue appendTwoZeroValuation
      (shortBinaryNumeralTerm sourceFinish) =
        termValue appendTwoZeroValuation
          (successorTerm (shortBinaryNumeralTerm sourceStart)) + sliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.1
  have htargetEndpoint : termValue appendTwoZeroValuation
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm sourceCount)) =
        termValue appendTwoZeroValuation
          (successorTerm (shortBinaryNumeralTerm targetStart)) + sliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.1
  have hsourceFinishBound : termValue appendTwoZeroValuation
      (shortBinaryNumeralTerm sourceFinish) <=
        termValue appendTwoZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.2.1
  have htargetFinishBound : termValue appendTwoZeroValuation
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm sourceCount)) <=
        termValue appendTwoZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.2.2.1
  have hbits : ∀ offset < sliceCount,
      ∀ bitIndex < termValue appendTwoZeroValuation
        (shortBinaryNumeralTerm width),
        (termValue appendTwoZeroValuation
          (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue appendTwoZeroValuation
                (successorTerm (shortBinaryNumeralTerm sourceStart)) + offset) *
              termValue appendTwoZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) =
          (termValue appendTwoZeroValuation
            (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue appendTwoZeroValuation
                (successorTerm (shortBinaryNumeralTerm targetStart)) + offset) *
              termValue appendTwoZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) := by
    intro offset hoffset bitIndex hbitIndex
    have hbitIndex' : bitIndex < width := by
      simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
    simpa [termValue_shortBinaryNumeralTerm] using
      hsliceSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex'
  have hfirstIndexClosed :
      (shortBinaryNumeralTerm sourceCount).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecondIndexClosed :
      (successorTerm (shortBinaryNumeralTerm sourceCount)).freeVariables ⊆
        {0} := by
    simpa [successorTerm, natListAtSuccessorTermAtValuationIndex] using
      natListAtSuccessorTermAtValuationIndex_freeVariables_subset
        (shortBinaryNumeralTerm sourceCount) hfirstIndexClosed
  have hfirstIndexValue : termValue
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
      (shortBinaryNumeralTerm sourceCount) = sourceCount := by
    simp [termValue_shortBinaryNumeralTerm]
  have hsecondIndexValue : termValue
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
      (successorTerm (shortBinaryNumeralTerm sourceCount)) = sourceCount + 1 := by
    simp [termValue_shortBinaryNumeralTerm]
  have hfirstValue' : termValue
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
      firstTerm = first := by
    change termValue (fun _ => 0) firstTerm = first
    change termValue (fun _ => 0) firstTerm = first at hfirstValue
    exact hfirstValue
  have hsecondValue' : termValue
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
      secondTerm = second := by
    change termValue (fun _ => 0) secondTerm = second
    change termValue (fun _ => 0) secondTerm = second at hsecondValue
    exact hsecondValue
  let sliceCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      appendTwoZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm sourceFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm sourceCount)) sliceCount hsliceCountBound
      hsourceEndpoint htargetEndpoint hsourceFinishBound htargetFinishBound hbits
  let firstCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
      tokenTable width tokenCount targetBoundary
      targetCount sourceCount first (shortBinaryNumeralTerm sourceCount)
      firstTerm hfirstIndexValue hfirstValue' hfirst
  let secondCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
      tokenTable width tokenCount targetBoundary
      targetCount (sourceCount + 1) second
      (successorTerm (shortBinaryNumeralTerm sourceCount)) secondTerm
      hsecondIndexValue hsecondValue' hsecond
  have hfinishValue : termValue appendTwoZeroValuation
      (shortBinaryNumeralTerm targetFinish) =
        termValue appendTwoZeroValuation
          (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
            (shortBinaryNumeralTerm targetCount)) := by
    simpa [termValue_shortBinaryNumeralTerm] using hfinish
  have hcountValue : termValue appendTwoZeroValuation
      (shortBinaryNumeralTerm targetCount) =
        termValue appendTwoZeroValuation
          (addTerm (shortBinaryNumeralTerm sourceCount)
            (‘2’ : ValuationTerm)) := by
    simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticTwo] using hcount
  let finishCertificate := valuationEqCertificate
    (shortBinaryNumeralTerm targetFinish)
    (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
      (shortBinaryNumeralTerm targetCount)) hfinishValue
  let countCertificate := valuationEqCertificate
    (shortBinaryNumeralTerm targetCount)
    (addTerm (shortBinaryNumeralTerm sourceCount) (‘2’ : ValuationTerm))
    hcountValue
  have hsliceResource :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
      appendTwoZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm sourceFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm sourceCount)) sliceCount hsliceCountBound
      hsourceEndpoint htargetEndpoint hsourceFinishBound htargetFinishBound hbits
  have hfirstResourceRaw :=
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount targetBoundary targetCount sourceCount first
      (shortBinaryNumeralTerm sourceCount) firstTerm hfirstIndexClosed
      hfirstClosed hfirstIndexValue hfirstValue' hfirst
  have hsecondResourceRaw :=
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount targetBoundary targetCount (sourceCount + 1)
      second (successorTerm (shortBinaryNumeralTerm sourceCount)) secondTerm
      hsecondIndexClosed hsecondClosed hsecondIndexValue hsecondValue' hsecond
  have hfirstResource : hybridFormulaStructuralPayloadBound firstCertificate <=
      compactAdditiveNatListAtRowsAtValuationIndexValueGraphPayloadEnvelope
        tokenTable width tokenCount targetBoundary targetCount sourceCount first
        (shortBinaryNumeralTerm sourceCount) firstTerm hfirst := by
    simpa only [firstCertificate] using hfirstResourceRaw
  have hsecondResource : hybridFormulaStructuralPayloadBound secondCertificate <=
      compactAdditiveNatListAtRowsAtValuationIndexValueGraphPayloadEnvelope
        tokenTable width tokenCount targetBoundary targetCount (sourceCount + 1)
        second (successorTerm (shortBinaryNumeralTerm sourceCount)) secondTerm
        hsecond := by
    simpa only [secondCertificate] using hsecondResourceRaw
  have hfinishResource :=
    valuationEqCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm targetFinish)
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm targetCount)) hfinishValue
  have hcountResource :=
    valuationEqCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm targetCount)
      (addTerm (shortBinaryNumeralTerm sourceCount) (‘2’ : ValuationTerm))
      hcountValue
  let rows := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    firstCertificate secondCertificate
  have hrowsResource := transparentHybridConjunctionPayloadBound_le
    firstCertificate secondCertificate _ _ hfirstResource hsecondResource
  let sliceRows := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    sliceCertificate rows
  have hsliceRows := transparentHybridConjunctionPayloadBound_le
    sliceCertificate rows _ _ hsliceResource hrowsResource
  let countTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    countCertificate sliceRows
  have hcountTail := transparentHybridConjunctionPayloadBound_le
    countCertificate sliceRows _ _ hcountResource hsliceRows
  let direct := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    finishCertificate countTail
  have hdirect := transparentHybridConjunctionPayloadBound_le
    finishCertificate countTail _ _ hfinishResource hcountTail
  unfold
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
  simp only [hybridFormulaStructuralPayloadBound]
  change hybridFormulaStructuralPayloadBound direct <= _
  dsimp only [appendTwoZeroValuation,
    FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation,
    FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.zeroValuation]
    at hdirect ⊢
  simpa only [
    compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope,
    sliceCount] using hdirect

#print axioms valuationEqCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent

end FoundationCompactNumericListedDirectNatListAppendTwoValuesPublicBounds
