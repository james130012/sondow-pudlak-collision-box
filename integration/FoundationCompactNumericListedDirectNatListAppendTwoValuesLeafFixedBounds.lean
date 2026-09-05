import integration.FoundationCompactNumericListedDirectNatListAppendTwoValuesFormulaFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAppendTwoValuesPublicBounds
import integration.FoundationCompactNumericListedDirectNatListAppendOneValueLeafFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueFullyFixedBounds

/-! # Fixed leaf resources for appending two exact values -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 180000

namespace FoundationCompactNumericListedDirectNatListAppendTwoValuesLeafFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListAppendOneValueLeafFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendTwoValues
open FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendTwoValuesFormulaFixedBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValuesPublicBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueFullyFixedBounds

private abbrev appendTwoFixedValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.zeroValuation

def appendTwoEqualityFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (appendTwoExactTermCodePolynomial bitBound)

def appendTwoSliceFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  appendOneSliceFixedPayloadPolynomial numericBound bitBound

def appendTwoExactRowFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactAdditiveNatListAtRowsExactValueFullyFixedPayloadPolynomial
    numericBound (appendTwoRowBitBound bitBound)

theorem appendTwoArithmeticTwoTerm_closed :
    (‘2’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator]

theorem appendTwoAddSuccessorAndShort_code_le
    (left right bitBound : Nat)
    (hleft : Nat.size left <= bitBound)
    (hright : Nat.size right <= bitBound) :
    (binaryTermCode
      (FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.addTerm
        (FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.successorTerm
          (shortBinaryNumeralTerm left))
        (shortBinaryNumeralTerm right))).length <=
      appendTwoExactTermCodePolynomial bitBound := by
  have hraw :=
    appendSourcePrefixAddSuccessorAndShort_code_le left right bitBound hleft
      hright
  have hsame :
      (binaryTermCode
        (FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.addTerm
          (FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.successorTerm
            (shortBinaryNumeralTerm left))
          (shortBinaryNumeralTerm right))).length <=
        appendSourcePrefixCompositeTermCodePolynomial bitBound := by
    simpa only [
      FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.addTerm,
      FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.successorTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.addTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.successorTerm]
      using hraw
  exact hsame.trans (appendSourcePrefixTermCode_le_appendTwoExact bitBound)

theorem appendTwoAddSuccessorAndShort_closed
    (left right : Nat) :
    (FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.addTerm
      (FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.successorTerm
        (shortBinaryNumeralTerm left))
      (shortBinaryNumeralTerm right)).freeVariables = ∅ := by
  simpa only [
    FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.addTerm,
    FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.successorTerm,
    FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.addTerm,
    FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.successorTerm]
    using appendSourcePrefixAddSuccessorAndShort_closed left right

theorem appendTwoAddShortAndTwo_code_le
    (left bitBound : Nat) (hleft : Nat.size left <= bitBound) :
    (binaryTermCode
      (FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.addTerm
        (shortBinaryNumeralTerm left) (‘2’ : ValuationTerm))).length <=
      appendTwoExactTermCodePolynomial bitBound := by
  have hleftCode :=
    binaryNumeralTerm_code_length_le_envelope left bitBound hleft
  have hraw := paAddTerm_code_length_le
    (shortBinaryNumeralTerm left) (‘2’ : ValuationTerm)
  change
    (binaryTermCode
      (paAddTerm (shortBinaryNumeralTerm left)
        (‘2’ : ValuationTerm))).length <=
      appendTwoExactTermCodePolynomial bitBound
  unfold appendTwoExactTermCodePolynomial
    appendSourcePrefixCompositeTermCodePolynomial
  omega

theorem appendTwoAddShortAndTwo_closed (left : Nat) :
    (FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.addTerm
      (shortBinaryNumeralTerm left) (‘2’ : ValuationTerm)).freeVariables =
        ∅ := by
  change
    (paAddTerm (shortBinaryNumeralTerm left)
      (‘2’ : ValuationTerm)).freeVariables = ∅
  rw [← appendSourcePrefixAddTerm_eq_paAddTerm]
  rw [appendSourcePrefixAddTerm_freeVariables,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    appendTwoArithmeticTwoTerm_closed]
  simp

theorem appendTwoEqualityPayloadEnvelope_le_fixed
    (left right : ValuationTerm) (bitBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <=
      appendTwoExactTermCodePolynomial bitBound)
    (hrightCode : (binaryTermCode right).length <=
      appendTwoExactTermCodePolynomial bitBound) :
    appendTwoEqualityPayloadEnvelope left right <=
      appendTwoEqualityFixedPayloadPolynomial bitBound := by
  unfold appendTwoEqualityPayloadEnvelope
    appendTwoEqualityFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    appendTwoFixedValuation Language.Eq.eq left right 0
    (appendTwoExactTermCodePolynomial bitBound) hleftClosed hrightClosed
    hleftCode hrightCode

theorem
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_appendTwoFixed
    (tokenTable width tokenCount boundaryTable count index value numericBound
      bitBound : Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hrows : CompactAdditiveNatListAtRows tokenTable width tokenCount
      boundaryTable count index value)
    (hindexValue :
      termValue
        FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
        indexTerm = index)
    (hvalueValue :
      termValue
        FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
        valueTerm = value)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hvalueClosed : valueTerm.freeVariables = ∅)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hindexSize : Nat.size index <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <=
      appendTwoExactTermCodePolynomial bitBound)
    (hvalueCode : (binaryTermCode valueTerm).length <=
      appendTwoExactTermCodePolynomial bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph
          FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
          tokenTable width tokenCount boundaryTable count index value indexTerm
          valueTerm hindexValue hvalueValue hrows) <=
      appendTwoExactRowFixedPayloadPolynomial numericBound bitBound := by
  have hbit := bitBound_le_appendTwoRowBitBound bitBound
  have hindexCode' : (binaryTermCode indexTerm).length <=
      natListAtRowsExactIndexCodeEnvelope (appendTwoRowBitBound bitBound) := by
    simpa only [natListAtRowsExactIndexCodeEnvelope] using
      appendTwoArbitraryTermCode_le_rowEnvelope indexTerm bitBound hindexCode
  have hvalueCode' : (binaryTermCode valueTerm).length <=
      binaryNumeralTermCodeEnvelope (appendTwoRowBitBound bitBound) :=
    appendTwoArbitraryTermCode_le_rowEnvelope valueTerm bitBound hvalueCode
  unfold appendTwoExactRowFixedPayloadPolynomial
  exact
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount boundaryTable count index value numericBound
      (appendTwoRowBitBound bitBound) indexTerm valueTerm hrows hindexValue
      hvalueValue hindexClosed hvalueClosed hwidthValue htokenCountValue
      hcountValue (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) (hboundarySize.trans hbit)
      (hcountSize.trans hbit) (hindexSize.trans hbit) (hvalueSize.trans hbit)
      hindexCode' hvalueCode'

#print axioms appendTwoAddSuccessorAndShort_code_le
#print axioms appendTwoAddShortAndTwo_code_le
#print axioms appendTwoEqualityPayloadEnvelope_le_fixed
#print axioms
  compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_appendTwoFixed

end FoundationCompactNumericListedDirectNatListAppendTwoValuesLeafFixedBounds
