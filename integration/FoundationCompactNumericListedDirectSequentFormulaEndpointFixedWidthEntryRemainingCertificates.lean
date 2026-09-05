import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryCertificateBound
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds

/-! # Cached endpoint entry certificates at the remaining three indices -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingCertificates

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryCertificateBound

theorem endpointOneTerm_value :
    termValue endpointEntryZeroValuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one endpointEntryZeroValuation ![]

theorem endpointOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

theorem endpointShortNumeralTerm_value (index : Nat) :
    termValue endpointEntryZeroValuation (shortBinaryNumeralTerm index) =
      index :=
  termValue_shortBinaryNumeralTerm endpointEntryZeroValuation index

def endpointSuccessorIndexTerm (index : Nat) : ValuationTerm :=
  ‘!!(shortBinaryNumeralTerm index) + 1’

private theorem endpointTermValue_add (left right : ValuationTerm) :
    termValue endpointEntryZeroValuation ‘!!left + !!right’ =
      termValue endpointEntryZeroValuation left +
        termValue endpointEntryZeroValuation right := by
  change termValue endpointEntryZeroValuation
      (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]) = _
  exact termValue_add endpointEntryZeroValuation ![left, right]

theorem endpointSuccessorIndexTerm_value (index : Nat) :
    termValue endpointEntryZeroValuation (endpointSuccessorIndexTerm index) =
      index + 1 := by
  unfold endpointSuccessorIndexTerm
  rw [endpointTermValue_add, termValue_shortBinaryNumeralTerm]
  exact congrArg (index + ·) endpointOneTerm_value

theorem endpointSuccessorIndexTerm_freeVariables_eq_empty (index : Nat) :
    (endpointSuccessorIndexTerm index).freeVariables = ∅ := by
  unfold endpointSuccessorIndexTerm
  rw [arithmeticAddTerm_freeVariables_eq_union,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    endpointOneTerm_freeVariables_eq_empty]
  simp

opaque sequentFormulaEndpointFixedWidthEntryOneBoundedCertificate
    (table width value : Nat)
    (hentry : CompactFixedWidthEntry table width 1 value) :
    SequentFormulaEndpointFixedWidthEntryBoundedCertificate
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        (‘1’ : ValuationTerm) (shortBinaryNumeralTerm value))
      (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial table width value
        (‘1’ : ValuationTerm)) := by
  exact buildSequentFormulaEndpointFixedWidthEntryBoundedCertificate table
    width 1 value (‘1’ : ValuationTerm) endpointOneTerm_value
    endpointOneTerm_freeVariables_eq_empty hentry

opaque sequentFormulaEndpointFixedWidthEntryNumeralBoundedCertificate
    (table width index value : Nat)
    (hentry : CompactFixedWidthEntry table width index value) :
    SequentFormulaEndpointFixedWidthEntryBoundedCertificate
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm index) (shortBinaryNumeralTerm value))
      (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial table width value
        (shortBinaryNumeralTerm index)) := by
  exact buildSequentFormulaEndpointFixedWidthEntryBoundedCertificate table
    width index value (shortBinaryNumeralTerm index)
    (endpointShortNumeralTerm_value index)
    (shortBinaryNumeralTerm_freeVariables_eq_empty index) hentry

opaque sequentFormulaEndpointFixedWidthEntrySuccessorBoundedCertificate
    (table width index value : Nat)
    (hentry : CompactFixedWidthEntry table width (index + 1) value) :
    SequentFormulaEndpointFixedWidthEntryBoundedCertificate
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        (endpointSuccessorIndexTerm index) (shortBinaryNumeralTerm value))
      (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial table width value
        (endpointSuccessorIndexTerm index)) := by
  exact buildSequentFormulaEndpointFixedWidthEntryBoundedCertificate table
    width (index + 1) value (endpointSuccessorIndexTerm index)
    (endpointSuccessorIndexTerm_value index)
    (endpointSuccessorIndexTerm_freeVariables_eq_empty index) hentry

#print axioms sequentFormulaEndpointFixedWidthEntryOneBoundedCertificate
#print axioms sequentFormulaEndpointFixedWidthEntryNumeralBoundedCertificate
#print axioms sequentFormulaEndpointFixedWidthEntrySuccessorBoundedCertificate

end FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingCertificates
