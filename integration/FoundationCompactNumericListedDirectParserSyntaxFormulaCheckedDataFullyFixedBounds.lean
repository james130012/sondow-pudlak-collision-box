import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataCasesA
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataCasesB
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataCleanCertificate

/-!
# Unified fully fixed bound for clean checked syntax-formula branch data

The eight checked-data constructors are exhausted against independently
compiled concrete bounds.  The binary constructor uses the clean modular
certificate implementation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataFullyFixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataPayloadPolynomial
open FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataCleanCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataCasesA
open FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataCasesB

theorem
    compactUnifiedParserSyntaxFormulaBranchCleanHybridCertificateFromData_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (data : CompactSyntaxFormulaCheckedBranchData tokenTable width tokenCount
      current next binderArity witness)
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
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hrelationAritySize : Nat.size witness.relationArity <= bitBound)
    (hrelationCodeSize : Nat.size witness.relationCode <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxFormulaBranchCleanHybridCertificateFromData
          tokenTable width tokenCount current next binderArity witness data) <=
      syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
  let bounds : SyntaxFormulaCheckedDataFixedBounds tokenTable width tokenCount
      current next binderArity numericBound bitBound witness := {
    width_le := hwidth
    tokenCount_le := htokenCount
    current_le := hcurrentValue
    next_le := hnextValue
    tokenTable_size := htokenTableSize
    current_size := hcurrentSize
    next_size := hnextSize
    tailBoundary_size := htailBoundarySize
    binderArity_size := hbinderAritySize
    relationArity_size := hrelationAritySize
    relationCode_size := hrelationCodeSize
    tag_size := htagSize
    numeric_size := hnumericSize
    bit_positive := hbitPositive
  }
  cases data with
  | empty hcount hfailure =>
      change hybridFormulaStructuralPayloadBound
          (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
            tokenTable width tokenCount current next binderArity witness
            (.empty hcount hfailure)) <= _
      exact empty_case tokenTable width tokenCount current next binderArity
        numericBound bitBound witness hcount hfailure bounds
  | relationShort hcount hatTag htag hshort hfailure =>
      change hybridFormulaStructuralPayloadBound
          (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
            tokenTable width tokenCount current next binderArity witness
            (.relationShort hcount hatTag htag hshort hfailure)) <= _
      exact relationShort_case tokenTable width tokenCount current next
        binderArity numericBound bitBound witness hcount hatTag htag hshort
        hfailure bounds
  | relationValid hcount hatTag htag hthree hatArity hatCode hvalid hfunction =>
      change hybridFormulaStructuralPayloadBound
          (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
            tokenTable width tokenCount current next binderArity witness
            (.relationValid hcount hatTag htag hthree hatArity hatCode hvalid
              hfunction)) <= _
      exact relationValid_case tokenTable width tokenCount current next
        binderArity numericBound bitBound witness hcount hatTag htag hthree
        hatArity hatCode hvalid hfunction bounds
  | relationInvalid hcount hatTag htag hthree hatArity hatCode hinvalid
      hfailure =>
      change hybridFormulaStructuralPayloadBound
          (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
            tokenTable width tokenCount current next binderArity witness
            (.relationInvalid hcount hatTag htag hthree hatArity hatCode hinvalid
              hfailure)) <= _
      exact relationInvalid_case tokenTable width tokenCount current next
        binderArity numericBound bitBound witness hcount hatTag htag hthree
        hatArity hatCode hinvalid hfailure bounds
  | logical hcount hatTag htag hcontinue =>
      change hybridFormulaStructuralPayloadBound
          (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
            tokenTable width tokenCount current next binderArity witness
            (.logical hcount hatTag htag hcontinue)) <= _
      exact logical_case tokenTable width tokenCount current next
        binderArity numericBound bitBound witness hcount hatTag htag hcontinue
        bounds
  | binary hcount hatTag htag hbinary =>
      exact binary_case tokenTable width tokenCount current next
        binderArity numericBound bitBound witness hcount hatTag htag hbinary
        bounds
  | quantifier hcount hatTag htag hquantifier =>
      change hybridFormulaStructuralPayloadBound
          (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
            tokenTable width tokenCount current next binderArity witness
            (.quantifier hcount hatTag htag hquantifier)) <= _
      exact quantifier_case tokenTable width tokenCount current next
        binderArity numericBound bitBound witness hcount hatTag htag hquantifier
        bounds
  | invalidTag hcount hatTag htag0 htag1 htag2 htag3 htag4 htag5 htag6 htag7
      hfailure =>
      change hybridFormulaStructuralPayloadBound
          (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
            tokenTable width tokenCount current next binderArity witness
            (.invalidTag hcount hatTag htag0 htag1 htag2 htag3 htag4 htag5
              htag6 htag7 hfailure)) <= _
      exact invalidTag_case tokenTable width tokenCount current next
        binderArity numericBound bitBound witness hcount hatTag htag0 htag1 htag2
        htag3 htag4 htag5 htag6 htag7 hfailure bounds

end FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataFullyFixedBounds
