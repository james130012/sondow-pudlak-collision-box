import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataPayloadPolynomial

/-!
# Clean checked-data certificate for the syntax-formula parser

The binary constructor uses the modular certificate whose quantitative bound
is fully fixed.  The other constructors retain the original checked-data
implementation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataCleanCertificate

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryModularFullyFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate

noncomputable def
    compactUnifiedParserSyntaxFormulaBranchCleanHybridCertificateFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (data : CompactSyntaxFormulaCheckedBranchData tokenTable width tokenCount
      current next binderArity witness) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.zeroValuation
      (compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  cases data with
  | binary hcount hatTag htag hbinary =>
      let tagCertificate :=
        compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0) (by simp)
          hatTag
      let binaryCertificate :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 4 5 htag)
          (compactUnifiedParserSyntaxFormulaBinaryModularCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount binderArity hbinary)
      let tagBranchCertificate :
          CheckedHybridValuationBoundedFormulaCertificate
            FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.zeroValuation
            (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
              width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              binaryCertificate))
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeShortLeCertificate 1 current.tokensCount hcount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            tagCertificate tagBranchCertificate))
  | empty hcount hfailure =>
      exact compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        tokenTable width tokenCount current next binderArity witness
        (.empty hcount hfailure)
  | relationShort hcount hatTag htag hshort hfailure =>
      exact compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        tokenTable width tokenCount current next binderArity witness
        (.relationShort hcount hatTag htag hshort hfailure)
  | relationValid hcount hatTag htag hthree hatArity hatCode hvalid hfunction =>
      exact compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        tokenTable width tokenCount current next binderArity witness
        (.relationValid hcount hatTag htag hthree hatArity hatCode hvalid
          hfunction)
  | relationInvalid hcount hatTag htag hthree hatArity hatCode hinvalid
      hfailure =>
      exact compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        tokenTable width tokenCount current next binderArity witness
        (.relationInvalid hcount hatTag htag hthree hatArity hatCode hinvalid
          hfailure)
  | logical hcount hatTag htag hcontinue =>
      exact compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        tokenTable width tokenCount current next binderArity witness
        (.logical hcount hatTag htag hcontinue)
  | quantifier hcount hatTag htag hquantifier =>
      exact compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        tokenTable width tokenCount current next binderArity witness
        (.quantifier hcount hatTag htag hquantifier)
  | invalidTag hcount hatTag htag0 htag1 htag2 htag3 htag4 htag5 htag6 htag7
      hfailure =>
      exact compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        tokenTable width tokenCount current next binderArity witness
        (.invalidTag hcount hatTag htag0 htag1 htag2 htag3 htag4 htag5 htag6
          htag7 hfailure)

end FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataCleanCertificate
