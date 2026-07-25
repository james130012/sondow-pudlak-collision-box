import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate

/-! Checked certificate for the invalid long relation branch. -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaRelationLongCertificates

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactArithmeticSymbolCode
open FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate

noncomputable def syntaxFormulaRelationInvalidBodyCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hthree : 3 <= current.tokensCount)
    (hatArity : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 1 witness.relationArity)
    (hatCode : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.relationCode)
    (hinvalid : ¬ ArithmeticRelCodeValid witness.relationArity
      witness.relationCode)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    CheckedHybridValuationBoundedFormulaCertificate (fun _ => 0)
      (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable
        width tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
  exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeShortLeCertificate 3 current.tokensCount hthree)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 1 witness.relationArity (fixedNumeralTerm 1)
          (by simp) hatArity)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 2 witness.relationCode (fixedNumeralTerm 2)
            (by simp) hatCode)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph
                witness.relationArity witness.relationCode hinvalid)
              (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current next witness.tailBoundary
                witness.tailCount hfailure))))))

#print axioms syntaxFormulaRelationInvalidBodyCertificate

end FoundationCompactNumericListedDirectParserSyntaxFormulaRelationLongCertificates
