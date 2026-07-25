import integration.FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBounds
import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidFixedBounds

/-! # Term function decisions using the fully fixed function-code certificates -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFunctionDecisionFixedCertificate

open FoundationCompactArithmeticSymbolCode
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataGraph
open FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

noncomputable def compactSyntaxTermTwoValidFixedDecisionCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (hthree : 3 <= current.tokensCount)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (hvalid : ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.argument) :
    CheckedHybridValuationBoundedFormulaCertificate termZeroValuation
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (nativeEqCertificate witness.tag 2 htag)
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeShortLeCertificate 3 current.tokensCount hthree)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 2 witness.functionCode (fixedNumeralTerm 2)
            (by simp) hatFunction)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveArithmeticFuncCodeValidFixedCertificateOfGraph
                witness.argument witness.functionCode hvalid)
              (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current next witness.tailBoundary
                witness.tailCount binderArity witness.argument hfunction))))))

noncomputable def compactSyntaxTermTwoInvalidFixedDecisionCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (hthree : 3 <= current.tokensCount)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (hinvalid : ¬ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    CheckedHybridValuationBoundedFormulaCertificate termZeroValuation
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
  apply CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (nativeEqCertificate witness.tag 2 htag)
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeShortLeCertificate 3 current.tokensCount hthree)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 2 witness.functionCode (fixedNumeralTerm 2)
            (by simp) hatFunction)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveArithmeticFuncCodeInvalidFixedCertificateOfGraph
                witness.argument witness.functionCode hinvalid)
              (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current next witness.tailBoundary
                witness.tailCount hfailure))))))

#print axioms compactSyntaxTermTwoValidFixedDecisionCertificate
#print axioms compactSyntaxTermTwoInvalidFixedDecisionCertificate

end FoundationCompactNumericListedDirectParserSyntaxTermFunctionDecisionFixedCertificate
