import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataPayloadPolynomial

/-! # Invalid-tag checked syntax-formula data constructor -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataCasesB

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaOuterConcreteBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataPayloadPolynomial
open FoundationCompactNumericListedDirectNatListAtRows

theorem invalidTag_case
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : 1 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
    (htag0 : witness.tag ≠ 0)
    (htag1 : witness.tag ≠ 1)
    (htag2 : witness.tag ≠ 2)
    (htag3 : witness.tag ≠ 3)
    (htag4 : witness.tag ≠ 4)
    (htag5 : witness.tag ≠ 5)
    (htag6 : witness.tag ≠ 6)
    (htag7 : witness.tag ≠ 7)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
    (bounds : SyntaxFormulaCheckedDataFixedBounds tokenTable width tokenCount
      current next binderArity numericBound bitBound witness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
          tokenTable width tokenCount current next binderArity witness
          (.invalidTag hcount hatTag htag0 htag1 htag2 htag3 htag4 htag5 htag6
            htag7 hfailure)) <=
      syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
  have hcase :=
    syntaxFormulaOuterInvalidTagCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      witness hcount hatTag htag0 htag1 htag2 htag3 htag4 htag5 htag6 htag7
      hfailure bounds.width_le bounds.tokenCount_le bounds.current_le
      bounds.next_le bounds.tokenTable_size bounds.current_size bounds.next_size
      bounds.tailBoundary_size bounds.binderArity_size
      bounds.relationArity_size bounds.relationCode_size bounds.tag_size
      bounds.numeric_size
  have hdom :
      syntaxFormulaOuterInvalidTagFullyFixedPayloadPolynomial numericBound
          bitBound <=
        syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound := by
    unfold syntaxFormulaCheckedDataFullyFixedPayloadPolynomial
    exact term8_le _ _ _ _ _ _ _ _
  unfold compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
  simp only [id_eq]
  exact Nat.le_trans hcase hdom

end FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataCasesB
