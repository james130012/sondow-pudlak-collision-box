import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataPayloadPolynomial

/-! # Quantifier checked syntax-formula data constructor -/

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

theorem quantifier_case
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : 1 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
    (htag : NativeEqEitherCheckedData witness.tag 6 7)
    (hquantifier : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity)
    (bounds : SyntaxFormulaCheckedDataFixedBounds tokenTable width tokenCount
      current next binderArity numericBound bitBound witness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
          tokenTable width tokenCount current next binderArity witness
          (.quantifier hcount hatTag htag hquantifier)) <=
      syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
  have hcase :=
    syntaxFormulaOuterQuantifierCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      witness hcount hatTag htag hquantifier bounds.width_le
      bounds.tokenCount_le bounds.current_le bounds.next_le
      bounds.tokenTable_size bounds.current_size bounds.next_size
      bounds.tailBoundary_size bounds.binderArity_size
      bounds.relationArity_size bounds.relationCode_size bounds.tag_size
      bounds.numeric_size
  have hdom :
      syntaxFormulaOuterQuantifierFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound <=
        syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound := by
    unfold syntaxFormulaCheckedDataFullyFixedPayloadPolynomial
    exact term7_le _ _ _ _ _ _ _ _
  unfold compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
  simp only [id_eq]
  exact Nat.le_trans hcase hdom

end FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataCasesB
