import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataPayloadPolynomial

/-! # First four checked syntax-formula data constructors -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataCasesA

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaOuterCertificateGeneralBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaOuterConcreteBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataPayloadPolynomial
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactArithmeticSymbolCode

theorem empty_case
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : current.tokensCount = 0)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
    (bounds : SyntaxFormulaCheckedDataFixedBounds tokenTable width tokenCount
      current next binderArity numericBound bitBound witness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
          tokenTable width tokenCount current next binderArity witness
          (.empty hcount hfailure)) <=
      syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
  have htailCount : witness.tailCount <= numericBound := by
    have htasks := hfailure.2.2
    unfold CompactAdditiveSyntaxTaskListSameRows at htasks
    have hnextTasksCount : next.tasksCount <= numericBound := by
      simpa [compactUnifiedParserStateCoordinateValues] using
        bounds.next_le (7 : Fin 8)
    omega
  have htailCountSize : Nat.size witness.tailCount <= bitBound :=
    (Nat.size_le_size htailCount).trans bounds.numeric_size
  have hcase :=
    syntaxFormulaOuterEmptyCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      witness hcount hfailure bounds.width_le bounds.tokenCount_le
      bounds.current_le bounds.next_le bounds.tokenTable_size bounds.width_size
      bounds.tokenCount_size bounds.current_size bounds.next_size
      bounds.tailBoundary_size htailCountSize bounds.binderArity_size
      bounds.relationArity_size bounds.relationCode_size bounds.tag_size
      bounds.numeric_size bounds.bit_positive
  have hdom :
      syntaxFormulaOuterEmptyFullyFixedPayloadPolynomial numericBound bitBound <=
        syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound := by
    unfold syntaxFormulaCheckedDataFullyFixedPayloadPolynomial
    exact term1_le _ _ _ _ _ _ _ _
  unfold compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
  simp only [id_eq]
  exact Nat.le_trans hcase hdom

theorem relationShort_case
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : 1 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
    (htag : NativeEqEitherCheckedData witness.tag 0 1)
    (hshort : current.tokensCount <= 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
    (bounds : SyntaxFormulaCheckedDataFixedBounds tokenTable width tokenCount
      current next binderArity numericBound bitBound witness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
          tokenTable width tokenCount current next binderArity witness
          (.relationShort hcount hatTag htag hshort hfailure)) <=
      syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
  have hcase :=
    syntaxFormulaOuterRelationShortCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      witness hcount hatTag htag hshort hfailure bounds.width_le
      bounds.tokenCount_le bounds.current_le bounds.next_le
      bounds.tokenTable_size bounds.current_size bounds.next_size
      bounds.tailBoundary_size bounds.binderArity_size
      bounds.relationArity_size bounds.relationCode_size bounds.tag_size
      bounds.numeric_size
  have hdom :
      syntaxFormulaOuterRelationShortFullyFixedPayloadPolynomial numericBound
          bitBound <=
        syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound := by
    unfold syntaxFormulaCheckedDataFullyFixedPayloadPolynomial
    exact term2_le _ _ _ _ _ _ _ _
  unfold compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
  simp only [id_eq]
  exact Nat.le_trans hcase hdom

theorem relationValid_case
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : 1 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
    (htag : NativeEqEitherCheckedData witness.tag 0 1)
    (hthree : 3 <= current.tokensCount)
    (hatArity : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 1 witness.relationArity)
    (hatCode : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.relationCode)
    (hvalid : ArithmeticRelCodeValid witness.relationArity
      witness.relationCode)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.relationArity)
    (bounds : SyntaxFormulaCheckedDataFixedBounds tokenTable width tokenCount
      current next binderArity numericBound bitBound witness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
          tokenTable width tokenCount current next binderArity witness
          (.relationValid hcount hatTag htag hthree hatArity hatCode hvalid
            hfunction)) <=
      syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
  have hcase :=
    syntaxFormulaOuterRelationValidCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      witness hcount hatTag htag hthree hatArity hatCode hvalid hfunction
      bounds.width_le bounds.tokenCount_le bounds.current_le bounds.next_le
      bounds.tokenTable_size bounds.current_size bounds.next_size
      bounds.tailBoundary_size bounds.binderArity_size
      bounds.relationArity_size bounds.relationCode_size bounds.tag_size
      bounds.numeric_size
  have hdom :
      syntaxFormulaOuterRelationValidFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound <=
        syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound := by
    unfold syntaxFormulaCheckedDataFullyFixedPayloadPolynomial
    exact term3_le _ _ _ _ _ _ _ _
  unfold compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
  simp only [id_eq]
  exact Nat.le_trans hcase hdom

theorem relationInvalid_case
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : 1 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
    (htag : NativeEqEitherCheckedData witness.tag 0 1)
    (hthree : 3 <= current.tokensCount)
    (hatArity : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 1 witness.relationArity)
    (hatCode : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.relationCode)
    (hinvalid : ¬ ArithmeticRelCodeValid witness.relationArity
      witness.relationCode)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
    (bounds : SyntaxFormulaCheckedDataFixedBounds tokenTable width tokenCount
      current next binderArity numericBound bitBound witness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
          tokenTable width tokenCount current next binderArity witness
          (.relationInvalid hcount hatTag htag hthree hatArity hatCode hinvalid
            hfailure)) <=
      syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
  have hcase :=
    syntaxFormulaOuterRelationInvalidCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      witness hcount hatTag htag hthree hatArity hatCode hinvalid hfailure
      bounds.width_le bounds.tokenCount_le bounds.current_le bounds.next_le
      bounds.tokenTable_size bounds.current_size bounds.next_size
      bounds.tailBoundary_size bounds.binderArity_size
      bounds.relationArity_size bounds.relationCode_size bounds.tag_size
      bounds.numeric_size
  have hdom :
      syntaxFormulaOuterRelationInvalidFullyFixedPayloadPolynomial numericBound
          bitBound <=
        syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound := by
    unfold syntaxFormulaCheckedDataFullyFixedPayloadPolynomial
    exact term4_le _ _ _ _ _ _ _ _
  unfold compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
  simp only [id_eq]
  exact Nat.le_trans hcase hdom

end FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataCasesA
