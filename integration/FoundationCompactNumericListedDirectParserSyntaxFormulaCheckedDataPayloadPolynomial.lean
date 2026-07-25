import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaOuterConcreteBranchesFullyFixedBounds

/-! # Unified fixed payload polynomial for checked syntax-formula data -/

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataPayloadPolynomial

open FoundationCompactNumericListedDirectParserSyntaxFormulaOuterCertificateGeneralBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaOuterConcreteBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows

structure SyntaxFormulaCheckedDataFixedBounds
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : Prop where
  width_le : width <= numericBound
  tokenCount_le : tokenCount <= numericBound
  current_le : CompactUnifiedParserStateCoordinateValueBound current numericBound
  next_le : CompactUnifiedParserStateCoordinateValueBound next numericBound
  tokenTable_size : Nat.size tokenTable <= bitBound
  current_size : CompactUnifiedParserStateCoordinateSizeBound current bitBound
  next_size : CompactUnifiedParserStateCoordinateSizeBound next bitBound
  tailBoundary_size : Nat.size witness.tailBoundary <= bitBound
  binderArity_size : Nat.size binderArity <= bitBound
  relationArity_size : Nat.size witness.relationArity <= bitBound
  relationCode_size : Nat.size witness.relationCode <= bitBound
  tag_size : Nat.size witness.tag <= bitBound
  numeric_size : Nat.size numericBound <= bitBound
  bit_positive : 1 <= bitBound

theorem SyntaxFormulaCheckedDataFixedBounds.width_size
    {tokenTable width tokenCount : Nat}
    {current next : CompactUnifiedParserStateRowCoordinates}
    {binderArity numericBound bitBound : Nat}
    {witness : CompactSyntaxFormulaTaskWitnessCoordinates}
    (bounds : SyntaxFormulaCheckedDataFixedBounds tokenTable width tokenCount
      current next binderArity numericBound bitBound witness) :
    Nat.size width <= bitBound :=
  (Nat.size_le_size bounds.width_le).trans bounds.numeric_size

theorem SyntaxFormulaCheckedDataFixedBounds.tokenCount_size
    {tokenTable width tokenCount : Nat}
    {current next : CompactUnifiedParserStateRowCoordinates}
    {binderArity numericBound bitBound : Nat}
    {witness : CompactSyntaxFormulaTaskWitnessCoordinates}
    (bounds : SyntaxFormulaCheckedDataFixedBounds tokenTable width tokenCount
      current next binderArity numericBound bitBound witness) :
    Nat.size tokenCount <= bitBound :=
  (Nat.size_le_size bounds.tokenCount_le).trans bounds.numeric_size

def syntaxFormulaCheckedDataFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  syntaxFormulaOuterEmptyFullyFixedPayloadPolynomial numericBound bitBound +
  syntaxFormulaOuterRelationShortFullyFixedPayloadPolynomial numericBound
      bitBound +
  syntaxFormulaOuterRelationValidFullyFixedPayloadPolynomial tokenCount
      numericBound bitBound +
  syntaxFormulaOuterRelationInvalidFullyFixedPayloadPolynomial numericBound
      bitBound +
  syntaxFormulaOuterLogicalFullyFixedPayloadPolynomial numericBound bitBound +
  syntaxFormulaOuterBinaryFullyFixedPayloadPolynomial numericBound bitBound +
  syntaxFormulaOuterQuantifierFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound +
  syntaxFormulaOuterInvalidTagFullyFixedPayloadPolynomial numericBound bitBound

theorem term1_le (a b c d e f g h : Nat) :
    a <= a + b + c + d + e + f + g + h := by omega

theorem term2_le (a b c d e f g h : Nat) :
    b <= a + b + c + d + e + f + g + h := by omega

theorem term3_le (a b c d e f g h : Nat) :
    c <= a + b + c + d + e + f + g + h := by omega

theorem term4_le (a b c d e f g h : Nat) :
    d <= a + b + c + d + e + f + g + h := by omega

theorem term5_le (a b c d e f g h : Nat) :
    e <= a + b + c + d + e + f + g + h := by omega

theorem term6_le (a b c d e f g h : Nat) :
    f <= a + b + c + d + e + f + g + h := by omega

theorem term7_le (a b c d e f g h : Nat) :
    g <= a + b + c + d + e + f + g + h := by omega

theorem term8_le (a b c d e f g h : Nat) :
    h <= a + b + c + d + e + f + g + h := by omega

end FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataPayloadPolynomial
