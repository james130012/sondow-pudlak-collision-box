import integration.FoundationCompactListedLocalCostPrimitives
import integration.FoundationCompactSyntaxTransformationCodeBounds

/-!
# Local binary-code bound for logical equivalence
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAFormulaIffCodeBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactSyntaxTransformationCodeBounds

private theorem binaryFormulaCode_and_length_le_arity
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode (left ⋏ right)).length <=
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length + 8 := by
  have htag : (binaryNatCode 4).length <= 8 := by decide
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_or_length_le_arity
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode (left ⋎ right)).length <=
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length + 8 := by
  have htag : (binaryNatCode 5).length <= 8 := by decide
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem binaryFormulaCode_iff_length_le
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode (left 🡘 right)).length <=
      3 * (binaryFormulaCode left).length +
        3 * (binaryFormulaCode right).length + 24 := by
  have hnegLeft := binaryFormulaCode_neg_length_le left
  have hnegRight := binaryFormulaCode_neg_length_le right
  have hforward := binaryFormulaCode_or_length_le_arity (∼left) right
  have hbackward := binaryFormulaCode_or_length_le_arity (∼right) left
  have hboth :=
    binaryFormulaCode_and_length_le_arity
      ((∼left) ⋎ right) ((∼right) ⋎ left)
  change (binaryFormulaCode
    (((∼left) ⋎ right) ⋏ ((∼right) ⋎ left))).length <= _
  omega

#print axioms binaryFormulaCode_iff_length_le

end FoundationCompactPAFormulaIffCodeBounds
