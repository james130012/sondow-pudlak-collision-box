import integration.FoundationCompactSyntaxTransformationCodeBounds

/-!
# Exact execution trace for formula negation

`Semiformula.neg` recursively visits the formula tree but reuses the term
vectors at atomic formulas.  This module exposes that traversal explicitly and
charges one step for every visited formula constructor.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactSyntaxNegationTrace

open FoundationSuccinctFiniteConsistencyTarget

def binaryFormulaNegTrace :
    {arity : Nat} ->
      LO.FirstOrder.ArithmeticSemiformula Nat arity ->
        LO.FirstOrder.ArithmeticSemiformula Nat arity × Nat
  | _, Semiformula.verum => (Semiformula.falsum, 1)
  | _, Semiformula.falsum => (Semiformula.verum, 1)
  | _, Semiformula.rel relationSymbol arguments =>
      (Semiformula.nrel relationSymbol arguments, 1)
  | _, Semiformula.nrel relationSymbol arguments =>
      (Semiformula.rel relationSymbol arguments, 1)
  | _, Semiformula.and left right =>
      let leftResult := binaryFormulaNegTrace left
      let rightResult := binaryFormulaNegTrace right
      (Semiformula.or leftResult.1 rightResult.1,
        leftResult.2 + rightResult.2 + 1)
  | _, Semiformula.or left right =>
      let leftResult := binaryFormulaNegTrace left
      let rightResult := binaryFormulaNegTrace right
      (Semiformula.and leftResult.1 rightResult.1,
        leftResult.2 + rightResult.2 + 1)
  | _, Semiformula.all body =>
      let bodyResult := binaryFormulaNegTrace body
      (Semiformula.exs bodyResult.1, bodyResult.2 + 1)
  | _, Semiformula.exs body =>
      let bodyResult := binaryFormulaNegTrace body
      (Semiformula.all bodyResult.1, bodyResult.2 + 1)

theorem binaryFormulaNegTrace_result
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    (binaryFormulaNegTrace formula).1 = ∼formula := by
  change (binaryFormulaNegTrace formula).1 = Semiformula.neg formula
  induction formula using Semiformula.rec' <;>
    simp [binaryFormulaNegTrace, Semiformula.neg, *]

theorem binaryFormulaNegTrace_cost_le_symbolCount
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    (binaryFormulaNegTrace formula).2 <= formulaSymbolCount formula := by
  induction formula using Semiformula.rec' <;>
    simp [binaryFormulaNegTrace, formulaSymbolCount, *] <;> omega

theorem binaryFormulaNegTrace_cost_le
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    (binaryFormulaNegTrace formula).2 <=
      (binaryFormulaCode formula).length := by
  exact (binaryFormulaNegTrace_cost_le_symbolCount formula).trans
    (formulaSymbolCount_le_binaryFormulaCode_length formula)

#print axioms binaryFormulaNegTrace_result
#print axioms binaryFormulaNegTrace_cost_le_symbolCount
#print axioms binaryFormulaNegTrace_cost_le

end FoundationCompactSyntaxNegationTrace
