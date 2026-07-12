import integration.FoundationCompactArithmeticSymbolCode
import integration.FoundationCompactNumericListedDirectArithmeticPrimitives

/-!
# Direct bounded formulas for arithmetic symbol-code validity

The ordered-ring language used by the compact parser has four accepted
function-code pairs and two accepted relation-code pairs.  These finite
domains are exposed directly as Delta-zero formulas, without a decoder or an
existential symbol witness.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula

open FoundationCompactArithmeticSymbolCode

def compactAdditiveArithmeticFuncCodeValidDef : 𝚺₀.Semisentence 2 := .mkSigma
  “arity code.
    (arity = 0 ∧ code = 0) ∨
    (arity = 0 ∧ code = 1) ∨
    (arity = 2 ∧ code = 0) ∨
    (arity = 2 ∧ code = 1)”

def compactAdditiveArithmeticRelCodeValidDef : 𝚺₀.Semisentence 2 := .mkSigma
  “arity code.
    (arity = 2 ∧ code = 0) ∨
    (arity = 2 ∧ code = 1)”

@[simp] theorem compactAdditiveArithmeticFuncCodeValidDef_spec
    (arity code : Nat) :
    compactAdditiveArithmeticFuncCodeValidDef.val.Evalb ![arity, code] ↔
      ArithmeticFuncCodeValid arity code := by
  simp [compactAdditiveArithmeticFuncCodeValidDef,
    ArithmeticFuncCodeValid]
  aesop

@[simp] theorem compactAdditiveArithmeticRelCodeValidDef_spec
    (arity code : Nat) :
    compactAdditiveArithmeticRelCodeValidDef.val.Evalb ![arity, code] ↔
      ArithmeticRelCodeValid arity code := by
  simp [compactAdditiveArithmeticRelCodeValidDef,
    ArithmeticRelCodeValid]
  aesop

theorem compactAdditiveArithmeticFuncCodeValidDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveArithmeticFuncCodeValidDef.val := by
  simp [compactAdditiveArithmeticFuncCodeValidDef]

theorem compactAdditiveArithmeticRelCodeValidDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveArithmeticRelCodeValidDef.val := by
  simp [compactAdditiveArithmeticRelCodeValidDef]

#print axioms compactAdditiveArithmeticFuncCodeValidDef_spec
#print axioms compactAdditiveArithmeticRelCodeValidDef_spec
#print axioms compactAdditiveArithmeticFuncCodeValidDef_sigmaZero
#print axioms compactAdditiveArithmeticRelCodeValidDef_sigmaZero

end FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula
