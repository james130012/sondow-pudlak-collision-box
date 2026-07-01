/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.SondowShortProofReproof
import BoundedArithmeticLab.SondowHilbertProofCodeBridge

open BoundedArithmeticLab

namespace SondowMainCheckedCodeBridge
/-!
## Product/log and decomposition pure-certificate frontier

The `3^n` component above now has a closed pure bounded-formula assembly for
the lcm/geometric tail route.  The product/log and decomposition components are
different: their main-library sources are analytic propositions involving
`Real.log`, `I`, `sondow_L`, and `A_rat`.  The following layer isolates the
exact source primitives and the compiler obligation needed before those sources
can be treated as Buss S21 proof objects.  In particular, the old project atoms
are explicitly ruled out as "pure" targets.
-/

abbrev ProductLogDecompositionAtomInterpretation :=
  BoundedArithmeticLab.FormulaFamily → ℕ → Prop

def productLogDecompositionBaBinaryLength (n : ℕ) : ℕ :=
  Nat.log2 n + 1

def productLogDecompositionBaSmash (x y : ℕ) : ℕ :=
  2 ^ (productLogDecompositionBaBinaryLength x *
    productLogDecompositionBaBinaryLength y)

def productLogDecompositionBaTermEval
    (env : ℕ → ℕ) : BATerm → ℕ
  | BATerm.var idx => env idx
  | BATerm.zero => 0
  | BATerm.one => 1
  | BATerm.succ t => productLogDecompositionBaTermEval env t + 1
  | BATerm.add x y =>
      productLogDecompositionBaTermEval env x +
        productLogDecompositionBaTermEval env y
  | BATerm.mul x y =>
      productLogDecompositionBaTermEval env x *
        productLogDecompositionBaTermEval env y
  | BATerm.length t =>
      productLogDecompositionBaBinaryLength
        (productLogDecompositionBaTermEval env t)
  | BATerm.smash x y =>
      productLogDecompositionBaSmash
        (productLogDecompositionBaTermEval env x)
        (productLogDecompositionBaTermEval env y)

def productLogDecompositionBaFormulaEval
    (atomEval : ProductLogDecompositionAtomInterpretation) :
    (ℕ → ℕ) → BAFormula → Prop
  | _env, BAFormula.atom family index => atomEval family index
  | _env, BAFormula.falsum => False
  | env, BAFormula.equal lhs rhs =>
      productLogDecompositionBaTermEval env lhs =
        productLogDecompositionBaTermEval env rhs
  | env, BAFormula.le lhs rhs =>
      productLogDecompositionBaTermEval env lhs ≤
        productLogDecompositionBaTermEval env rhs
  | env, BAFormula.not φ =>
      ¬ productLogDecompositionBaFormulaEval atomEval env φ
  | env, BAFormula.and φ ψ =>
      productLogDecompositionBaFormulaEval atomEval env φ ∧
        productLogDecompositionBaFormulaEval atomEval env ψ
  | env, BAFormula.or φ ψ =>
      productLogDecompositionBaFormulaEval atomEval env φ ∨
        productLogDecompositionBaFormulaEval atomEval env ψ
  | env, BAFormula.imp φ ψ =>
      productLogDecompositionBaFormulaEval atomEval env φ →
        productLogDecompositionBaFormulaEval atomEval env ψ
  | env, BAFormula.forallBounded idx bound body =>
      ∀ value : ℕ,
        value ≤ productLogDecompositionBaTermEval env bound →
          productLogDecompositionBaFormulaEval atomEval
            (Function.update env idx value) body
  | env, BAFormula.existsBounded idx bound body =>
      ∃ value : ℕ,
        value ≤ productLogDecompositionBaTermEval env bound ∧
          productLogDecompositionBaFormulaEval atomEval
            (Function.update env idx value) body

def productLogDecompositionBaFormulaAtomFree : BAFormula → Prop
  | BAFormula.atom _ _ => False
  | BAFormula.falsum => True
  | BAFormula.equal _ _ => True
  | BAFormula.le _ _ => True
  | BAFormula.not φ => productLogDecompositionBaFormulaAtomFree φ
  | BAFormula.and φ ψ =>
      productLogDecompositionBaFormulaAtomFree φ ∧
        productLogDecompositionBaFormulaAtomFree ψ
  | BAFormula.or φ ψ =>
      productLogDecompositionBaFormulaAtomFree φ ∧
        productLogDecompositionBaFormulaAtomFree ψ
  | BAFormula.imp φ ψ =>
      productLogDecompositionBaFormulaAtomFree φ ∧
        productLogDecompositionBaFormulaAtomFree ψ
  | BAFormula.forallBounded _ _ body =>
      productLogDecompositionBaFormulaAtomFree body
  | BAFormula.existsBounded _ _ body =>
      productLogDecompositionBaFormulaAtomFree body

abbrev productLogDecompositionAtomFree : BAFormula → Prop :=
  productLogDecompositionBaFormulaAtomFree

abbrev productLogDecompositionAtomInterpretation :
    ProductLogDecompositionAtomInterpretation :=
  fun _family _index => False

abbrev productLogDecompositionFormulaEval :
    (ℕ → ℕ) → BAFormula → Prop :=
  productLogDecompositionBaFormulaEval
    productLogDecompositionAtomInterpretation

def productLogDecompositionProofObjectOfAxiom
    {φ : BAFormula} (hφ : BussS21Axiom φ) :
    BAProofObject BussS21Axiom where
  conclusion := φ
  derivation := BADerivation.ax hφ

def productLogDecompositionPolytimeDefinabilityProofObject
    (name : ℕ) (graph : BAFormula) :
    BAProofObject BussS21Axiom :=
  productLogDecompositionProofObjectOfAxiom
    (BussS21Axiom.polytimeDefinability name graph)
def productLogBaNatLiteral : ℕ → BATerm
  | 0 => BATerm.zero
  | n + 1 => BATerm.succ (productLogBaNatLiteral n)

@[simp] theorem productLogBaNatLiteral_eval
    (env : ℕ → ℕ) (n : ℕ) :
    productLogDecompositionBaTermEval env
        (productLogBaNatLiteral n) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [productLogBaNatLiteral, productLogDecompositionBaTermEval, ih]

end SondowMainCheckedCodeBridge
