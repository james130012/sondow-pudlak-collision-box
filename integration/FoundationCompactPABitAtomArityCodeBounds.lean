import integration.FoundationCompactPABitMembershipRuleCompiler
import integration.FoundationCompactPABitMembershipValuationCompilerPublicBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-!
# Uniform code bound for bit atoms at arbitrary binder arity

The existing valuation compiler bound is specialized to arity zero.  This
module exposes the same substitution argument for bounded-universal bodies.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactPABitAtomArityCodeBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipValuationCompilerPublicBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds

def bitAtomArityCodePolynomial (termBound : Nat) : Nat :=
  uniformRewritingFormulaFactor (termBound + 4) (termBound + 1)
      (formulaSymbolCount binaryBitEmbeddedFormula) *
    (binaryFormulaCode binaryBitEmbeddedFormula).length

theorem binaryBitAtomAtTerms_code_length_le_arity
    {arity : Nat}
    (index value : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (termBound : Nat)
    (hindex : (binaryTermCode index).length <= termBound)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryFormulaCode (binaryBitAtomAtTerms index value)).length <=
      bitAtomArityCodePolynomial termBound := by
  let rewriting : Rew ℒₒᵣ Nat 2 Nat arity := Rew.subst ![index, value]
  have hindexSymbols : termSymbolCount index <= termBound :=
    (termSymbolCount_le_binaryTermCode_length index).trans hindex
  have hvalueSymbols : termSymbolCount value <= termBound :=
    (termSymbolCount_le_binaryTermCode_length value).trans hvalue
  have hbound : UniformRewritingImageBound rewriting (termBound + 4)
      (termBound + 1) := by
    constructor
    · intro coordinate
      cases coordinate using Fin.cases with
      | zero =>
          simp [rewriting, Rew.subst_bvar]
          omega
      | succ coordinate =>
          cases coordinate using Fin.cases with
          | zero =>
              simp [rewriting, Rew.subst_bvar]
              omega
          | succ coordinate => exact Fin.elim0 coordinate
    · constructor
      · intro coordinate
        cases coordinate using Fin.cases with
        | zero =>
            simp [rewriting, Rew.subst_bvar]
            omega
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero =>
                simp [rewriting, Rew.subst_bvar]
                omega
            | succ coordinate => exact Fin.elim0 coordinate
      · exact fun freeIndex => by
          change (Rew.subst ![index, value])
            (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat 2) =
              (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat arity)
          exact Rew.subst_fvar ![index, value] freeIndex
  have hraw := binaryFormulaCode_rewriting_length_le_factor
    binaryBitEmbeddedFormula rewriting (by omega) (by omega) hbound
  have hatomEq : binaryBitAtomAtTerms index value =
      rewriting ▹ binaryBitEmbeddedFormula := by
    unfold binaryBitAtomAtTerms binaryBitEmbeddedFormula
    rfl
  rw [hatomEq]
  unfold bitAtomArityCodePolynomial
  exact hraw

#print axioms binaryBitAtomAtTerms_code_length_le_arity

end FoundationCompactPABitAtomArityCodeBounds
