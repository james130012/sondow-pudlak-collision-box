import integration.FoundationCompactNumericFormulaFvSup

/-!
# Pure numeric iterated universal closure

The runtime function prepends one universal-quantifier token per closure step.
It is primitive recursive but is not by itself claimed polynomial in the bit
length of a binary-encoded depth. The guarded caller must first bound that
depth by the candidate sentence length.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericAllClosure

open FoundationCompactSyntaxTokenMachine

def compactAllClosureTokenStep (tokens : List Nat) : List Nat :=
  6 :: tokens

theorem compactAllClosureTokenStep_primrec :
    Primrec compactAllClosureTokenStep := by
  exact Primrec.list_cons.comp (Primrec.const 6) Primrec.id

def compactAllClosureTokens
    (depth : Nat) (formulaTokens : List Nat) : List Nat :=
  (compactAllClosureTokenStep^[depth]) formulaTokens

theorem compactAllClosureTokens_primrec :
    Primrec₂ compactAllClosureTokens := by
  apply Primrec₂.mk
  have hfuel : Primrec (fun input : Nat × List Nat => input.1) :=
    Primrec.fst
  have hinitial : Primrec (fun input : Nat × List Nat => input.2) :=
    Primrec.snd
  have hstep : Primrec₂
      (fun (_input : Nat × List Nat) (tokens : List Nat) =>
        compactAllClosureTokenStep tokens) :=
    (compactAllClosureTokenStep_primrec.comp Primrec.snd).to₂
  exact
    (Primrec.nat_iterate hfuel hinitial hstep).of_eq
      fun input => by rfl

theorem compactAllClosureTokens_canonical :
    forall {depth : Nat}
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat depth),
      compactAllClosureTokens depth
          (compactArithmeticFormulaTokens formula) =
        compactArithmeticFormulaTokens (∀⁰* formula)
  | 0, formula => rfl
  | depth + 1, formula => by
      have ih := compactAllClosureTokens_canonical (∀⁰ formula)
      simpa [compactAllClosureTokens, Function.iterate_succ_apply,
        compactAllClosureTokenStep, compactArithmeticFormulaTokens,
        allClosure_succ] using ih

#print axioms compactAllClosureTokenStep_primrec
#print axioms compactAllClosureTokens_primrec
#print axioms compactAllClosureTokens_canonical

end FoundationCompactNumericAllClosure
