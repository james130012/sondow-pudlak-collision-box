import integration.FoundationCompactNumericFormulaListChecks

/-!
# Pure numeric formula constructors

These constructors operate only on canonical natural-token values.  They are
the exact token-level counterparts of the six non-recursive logical formula
constructors used by the listed local checker.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericFormulaConstructors

open FoundationCompactSyntaxTokenMachine

def tokenFormulaVerum : List Nat := [2]

def tokenFormulaFalsum : List Nat := [3]

def tokenFormulaAnd (left right : List Nat) : List Nat :=
  4 :: left ++ right

def tokenFormulaOr (left right : List Nat) : List Nat :=
  5 :: left ++ right

def tokenFormulaAll (body : List Nat) : List Nat :=
  6 :: body

def tokenFormulaExs (body : List Nat) : List Nat :=
  7 :: body

theorem tokenFormulaVerum_primrec :
    Primrec (fun _unit : Unit => tokenFormulaVerum) := by
  exact Primrec.const tokenFormulaVerum

theorem tokenFormulaFalsum_primrec :
    Primrec (fun _unit : Unit => tokenFormulaFalsum) := by
  exact Primrec.const tokenFormulaFalsum

theorem tokenFormulaAnd_primrec : Primrec₂ tokenFormulaAnd := by
  exact Primrec.list_cons.comp₂
    (Primrec₂.const 4) Primrec.list_append

theorem tokenFormulaOr_primrec : Primrec₂ tokenFormulaOr := by
  exact Primrec.list_cons.comp₂
    (Primrec₂.const 5) Primrec.list_append

theorem tokenFormulaAll_primrec : Primrec tokenFormulaAll := by
  exact Primrec.list_cons.comp (Primrec.const 6) Primrec.id

theorem tokenFormulaExs_primrec : Primrec tokenFormulaExs := by
  exact Primrec.list_cons.comp (Primrec.const 7) Primrec.id

@[simp] theorem tokenFormulaVerum_canonical
    {binderArity : Nat} :
    tokenFormulaVerum =
      compactArithmeticFormulaTokens
        (⊤ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) := rfl

@[simp] theorem tokenFormulaFalsum_canonical
    {binderArity : Nat} :
    tokenFormulaFalsum =
      compactArithmeticFormulaTokens
        (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) := rfl

@[simp] theorem tokenFormulaAnd_canonical
    {binderArity : Nat}
    (left right :
      LO.FirstOrder.ArithmeticSemiformula Nat binderArity) :
    tokenFormulaAnd (compactArithmeticFormulaTokens left)
        (compactArithmeticFormulaTokens right) =
      compactArithmeticFormulaTokens (left ⋏ right) := rfl

@[simp] theorem tokenFormulaOr_canonical
    {binderArity : Nat}
    (left right :
      LO.FirstOrder.ArithmeticSemiformula Nat binderArity) :
    tokenFormulaOr (compactArithmeticFormulaTokens left)
        (compactArithmeticFormulaTokens right) =
      compactArithmeticFormulaTokens (left ⋎ right) := rfl

@[simp] theorem tokenFormulaAll_canonical
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1)) :
    tokenFormulaAll (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens (∀⁰ body) := rfl

@[simp] theorem tokenFormulaExs_canonical
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1)) :
    tokenFormulaExs (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens (∃⁰ body) := rfl

#print axioms tokenFormulaVerum_primrec
#print axioms tokenFormulaFalsum_primrec
#print axioms tokenFormulaAnd_primrec
#print axioms tokenFormulaOr_primrec
#print axioms tokenFormulaAll_primrec
#print axioms tokenFormulaExs_primrec
#print axioms tokenFormulaAnd_canonical
#print axioms tokenFormulaOr_canonical
#print axioms tokenFormulaAll_canonical
#print axioms tokenFormulaExs_canonical

end FoundationCompactNumericFormulaConstructors
