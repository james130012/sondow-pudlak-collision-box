import integration.FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificates for arithmetic function-code validity

The four accepted `(arity, code)` pairs are exposed as equality branches.  The
complement is exposed as four checked disjunctions of disequalities.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula
open FoundationCompactArithmeticSymbolCode
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

def funcCodeFixedNumeralTerm (value : Nat) : ValuationTerm :=
  (Semiterm.Operator.numeral ℒₒᵣ value : Semiterm.Const ℒₒᵣ)

@[simp] theorem termValue_funcCodeFixedNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (funcCodeFixedNumeralTerm value) = value := by
  unfold termValue funcCodeFixedNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘ (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) =
        (![] : Fin 0 -> Nat) by
      funext index
      exact Fin.elim0 index]
  simp

def funcCodeFixedEqFormula (value expected : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) = !!(funcCodeFixedNumeralTerm expected)”

def funcCodeFixedNeFormula (value expected : Nat) : ValuationFormula :=
  ∼funcCodeFixedEqFormula value expected

def compactAdditiveArithmeticFuncCodeValidClosedFormula
    (arity code : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveArithmeticFuncCodeValidDef.val) ⇜
    ![shortBinaryNumeralTerm arity, shortBinaryNumeralTerm code]

def compactAdditiveArithmeticFuncCodeValidExplicitFormula
    (arity code : Nat) : ValuationFormula :=
  (funcCodeFixedEqFormula arity 0 ⋏ funcCodeFixedEqFormula code 0) ⋎
    (funcCodeFixedEqFormula arity 0 ⋏ funcCodeFixedEqFormula code 1) ⋎
    (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 0) ⋎
    (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 1)

theorem compactAdditiveArithmeticFuncCodeValidClosedFormula_alignment
    (arity code : Nat) :
    compactAdditiveArithmeticFuncCodeValidClosedFormula arity code =
      compactAdditiveArithmeticFuncCodeValidExplicitFormula arity code := by
  unfold compactAdditiveArithmeticFuncCodeValidClosedFormula
  unfold compactAdditiveArithmeticFuncCodeValidExplicitFormula
  unfold compactAdditiveArithmeticFuncCodeValidDef
  unfold funcCodeFixedEqFormula funcCodeFixedNumeralTerm
  simp

def compactAdditiveArithmeticFuncCodeInvalidClosedFormula
    (arity code : Nat) : ValuationFormula :=
  ∼compactAdditiveArithmeticFuncCodeValidClosedFormula arity code

def compactAdditiveArithmeticFuncCodeInvalidExplicitFormula
    (arity code : Nat) : ValuationFormula :=
  (funcCodeFixedNeFormula arity 0 ⋎ funcCodeFixedNeFormula code 0) ⋏
    ((funcCodeFixedNeFormula arity 0 ⋎ funcCodeFixedNeFormula code 1) ⋏
      ((funcCodeFixedNeFormula arity 2 ⋎ funcCodeFixedNeFormula code 0) ⋏
        (funcCodeFixedNeFormula arity 2 ⋎ funcCodeFixedNeFormula code 1)))

theorem compactAdditiveArithmeticFuncCodeInvalidClosedFormula_alignment
    (arity code : Nat) :
    compactAdditiveArithmeticFuncCodeInvalidClosedFormula arity code =
      compactAdditiveArithmeticFuncCodeInvalidExplicitFormula arity code := by
  unfold compactAdditiveArithmeticFuncCodeInvalidClosedFormula
  rw [compactAdditiveArithmeticFuncCodeValidClosedFormula_alignment]
  rfl

noncomputable def funcCodeFixedEqCertificate
    (value expected : Nat) (heq : value = expected) :
    HybridCertificate (funcCodeFixedEqFormula value expected) := by
  unfold funcCodeFixedEqFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, funcCodeFixedNumeralTerm expected]
  change termValue zeroValuation (shortBinaryNumeralTerm value) =
    termValue zeroValuation (funcCodeFixedNumeralTerm expected)
  simpa [termValue_shortBinaryNumeralTerm] using heq

noncomputable def funcCodeFixedNeCertificate
    (value expected : Nat) (hne : value ≠ expected) :
    HybridCertificate (funcCodeFixedNeFormula value expected) := by
  unfold funcCodeFixedNeFormula funcCodeFixedEqFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, funcCodeFixedNumeralTerm expected]
  change ¬termValue zeroValuation (shortBinaryNumeralTerm value) =
    termValue zeroValuation (funcCodeFixedNumeralTerm expected)
  simpa [termValue_shortBinaryNumeralTerm] using hne

private theorem compactAdditiveArithmeticFuncCodeValidCertificate_nonempty
    (arity code : Nat) (hvalid : ArithmeticFuncCodeValid arity code) :
    Nonempty
      (HybridCertificate
        (compactAdditiveArithmeticFuncCodeValidExplicitFormula arity code)) := by
  unfold ArithmeticFuncCodeValid at hvalid
  rcases hvalid with hvalid | hvalid | hvalid | hvalid
  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (funcCodeFixedEqCertificate arity 0 hvalid.1)
        (funcCodeFixedEqCertificate code 0 hvalid.2))⟩
  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (funcCodeFixedEqCertificate arity 0 hvalid.1)
          (funcCodeFixedEqCertificate code 1 hvalid.2)))⟩
  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (funcCodeFixedEqCertificate arity 2 hvalid.1)
            (funcCodeFixedEqCertificate code 0 hvalid.2))))⟩
  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (funcCodeFixedEqCertificate arity 2 hvalid.1)
          (funcCodeFixedEqCertificate code 1 hvalid.2))))⟩

noncomputable def funcCodeValidCase00Certificate
    (arity code : Nat) (hpair : arity = 0 ∧ code = 0) :
    HybridCertificate
      (compactAdditiveArithmeticFuncCodeValidExplicitFormula arity code) := by
  unfold compactAdditiveArithmeticFuncCodeValidExplicitFormula
  exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (funcCodeFixedEqCertificate arity 0 hpair.1)
      (funcCodeFixedEqCertificate code 0 hpair.2))

noncomputable def funcCodeValidCase01Certificate
    (arity code : Nat) (hpair : arity = 0 ∧ code = 1) :
    HybridCertificate
      (compactAdditiveArithmeticFuncCodeValidExplicitFormula arity code) := by
  unfold compactAdditiveArithmeticFuncCodeValidExplicitFormula
  exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (funcCodeFixedEqCertificate arity 0 hpair.1)
        (funcCodeFixedEqCertificate code 1 hpair.2)))

noncomputable def funcCodeValidCase20Certificate
    (arity code : Nat) (hpair : arity = 2 ∧ code = 0) :
    HybridCertificate
      (compactAdditiveArithmeticFuncCodeValidExplicitFormula arity code) := by
  unfold compactAdditiveArithmeticFuncCodeValidExplicitFormula
  exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (funcCodeFixedEqCertificate arity 2 hpair.1)
          (funcCodeFixedEqCertificate code 0 hpair.2))))

noncomputable def funcCodeValidCase21Certificate
    (arity code : Nat) (hpair : arity = 2 ∧ code = 1) :
    HybridCertificate
      (compactAdditiveArithmeticFuncCodeValidExplicitFormula arity code) := by
  unfold compactAdditiveArithmeticFuncCodeValidExplicitFormula
  exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (funcCodeFixedEqCertificate arity 2 hpair.1)
          (funcCodeFixedEqCertificate code 1 hpair.2))))

noncomputable def compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificate
    (arity code : Nat) (hvalid : ArithmeticFuncCodeValid arity code) :
    HybridCertificate
      (compactAdditiveArithmeticFuncCodeValidExplicitFormula arity code) := by
  let direct : HybridCertificate
      (compactAdditiveArithmeticFuncCodeValidExplicitFormula arity code) :=
    if h00 : arity = 0 ∧ code = 0 then
      funcCodeValidCase00Certificate arity code h00
    else if h01 : arity = 0 ∧ code = 1 then
      funcCodeValidCase01Certificate arity code h01
    else if h20 : arity = 2 ∧ code = 0 then
      funcCodeValidCase20Certificate arity code h20
    else if h21 : arity = 2 ∧ code = 1 then
      funcCodeValidCase21Certificate arity code h21
    else
      False.elim (by
        unfold ArithmeticFuncCodeValid at hvalid
        rcases hvalid with hvalid | hvalid | hvalid | hvalid
        · exact h00 hvalid
        · exact h01 hvalid
        · exact h20 hvalid
        · exact h21 hvalid)
  exact direct

noncomputable def compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificateOfGraph
    (arity code : Nat) (hvalid : ArithmeticFuncCodeValid arity code) :
    HybridCertificate
      (compactAdditiveArithmeticFuncCodeValidClosedFormula arity code) :=
  .cast
    (compactAdditiveArithmeticFuncCodeValidClosedFormula_alignment arity code).symm
    (compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificate arity code hvalid)

private theorem funcCodeInvalidPairCertificate_nonempty
    (left leftExpected right rightExpected : Nat)
    (hinvalid : ¬(left = leftExpected ∧ right = rightExpected)) :
    Nonempty
      (HybridCertificate
        (funcCodeFixedNeFormula left leftExpected ⋎
          funcCodeFixedNeFormula right rightExpected)) := by
  by_cases hleft : left = leftExpected
  · have hright : right ≠ rightExpected := by
      intro hright
      exact hinvalid ⟨hleft, hright⟩
    exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (funcCodeFixedNeCertificate right rightExpected hright)⟩
  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (funcCodeFixedNeCertificate left leftExpected hleft)⟩

noncomputable def funcCodeInvalidPairCertificate
    (left leftExpected right rightExpected : Nat)
    (hinvalid : ¬(left = leftExpected ∧ right = rightExpected)) :
    HybridCertificate
      (funcCodeFixedNeFormula left leftExpected ⋎
        funcCodeFixedNeFormula right rightExpected) := by
  if hleft : left = leftExpected then
    have hright : right ≠ rightExpected := by
      intro hright
      exact hinvalid ⟨hleft, hright⟩
    exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (funcCodeFixedNeCertificate right rightExpected hright)
  else
    exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (funcCodeFixedNeCertificate left leftExpected hleft)

noncomputable def compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificate
    (arity code : Nat) (hinvalid : ¬ArithmeticFuncCodeValid arity code) :
    HybridCertificate
      (compactAdditiveArithmeticFuncCodeInvalidExplicitFormula arity code) := by
  have h00 : ¬(arity = 0 ∧ code = 0) := by
    intro hpair
    exact hinvalid (by simp [ArithmeticFuncCodeValid, hpair])
  have h01 : ¬(arity = 0 ∧ code = 1) := by
    intro hpair
    exact hinvalid (by simp [ArithmeticFuncCodeValid, hpair])
  have h20 : ¬(arity = 2 ∧ code = 0) := by
    intro hpair
    exact hinvalid (by simp [ArithmeticFuncCodeValid, hpair])
  have h21 : ¬(arity = 2 ∧ code = 1) := by
    intro hpair
    exact hinvalid (by simp [ArithmeticFuncCodeValid, hpair])
  let direct := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (funcCodeInvalidPairCertificate arity 0 code 0 h00)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (funcCodeInvalidPairCertificate arity 0 code 1 h01)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (funcCodeInvalidPairCertificate arity 2 code 0 h20)
        (funcCodeInvalidPairCertificate arity 2 code 1 h21)))
  exact direct

noncomputable def compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificateOfGraph
    (arity code : Nat) (hinvalid : ¬ArithmeticFuncCodeValid arity code) :
    HybridCertificate
      (compactAdditiveArithmeticFuncCodeInvalidClosedFormula arity code) :=
  .cast
    (compactAdditiveArithmeticFuncCodeInvalidClosedFormula_alignment arity code).symm
    (compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificate arity code hinvalid)

#print axioms compactAdditiveArithmeticFuncCodeValidClosedFormula_alignment
#print axioms compactAdditiveArithmeticFuncCodeInvalidClosedFormula_alignment
#print axioms compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificateOfGraph
#print axioms compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
