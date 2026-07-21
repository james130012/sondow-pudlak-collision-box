import integration.FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificates for arithmetic relation-code validity

The two accepted `(arity, code)` pairs and their complement are certified by
closed equality and disequality atoms.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula
open FoundationCompactArithmeticSymbolCode
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

def relCodeFixedNumeralTerm (value : Nat) : ValuationTerm :=
  (Semiterm.Operator.numeral ℒₒᵣ value : Semiterm.Const ℒₒᵣ)

@[simp] theorem termValue_relCodeFixedNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (relCodeFixedNumeralTerm value) = value := by
  unfold termValue relCodeFixedNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘ (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) =
        (![] : Fin 0 -> Nat) by
      funext index
      exact Fin.elim0 index]
  simp

def relCodeFixedEqFormula (value expected : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) = !!(relCodeFixedNumeralTerm expected)”

def relCodeFixedNeFormula (value expected : Nat) : ValuationFormula :=
  ∼relCodeFixedEqFormula value expected

def compactAdditiveArithmeticRelCodeValidClosedFormula
    (arity code : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveArithmeticRelCodeValidDef.val) ⇜
    ![shortBinaryNumeralTerm arity, shortBinaryNumeralTerm code]

def compactAdditiveArithmeticRelCodeValidExplicitFormula
    (arity code : Nat) : ValuationFormula :=
  (relCodeFixedEqFormula arity 2 ⋏ relCodeFixedEqFormula code 0) ⋎
    (relCodeFixedEqFormula arity 2 ⋏ relCodeFixedEqFormula code 1)

theorem compactAdditiveArithmeticRelCodeValidClosedFormula_alignment
    (arity code : Nat) :
    compactAdditiveArithmeticRelCodeValidClosedFormula arity code =
      compactAdditiveArithmeticRelCodeValidExplicitFormula arity code := by
  unfold compactAdditiveArithmeticRelCodeValidClosedFormula
  unfold compactAdditiveArithmeticRelCodeValidExplicitFormula
  unfold compactAdditiveArithmeticRelCodeValidDef
  unfold relCodeFixedEqFormula relCodeFixedNumeralTerm
  simp

def compactAdditiveArithmeticRelCodeInvalidClosedFormula
    (arity code : Nat) : ValuationFormula :=
  ∼compactAdditiveArithmeticRelCodeValidClosedFormula arity code

def compactAdditiveArithmeticRelCodeInvalidExplicitFormula
    (arity code : Nat) : ValuationFormula :=
  (relCodeFixedNeFormula arity 2 ⋎ relCodeFixedNeFormula code 0) ⋏
    (relCodeFixedNeFormula arity 2 ⋎ relCodeFixedNeFormula code 1)

theorem compactAdditiveArithmeticRelCodeInvalidClosedFormula_alignment
    (arity code : Nat) :
    compactAdditiveArithmeticRelCodeInvalidClosedFormula arity code =
      compactAdditiveArithmeticRelCodeInvalidExplicitFormula arity code := by
  unfold compactAdditiveArithmeticRelCodeInvalidClosedFormula
  rw [compactAdditiveArithmeticRelCodeValidClosedFormula_alignment]
  rfl

noncomputable def relCodeFixedEqCertificate
    (value expected : Nat) (heq : value = expected) :
    HybridCertificate (relCodeFixedEqFormula value expected) := by
  unfold relCodeFixedEqFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, relCodeFixedNumeralTerm expected]
  change termValue zeroValuation (shortBinaryNumeralTerm value) =
    termValue zeroValuation (relCodeFixedNumeralTerm expected)
  simpa [termValue_shortBinaryNumeralTerm] using heq

noncomputable def relCodeFixedNeCertificate
    (value expected : Nat) (hne : value ≠ expected) :
    HybridCertificate (relCodeFixedNeFormula value expected) := by
  unfold relCodeFixedNeFormula relCodeFixedEqFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, relCodeFixedNumeralTerm expected]
  change ¬termValue zeroValuation (shortBinaryNumeralTerm value) =
    termValue zeroValuation (relCodeFixedNumeralTerm expected)
  simpa [termValue_shortBinaryNumeralTerm] using hne

private theorem compactAdditiveArithmeticRelCodeValidCertificate_nonempty
    (arity code : Nat) (hvalid : ArithmeticRelCodeValid arity code) :
    Nonempty
      (HybridCertificate
        (compactAdditiveArithmeticRelCodeValidExplicitFormula arity code)) := by
  unfold ArithmeticRelCodeValid at hvalid
  rcases hvalid with hvalid | hvalid
  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (relCodeFixedEqCertificate arity 2 hvalid.1)
        (relCodeFixedEqCertificate code 0 hvalid.2))⟩
  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (relCodeFixedEqCertificate arity 2 hvalid.1)
        (relCodeFixedEqCertificate code 1 hvalid.2))⟩

noncomputable def relCodeValidCase20Certificate
    (arity code : Nat) (hpair : arity = 2 ∧ code = 0) :
    HybridCertificate
      (compactAdditiveArithmeticRelCodeValidExplicitFormula arity code) := by
  unfold compactAdditiveArithmeticRelCodeValidExplicitFormula
  exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (relCodeFixedEqCertificate arity 2 hpair.1)
      (relCodeFixedEqCertificate code 0 hpair.2))

noncomputable def relCodeValidCase21Certificate
    (arity code : Nat) (hpair : arity = 2 ∧ code = 1) :
    HybridCertificate
      (compactAdditiveArithmeticRelCodeValidExplicitFormula arity code) := by
  unfold compactAdditiveArithmeticRelCodeValidExplicitFormula
  exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (relCodeFixedEqCertificate arity 2 hpair.1)
      (relCodeFixedEqCertificate code 1 hpair.2))

noncomputable def compactAdditiveArithmeticRelCodeValidExplicitHybridCertificate
    (arity code : Nat) (hvalid : ArithmeticRelCodeValid arity code) :
    HybridCertificate
      (compactAdditiveArithmeticRelCodeValidExplicitFormula arity code) := by
  let direct : HybridCertificate
      (compactAdditiveArithmeticRelCodeValidExplicitFormula arity code) :=
    if h20 : arity = 2 ∧ code = 0 then
      relCodeValidCase20Certificate arity code h20
    else if h21 : arity = 2 ∧ code = 1 then
      relCodeValidCase21Certificate arity code h21
    else
      False.elim (by
        unfold ArithmeticRelCodeValid at hvalid
        rcases hvalid with hvalid | hvalid
        · exact h20 hvalid
        · exact h21 hvalid)
  exact direct

noncomputable def compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph
    (arity code : Nat) (hvalid : ArithmeticRelCodeValid arity code) :
    HybridCertificate
      (compactAdditiveArithmeticRelCodeValidClosedFormula arity code) :=
  .cast (compactAdditiveArithmeticRelCodeValidClosedFormula_alignment arity code).symm
    (compactAdditiveArithmeticRelCodeValidExplicitHybridCertificate arity code
      hvalid)

private theorem relCodeInvalidPairCertificate_nonempty
    (left leftExpected right rightExpected : Nat)
    (hinvalid : ¬(left = leftExpected ∧ right = rightExpected)) :
    Nonempty
      (HybridCertificate
        (relCodeFixedNeFormula left leftExpected ⋎
          relCodeFixedNeFormula right rightExpected)) := by
  by_cases hleft : left = leftExpected
  · have hright : right ≠ rightExpected := by
      intro hright
      exact hinvalid ⟨hleft, hright⟩
    exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (relCodeFixedNeCertificate right rightExpected hright)⟩
  · exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (relCodeFixedNeCertificate left leftExpected hleft)⟩

noncomputable def relCodeInvalidPairCertificate
    (left leftExpected right rightExpected : Nat)
    (hinvalid : ¬(left = leftExpected ∧ right = rightExpected)) :
    HybridCertificate
      (relCodeFixedNeFormula left leftExpected ⋎
        relCodeFixedNeFormula right rightExpected) := by
  if hleft : left = leftExpected then
    have hright : right ≠ rightExpected := by
      intro hright
      exact hinvalid ⟨hleft, hright⟩
    exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (relCodeFixedNeCertificate right rightExpected hright)
  else
    exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (relCodeFixedNeCertificate left leftExpected hleft)

noncomputable def compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificate
    (arity code : Nat) (hinvalid : ¬ArithmeticRelCodeValid arity code) :
    HybridCertificate
      (compactAdditiveArithmeticRelCodeInvalidExplicitFormula arity code) := by
  have h20 : ¬(arity = 2 ∧ code = 0) := by
    intro hpair
    exact hinvalid (by simp [ArithmeticRelCodeValid, hpair])
  have h21 : ¬(arity = 2 ∧ code = 1) := by
    intro hpair
    exact hinvalid (by simp [ArithmeticRelCodeValid, hpair])
  let direct := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (relCodeInvalidPairCertificate arity 2 code 0 h20)
    (relCodeInvalidPairCertificate arity 2 code 1 h21)
  exact direct

noncomputable def compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph
    (arity code : Nat) (hinvalid : ¬ArithmeticRelCodeValid arity code) :
    HybridCertificate
      (compactAdditiveArithmeticRelCodeInvalidClosedFormula arity code) := by
  exact .cast
    (compactAdditiveArithmeticRelCodeInvalidClosedFormula_alignment arity code).symm
    (compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificate arity
      code hinvalid)

#print axioms compactAdditiveArithmeticRelCodeValidClosedFormula_alignment
#print axioms compactAdditiveArithmeticRelCodeInvalidClosedFormula_alignment
#print axioms compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph
#print axioms compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate
