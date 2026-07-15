import integration.FoundationCompactCertificateTokenMachineInversion
import integration.FoundationCompactNumericListedNodeFields

/-!
# Exact failure semantics for structural-certificate nodes

The PA-certificate parser has four genuine failure families.  This file proves
that they are exhaustive, then lifts the result through the outer structural
certificate-node dispatch.  No bounded graph or existence interface is used.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactNumericListedDirectCertificateNodeFailureSemantics

open FoundationCompactArithmeticSymbolCode
open FoundationCompactCertificateTokenMachine
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedNodeFields

def CompactPAAxiomCertificateTokenFailureShape (tokens : List Nat) : Prop :=
  tokens = [] ∨
    ∃ tag body, tokens = tag :: body ∧
      ((tag = 3 ∧
          (body.length < 2 ∨
            ¬ ArithmeticFuncCodeValid
              (compactTokenAt 0 body) (compactTokenAt 1 body))) ∨
        (tag = 4 ∧
          (body.length < 2 ∨
            ¬ ArithmeticRelCodeValid
              (compactTokenAt 0 body) (compactTokenAt 1 body))) ∨
        (tag = 22 ∧ compactFormulaTokenParser 1 body = none) ∨
        22 < tag)

theorem compactPAAxiomCertificateTokenParser_eq_none_iff_failureShape
    (tokens : List Nat) :
    compactPAAxiomCertificateTokenParser tokens = none ↔
      CompactPAAxiomCertificateTokenFailureShape tokens := by
  constructor
  · intro hparser
    cases tokens with
    | nil => exact Or.inl rfl
    | cons tag body =>
        right
        refine ⟨tag, body, rfl, ?_⟩
        by_cases h3 : tag = 3
        · subst tag
          left
          refine ⟨rfl, ?_⟩
          by_cases hlength : 2 ≤ body.length
          · right
            by_contra hvalid
            simp [compactPAAxiomCertificateTokenParser, hlength,
              hvalid] at hparser
          · left
            omega
        · by_cases h4 : tag = 4
          · subst tag
            right
            left
            refine ⟨rfl, ?_⟩
            by_cases hlength : 2 ≤ body.length
            · right
              by_contra hvalid
              simp [compactPAAxiomCertificateTokenParser, h3,
                hlength, hvalid] at hparser
            · left
              omega
          · by_cases h22 : tag = 22
            · subst tag
              right
              right
              left
              refine ⟨rfl, ?_⟩
              simpa [compactPAAxiomCertificateTokenParser, h3, h4] using hparser
            · right
              right
              right
              by_contra hnot
              have hlt : tag < 22 := by omega
              simp [compactPAAxiomCertificateTokenParser, h3, h4,
                h22, hlt] at hparser
  · intro hfailure
    rcases hfailure with rfl | ⟨tag, body, rfl, hshape⟩
    · simp [compactPAAxiomCertificateTokenParser]
    · rcases hshape with hfunc | hrel | hformula | hlarge
      · rcases hfunc with ⟨rfl, hshort | hinvalid⟩
        · have hnotLength : ¬ 2 ≤ body.length := by omega
          simp [compactPAAxiomCertificateTokenParser, hnotLength]
        · by_cases hlength : 2 ≤ body.length
          · simp [compactPAAxiomCertificateTokenParser, hlength, hinvalid]
          · simp [compactPAAxiomCertificateTokenParser, hlength]
      · rcases hrel with ⟨rfl, hshort | hinvalid⟩
        · have hnotLength : ¬ 2 ≤ body.length := by omega
          simp [compactPAAxiomCertificateTokenParser, hnotLength]
        · by_cases hlength : 2 ≤ body.length
          · simp [compactPAAxiomCertificateTokenParser, hlength, hinvalid]
          · simp [compactPAAxiomCertificateTokenParser, hlength]
      · rcases hformula with ⟨rfl, hformula⟩
        simpa [compactPAAxiomCertificateTokenParser] using hformula
      · have h3 : tag ≠ 3 := by omega
        have h4 : tag ≠ 4 := by omega
        have h22 : tag ≠ 22 := by omega
        have hnotLt : ¬ tag < 22 := by omega
        simp [compactPAAxiomCertificateTokenParser, h3, h4, h22, hnotLt]

def CompactStructuralCertificateNodeFailureShape (tokens : List Nat) : Prop :=
  tokens = [] ∨
    ∃ tag tail, tokens = tag :: tail ∧
      ((tag = 1 ∧ CompactPAAxiomCertificateTokenFailureShape tail) ∨
        (tag ≠ 0 ∧ tag ≠ 1 ∧ tag ≠ 2 ∧ tag ≠ 3))

theorem compactStructuralCertificateNodeParser_eq_none_iff_failureShape
    (tokens : List Nat) :
    compactStructuralCertificateNodeParser tokens = none ↔
      CompactStructuralCertificateNodeFailureShape tokens := by
  constructor
  · intro hparser
    cases tokens with
    | nil => exact Or.inl rfl
    | cons tag tail =>
        right
        refine ⟨tag, tail, rfl, ?_⟩
        by_cases h0 : tag = 0
        · subst tag
          simp [compactStructuralCertificateNodeParser] at hparser
        · by_cases h1 : tag = 1
          · subst tag
            left
            refine ⟨rfl, ?_⟩
            apply (compactPAAxiomCertificateTokenParser_eq_none_iff_failureShape
              tail).mp
            cases hpa : compactPAAxiomCertificateTokenParser tail with
            | none => rfl
            | some suffix =>
                simp [compactStructuralCertificateNodeParser, h0, hpa] at hparser
          · by_cases h2 : tag = 2
            · subst tag
              simp [compactStructuralCertificateNodeParser, h0, h1] at hparser
            · by_cases h3 : tag = 3
              · subst tag
                simp [compactStructuralCertificateNodeParser,
                  h0, h1, h2] at hparser
              · exact Or.inr ⟨h0, h1, h2, h3⟩
  · intro hfailure
    rcases hfailure with rfl | ⟨tag, tail, rfl, hshape⟩
    · simp [compactStructuralCertificateNodeParser]
    · rcases hshape with ⟨rfl, hpaFailure⟩ | hinvalid
      · have hpa : compactPAAxiomCertificateTokenParser tail = none :=
          (compactPAAxiomCertificateTokenParser_eq_none_iff_failureShape
            tail).mpr hpaFailure
        simp [compactStructuralCertificateNodeParser, hpa]
      · rcases hinvalid with ⟨h0, h1, h2, h3⟩
        simp [compactStructuralCertificateNodeParser, h0, h1, h2, h3]

#print axioms compactPAAxiomCertificateTokenParser_eq_none_iff_failureShape
#print axioms compactStructuralCertificateNodeParser_eq_none_iff_failureShape

end FoundationCompactNumericListedDirectCertificateNodeFailureSemantics
