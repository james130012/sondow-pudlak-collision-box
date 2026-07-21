import integration.FoundationCompactNumericListedNodeFields
import integration.FoundationCompactCertificateTokenMachineInversion

/-!
# Typed inversion of one structural-certificate node
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedCertificateNodeTypedInversion

open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactCertificateTokenMachineInversion
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields

inductive CompactNumericCertificateNodeTyped :
    List Nat -> CompactNumericCertificateNode -> Prop
  | leaf (suffix : List Nat) :
      CompactNumericCertificateNodeTyped
        (0 :: suffix) (0, ([], suffix))
  | pa (certificate : PAAxiomCertificate) (suffix : List Nat) :
      CompactNumericCertificateNodeTyped
        (1 :: compactPAAxiomCertificateTokens certificate ++ suffix)
        (1, (compactPAAxiomCertificateTokens certificate, suffix))
  | unary (suffix : List Nat) :
      CompactNumericCertificateNodeTyped
        (2 :: suffix) (2, ([], suffix))
  | binary (suffix : List Nat) :
      CompactNumericCertificateNodeTyped
        (3 :: suffix) (3, ([], suffix))

theorem compactStructuralCertificateNodeParser_eq_some_iff_typed
    (tokens : List Nat) (node : CompactNumericCertificateNode) :
    compactStructuralCertificateNodeParser tokens = some node <->
      CompactNumericCertificateNodeTyped tokens node := by
  constructor
  · intro hparser
    cases tokens with
    | nil =>
        simp [compactStructuralCertificateNodeParser] at hparser
    | cons tag body =>
        by_cases h0 : tag = 0
        · subst tag
          have hnode : node = (0, (([] : List Nat), body)) := by
            simpa [compactStructuralCertificateNodeParser] using hparser.symm
          subst node
          exact CompactNumericCertificateNodeTyped.leaf body
        · by_cases h1 : tag = 1
          · subst tag
            cases haxiom : compactPAAxiomCertificateTokenParser body with
            | none =>
                simp [compactStructuralCertificateNodeParser, haxiom]
                  at hparser
            | some suffix =>
                have hnode : node =
                    (1, (consumedTokenPrefix body suffix, suffix)) := by
                  simpa [compactStructuralCertificateNodeParser, haxiom]
                    using hparser.symm
                obtain ⟨certificate, hbody⟩ :=
                  (compactPAAxiomCertificateTokenParser_success_iff
                    body suffix).mp haxiom
                subst node
                subst body
                simpa using
                  CompactNumericCertificateNodeTyped.pa
                    certificate suffix
          · by_cases h2 : tag = 2
            · subst tag
              have hnode : node = (2, (([] : List Nat), body)) := by
                simpa [compactStructuralCertificateNodeParser, h0, h1]
                  using hparser.symm
              subst node
              exact CompactNumericCertificateNodeTyped.unary body
            · by_cases h3 : tag = 3
              · subst tag
                have hnode : node = (3, (([] : List Nat), body)) := by
                  simpa [compactStructuralCertificateNodeParser, h0, h1, h2]
                    using hparser.symm
                subst node
                exact CompactNumericCertificateNodeTyped.binary body
              · simp [compactStructuralCertificateNodeParser,
                  h0, h1, h2, h3] at hparser
  · intro htyped
    cases htyped with
    | leaf suffix =>
        simp [compactStructuralCertificateNodeParser]
    | pa certificate suffix =>
        simp [compactStructuralCertificateNodeParser,
          compactPAAxiomCertificateTokenParser_canonical_append]
    | unary suffix =>
        simp [compactStructuralCertificateNodeParser]
    | binary suffix =>
        simp [compactStructuralCertificateNodeParser]

#print axioms compactStructuralCertificateNodeParser_eq_some_iff_typed

end FoundationCompactNumericListedCertificateNodeTypedInversion
