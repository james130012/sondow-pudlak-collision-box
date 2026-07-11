import integration.FoundationCompactNumericGuardedInductionSentence
import integration.FoundationCompactNumericFixedPAAxiomSentence
import integration.FoundationCompactCertificateTokenMachineInversion

/-!
# Pure numeric comparator for all PA-axiom certificates

The comparator first requires the certificate token parser to consume the
entire certificate.  It then dispatches tags `0..21` through the fixed table
and tag `22` through the guarded induction constructor.  Runtime data contains
only naturals and lists of naturals.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericPAAxiomComparator

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaListChecks
open FoundationCompactCertificateTokenMachine
open FoundationCompactCertificateTokenMachineInversion
open FoundationCompactPAAxiomCertificate
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericGuardedInductionSentence

def compactFixedPAAxiomSentenceEqTokens
    (parametersAndCandidate :
      (Nat × (Nat × Nat)) × List Nat) : Bool :=
  match compactFixedPAAxiomSentenceTokens
      parametersAndCandidate.1.1 parametersAndCandidate.1.2 with
  | none => false
  | some generated =>
      tokenFormulaEq generated parametersAndCandidate.2

theorem compactFixedPAAxiomSentenceEqTokens_primrec :
    Primrec compactFixedPAAxiomSentenceEqTokens := by
  have hgenerated : Primrec
      (fun input : (Nat × (Nat × Nat)) × List Nat =>
        compactFixedPAAxiomSentenceTokens input.1.1 input.1.2) :=
    compactFixedPAAxiomSentenceTokens_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)
  have hsuccess : Primrec₂
      (fun (input : (Nat × (Nat × Nat)) × List Nat)
          (generated : List Nat) =>
        tokenFormulaEq generated input.2) :=
    tokenFormulaEq_primrec.comp₂ Primrec₂.right
      ((Primrec.snd.comp Primrec.fst).to₂)
  exact
    (Primrec.option_casesOn hgenerated (Primrec.const false) hsuccess).of_eq
      fun input => by
        cases hresult : compactFixedPAAxiomSentenceTokens
            input.1.1 input.1.2 <;>
          simp [compactFixedPAAxiomSentenceEqTokens, hresult]

theorem compactFixedPAAxiomSentenceEqTokens_canonical
    (certificate : PAAxiomCertificate)
    (hfixed :
      FoundationCompactNumericFixedPAAxiomSentence.FixedPAAxiomCertificate
        certificate)
    (candidate : LO.FirstOrder.ArithmeticSentence) :
    compactFixedPAAxiomSentenceEqTokens
        (((compactTokenAt 0
              (compactPAAxiomCertificateTokens certificate)),
            (compactTokenAt 1
                (compactPAAxiomCertificateTokens certificate),
              compactTokenAt 2
                (compactPAAxiomCertificateTokens certificate))),
          compactSentenceTokens candidate) = true ↔
      certificate.sentence = candidate := by
  unfold compactFixedPAAxiomSentenceEqTokens
  rw [compactFixedPAAxiomSentenceTokens_canonical certificate hfixed]
  simp only [tokenFormulaEq_eq_true_iff]
  change arithmeticPropositionTokenValue
        (Rewriting.emb certificate.sentence :
          LO.FirstOrder.ArithmeticProposition) =
      arithmeticPropositionTokenValue
        (Rewriting.emb candidate :
          LO.FirstOrder.ArithmeticProposition) ↔ _
  rw [arithmeticPropositionTokenValue_injective.eq_iff]
  exact Rewriting.emb_injective.eq_iff

def compactPAAxiomSentenceEqTokens
    (certificateAndCandidate : List Nat × List Nat) : Bool :=
  if compactPAAxiomCertificateTokenParser
      certificateAndCandidate.1 = some [] then
    let tag := compactTokenAt 0 certificateAndCandidate.1
    if tag = 22 then
      compactGuardedInductionSentenceEq
        (certificateAndCandidate.1.tail, certificateAndCandidate.2)
    else
      compactFixedPAAxiomSentenceEqTokens
        (((tag,
            (compactTokenAt 1 certificateAndCandidate.1,
              compactTokenAt 2 certificateAndCandidate.1))),
          certificateAndCandidate.2)
  else
    false

theorem compactPAAxiomSentenceEqTokens_primrec :
    Primrec compactPAAxiomSentenceEqTokens := by
  let Input := List Nat × List Nat
  have hcertificate : Primrec (fun input : Input => input.1) :=
    Primrec.fst
  have hcandidate : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hparser : Primrec (fun input : Input =>
      compactPAAxiomCertificateTokenParser input.1) :=
    compactPAAxiomCertificateTokenParser_primrec.comp hcertificate
  have hexact : PrimrecPred (fun input : Input =>
      compactPAAxiomCertificateTokenParser input.1 = some []) :=
    Primrec.eq.comp hparser (Primrec.const (some []))
  have htag : Primrec (fun input : Input =>
      compactTokenAt 0 input.1) :=
    compactTokenAt_primrec.comp (Primrec.const 0) hcertificate
  have harity : Primrec (fun input : Input =>
      compactTokenAt 1 input.1) :=
    compactTokenAt_primrec.comp (Primrec.const 1) hcertificate
  have hsymbolCode : Primrec (fun input : Input =>
      compactTokenAt 2 input.1) :=
    compactTokenAt_primrec.comp (Primrec.const 2) hcertificate
  have htag22 : PrimrecPred (fun input : Input =>
      compactTokenAt 0 input.1 = 22) :=
    Primrec.eq.comp htag (Primrec.const 22)
  have hinduction : Primrec (fun input : Input =>
      compactGuardedInductionSentenceEq
        (input.1.tail, input.2)) :=
    compactGuardedInductionSentenceEq_primrec.comp
      (Primrec.pair
        (Primrec.list_tail.comp hcertificate) hcandidate)
  have hfixedInput : Primrec (fun input : Input =>
      (((compactTokenAt 0 input.1,
          (compactTokenAt 1 input.1,
            compactTokenAt 2 input.1))), input.2)) :=
    Primrec.pair
      (Primrec.pair htag (Primrec.pair harity hsymbolCode)) hcandidate
  have hfixed : Primrec (fun input : Input =>
      compactFixedPAAxiomSentenceEqTokens
        (((compactTokenAt 0 input.1,
            (compactTokenAt 1 input.1,
              compactTokenAt 2 input.1))), input.2)) :=
    compactFixedPAAxiomSentenceEqTokens_primrec.comp hfixedInput
  exact
    (Primrec.ite hexact
      (Primrec.ite htag22 hinduction hfixed)
      (Primrec.const false)).of_eq fun input => by
        simp [compactPAAxiomSentenceEqTokens]

theorem fixedPAAxiomCertificate_or_induction
    (certificate : PAAxiomCertificate) :
    FoundationCompactNumericFixedPAAxiomSentence.FixedPAAxiomCertificate
        certificate ∨
      exists body : LO.FirstOrder.ArithmeticSemiformula Nat 1,
        certificate = .induction body := by
  cases certificate <;>
    simp [FoundationCompactNumericFixedPAAxiomSentence.FixedPAAxiomCertificate]

theorem compactPAAxiomSentenceEqTokens_canonical_of_fixed
    (certificate : PAAxiomCertificate)
    (hfixed :
      FoundationCompactNumericFixedPAAxiomSentence.FixedPAAxiomCertificate
        certificate)
    (candidate : LO.FirstOrder.ArithmeticSentence) :
    compactPAAxiomSentenceEqTokens
        (compactPAAxiomCertificateTokens certificate,
          compactSentenceTokens candidate) = true ↔
      certificate.sentence = candidate := by
  have hparse : compactPAAxiomCertificateTokenParser
      (compactPAAxiomCertificateTokens certificate) = some [] := by
    simpa using
      compactPAAxiomCertificateTokenParser_canonical_append certificate []
  have htag : compactTokenAt 0
      (compactPAAxiomCertificateTokens certificate) ≠ 22 := by
    cases certificate <;>
      simp [FoundationCompactNumericFixedPAAxiomSentence.FixedPAAxiomCertificate,
        compactPAAxiomCertificateTokens, compactTokenAt] at hfixed ⊢
  unfold compactPAAxiomSentenceEqTokens
  rw [if_pos hparse, if_neg htag]
  exact compactFixedPAAxiomSentenceEqTokens_canonical
    certificate hfixed candidate

theorem compactPAAxiomSentenceEqTokens_canonical
    (certificate : PAAxiomCertificate)
    (candidate : LO.FirstOrder.ArithmeticSentence) :
    compactPAAxiomSentenceEqTokens
        (compactPAAxiomCertificateTokens certificate,
          compactSentenceTokens candidate) = true ↔
      certificate.sentence = candidate := by
  rcases fixedPAAxiomCertificate_or_induction certificate with
    hfixed | ⟨body, rfl⟩
  · exact compactPAAxiomSentenceEqTokens_canonical_of_fixed
      certificate hfixed candidate
  · have hparse : compactPAAxiomCertificateTokenParser
        (compactPAAxiomCertificateTokens (.induction body)) = some [] := by
      simpa using compactPAAxiomCertificateTokenParser_canonical_append
        (.induction body) []
    unfold compactPAAxiomSentenceEqTokens
    rw [if_pos hparse]
    simpa [compactPAAxiomCertificateTokens, compactTokenAt,
      compactSentenceTokens] using
        compactGuardedInductionSentenceEq_canonical body candidate

theorem compactPAAxiomSentenceEqTokens_true_implies_exact_parser
    (certificateTokens candidateTokens : List Nat)
    (htrue : compactPAAxiomSentenceEqTokens
      (certificateTokens, candidateTokens) = true) :
    compactPAAxiomCertificateTokenParser certificateTokens = some [] := by
  unfold compactPAAxiomSentenceEqTokens at htrue
  by_cases hparse : compactPAAxiomCertificateTokenParser
      certificateTokens = some []
  · exact hparse
  · simp [hparse] at htrue

theorem compactPAAxiomSentenceEqTokens_exact_candidate_iff
    (certificateTokens : List Nat)
    (candidate : LO.FirstOrder.ArithmeticSentence) :
    compactPAAxiomSentenceEqTokens
        (certificateTokens, compactSentenceTokens candidate) = true ↔
      exists certificate : PAAxiomCertificate,
        certificateTokens = compactPAAxiomCertificateTokens certificate ∧
          certificate.sentence = candidate := by
  constructor
  · intro htrue
    have hparse :=
      compactPAAxiomSentenceEqTokens_true_implies_exact_parser
        certificateTokens (compactSentenceTokens candidate) htrue
    obtain ⟨certificate, htokens⟩ :=
      (compactPAAxiomCertificateTokenParser_success_iff
        certificateTokens []).1 hparse
    have hexact : certificateTokens =
        compactPAAxiomCertificateTokens certificate := by
      simpa using htokens
    refine ⟨certificate, hexact, ?_⟩
    subst certificateTokens
    have hcanonical : compactPAAxiomSentenceEqTokens
        (compactPAAxiomCertificateTokens certificate,
          compactSentenceTokens candidate) = true := by
      simpa using htrue
    exact (compactPAAxiomSentenceEqTokens_canonical
      certificate candidate).1 hcanonical
  · rintro ⟨certificate, rfl, hsentence⟩
    exact (compactPAAxiomSentenceEqTokens_canonical
      certificate candidate).2 hsentence

#print axioms compactFixedPAAxiomSentenceEqTokens_primrec
#print axioms compactFixedPAAxiomSentenceEqTokens_canonical
#print axioms compactPAAxiomSentenceEqTokens_primrec
#print axioms compactPAAxiomSentenceEqTokens_canonical
#print axioms compactPAAxiomSentenceEqTokens_exact_candidate_iff

end FoundationCompactNumericPAAxiomComparator
