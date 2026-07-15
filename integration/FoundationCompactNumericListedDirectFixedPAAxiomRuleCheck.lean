import integration.FoundationCompactNumericListedDirectFixedPAAxiomCandidate
import integration.FoundationCompactNumericListedDirectFormulaMembership
import integration.FoundationCompactNumericListedRuleChecks

/-!
# Direct result graph for fixed PA-axiom rule checks

The graph combines the direct fixed-axiom candidate relation with membership
of that same candidate slice in the sequent.  Its result bit is proved equal
to the public `compactAxmRuleCheck` on canonical fixed certificates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFixedPAAxiomRuleCheck

open FoundationCompactSyntaxTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactPAAxiomCertificate
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericPAAxiomComparator
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFixedPAAxiomCandidate
open FoundationCompactNumericListedDirectFormulaMembership

def CompactAdditiveFixedPAAxiomRuleCheck
    (tokenTable width tokenCount gammaBoundary gammaCount
      candidateStart candidateFinish candidateCount
      paTag arity symbolCode resultBoolValue : Nat) : Prop :=
  resultBoolValue <= 1 ∧
    (resultBoolValue = 1 ↔
      CompactFixedPAAxiomCandidateRows
          tokenTable width tokenCount candidateStart candidateCount
            paTag arity symbolCode ∧
        CompactAdditiveFormulaMemberRows
          tokenTable width tokenCount gammaBoundary gammaCount
            candidateStart candidateFinish)

def compactAdditiveFixedPAAxiomRuleCheckDef :
    𝚺₀.Semisentence 12 := .mkSigma
  “tokenTable width tokenCount gammaBoundary gammaCount
      candidateStart candidateFinish candidateCount
      paTag arity symbolCode resultBoolValue.
    resultBoolValue ≤ 1 ∧
    (resultBoolValue = 1 ↔
      !(compactFixedPAAxiomCandidateRowsDef)
        tokenTable width tokenCount candidateStart candidateCount
          paTag arity symbolCode ∧
      !(compactAdditiveFormulaMemberRowsDef)
        tokenTable width tokenCount gammaBoundary gammaCount
          candidateStart candidateFinish)”

@[simp] theorem compactAdditiveFixedPAAxiomRuleCheckDef_spec
    (tokenTable width tokenCount gammaBoundary gammaCount
      candidateStart candidateFinish candidateCount
      paTag arity symbolCode resultBoolValue : Nat) :
    compactAdditiveFixedPAAxiomRuleCheckDef.val.Evalb
        ![tokenTable, width, tokenCount, gammaBoundary, gammaCount,
          candidateStart, candidateFinish, candidateCount,
          paTag, arity, symbolCode, resultBoolValue] ↔
      CompactAdditiveFixedPAAxiomRuleCheck
        tokenTable width tokenCount gammaBoundary gammaCount
          candidateStart candidateFinish candidateCount
          paTag arity symbolCode resultBoolValue := by
  let env : Fin 12 → Nat :=
    ![tokenTable, width, tokenCount, gammaBoundary, gammaCount,
      candidateStart, candidateFinish, candidateCount,
      paTag, arity, symbolCode, resultBoolValue]
  change compactAdditiveFixedPAAxiomRuleCheckDef.val.Evalb env ↔ _
  have hcandidateEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 12), #1, #2, #5,
          #7, #8, #9, #10]) =
        ![tokenTable, width, tokenCount, candidateStart,
          candidateCount, paTag, arity, symbolCode] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hmemberEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 12), #1, #2, #3,
          #4, #5, #6]) =
        ![tokenTable, width, tokenCount, gammaBoundary, gammaCount,
          candidateStart, candidateFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hresultValue : env 11 = resultBoolValue := rfl
  simp [compactAdditiveFixedPAAxiomRuleCheckDef,
    CompactAdditiveFixedPAAxiomRuleCheck,
    hcandidateEnv, hmemberEnv, hresultValue]

theorem compactAdditiveFixedPAAxiomRuleCheckDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveFixedPAAxiomRuleCheckDef.val := by
  simp [compactAdditiveFixedPAAxiomRuleCheckDef]

theorem compactSentenceTokens_injective :
    Function.Injective compactSentenceTokens := by
  intro left right htokens
  have hemb :
      (Rewriting.emb left : LO.FirstOrder.ArithmeticProposition) =
        (Rewriting.emb right : LO.FirstOrder.ArithmeticProposition) := by
    apply arithmeticPropositionTokenValue_injective
    simpa [compactSentenceTokens, arithmeticPropositionTokenValue] using htokens
  exact Rewriting.emb_injective hemb

theorem compactAdditiveFixedPAAxiomRuleCheck_canonical_iff
    {tokenTable width tokenCount gammaBoundary
      candidateStart candidateFinish resultBoolValue : Nat}
    {Gamma : List (List Nat)}
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate)
    (hfixed : FixedPAAxiomCertificate certificate)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hCandidate : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount candidateStart candidateFinish
        (compactSentenceTokens candidate)) :
    CompactAdditiveFixedPAAxiomRuleCheck
        tokenTable width tokenCount gammaBoundary Gamma.length
          candidateStart candidateFinish
          (compactSentenceTokens candidate).length
          (compactTokenAt 0 (compactPAAxiomCertificateTokens certificate))
          (compactTokenAt 1 (compactPAAxiomCertificateTokens certificate))
          (compactTokenAt 2 (compactPAAxiomCertificateTokens certificate))
          resultBoolValue ↔
      resultBoolValue = compactAdditiveBoolTag
        (compactAxmRuleCheck
          (Gamma, (compactSentenceTokens candidate,
            compactPAAxiomCertificateTokens certificate))) := by
  simp only [CompactAdditiveFixedPAAxiomRuleCheck]
  rw [show CompactFixedPAAxiomCandidateRows
      tokenTable width tokenCount candidateStart
        (compactSentenceTokens candidate).length
        (compactTokenAt 0 (compactPAAxiomCertificateTokens certificate))
        (compactTokenAt 1 (compactPAAxiomCertificateTokens certificate))
        (compactTokenAt 2 (compactPAAxiomCertificateTokens certificate)) ↔
      compactSentenceTokens candidate =
        compactSentenceTokens certificate.sentence by
    exact compactFixedPAAxiomCandidateRows_canonical_iff
      certificate hfixed hCandidate rfl]
  rw [compactAdditiveFormulaMemberRows_iff_mem hGamma hCandidate]
  have hsentence :
      compactSentenceTokens candidate =
          compactSentenceTokens certificate.sentence ↔
        certificate.sentence = candidate := by
    constructor
    · intro htokens
      exact (compactSentenceTokens_injective htokens).symm
    · intro hsentence
      exact congrArg compactSentenceTokens hsentence.symm
  rw [hsentence]
  have haxiom := compactPAAxiomSentenceEqTokens_canonical
    certificate candidate
  have hmember := tokenFormulaMem_eq_true_iff
    (compactSentenceTokens candidate) Gamma
  unfold compactAxmRuleCheck
  cases haxiomValue : compactPAAxiomSentenceEqTokens
      (compactPAAxiomCertificateTokens certificate,
        compactSentenceTokens candidate) <;>
    cases hmemberValue : tokenFormulaMem
      (compactSentenceTokens candidate) Gamma <;>
      simp [CompactAdditiveFixedPAAxiomRuleCheck,
        compactAdditiveBoolTag, haxiomValue, hmemberValue] at haxiom hmember ⊢ <;>
      aesop <;> omega

#print axioms compactAdditiveFixedPAAxiomRuleCheckDef_spec
#print axioms compactAdditiveFixedPAAxiomRuleCheckDef_sigmaZero
#print axioms compactSentenceTokens_injective
#print axioms compactAdditiveFixedPAAxiomRuleCheck_canonical_iff

end FoundationCompactNumericListedDirectFixedPAAxiomRuleCheck
