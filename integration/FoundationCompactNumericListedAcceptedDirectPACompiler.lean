import integration.FoundationCompactPAValuationSigmaOneFormulaCompiler
import integration.FoundationCompactNumericListedDirectProofPredicateExactness

/-!
# Accepted direct witnesses compile to real PA proofs

The two public parameters are instantiated by short binary numerals in the
same direct Sigma-one formula.  Numeric public-verifier acceptance supplies
standard-model truth; the proof-producing compiler then returns a genuine
certified PA derivation of that exact closed instance.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedAcceptedDirectPACompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedCertifiedVerifier
open FoundationCompactNumericListedPublicVerifier
open FoundationCompactNumericListedDirectProofPredicate
open FoundationCompactNumericListedDirectProofPredicateExactness
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationSigmaOneFormulaCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof

def compactListedPADirectProofInstance
    (bound formulaCode : Nat) :
    LO.FirstOrder.ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat)
      compactListedPADirectProofFormula.val) ⇜
    ![shortBinaryNumeralTerm bound,
      shortBinaryNumeralTerm formulaCode]

theorem embeddedClosedSubstitution_freeVariables_eq_empty
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty arity)
    (terms : Fin arity ->
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (hclosed : ∀ coordinate,
      (terms coordinate).freeVariables = ∅) :
    ((Rewriting.emb (ξ := Nat) formula) ⇜
      terms).freeVariables = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro index hindex
  rcases LO.FirstOrder.Semiformula.fvar?_rew hindex with
      hbound | hfree
  · rcases hbound with ⟨coordinate, hcoordinate⟩
    have hcoordinate' :
        index ∈ (terms coordinate).freeVariables := by
      simpa using hcoordinate
    rw [hclosed coordinate] at hcoordinate'
    simp at hcoordinate'
  · rcases hfree with ⟨sourceIndex, hsource, _⟩
    have hemb : (Rewriting.emb (ξ := Nat) formula :
        LO.FirstOrder.ArithmeticSemiformula Nat arity).freeVariables = ∅ := by
      simp
    have hsource' : sourceIndex ∈
        (Rewriting.emb (ξ := Nat) formula :
          LO.FirstOrder.ArithmeticSemiformula Nat arity).freeVariables :=
      hsource
    rw [hemb] at hsource'
    simp at hsource'

theorem compactListedPADirectProofInstance_sigmaOne
    (bound formulaCode : Nat) :
    Hierarchy Polarity.sigma 1
      (compactListedPADirectProofInstance bound formulaCode) := by
  exact
    (compactListedPADirectProofFormula_sigmaOne.rew Rew.emb).rew
      (Rew.subst
        ![shortBinaryNumeralTerm bound,
          shortBinaryNumeralTerm formulaCode])

theorem compactListedPADirectProofInstance_freeVariables_eq_empty
    (bound formulaCode : Nat) :
    (compactListedPADirectProofInstance
      bound formulaCode).freeVariables = ∅ := by
  exact embeddedClosedSubstitution_freeVariables_eq_empty
    compactListedPADirectProofFormula.val
    ![shortBinaryNumeralTerm bound,
      shortBinaryNumeralTerm formulaCode]
    (by
      intro coordinate
      fin_cases coordinate
      · exact shortBinaryNumeralTerm_freeVariables_eq_empty bound
      · exact shortBinaryNumeralTerm_freeVariables_eq_empty formulaCode)

theorem compactListedPADirectProofInstance_truth_of_public
    {bound proofCode formulaCode : Nat}
    (hbound : packedPayloadLength proofCode <= bound)
    (hpublic :
      compactNumericListedPublicVerifier proofCode formulaCode = true) :
    formulaValue (fun _ => 0)
      (compactListedPADirectProofInstance bound formulaCode) := by
  have htruth :=
    (compactListedPADirectProofFormula_iff_exists_publicVerifier
      bound formulaCode).2 ⟨proofCode, hbound, hpublic⟩
  change LO.FirstOrder.Semiformula.Eval ![] (fun _ => 0)
    ((Rewriting.emb (ξ := Nat)
        compactListedPADirectProofFormula.val) ⇜
      ![shortBinaryNumeralTerm bound,
        shortBinaryNumeralTerm formulaCode])
  rw [LO.FirstOrder.Semiformula.eval_substs]
  have hvalues :
      (LO.FirstOrder.Semiterm.val ![] (fun _ => 0) ∘
        ![shortBinaryNumeralTerm bound,
          shortBinaryNumeralTerm formulaCode]) =
        ![bound, formulaCode] := by
    funext coordinate
    fin_cases coordinate
    · exact termValue_shortBinaryNumeralTerm (fun _ => 0) bound
    · exact termValue_shortBinaryNumeralTerm
        (fun _ => 0) formulaCode
  rw [hvalues]
  simpa using htruth

def certifiedContextProofOfEmpty
    {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAContextProof ∅ formula) :
    CertifiedPAProof formula where
  derivation := by simpa using proof.derivation
  certificate := proof.certificate
  certificate_valid := by simpa using proof.certificate_valid

noncomputable def compileAcceptedDirectContext
    {bound proofCode formulaCode : Nat}
    (hbound : packedPayloadLength proofCode <= bound)
    (hpublic :
      compactNumericListedPublicVerifier proofCode formulaCode = true) :
    CertifiedPAContextProof ∅
      (compactListedPADirectProofInstance bound formulaCode) := by
  let raw := compileSigmaOneTruth
    (compactListedPADirectProofInstance bound formulaCode)
    (compactListedPADirectProofInstance_sigmaOne bound formulaCode)
    (fun _ => 0)
    (compactListedPADirectProofInstance_truth_of_public hbound hpublic)
  have hcontext : valuationContext
      (compactListedPADirectProofInstance
        bound formulaCode).freeVariables (fun _ => 0) = ∅ := by
    rw [compactListedPADirectProofInstance_freeVariables_eq_empty]
    simp [valuationContext]
  rw [hcontext] at raw
  exact raw

noncomputable def compileAcceptedDirect
    {bound proofCode formulaCode : Nat}
    (hbound : packedPayloadLength proofCode <= bound)
    (hpublic :
      compactNumericListedPublicVerifier proofCode formulaCode = true) :
    CertifiedPAProof
      (compactListedPADirectProofInstance bound formulaCode) :=
  certifiedContextProofOfEmpty
    (compileAcceptedDirectContext hbound hpublic)

theorem compileAcceptedDirect_publicVerifier_eq_true
    {bound proofCode formulaCode : Nat}
    (hbound : packedPayloadLength proofCode <= bound)
    (hpublic :
      compactNumericListedPublicVerifier proofCode formulaCode = true) :
    compactNumericListedPublicVerifier
        (compileAcceptedDirect hbound hpublic).code
        (compactFormulaCode
          (compactListedPADirectProofInstance bound formulaCode)) = true := by
  rw [compactNumericListedPublicVerifier_pointwise]
  exact (compileAcceptedDirect hbound hpublic).verifier_eq_true

#print axioms compactListedPADirectProofInstance_sigmaOne
#print axioms compactListedPADirectProofInstance_truth_of_public
#print axioms compileAcceptedDirect
#print axioms compileAcceptedDirect_publicVerifier_eq_true

end FoundationCompactNumericListedAcceptedDirectPACompiler
