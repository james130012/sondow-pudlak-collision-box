import integration.FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransport
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Proof-driven fixed bounds for finite all-closure specialization -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransport

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPABinaryNumeralAdditionBounds

private theorem allClosureSpecializationTailFormula_fixed
    {arity : Nat}
    (formula : ArithmeticSemiformula Nat (arity + 1))
    (terms : Fin (arity + 1) -> ArithmeticSemiterm Nat 0) :
    (Rew.subst (allClosureSpecializationTailTerms terms) ▹
        (∀⁰ formula : ArithmeticSemiformula Nat arity)) =
      ∀⁰ ((Rew.subst
        (allClosureSpecializationTailTerms terms)).q ▹ formula) := by
  simp

private theorem certifiedPAProof_conclusionCodeLength_le_payloadLength
    {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof formula) :
    (binaryFormulaCode formula).length <= proof.payloadLength := by
  have hformula : formula ∈ ({formula} :
      Finset LO.FirstOrder.ArithmeticProposition) := by simp
  have hsequent :=
    binaryFormulaCode_length_le_binarySequentCode_length_of_mem
      {formula} formula hformula
  have hproof := binarySequentCode_length_le_binaryProofLength proof.derivation
  have hpayload : binaryProofLength proof.derivation <= proof.payloadLength := by
    rw [CertifiedPAProof.payloadLength_eq]
    omega
  exact hsequent.trans (hproof.trans hpayload)

def allClosureSpecializationFixedStepCost
    (proofBound termCodeBound : Nat) : Nat :=
  let scale := proofBound + termCodeBound + 1
  192 + 2048 * scale * scale * scale

def allClosureSpecializationFixedPayloadBound :
    Nat -> Nat -> Nat -> Nat
  | 0, proofBound, _termCodeBound => proofBound
  | arity + 1, proofBound, termCodeBound =>
      let tailBound :=
        allClosureSpecializationFixedPayloadBound arity proofBound
          termCodeBound
      tailBound +
        allClosureSpecializationFixedStepCost tailBound termCodeBound

theorem specializeAllClosure_payloadLength_le_fixed :
    {arity : Nat} ->
    (formula : ArithmeticSemiformula Nat arity) ->
    (proof : CertifiedPAProof (∀⁰* formula)) ->
    (terms : Fin arity -> ArithmeticSemiterm Nat 0) ->
    (proofBound termCodeBound : Nat) ->
    proof.payloadLength <= proofBound ->
    (∀ coordinate,
      (binaryTermCode (terms coordinate)).length <= termCodeBound) ->
    (specializeAllClosure formula proof terms).payloadLength <=
      allClosureSpecializationFixedPayloadBound arity proofBound termCodeBound
  | 0, formula, proof, terms, proofBound, termCodeBound, hproof, _hterms => by
      change (CertifiedPAProof.cast _ proof).payloadLength <= proofBound
      rw [CertifiedPAProof.cast_payloadLength]
      exact hproof
  | arity + 1, formula, proof, terms, proofBound, termCodeBound, hproof,
      hterms => by
      let tailTerms := allClosureSpecializationTailTerms terms
      let tailProof := specializeAllClosure
        (∀⁰ formula : ArithmeticSemiformula Nat arity) proof tailTerms
      let tailBound := allClosureSpecializationFixedPayloadBound arity
        proofBound termCodeBound
      let body := (Rew.subst tailTerms).q ▹ formula
      let universalProof : CertifiedPAProof (∀⁰ body) :=
        CertifiedPAProof.cast
          (allClosureSpecializationTailFormula_fixed formula terms) tailProof
      let headProof := CertifiedPAProof.specialize universalProof (terms 0)
      have htailTerms : ∀ coordinate,
          (binaryTermCode (tailTerms coordinate)).length <= termCodeBound := by
        intro coordinate
        exact hterms coordinate.succ
      have htail : tailProof.payloadLength <= tailBound := by
        exact specializeAllClosure_payloadLength_le_fixed
          (∀⁰ formula : ArithmeticSemiformula Nat arity) proof tailTerms
          proofBound termCodeBound hproof htailTerms
      have huniversal : universalProof.payloadLength =
          tailProof.payloadLength := by
        dsimp only [universalProof]
        rw [CertifiedPAProof.cast_payloadLength]
      have hbodyCode : (binaryFormulaCode body).length <= tailBound := by
        have hbodyAll := binaryFormulaCode_all_body_le body
        have hconclusion :=
          certifiedPAProof_conclusionCodeLength_le_payloadLength universalProof
        exact hbodyAll.trans (hconclusion.trans (by
          rw [huniversal]
          exact htail))
      have htermCode :
          (binaryTermCode (terms 0)).length <= termCodeBound := hterms 0
      have hscale : specializationScale body (terms 0) <=
          tailBound + termCodeBound + 1 := by
        unfold specializationScale
        omega
      have hcost : specializationCost body (terms 0) <=
          allClosureSpecializationFixedStepCost tailBound termCodeBound := by
        unfold specializationCost allClosureSpecializationFixedStepCost
        dsimp only
        gcongr
      have hhead := CertifiedPAProof.specialize_payloadLength_le_cost
        universalProof (terms 0)
      change (CertifiedPAProof.cast _ headProof).payloadLength <= _
      rw [CertifiedPAProof.cast_payloadLength]
      calc
        headProof.payloadLength <= universalProof.payloadLength +
            specializationCost body (terms 0) := hhead
        _ = tailProof.payloadLength + specializationCost body (terms 0) := by
          rw [huniversal]
        _ <= tailBound +
            allClosureSpecializationFixedStepCost tailBound termCodeBound :=
          Nat.add_le_add htail hcost
        _ = allClosureSpecializationFixedPayloadBound (arity + 1) proofBound
            termCodeBound := by
          rfl

#print axioms specializeAllClosure_payloadLength_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransport
