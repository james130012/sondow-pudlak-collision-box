import integration.FoundationCompactNumericListedPublicVerifier
import integration.FoundationCompactListedFiniteConsistencyTarget
import integration.FoundationCompactSyntaxTransformationBounds
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Mathlib.Computability.Primrec.List

/-!
# Arithmetic predicate for the compact listed numeric verifier

This module is a semantic audit of the bounded proof predicate on the exact
public payload coordinate.  It gives an exact two-variable Sigma-one
representation and a qualitative PA-provability endpoint.

The generic `REPred.projection` construction used below passes through an
unbounded `rfind` program.  Its arithmetic representation contains a bounded
minimality prefix for the successful search stage.  No polynomial PA proof
bound for that prefix is claimed here.  Consequently this formula must not be
used as the final suitable numeration for the quantitative Pudlak route; that
route requires a direct, non-minimizing witness-and-verifier-trace formula.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedProofPredicate

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactListedMinProofLength
open FoundationCompactListedFiniteConsistencyTarget
open FoundationCompactListedVerifierArithmeticInput
open FoundationCompactNumericListedPublicVerifier
open FoundationCompactSyntaxTransformationBounds
open Primrec

/-- The direct accepted-code relation of the pure numeric public verifier. -/
def CompactNumericListedAcceptedCode
    (code formulaCode : Nat) : Prop :=
  compactNumericListedPublicVerifier code formulaCode = true

theorem compactNumericListedAcceptedCode_primrec :
    PrimrecPred (fun input : Nat × Nat =>
      CompactNumericListedAcceptedCode input.1 input.2) := by
  exact Primrec.eq.comp
    (compactNumericListedPublicVerifier_primrec.comp
      Primrec.fst Primrec.snd)
    (Primrec.const true)

theorem compactNumericListedAcceptedCode_iff_public
    (code formulaCode : Nat) :
    CompactNumericListedAcceptedCode code formulaCode ↔
      listedCompactCertifiedPAProofVerifier code formulaCode = true := by
  simp [CompactNumericListedAcceptedCode,
    compactNumericListedPublicVerifier_pointwise]

theorem packedPayloadLength_primrec :
    Primrec packedPayloadLength := by
  have hsize : Primrec Nat.size :=
    (Primrec.list_length.comp natBits_primrec).of_eq fun code => by
      simp [Nat.size_eq_bits_len]
  exact
    (Primrec.nat_sub.comp hsize (Primrec.const 1)).of_eq fun code => by
      rfl

/-- Pudlak's bounded proof predicate on the same complete payload coordinate. -/
def CompactListedPAProofPredicate
    (bound formulaCode : Nat) : Prop :=
  exists code : Nat,
    packedPayloadLength code <= bound ∧
      CompactNumericListedAcceptedCode code formulaCode

theorem compactListedPAProofWitness_primrec :
    PrimrecPred (fun input : (Nat × Nat) × Nat =>
      packedPayloadLength input.2 <= input.1.1 ∧
        CompactNumericListedAcceptedCode input.2 input.1.2) := by
  have hlength : PrimrecPred (fun input : (Nat × Nat) × Nat =>
      packedPayloadLength input.2 <= input.1.1) :=
    Primrec.nat_le.comp
      (packedPayloadLength_primrec.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  have haccept : PrimrecPred (fun input : (Nat × Nat) × Nat =>
      CompactNumericListedAcceptedCode input.2 input.1.2) := by
    exact Primrec.eq.comp
      (compactNumericListedPublicVerifier_primrec.comp
        Primrec.snd (Primrec.snd.comp Primrec.fst))
      (Primrec.const true)
  exact hlength.and haccept

theorem primrecPred_to_re
    {alpha : Type*} [Primcodable alpha]
    {predicate : alpha -> Prop}
    (hpredicate : PrimrecPred predicate) :
    REPred predicate := by
  rcases hpredicate with ⟨decision, hdecide⟩
  letI : DecidablePred predicate := decision
  refine ComputablePred.to_re <|
    ComputablePred.computable_iff.mpr ?_
  exact ⟨fun input => decide (predicate input),
    Primrec.to_comp hdecide, by funext input; simp⟩

theorem compactListedPAProofPredicate_re :
    REPred (fun input : Nat × Nat =>
      CompactListedPAProofPredicate input.1 input.2) := by
  have hwitness : REPred (fun input : (Nat × Nat) × Nat =>
      packedPayloadLength input.2 <= input.1.1 ∧
        CompactNumericListedAcceptedCode input.2 input.1.2) :=
    primrecPred_to_re compactListedPAProofWitness_primrec
  exact
    (REPred.projection hwitness).of_eq fun input => by
      simp only [CompactListedPAProofPredicate]

/- The projection theorem above is semantically exact, but its implementation
uses search for a first successful computation stage.  Everything below this
point is therefore an exact qualitative representation audit, not a
proof-length compiler. -/

def pairedCompactListedPAProofPredicate (code : Nat) : Prop :=
  CompactListedPAProofPredicate code.unpair.1 code.unpair.2

theorem pairedCompactListedPAProofPredicate_re :
    REPred pairedCompactListedPAProofPredicate := by
  exact
    (compactListedPAProofPredicate_re.comp
      Primrec.unpair.to_comp).of_eq fun code => by rfl

/-- The concrete partial characteristic computation used by the arithmetic
representation.  Its domain is exactly the paired bounded proof predicate. -/
def pairedCompactListedPAProofSemidecision (code : Nat) : Part Unit :=
  Part.assert (pairedCompactListedPAProofPredicate code) fun _ =>
    Part.some ()

theorem pairedCompactListedPAProofSemidecision_partrec :
    Partrec pairedCompactListedPAProofSemidecision := by
  change REPred pairedCompactListedPAProofPredicate
  exact pairedCompactListedPAProofPredicate_re

def pairedCompactListedPAProofPartFunction
    (values : List.Vector Nat 1) : Part Nat :=
  (pairedCompactListedPAProofSemidecision (values.get 0)).map
    fun _ => 0

theorem pairedCompactListedPAProofPartFunction_partrec :
    Partrec pairedCompactListedPAProofPartFunction := by
  have hinput : Computable (fun values : List.Vector Nat 1 =>
      values.get 0) :=
    Primrec.to_comp <|
      Primrec.vector_get.comp Primrec.id (Primrec.const 0)
  exact Partrec.map
    (Partrec.comp pairedCompactListedPAProofSemidecision_partrec hinput)
    (Computable.const 0).to₂

theorem exists_pairedCompactListedPAProofRepresentationProgram :
    exists program : Nat.ArithPart₁.Code 1,
      program.eval pairedCompactListedPAProofPartFunction := by
  apply Nat.ArithPart₁.exists_code
  apply Nat.ArithPart₁.of_partrec
  exact Nat.Partrec'.of_part
    pairedCompactListedPAProofPartFunction_partrec

noncomputable def pairedCompactListedPAProofRepresentationProgram :
    Nat.ArithPart₁.Code 1 :=
  Classical.choose
    exists_pairedCompactListedPAProofRepresentationProgram

theorem pairedCompactListedPAProofRepresentationProgram_eval :
    pairedCompactListedPAProofRepresentationProgram.eval
      pairedCompactListedPAProofPartFunction :=
  Classical.choose_spec
    exists_pairedCompactListedPAProofRepresentationProgram

noncomputable def pairedCompactListedPAProofFormula :
    𝚺₁.Semisentence 1 :=
  .mkSigma
    ((LO.FirstOrder.Arithmetic.code
      pairedCompactListedPAProofRepresentationProgram)/[‘0’, #0])
    (by simp)

@[simp] theorem pairedCompactListedPAProofFormula_spec
    (code : Nat) :
    pairedCompactListedPAProofFormula.val.Evalb ![code] ↔
      pairedCompactListedPAProofPredicate code := by
  simpa [pairedCompactListedPAProofFormula,
    Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton,
    pairedCompactListedPAProofPartFunction,
    pairedCompactListedPAProofSemidecision] using
      (LO.FirstOrder.Arithmetic.models_code
        pairedCompactListedPAProofRepresentationProgram_eval
        (y := 0) (v := ![code]))

/-- The exact two-variable Sigma-one formula `P(bound, formulaCode)`. -/
noncomputable def compactListedPAProofFormula :
    𝚺₁.Semisentence 2 :=
  .mkSigma
    “bound formulaCode. ∃ paired,
      !pairDef paired bound formulaCode ∧
      !(pairedCompactListedPAProofFormula) paired”

@[simp] theorem compactListedPAProofFormula_spec
    (bound formulaCode : Nat) :
    compactListedPAProofFormula.val.Evalb ![bound, formulaCode] ↔
      CompactListedPAProofPredicate bound formulaCode := by
  simp [compactListedPAProofFormula,
    pairedCompactListedPAProofPredicate, nat_pair_eq,
    Nat.unpair_pair]

theorem binaryPairSubstitution_termImageBound
    (left right : LO.FirstOrder.ArithmeticSemiterm Empty 0) :
    RewritingTermImageBound
        (Rew.subst ![left, right])
        (termSymbolCount left + termSymbolCount right) := by
  constructor
  · intro index
    cases index using Fin.cases with
    | zero => simp
    | succ index =>
        have hindex : index = 0 := Fin.eq_zero index
        subst index
        simp
  · intro index
    exact Empty.elim index

theorem compactListedPAProofFormula_substitution_symbolCount_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Empty 0) :
    formulaSymbolCount
        ((compactListedPAProofFormula.val)/[left, right]) <=
      formulaSymbolCount compactListedPAProofFormula.val *
        (termSymbolCount left + termSymbolCount right) := by
  apply formulaSymbolCount_rewriting_le_mul
      (Rew.subst ![left, right])
  · have hleft := one_le_termSymbolCount left
    omega
  · exact binaryPairSubstitution_termImageBound left right

noncomputable def compactListedPAProofSentence
    (bound formulaCode : Nat) : LO.FirstOrder.ArithmeticSentence :=
  (compactListedPAProofFormula.val)/[
    binaryNumeralTerm bound, binaryNumeralTerm formulaCode]

noncomputable def compactListedPAProofFormulaSymbolConstant : Nat :=
  formulaSymbolCount compactListedPAProofFormula.val

theorem compactListedPAProofSentence_symbolCount_le
    (bound formulaCode : Nat) :
    formulaSymbolCount
        (compactListedPAProofSentence bound formulaCode) <=
      compactListedPAProofFormulaSymbolConstant *
        (6 * Nat.size bound + 6 * Nat.size formulaCode + 2) := by
  calc
    formulaSymbolCount
        (compactListedPAProofSentence bound formulaCode) <=
      formulaSymbolCount compactListedPAProofFormula.val *
        (termSymbolCount (binaryNumeralTerm bound) +
          termSymbolCount (binaryNumeralTerm formulaCode)) := by
            simpa [compactListedPAProofSentence] using
              compactListedPAProofFormula_substitution_symbolCount_le
                (binaryNumeralTerm bound)
                (binaryNumeralTerm formulaCode)
    _ <= compactListedPAProofFormulaSymbolConstant *
        (6 * Nat.size bound + 6 * Nat.size formulaCode + 2) := by
      apply Nat.mul_le_mul_left
      have hbound := binaryNumeralTerm_symbolCount_le bound
      have hformula := binaryNumeralTerm_symbolCount_le formulaCode
      omega

theorem compactListedPAProofSentence_sigmaOne
    (bound formulaCode : Nat) :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 1
      (compactListedPAProofSentence bound formulaCode) := by
  simp [compactListedPAProofSentence]

@[simp] theorem models_compactListedPAProofSentence
    (bound formulaCode : Nat) :
    Nat↓[ℒₒᵣ] ⊧ compactListedPAProofSentence bound formulaCode ↔
      CompactListedPAProofPredicate bound formulaCode := by
  simp [compactListedPAProofSentence, models_iff,
    Semiformula.eval_substs,
    val_binaryNumeralTerm]

def compactListedFalsumCode : Nat :=
  compactFormulaCode
    (⊥ : LO.FirstOrder.ArithmeticProposition)

noncomputable def compactListedFiniteConsistencySentence
    (bound : Nat) : LO.FirstOrder.ArithmeticSentence :=
  ∼compactListedPAProofSentence bound compactListedFalsumCode

theorem compactListedFiniteConsistencySentence_symbolCount_le
    (bound : Nat) :
    formulaSymbolCount
        (compactListedFiniteConsistencySentence bound) <=
      compactListedPAProofFormulaSymbolConstant *
        (6 * Nat.size bound +
          6 * Nat.size compactListedFalsumCode + 2) := by
  simpa [compactListedFiniteConsistencySentence,
    formulaSymbolCount_neg] using
      compactListedPAProofSentence_symbolCount_le
        bound compactListedFalsumCode

theorem compactListedPAProofPredicate_iff_public
    (bound formulaCode : Nat) :
    CompactListedPAProofPredicate bound formulaCode ↔
      exists code : Nat,
        packedPayloadLength code <= bound ∧
          listedCompactCertifiedPAProofVerifier code formulaCode = true := by
  simp [CompactListedPAProofPredicate,
    CompactNumericListedAcceptedCode,
    compactNumericListedPublicVerifier_pointwise]

/-- Qualitative audit endpoint only.  This proves that every accepted instance
is PA-provable, but `sigma_one_completeness` supplies no uniform proof-length
bound and therefore does not discharge the accepted-trace node. -/
theorem compactListedPAProofSentence_provable_qualitative
    {bound formulaCode : Nat}
    (hproof : CompactListedPAProofPredicate bound formulaCode) :
    PA ⊢ compactListedPAProofSentence bound formulaCode :=
  LO.FirstOrder.Arithmetic.sigma_one_completeness
    (compactListedPAProofSentence_sigmaOne bound formulaCode)
    ((models_compactListedPAProofSentence bound formulaCode).2 hproof)

theorem compactListedPAProofSentence_derivation_nonempty_qualitative
    {bound formulaCode : Nat}
    (hproof : CompactListedPAProofPredicate bound formulaCode) :
    Nonempty (LO.FirstOrder.Derivation2 PA
      {((compactListedPAProofSentence bound formulaCode) :
        LO.FirstOrder.ArithmeticProposition)}) :=
  (LO.FirstOrder.provable_iff_derivable2 (T := PA)).mp
    (compactListedPAProofSentence_provable_qualitative hproof)

@[simp] theorem models_compactListedFiniteConsistencySentence_iff
    (bound : Nat) :
    Nat↓[ℒₒᵣ] ⊧ compactListedFiniteConsistencySentence bound ↔
      ListedCertifiedFiniteConsistencyAt bound := by
  unfold compactListedFiniteConsistencySentence
  change
    Semiformula.EvalAux
        (LO.FirstOrder.Arithmetic.standardModel Nat)
        Empty.elim ![]
        (∼compactListedPAProofSentence bound compactListedFalsumCode) ↔ _
  rw [Semiformula.EvalAux_neg]
  have hspec := models_compactListedPAProofSentence
    bound compactListedFalsumCode
  change
    (Semiformula.EvalAux
        (LO.FirstOrder.Arithmetic.standardModel Nat)
        Empty.elim ![]
        (compactListedPAProofSentence bound compactListedFalsumCode) ↔
      CompactListedPAProofPredicate bound compactListedFalsumCode) at hspec
  rw [hspec]
  rw [compactListedPAProofPredicate_iff_public]
  rfl

#print axioms compactNumericListedAcceptedCode_primrec
#print axioms packedPayloadLength_primrec
#print axioms compactListedPAProofWitness_primrec
#print axioms compactListedPAProofPredicate_re
#print axioms pairedCompactListedPAProofRepresentationProgram_eval
#print axioms compactListedPAProofFormula_spec
#print axioms compactListedPAProofSentence_symbolCount_le
#print axioms models_compactListedPAProofSentence
#print axioms compactListedPAProofSentence_derivation_nonempty_qualitative
#print axioms models_compactListedFiniteConsistencySentence_iff

end FoundationCompactNumericListedProofPredicate
