import integration.FoundationCompactNumericListedAcceptedDirectPACompiler
import integration.FoundationCompactListedFiniteConsistencyTarget

/-!
# Direct finite consistency for the listed compact PA verifier

This module fixes the finite-consistency family used by the quantitative
Pudlak route.  It is literally the negation of the already audited direct
two-variable proof predicate at the compact code of falsity.  Consequently
the formula, checker, conclusion code, and complete packed-payload length
coordinate are definitionally shared; no reflection-graft payload or
project-level proof-length function occurs here.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFiniteConsistencyTarget

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactListedFiniteConsistencyTarget
open FoundationCompactNumericListedPublicVerifier
open FoundationCompactNumericListedDirectProofPredicate
open FoundationCompactNumericListedDirectProofPredicateExactness
open FoundationCompactNumericListedAcceptedDirectPACompiler
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationTermCompiler

def compactListedPADirectFalsumCode : Nat :=
  compactFormulaCode
    (⊥ : LO.FirstOrder.ArithmeticProposition)

noncomputable def compactListedPADirectFiniteConsistencySentence
    (bound : Nat) : LO.FirstOrder.ArithmeticProposition :=
  ∼compactListedPADirectProofInstance
    bound compactListedPADirectFalsumCode

theorem compactListedPADirectProofInstance_formulaValue_iff
    (bound formulaCode : Nat) :
    formulaValue (fun _ => 0)
        (compactListedPADirectProofInstance bound formulaCode) ↔
      compactListedPADirectProofFormula.val.Evalb
        ![bound, formulaCode] := by
  unfold compactListedPADirectProofInstance formulaValue
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
  exact LO.FirstOrder.Semiformula.eval_emb
    compactListedPADirectProofFormula.val

theorem compactListedPADirectProofInstance_iff_exists_publicVerifier
    (bound formulaCode : Nat) :
    formulaValue (fun _ => 0)
        (compactListedPADirectProofInstance bound formulaCode) ↔
      ∃ proofCode : Nat,
        packedPayloadLength proofCode ≤ bound ∧
          compactNumericListedPublicVerifier
            proofCode formulaCode = true := by
  rw [compactListedPADirectProofInstance_formulaValue_iff]
  exact
    compactListedPADirectProofFormula_iff_exists_publicVerifier
      bound formulaCode

theorem compactListedPADirectFiniteConsistencySentence_piOne
    (bound : Nat) :
    Hierarchy Polarity.pi 1
      (compactListedPADirectFiniteConsistencySentence bound) := by
  exact
    (compactListedPADirectProofInstance_sigmaOne
      bound compactListedPADirectFalsumCode).neg

@[simp] theorem
    models_compactListedPADirectFiniteConsistencySentence_iff
    (bound : Nat) :
    formulaValue (fun _ => 0)
        (compactListedPADirectFiniteConsistencySentence bound) ↔
      ListedCertifiedFiniteConsistencyAt bound := by
  rw [compactListedPADirectFiniteConsistencySentence]
  change
    LO.FirstOrder.Semiformula.EvalAux
        (LO.FirstOrder.Arithmetic.standardModel Nat)
        (fun _ => 0) ![]
        (∼compactListedPADirectProofInstance
          bound compactListedPADirectFalsumCode) ↔
      ListedCertifiedFiniteConsistencyAt bound
  rw [LO.FirstOrder.Semiformula.EvalAux_neg]
  change
    (¬formulaValue (fun _ => 0)
        (compactListedPADirectProofInstance
          bound compactListedPADirectFalsumCode)) ↔
      ListedCertifiedFiniteConsistencyAt bound
  rw [compactListedPADirectProofInstance_iff_exists_publicVerifier]
  change
    (¬∃ proofCode : Nat,
      packedPayloadLength proofCode ≤ bound ∧
        compactNumericListedPublicVerifier
          proofCode compactListedPADirectFalsumCode = true) ↔
      ¬∃ code : Nat,
        packedPayloadLength code ≤ bound ∧
          listedCompactCertifiedPAProofVerifier
            code compactListedPADirectFalsumCode = true
  simp only [compactNumericListedPublicVerifier_pointwise]

theorem models_compactListedPADirectFiniteConsistencySentence
    (bound : Nat) :
    formulaValue (fun _ => 0)
      (compactListedPADirectFiniteConsistencySentence bound) := by
  rw [models_compactListedPADirectFiniteConsistencySentence_iff]
  exact listedCertifiedFiniteConsistencyAt bound

def compactListedPADirectFiniteConsistencyFormulaCode
    (bound : Nat) : Nat :=
  compactFormulaCode
    (compactListedPADirectFiniteConsistencySentence bound)

#print axioms
  compactListedPADirectProofInstance_formulaValue_iff
#print axioms
  compactListedPADirectProofInstance_iff_exists_publicVerifier
#print axioms
  compactListedPADirectFiniteConsistencySentence_piOne
#print axioms
  models_compactListedPADirectFiniteConsistencySentence_iff
#print axioms
  models_compactListedPADirectFiniteConsistencySentence

end FoundationCompactNumericListedDirectFiniteConsistencyTarget
