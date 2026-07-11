import integration.FoundationCompactListedProofDecoder
import integration.FoundationCompactSyntaxTransformationTrace

/-!
# Explicit costed certificate checks on list sequents
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedCertificateVerifier

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedProofDecoder
open FoundationCompactVerifierFormulaListChecks
open FoundationCompactSyntaxTransformationTrace

def traceAnd (left right : Bool × Nat) : Bool × Nat :=
  (left.1 && right.1, left.2 + right.2 + 1)

@[simp] theorem traceAnd_result_eq_true_iff
    (left right : Bool × Nat) :
    (traceAnd left right).1 = true ↔
      left.1 = true ∧ right.1 = true := by
  simp [traceAnd]

@[simp] theorem traceAnd_cost
    (left right : Bool × Nat) :
    (traceAnd left right).2 = left.2 + right.2 + 1 := rfl

def sentenceEqTrace
    (left right : LO.FirstOrder.ArithmeticSentence) : Bool × Nat :=
  formulaEqTrace
    (Rewriting.emb left : LO.FirstOrder.ArithmeticProposition)
    (Rewriting.emb right : LO.FirstOrder.ArithmeticProposition)

theorem sentenceEqTrace_result_eq_true_iff
    (left right : LO.FirstOrder.ArithmeticSentence) :
    (sentenceEqTrace left right).1 = true ↔ left = right := by
  rw [sentenceEqTrace, formulaEqTrace_result_eq_true_iff]
  exact Rewriting.emb_injective.eq_iff

@[simp] theorem toFinset_map_shift
    (formulas : List LO.FirstOrder.ArithmeticProposition) :
    (formulas.map Rewriting.shift).toFinset =
      formulas.toFinset.image Rewriting.shift := by
  ext formula
  simp

def listedCertificateValid :
    ListedCheckedPAProofTree -> StructuralValidityCertificate -> Prop
  | .closed Gamma formula, .leaf =>
      formula ∈ Gamma ∧ ∼formula ∈ Gamma
  | .axm Gamma sentence, .axiomCert certificate =>
      certificate.sentence = sentence ∧
        (Rewriting.emb sentence : LO.FirstOrder.ArithmeticProposition) ∈ Gamma
  | .verum Gamma, .leaf =>
      (⊤ : LO.FirstOrder.ArithmeticProposition) ∈ Gamma
  | .and Gamma leftFormula rightFormula left right,
      .binary leftCertificate rightCertificate =>
      leftFormula ⋏ rightFormula ∈ Gamma ∧
        left.conclusionList.toFinset =
          (leftFormula :: Gamma).toFinset ∧
        right.conclusionList.toFinset =
          (rightFormula :: Gamma).toFinset ∧
        listedCertificateValid left leftCertificate ∧
        listedCertificateValid right rightCertificate
  | .or Gamma leftFormula rightFormula premise,
      .unary premiseCertificate =>
      leftFormula ⋎ rightFormula ∈ Gamma ∧
        premise.conclusionList.toFinset =
          (leftFormula :: rightFormula :: Gamma).toFinset ∧
        listedCertificateValid premise premiseCertificate
  | .all Gamma formula premise, .unary premiseCertificate =>
      ∀⁰ formula ∈ Gamma ∧
        premise.conclusionList.toFinset =
          (Rewriting.free formula :: Gamma.map Rewriting.shift).toFinset ∧
        listedCertificateValid premise premiseCertificate
  | .exs Gamma formula witness premise, .unary premiseCertificate =>
      ∃⁰ formula ∈ Gamma ∧
        premise.conclusionList.toFinset =
          (formula/[witness] :: Gamma).toFinset ∧
        listedCertificateValid premise premiseCertificate
  | .wk Gamma premise, .unary premiseCertificate =>
      premise.conclusionList.toFinset ⊆ Gamma.toFinset ∧
        listedCertificateValid premise premiseCertificate
  | .shift Gamma premise, .unary premiseCertificate =>
      Gamma.toFinset =
          (premise.conclusionList.map Rewriting.shift).toFinset ∧
        listedCertificateValid premise premiseCertificate
  | .cut Gamma formula left right,
      .binary leftCertificate rightCertificate =>
      left.conclusionList.toFinset = (formula :: Gamma).toFinset ∧
        right.conclusionList.toFinset = (∼formula :: Gamma).toFinset ∧
        listedCertificateValid left leftCertificate ∧
        listedCertificateValid right rightCertificate
  | _, _ => False

def listedCertificateValidTrace :
    ListedCheckedPAProofTree -> StructuralValidityCertificate -> Bool × Nat
  | .closed Gamma formula, .leaf =>
      traceAnd (formulaMemTrace formula Gamma)
        (formulaMemTrace (∼formula) Gamma)
  | .axm Gamma sentence, .axiomCert certificate =>
      traceAnd (guardedAxiomSentenceEqTrace certificate sentence)
        (formulaMemTrace
          (Rewriting.emb sentence : LO.FirstOrder.ArithmeticProposition) Gamma)
  | .verum Gamma, .leaf =>
      formulaMemTrace (⊤ : LO.FirstOrder.ArithmeticProposition) Gamma
  | .and Gamma leftFormula rightFormula left right,
      .binary leftCertificate rightCertificate =>
      traceAnd (formulaMemTrace (leftFormula ⋏ rightFormula) Gamma)
        (traceAnd
          (formulaSetEqTrace left.conclusionList (leftFormula :: Gamma))
          (traceAnd
            (formulaSetEqTrace right.conclusionList (rightFormula :: Gamma))
            (traceAnd
              (listedCertificateValidTrace left leftCertificate)
              (listedCertificateValidTrace right rightCertificate))))
  | .or Gamma leftFormula rightFormula premise,
      .unary premiseCertificate =>
      traceAnd (formulaMemTrace (leftFormula ⋎ rightFormula) Gamma)
        (traceAnd
          (formulaSetEqTrace premise.conclusionList
            (leftFormula :: rightFormula :: Gamma))
          (listedCertificateValidTrace premise premiseCertificate))
  | .all Gamma formula premise, .unary premiseCertificate =>
      traceAnd (formulaMemTrace (∀⁰ formula) Gamma)
        (traceAnd
          (formulaSetEqTrace premise.conclusionList
            (Rewriting.free formula :: Gamma.map Rewriting.shift))
          (listedCertificateValidTrace premise premiseCertificate))
  | .exs Gamma formula witness premise, .unary premiseCertificate =>
      traceAnd (formulaMemTrace (∃⁰ formula) Gamma)
        (traceAnd
          (formulaSetEqTrace premise.conclusionList
            (formula/[witness] :: Gamma))
          (listedCertificateValidTrace premise premiseCertificate))
  | .wk Gamma premise, .unary premiseCertificate =>
      traceAnd (formulaSubsetTrace premise.conclusionList Gamma)
        (listedCertificateValidTrace premise premiseCertificate)
  | .shift Gamma premise, .unary premiseCertificate =>
      traceAnd
        (formulaSetEqTrace Gamma
          (premise.conclusionList.map Rewriting.shift))
        (listedCertificateValidTrace premise premiseCertificate)
  | .cut Gamma formula left right,
      .binary leftCertificate rightCertificate =>
      traceAnd
        (formulaSetEqTrace left.conclusionList (formula :: Gamma))
        (traceAnd
          (formulaSetEqTrace right.conclusionList (∼formula :: Gamma))
          (traceAnd
            (listedCertificateValidTrace left leftCertificate)
            (listedCertificateValidTrace right rightCertificate)))
  | _, _ => (false, 1)

theorem listedCertificateValidTrace_result_eq_true_iff
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    (listedCertificateValidTrace tree certificate).1 = true ↔
      listedCertificateValid tree certificate := by
  induction tree generalizing certificate <;>
    cases certificate <;>
    simp [listedCertificateValidTrace, listedCertificateValid,
      formulaMemTrace_result_eq_true_iff,
      formulaSetEqTrace_result_eq_true_iff,
      formulaSubsetTrace_result_eq_true_iff,
      guardedAxiomSentenceEqTrace_result_eq_true_iff, *]

theorem listedCertificateValid_toChecked_iff
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    listedCertificateValid tree certificate ↔
      certificateValid tree.toChecked certificate := by
  induction tree generalizing certificate <;>
    cases certificate <;>
    simp [listedCertificateValid, certificateValid,
      ListedCheckedPAProofTree.toChecked,
      ListedCheckedPAProofTree.conclusionList, *]

theorem listedCertificateValidTrace_toChecked_iff
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    (listedCertificateValidTrace tree certificate).1 = true ↔
      certificateValid tree.toChecked certificate := by
  rw [listedCertificateValidTrace_result_eq_true_iff,
    listedCertificateValid_toChecked_iff]

#print axioms listedCertificateValidTrace_result_eq_true_iff
#print axioms listedCertificateValidTrace_toChecked_iff

end FoundationCompactListedCertificateVerifier
