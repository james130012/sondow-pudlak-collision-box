import integration.FoundationCompactListedProofProjectionComplete

/-!
# Public list-preserving certified proof verifier

The local proof checks use only explicit bit/list traces.  This file proves
their exact equivalence to the original certified Foundation proof relation.
The separate decoder-runtime bound remains a later obligation.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedCertifiedVerifier

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactListedProofProjectionComplete
open FoundationCompactVerifierBitCostPrimitives
open FoundationCompactVerifierFormulaListChecks

def decodeCompactListedCertifiedPAProof
    (fuel : Nat) (bits : List Bool) :
    Option
      ((ListedCheckedPAProofTree × StructuralValidityCertificate) ×
        List Bool) := do
  let (tree, bits) <- decodeCompactListedProof fuel bits
  let (certificate, bits) <-
    decodeStructuralValidityCertificate fuel bits
  pure ((tree, certificate), bits)

theorem decodeCompactListedCertifiedPAProof_toChecked
    {fuel : Nat} {bits suffix : List Bool}
    {tree : ListedCheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    (hdecode : decodeCompactListedCertifiedPAProof fuel bits =
      some ((tree, certificate), suffix)) :
    decodeCompactCertifiedPAProof fuel bits =
      some ((tree.toChecked, certificate), suffix) := by
  cases htree : decodeCompactListedProof fuel bits with
  | none =>
      simp [decodeCompactListedCertifiedPAProof, htree] at hdecode
  | some treeResult =>
      rcases treeResult with ⟨decodedTree, afterTree⟩
      cases hcertificate :
          decodeStructuralValidityCertificate fuel afterTree with
      | none =>
          simp [decodeCompactListedCertifiedPAProof, htree, hcertificate]
            at hdecode
      | some certificateResult =>
          rcases certificateResult with
            ⟨decodedCertificate, afterCertificate⟩
          simp [decodeCompactListedCertifiedPAProof, htree, hcertificate]
            at hdecode
          rcases hdecode with ⟨⟨rfl, rfl⟩, rfl⟩
          have hcheckedTree := decodeCompactListedProof_toChecked htree
          simp [decodeCompactCertifiedPAProof, hcheckedTree, hcertificate]

def decodeCompactPackedListedCertifiedPAProof
    (code : Nat) :
    Option (ListedCheckedPAProofTree × StructuralValidityCertificate) := do
  let bits := code.bits
  guard (bits.getLast? = some true)
  let payload := bits.dropLast
  let (proof, suffix) <-
    decodeCompactListedCertifiedPAProof (payload.length + 1) payload
  guard suffix.isEmpty
  pure proof

theorem decodeCompactPackedListedCertifiedPAProof_toChecked
    {code : Nat} {tree : ListedCheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    (hdecode : decodeCompactPackedListedCertifiedPAProof code =
      some (tree, certificate)) :
    decodeCompactPackedCertifiedPAProof code =
      some (tree.toChecked, certificate) := by
  simp only [decodeCompactPackedListedCertifiedPAProof] at hdecode
  cases hlast : code.bits.getLast? with
  | none => simp [hlast] at hdecode
  | some lastBit =>
      cases lastBit with
      | false => simp [hlast] at hdecode
      | true =>
          cases hproof :
              decodeCompactListedCertifiedPAProof
                (code.bits.length - 1 + 1) code.bits.dropLast with
          | none => simp [hproof] at hdecode
          | some proofResult =>
              rcases proofResult with ⟨decodedProof, suffix⟩
              cases suffix with
              | cons head tail => simp [hproof, hlast] at hdecode
              | nil =>
                  rcases decodedProof with
                    ⟨decodedTree, decodedCertificate⟩
                  simp [hproof, hlast] at hdecode
                  rcases hdecode with ⟨rfl, rfl⟩
                  have hcheckedProof :=
                    decodeCompactListedCertifiedPAProof_toChecked hproof
                  simp [decodeCompactPackedCertifiedPAProof, hlast,
                    hcheckedProof]

def listedCertifiedPAProofLocalTrace
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (formulaCode : Nat) : Bool × Nat :=
  traceAnd (listedCertificateValidTrace tree certificate)
    (traceAnd
      (formulaSetEqTrace tree.conclusionList [formula])
      (natEqTrace (compactFormulaCode formula) formulaCode))

theorem listedCertifiedPAProofLocalTrace_result_eq_true_iff
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (formulaCode : Nat) :
    (listedCertifiedPAProofLocalTrace
        tree certificate formula formulaCode).1 = true ↔
      listedCertificateValid tree certificate ∧
        tree.conclusionList.toFinset = {formula} ∧
        compactFormulaCode formula = formulaCode := by
  simp [listedCertifiedPAProofLocalTrace,
    listedCertificateValidTrace_result_eq_true_iff,
    formulaSetEqTrace_result_eq_true_iff,
    natEqTrace_result_eq_true_iff]

def ListedCompactCertifiedPAProofChecks
    (code formulaCode : Nat) : Prop :=
  exists (tree : ListedCheckedPAProofTree)
      (certificate : StructuralValidityCertificate)
      (formula : LO.FirstOrder.ArithmeticProposition),
    decodeCompactPackedListedCertifiedPAProof code =
        some (tree, certificate) ∧
      listedCertificateValid tree certificate ∧
      tree.conclusionList.toFinset = {formula} ∧
      compactFormulaCode formula = formulaCode

def listedCompactCertifiedPAProofVerifier
    (code formulaCode : Nat) : Bool :=
  match decodeCompactPackedListedCertifiedPAProof code,
      decodeCompactPackedFormula formulaCode with
  | some (tree, certificate), some formula =>
      (listedCertifiedPAProofLocalTrace
        tree certificate formula formulaCode).1
  | _, _ => false

theorem listedCompactCertifiedPAProofVerifier_eq_true_iff
    (code formulaCode : Nat) :
    listedCompactCertifiedPAProofVerifier code formulaCode = true ↔
      ListedCompactCertifiedPAProofChecks code formulaCode := by
  constructor
  · intro haccept
    cases hproof : decodeCompactPackedListedCertifiedPAProof code with
    | none =>
        simp [listedCompactCertifiedPAProofVerifier, hproof] at haccept
    | some proof =>
        rcases proof with ⟨tree, certificate⟩
        cases hformula : decodeCompactPackedFormula formulaCode with
        | none =>
            simp [listedCompactCertifiedPAProofVerifier, hproof, hformula]
              at haccept
        | some formula =>
            have hlocal :=
              (listedCertifiedPAProofLocalTrace_result_eq_true_iff
                tree certificate formula formulaCode).mp
                (by simpa [listedCompactCertifiedPAProofVerifier,
                  hproof, hformula] using haccept)
            exact ⟨tree, certificate, formula, hproof,
              hlocal.1, hlocal.2.1, hlocal.2.2⟩
  · rintro ⟨tree, certificate, formula, hdecode, hcertificate,
      hconclusion, hformulaCode⟩
    subst formulaCode
    have hlocal :
        (listedCertifiedPAProofLocalTrace tree certificate formula
          (compactFormulaCode formula)).1 = true :=
      (listedCertifiedPAProofLocalTrace_result_eq_true_iff
        tree certificate formula (compactFormulaCode formula)).2
        ⟨hcertificate, hconclusion, rfl⟩
    simp [listedCompactCertifiedPAProofVerifier, hdecode, hlocal]

theorem ListedCompactCertifiedPAProofChecks.toChecked
    {code formulaCode : Nat}
    (hchecks : ListedCompactCertifiedPAProofChecks code formulaCode) :
    CompactCertifiedPAProofChecks code formulaCode := by
  rcases hchecks with
    ⟨tree, certificate, formula, hdecode, hcertificate,
      hconclusion, hformulaCode⟩
  refine ⟨tree.toChecked, certificate, formula,
    decodeCompactPackedListedCertifiedPAProof_toChecked hdecode,
    (listedCertificateValid_toChecked_iff tree certificate).mp hcertificate,
    ?_, hformulaCode⟩
  rw [ListedCheckedPAProofTree.toChecked_conclusion]
  exact hconclusion

theorem listedCompactCertifiedPAProofVerifier_toDerivation
    {code : Nat} {formula : LO.FirstOrder.ArithmeticProposition}
    (haccept : listedCompactCertifiedPAProofVerifier code
      (compactFormulaCode formula) = true) :
    Nonempty (LO.FirstOrder.Derivation2 PA {formula}) := by
  exact (listedCompactCertifiedPAProofVerifier_eq_true_iff _ _).mp haccept
    |>.toChecked.toDerivation

#print axioms decodeCompactPackedListedCertifiedPAProof_toChecked
#print axioms listedCompactCertifiedPAProofVerifier_eq_true_iff
#print axioms listedCompactCertifiedPAProofVerifier_toDerivation

end FoundationCompactListedCertifiedVerifier
