import integration.FoundationCompactPAAxiomCertificate

/-!
# One honest compact code for a PA proof and its local certificate

The structural certificate is part of the proof string and therefore part of
the length coordinate.  No unbounded auxiliary witness is hidden behind the
bounded proof predicate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertifiedPAProof

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate

def binaryCertifiedPAProofCode
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) : List Bool :=
  tree.binaryCode ++
    binaryStructuralValidityCertificateCode certificate

def certifiedPAProofParseWeight
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) : Nat :=
  max tree.parseWeight
    (structuralCertificateParseWeight certificate)

def decodeCompactCertifiedPAProof
    (fuel : Nat) (bits : List Bool) :
    Option
      ((CheckedPAProofTree × StructuralValidityCertificate) × List Bool) := do
  let (tree, bits) ← decodeCompactProof fuel bits
  let (certificate, bits) ←
    decodeStructuralValidityCertificate fuel bits
  pure ((tree, certificate), bits)

theorem decodeCompactCertifiedPAProof_binaryCode_append
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (fuel : Nat)
    (hfuel : certifiedPAProofParseWeight tree certificate < fuel)
    (suffix : List Bool) :
    decodeCompactCertifiedPAProof fuel
        (binaryCertifiedPAProofCode tree certificate ++ suffix) =
      some ((tree, certificate), suffix) := by
  have htree : tree.parseWeight < fuel := by
    exact lt_of_le_of_lt (Nat.le_max_left _ _) hfuel
  have hcertificate :
      structuralCertificateParseWeight certificate < fuel := by
    exact lt_of_le_of_lt (Nat.le_max_right _ _) hfuel
  simp [decodeCompactCertifiedPAProof, binaryCertifiedPAProofCode,
    decodeCompactProof_binaryCode_append tree fuel htree,
    decodeStructuralValidityCertificate_binaryCode_append
      certificate fuel hcertificate]

theorem certifiedPAProofParseWeight_le_binaryCode_length
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    certifiedPAProofParseWeight tree certificate ≤
      (binaryCertifiedPAProofCode tree certificate).length := by
  have htree := tree.parseWeight_le_binaryLength
  have hcertificate :=
    structuralCertificateParseWeight_le_binaryCode_length certificate
  simp only [certifiedPAProofParseWeight, binaryCertifiedPAProofCode,
    CheckedPAProofTree.binaryLength, List.length_append] at htree hcertificate ⊢
  exact max_le (htree.trans (Nat.le_add_right _ _))
    (hcertificate.trans (Nat.le_add_left _ _))

theorem decodeCompactCertifiedPAProof_binaryCode
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    decodeCompactCertifiedPAProof
        ((binaryCertifiedPAProofCode tree certificate).length + 1)
        (binaryCertifiedPAProofCode tree certificate) =
      some ((tree, certificate), []) := by
  have hfuel :
      certifiedPAProofParseWeight tree certificate <
        (binaryCertifiedPAProofCode tree certificate).length + 1 := by
    have hweight :=
      certifiedPAProofParseWeight_le_binaryCode_length tree certificate
    omega
  simpa using
    decodeCompactCertifiedPAProof_binaryCode_append tree certificate
      ((binaryCertifiedPAProofCode tree certificate).length + 1)
      hfuel []

def packedCertifiedPAProofCode
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) : Nat :=
  packBinaryString (binaryCertifiedPAProofCode tree certificate)

def decodeCompactPackedCertifiedPAProof
    (code : Nat) :
    Option (CheckedPAProofTree × StructuralValidityCertificate) := do
  let bits := code.bits
  guard (bits.getLast? = some true)
  let payload := bits.dropLast
  let (proof, suffix) ←
    decodeCompactCertifiedPAProof (payload.length + 1) payload
  guard suffix.isEmpty
  pure proof

@[simp] theorem decodeCompactPackedCertifiedPAProof_packedCode
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    decodeCompactPackedCertifiedPAProof
        (packedCertifiedPAProofCode tree certificate) =
      some (tree, certificate) := by
  simp [decodeCompactPackedCertifiedPAProof,
    packedCertifiedPAProofCode,
    decodeCompactCertifiedPAProof_binaryCode]

@[simp] theorem size_packedCertifiedPAProofCode
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    Nat.size (packedCertifiedPAProofCode tree certificate) =
      (binaryCertifiedPAProofCode tree certificate).length + 1 := by
  simp [packedCertifiedPAProofCode]

@[simp] theorem packedPayloadLength_packedCertifiedPAProofCode
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    packedPayloadLength (packedCertifiedPAProofCode tree certificate) =
      (binaryCertifiedPAProofCode tree certificate).length := by
  simp [packedPayloadLength]

def decodeCompactPackedFormula
    (code : Nat) : Option LO.FirstOrder.ArithmeticProposition := do
  let bits := code.bits
  guard (bits.getLast? = some true)
  let payload := bits.dropLast
  let (formula, suffix) ←
    decodeCompactFormula 0 (payload.length + 1) payload
  guard suffix.isEmpty
  pure formula

theorem decodeCompactFormula_binaryFormulaCode
    (formula : LO.FirstOrder.ArithmeticProposition) :
    decodeCompactFormula 0
        ((binaryFormulaCode formula).length + 1)
        (binaryFormulaCode formula) = some (formula, []) := by
  have hfuel :
      formulaSymbolCount formula <
        (binaryFormulaCode formula).length + 1 := by
    have hweight := formulaSymbolCount_le_binaryFormulaCode_length formula
    omega
  simpa using
    decodeCompactFormula_binaryFormulaCode_append formula
      ((binaryFormulaCode formula).length + 1) hfuel []

@[simp] theorem decodeCompactPackedFormula_compactFormulaCode
    (formula : LO.FirstOrder.ArithmeticProposition) :
    decodeCompactPackedFormula (compactFormulaCode formula) =
      some formula := by
  simp [decodeCompactPackedFormula, compactFormulaCode,
    decodeCompactFormula_binaryFormulaCode]

/-- Exact standard-model relation checked by the certified proof decoder. -/
def CompactCertifiedPAProofChecks
    (code formulaCode : Nat) : Prop :=
  ∃ (tree : CheckedPAProofTree)
      (certificate : StructuralValidityCertificate)
      (formula : LO.FirstOrder.ArithmeticProposition),
    decodeCompactPackedCertifiedPAProof code =
        some (tree, certificate) ∧
      certificateValid tree certificate ∧
      tree.conclusion = {formula} ∧
      compactFormulaCode formula = formulaCode

/-- Executable verifier for the exact relation above.  The final equality
rejects noncanonical encodings of an otherwise decodable formula. -/
def compactCertifiedPAProofVerifier
    (code formulaCode : Nat) : Bool :=
  match decodeCompactPackedCertifiedPAProof code,
      decodeCompactPackedFormula formulaCode with
  | some (tree, certificate), some formula =>
      certificateValidBool tree certificate &&
        decide (tree.conclusion = {formula}) &&
        decide (compactFormulaCode formula = formulaCode)
  | _, _ => false

theorem compactCertifiedPAProofVerifier_eq_true_of_checks
    {code formulaCode : Nat}
    (hcheck : CompactCertifiedPAProofChecks code formulaCode) :
    compactCertifiedPAProofVerifier code formulaCode = true := by
  rcases hcheck with
    ⟨tree, certificate, formula, hdecode,
      hcertificate, hconclusion, hformulaCode⟩
  subst formulaCode
  have hcertificateBool :
      certificateValidBool tree certificate = true :=
    (certificateValidBool_eq_true_iff tree certificate).2 hcertificate
  simp [compactCertifiedPAProofVerifier, hdecode,
    hcertificateBool, hconclusion]

theorem checks_of_compactCertifiedPAProofVerifier_eq_true
    {code formulaCode : Nat}
    (haccept : compactCertifiedPAProofVerifier code formulaCode = true) :
    CompactCertifiedPAProofChecks code formulaCode := by
  cases hproof : decodeCompactPackedCertifiedPAProof code with
  | none =>
      simp [compactCertifiedPAProofVerifier, hproof] at haccept
  | some proof =>
      rcases proof with ⟨tree, certificate⟩
      cases hformula : decodeCompactPackedFormula formulaCode with
      | none =>
          simp [compactCertifiedPAProofVerifier, hproof, hformula] at haccept
      | some formula =>
          have hconditions :
              certificateValid tree certificate ∧
                tree.conclusion = {formula} ∧
                compactFormulaCode formula = formulaCode := by
            simpa [compactCertifiedPAProofVerifier, hproof, hformula,
              certificateValidBool_eq_true_iff, and_assoc]
              using haccept
          exact ⟨tree, certificate, formula, hproof,
            hconditions.1, hconditions.2.1, hconditions.2.2⟩

theorem compactCertifiedPAProofVerifier_eq_true_iff
    (code formulaCode : Nat) :
    compactCertifiedPAProofVerifier code formulaCode = true ↔
      CompactCertifiedPAProofChecks code formulaCode := by
  exact ⟨checks_of_compactCertifiedPAProofVerifier_eq_true,
    compactCertifiedPAProofVerifier_eq_true_of_checks⟩

/-- The bound counts the complete certified proof payload, including every
local witness used to recognize PA axioms. -/
def EfficientCertifiedPAProofPredicate
    (bound formulaCode : Nat) : Prop :=
  ∃ code : Nat,
    packedPayloadLength code ≤ bound ∧
      CompactCertifiedPAProofChecks code formulaCode

theorem certifiedTree_checks
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (hcertificate : certificateValid tree certificate)
    (hconclusion : tree.conclusion = {formula}) :
    CompactCertifiedPAProofChecks
      (packedCertifiedPAProofCode tree certificate)
      (compactFormulaCode formula) := by
  exact ⟨tree, certificate, formula, by simp,
    hcertificate, hconclusion, rfl⟩

theorem EfficientCertifiedPAProofPredicate.mono
    {smaller larger formulaCode : Nat}
    (hbound : smaller ≤ larger)
    (hproof : EfficientCertifiedPAProofPredicate smaller formulaCode) :
    EfficientCertifiedPAProofPredicate larger formulaCode := by
  rcases hproof with ⟨code, hlength, hcheck⟩
  exact ⟨code, hlength.trans hbound, hcheck⟩

theorem derivation_to_efficientCertifiedPAProofPredicate
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (derivation : LO.FirstOrder.Derivation2 PA Gamma)
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hconclusion : Gamma = {formula}) :
    ∃ bound : Nat,
      EfficientCertifiedPAProofPredicate bound
        (compactFormulaCode formula) := by
  let tree := CheckedPAProofTree.ofDerivation derivation
  have hvalid : structurallyValid tree :=
    structurallyValid_ofDerivation derivation
  rcases exists_certificateValid tree hvalid with
    ⟨certificate, hcertificate⟩
  let bound := (binaryCertifiedPAProofCode tree certificate).length
  refine ⟨bound, packedCertifiedPAProofCode tree certificate, ?_, ?_⟩
  · simp [bound]
  · apply certifiedTree_checks tree certificate formula hcertificate
    simpa [tree] using hconclusion

theorem CompactCertifiedPAProofChecks.toDerivation
    {code : Nat}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hcheck : CompactCertifiedPAProofChecks code
      (compactFormulaCode formula)) :
    Nonempty (LO.FirstOrder.Derivation2 PA {formula}) := by
  rcases hcheck with
    ⟨tree, certificate, decodedFormula, _, hcertificate,
      hconclusion, hformulaCode⟩
  have hformula : decodedFormula = formula :=
    compactFormulaCode_injective hformulaCode
  subst hformula
  rcases structurallyValid_toDerivation tree
      (certificateValid_sound hcertificate) with
    ⟨derivation⟩
  exact ⟨LO.FirstOrder.Derivation2.cast derivation hconclusion⟩

theorem EfficientCertifiedPAProofPredicate.toDerivation
    {bound : Nat}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hproof : EfficientCertifiedPAProofPredicate bound
      (compactFormulaCode formula)) :
    Nonempty (LO.FirstOrder.Derivation2 PA {formula}) := by
  rcases hproof with ⟨code, _, hcheck⟩
  exact hcheck.toDerivation

end FoundationCompactCertifiedPAProof
