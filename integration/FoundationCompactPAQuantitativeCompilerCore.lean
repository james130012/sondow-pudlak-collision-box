import integration.FoundationCompactCertifiedConjunction

/-!
# Root proof-producing core for quantitative PA compilation

This file works only with the real Foundation `Derivation2 PA` calculus and
the complete public proof-plus-certificate payload.  The bundle below carries
an actual derivation and an actual structural certificate; it has no field for
proof existence, soundness, or a length bound.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAQuantitativeCompilerCore

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationComputableCompactPAProofEncoder
open FoundationCompactListedCertifiedVerifier
open FoundationCompactListedCertifiedEncoder
open FoundationCompactDerivationSpecialization
open FoundationCompactCertifiedDerivationSpecialization
open FoundationCompactCertifiedModusPonens
open FoundationCompactCertifiedConjunction

/-- A real PA derivation paired with the exact certificate checked by the
public compact verifier.  There is no assumed proof or checker field. -/
structure CertifiedPAProof
    (formula : LO.FirstOrder.ArithmeticProposition) where
  derivation : LO.FirstOrder.Derivation2 PA {formula}
  certificate : StructuralValidityCertificate
  certificate_valid :
    certificateValid (CheckedPAProofTree.ofDerivation derivation) certificate

namespace CertifiedPAProof

def tree {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof formula) : CheckedPAProofTree :=
  CheckedPAProofTree.ofDerivation proof.derivation

def code {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof formula) : Nat :=
  canonicalPackedCertifiedPAProofCode proof.tree proof.certificate

def payloadLength {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof formula) : Nat :=
  packedPayloadLength proof.code

@[simp] theorem payloadLength_eq
    {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof formula) :
    proof.payloadLength =
      binaryProofLength proof.derivation +
        (binaryStructuralValidityCertificateCode proof.certificate).length := by
  simp [payloadLength, code, tree,
    canonicalBinaryCertifiedPAProofCode,
    canonicalBinaryProofCode_length, binaryProofLength]

/-- Transport along a kernel-checked syntactic equality.  This changes no
proof tree, certificate, code, or length. -/
def cast
    {source target : LO.FirstOrder.ArithmeticProposition}
    (formulaEq : source = target)
    (proof : CertifiedPAProof source) : CertifiedPAProof target := by
  subst target
  exact proof

@[simp] theorem cast_code
    {source target : LO.FirstOrder.ArithmeticProposition}
    (formulaEq : source = target)
    (proof : CertifiedPAProof source) :
    (cast formulaEq proof).code = proof.code := by
  subst target
  rfl

@[simp] theorem cast_payloadLength
    {source target : LO.FirstOrder.ArithmeticProposition}
    (formulaEq : source = target)
    (proof : CertifiedPAProof source) :
    (cast formulaEq proof).payloadLength = proof.payloadLength := by
  subst target
  rfl

theorem verifier_eq_true
    {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof formula) :
    listedCompactCertifiedPAProofVerifier proof.code
      (compactFormulaCode formula) = true := by
  apply listedCompactCertifiedPAProofVerifier_eq_true_of_certifiedTree
  · exact proof.certificate_valid
  · exact CheckedPAProofTree.conclusion_ofDerivation proof.derivation

/-- A PA axiom certificate produces an actual one-node PA proof. -/
def ofAxiom (axiomCertificate : PAAxiomCertificate) :
    CertifiedPAProof
      (Rewriting.emb axiomCertificate.sentence :
        LO.FirstOrder.ArithmeticProposition) where
  derivation := LO.FirstOrder.Derivation2.axm axiomCertificate.sentence
    axiomCertificate.sentence_mem_PA (by simp)
  certificate := .axiomCert axiomCertificate
  certificate_valid := by
    simp [certificateValid, CheckedPAProofTree.ofDerivation,
      PAAxiomCertificate.sentence]

def axiomSyntaxBudget (axiomCertificate : PAAxiomCertificate) : Nat :=
  (binaryFormulaCode
      (Rewriting.emb axiomCertificate.sentence :
        LO.FirstOrder.ArithmeticProposition)).length +
    (binaryStructuralValidityCertificateCode
      (.axiomCert axiomCertificate)).length + 1

theorem ofAxiom_payloadLength_le
    (axiomCertificate : PAAxiomCertificate) :
    (ofAxiom axiomCertificate).payloadLength <=
      32 + 10 * axiomSyntaxBudget axiomCertificate := by
  let axiomFormula :=
    (Rewriting.emb axiomCertificate.sentence :
      LO.FirstOrder.ArithmeticProposition)
  have hsequent := binarySequentCode_length_le_three_formula_budget
    {axiomFormula} axiomFormula axiomFormula axiomFormula (by simp)
  have htag1 : (binaryNatCode 1).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  rw [payloadLength_eq]
  simp only [ofAxiom, binaryProofLength, binaryDerivationCode,
    List.length_append]
  change _ <= 32 + 10 * axiomSyntaxBudget axiomCertificate
  dsimp only [axiomSyntaxBudget, axiomFormula] at hsequent ⊢
  omega

/-- The one-node proof of truth used by finite conjunction matrices. -/
def verumProof :
    CertifiedPAProof (⊤ : LO.FirstOrder.ArithmeticProposition) where
  derivation := LO.FirstOrder.Derivation2.verum (by simp)
  certificate := .leaf
  certificate_valid := by
    simp [CheckedPAProofTree.ofDerivation, certificateValid]

def verumSyntaxBudget : Nat :=
  (binaryFormulaCode
    (⊤ : LO.FirstOrder.ArithmeticProposition)).length + 1

theorem verumProof_payloadLength_le :
    verumProof.payloadLength <= 48 + 9 * verumSyntaxBudget := by
  let truth := (⊤ : LO.FirstOrder.ArithmeticProposition)
  have hsequent := binarySequentCode_length_le_three_formula_budget
    {truth} truth truth truth (by simp)
  have htag0 : (binaryNatCode 0).length <= 16 := by decide
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  rw [payloadLength_eq]
  simp only [verumProof, binaryProofLength, binaryDerivationCode,
    binaryStructuralValidityCertificateCode, List.length_append]
  change _ <= 48 + 9 * verumSyntaxBudget
  dsimp only [verumSyntaxBudget, truth] at hsequent ⊢
  omega

theorem verumProof_verifier_eq_true :
    listedCompactCertifiedPAProofVerifier verumProof.code
      (compactFormulaCode
        (⊤ : LO.FirstOrder.ArithmeticProposition)) = true :=
  verumProof.verifier_eq_true

/-- Explicit universal instantiation in the real sequent calculus. -/
def specialize
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (proof : CertifiedPAProof (∀⁰ formula))
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof (formula/[witness]) where
  derivation := specializeDerivation proof.derivation witness
  certificate := specializeCertificate proof.certificate
  certificate_valid :=
    specializeCertificate_valid proof.derivation witness proof.certificate
      proof.certificate_valid

def specializationScale
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  (binaryFormulaCode formula).length +
    (binaryTermCode witness).length + 1

theorem specialize_payloadLength_le
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (proof : CertifiedPAProof (∀⁰ formula))
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (specialize proof witness).payloadLength <=
      proof.payloadLength + 192 +
        2048 * specializationScale formula witness *
          specializationScale formula witness *
          specializationScale formula witness := by
  have hproof := specializeDerivation_binaryProofLength_le_cubic
    proof.derivation witness
  have hcertificate := specializeCertificate_code_length_le
    proof.certificate
  rw [payloadLength_eq, payloadLength_eq]
  change
    binaryProofLength
        (specializeDerivation proof.derivation witness) +
      (binaryStructuralValidityCertificateCode
        (specializeCertificate proof.certificate)).length <= _
  dsimp only [specializationScale] at hproof ⊢
  omega

def specializationCost
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  192 + 2048 * specializationScale formula witness *
    specializationScale formula witness *
    specializationScale formula witness

theorem specialize_payloadLength_le_cost
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (proof : CertifiedPAProof (∀⁰ formula))
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (specialize proof witness).payloadLength <=
      proof.payloadLength + specializationCost formula witness := by
  simpa [specializationCost, Nat.add_assoc] using
    specialize_payloadLength_le proof witness

/-- Explicit modus ponens in the real sequent calculus. -/
def modusPonens
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : CertifiedPAProof (antecedent 🡒 consequent))
    (antecedentProof : CertifiedPAProof antecedent) :
    CertifiedPAProof consequent where
  derivation := modusPonensDerivation implicationProof.derivation
    antecedentProof.derivation
  certificate := modusPonensCertificate implicationProof.certificate
    antecedentProof.certificate
  certificate_valid := modusPonensCertificate_valid
    implicationProof.derivation antecedentProof.derivation
    implicationProof.certificate antecedentProof.certificate
    implicationProof.certificate_valid antecedentProof.certificate_valid

theorem modusPonens_payloadLength_le
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : CertifiedPAProof (antecedent 🡒 consequent))
    (antecedentProof : CertifiedPAProof antecedent) :
    (modusPonens implicationProof antecedentProof).payloadLength <=
      implicationProof.payloadLength + antecedentProof.payloadLength +
        240 + 34 * modusPonensSyntaxBudget antecedent consequent := by
  have hproof := modusPonensDerivation_binaryProofLength_le
    implicationProof.derivation antecedentProof.derivation
  have hcertificate := modusPonensCertificate_code_length_le
    implicationProof.certificate antecedentProof.certificate
  rw [payloadLength_eq, payloadLength_eq, payloadLength_eq]
  change
    binaryProofLength
        (modusPonensDerivation implicationProof.derivation
          antecedentProof.derivation) +
      (binaryStructuralValidityCertificateCode
        (modusPonensCertificate implicationProof.certificate
          antecedentProof.certificate)).length <= _
  omega

/-- The concrete five-node conjunction derivation. -/
def conjunctionDerivation
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : LO.FirstOrder.Derivation2 PA {left})
    (rightProof : LO.FirstOrder.Derivation2 PA {right}) :
    LO.FirstOrder.Derivation2 PA {left ⋏ right} :=
  LO.FirstOrder.Derivation2.and (Γ := {left ⋏ right})
    (φ := left) (ψ := right) (by simp)
    (LO.FirstOrder.Derivation2.wk leftProof (by simp))
    (LO.FirstOrder.Derivation2.wk rightProof (by simp))

@[simp] theorem ofDerivation_conjunctionDerivation
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : LO.FirstOrder.Derivation2 PA {left})
    (rightProof : LO.FirstOrder.Derivation2 PA {right}) :
    CheckedPAProofTree.ofDerivation
        (conjunctionDerivation leftProof rightProof) =
      checkedConjunctionTree left right
        (CheckedPAProofTree.ofDerivation leftProof)
        (CheckedPAProofTree.ofDerivation rightProof) := by
  rfl

theorem conjunctionDerivation_binaryProofLength_le
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : LO.FirstOrder.Derivation2 PA {left})
    (rightProof : LO.FirstOrder.Derivation2 PA {right}) :
    binaryProofLength (conjunctionDerivation leftProof rightProof) <=
      binaryProofLength leftProof + binaryProofLength rightProof + 96 +
        11 * conjunctionSyntaxBudget left right := by
  let conjunctionFormula := left ⋏ right
  let syntaxBudget := conjunctionSyntaxBudget left right
  have hbudget : syntaxBudget =
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length +
        (binaryFormulaCode conjunctionFormula).length := by
    rfl
  have hseq
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (hmem : ∀ candidate ∈ Gamma,
        candidate = left ∨ candidate = right ∨
          candidate = conjunctionFormula) :
      (binarySequentCode Gamma).length <=
        (binaryNatCode 3).length + 3 * syntaxBudget := by
    simpa [hbudget] using
      binarySequentCode_length_le_three_formula_budget
        Gamma left right conjunctionFormula hmem
  have hseqRoot := hseq {conjunctionFormula} (by simp)
  have hseqLeft := hseq (insert left {conjunctionFormula}) (by simp)
  have hseqRight := hseq (insert right {conjunctionFormula}) (by simp)
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  have hleft : (binaryFormulaCode left).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  have hright : (binaryFormulaCode right).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  simp only [conjunctionDerivation, binaryProofLength,
    binaryDerivationCode, List.length_append]
  dsimp only [conjunctionFormula] at hseqRoot hseqLeft hseqRight
  change _ <= (binaryDerivationCode leftProof).length +
    (binaryDerivationCode rightProof).length + 96 + 11 * syntaxBudget
  omega

/-- Explicit conjunction introduction. -/
def conjunction
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : CertifiedPAProof left)
    (rightProof : CertifiedPAProof right) :
    CertifiedPAProof (left ⋏ right) where
  derivation := conjunctionDerivation leftProof.derivation
    rightProof.derivation
  certificate := conjunctionCertificate leftProof.certificate
    rightProof.certificate
  certificate_valid := by
    rw [ofDerivation_conjunctionDerivation]
    exact
      checkedConjunctionCertificate_valid
        (CheckedPAProofTree.ofDerivation leftProof.derivation)
        (CheckedPAProofTree.ofDerivation rightProof.derivation)
        leftProof.certificate rightProof.certificate
        (CheckedPAProofTree.conclusion_ofDerivation leftProof.derivation)
        (CheckedPAProofTree.conclusion_ofDerivation rightProof.derivation)
        leftProof.certificate_valid rightProof.certificate_valid

theorem conjunction_payloadLength_le
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : CertifiedPAProof left)
    (rightProof : CertifiedPAProof right) :
    (conjunction leftProof rightProof).payloadLength <=
      leftProof.payloadLength + rightProof.payloadLength + 144 +
        11 * conjunctionSyntaxBudget left right := by
  have hproof := conjunctionDerivation_binaryProofLength_le
    leftProof.derivation rightProof.derivation
  have hcertificate := conjunctionCertificate_code_length_le
    leftProof.certificate rightProof.certificate
  rw [payloadLength_eq, payloadLength_eq, payloadLength_eq]
  change
    binaryProofLength
        (conjunctionDerivation leftProof.derivation
          rightProof.derivation) +
      (binaryStructuralValidityCertificateCode
        (conjunctionCertificate leftProof.certificate
          rightProof.certificate)).length <= _
  omega

/-- The concrete two-node existential-introduction derivation. -/
def existsIntroDerivation
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bodyProof : LO.FirstOrder.Derivation2 PA {formula/[witness]}) :
    LO.FirstOrder.Derivation2 PA {∃⁰ formula} :=
  LO.FirstOrder.Derivation2.exs (Γ := {∃⁰ formula})
    (φ := formula) (by simp) witness
    (LO.FirstOrder.Derivation2.wk bodyProof (by simp))

def existsIntroCertificate
    (bodyCertificate : StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .unary (.unary bodyCertificate)

def existsIntroSyntaxBudget
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  (binaryFormulaCode formula).length +
    (binaryFormulaCode (formula/[witness])).length +
    (binaryFormulaCode (∃⁰ formula)).length +
    (binaryTermCode witness).length + 1

theorem existsIntroDerivation_binaryProofLength_le
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bodyProof : LO.FirstOrder.Derivation2 PA {formula/[witness]}) :
    binaryProofLength (existsIntroDerivation witness bodyProof) <=
      binaryProofLength bodyProof + 64 +
        14 * existsIntroSyntaxBudget formula witness := by
  let instantiated := formula/[witness]
  let existential := ∃⁰ formula
  let syntaxBudget := existsIntroSyntaxBudget formula witness
  have hbudget : syntaxBudget =
      (binaryFormulaCode formula).length +
        (binaryFormulaCode instantiated).length +
        (binaryFormulaCode existential).length +
        (binaryTermCode witness).length + 1 := by
    rfl
  have hseq
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (hmem : ∀ candidate ∈ Gamma,
        candidate = instantiated ∨ candidate = existential ∨
          candidate = existential) :
      (binarySequentCode Gamma).length <=
        (binaryNatCode 3).length +
          3 * ((binaryFormulaCode instantiated).length +
            (binaryFormulaCode existential).length +
            (binaryFormulaCode existential).length) :=
    binarySequentCode_length_le_three_formula_budget
      Gamma instantiated existential existential hmem
  have hseqRoot := hseq {existential} (by simp)
  have hseqPremise := hseq (insert instantiated {existential}) (by simp)
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  have htag6 : (binaryNatCode 6).length <= 16 := by decide
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  simp only [existsIntroDerivation, binaryProofLength,
    binaryDerivationCode, List.length_append]
  dsimp only [instantiated, existential] at hseqRoot hseqPremise
  change _ <= (binaryDerivationCode bodyProof).length + 64 +
    14 * syntaxBudget
  dsimp only [syntaxBudget, existsIntroSyntaxBudget,
    instantiated, existential] at *
  omega

theorem existsIntroCertificate_code_length_le
    (bodyCertificate : StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (existsIntroCertificate bodyCertificate)).length <=
      (binaryStructuralValidityCertificateCode bodyCertificate).length + 32 := by
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  simp only [existsIntroCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

/-- Explicit existential introduction with a concrete witness term. -/
def existsIntro
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bodyProof : CertifiedPAProof (formula/[witness])) :
    CertifiedPAProof (∃⁰ formula) where
  derivation := existsIntroDerivation witness bodyProof.derivation
  certificate := existsIntroCertificate bodyProof.certificate
  certificate_valid := by
    have hconclusion :=
      CheckedPAProofTree.conclusion_ofDerivation bodyProof.derivation
    simp [existsIntroDerivation, existsIntroCertificate,
      CheckedPAProofTree.ofDerivation,
      CheckedPAProofTree.conclusion, certificateValid,
      bodyProof.certificate_valid]
    change (CheckedPAProofTree.ofDerivation bodyProof.derivation).conclusion ⊆
      insert (formula/[witness]) {∃⁰ formula}
    rw [hconclusion]
    simp

theorem existsIntro_payloadLength_le
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bodyProof : CertifiedPAProof (formula/[witness])) :
    (existsIntro witness bodyProof).payloadLength <=
      bodyProof.payloadLength + 96 +
        14 * existsIntroSyntaxBudget formula witness := by
  have hproof := existsIntroDerivation_binaryProofLength_le
    witness bodyProof.derivation
  have hcertificate := existsIntroCertificate_code_length_le
    bodyProof.certificate
  rw [payloadLength_eq, payloadLength_eq]
  change
    binaryProofLength
        (existsIntroDerivation witness bodyProof.derivation) +
      (binaryStructuralValidityCertificateCode
        (existsIntroCertificate bodyProof.certificate)).length <= _
  omega

/-! ## First concrete arithmetic compiler primitive -/

def equalityReflexivityBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 = #0”

def equalityReflexivityAxiomProof :
    CertifiedPAProof (∀⁰ equalityReflexivityBody) := by
  simpa [equalityReflexivityBody, PAAxiomCertificate.sentence] using
    (ofAxiom .eqRefl)

/-- For every concrete term, emit a real certified PA proof of `t = t`. -/
def proveEqualityReflexivity
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof (equalityReflexivityBody/[term]) :=
  specialize equalityReflexivityAxiomProof term

theorem proveEqualityReflexivity_verifier_eq_true
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier
      (proveEqualityReflexivity term).code
      (compactFormulaCode (“!!term = !!term” :
        LO.FirstOrder.ArithmeticProposition)) = true := by
  simpa [equalityReflexivityBody] using
    (proveEqualityReflexivity term).verifier_eq_true

theorem proveEqualityReflexivity_payloadLength_le
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveEqualityReflexivity term).payloadLength <=
      equalityReflexivityAxiomProof.payloadLength + 192 +
        2048 * specializationScale equalityReflexivityBody term *
          specializationScale equalityReflexivityBody term *
          specializationScale equalityReflexivityBody term := by
  simpa [proveEqualityReflexivity] using
    specialize_payloadLength_le equalityReflexivityAxiomProof term

def equalitySymmetryOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ (#1 = #0 → #0 = #1)”

def equalitySymmetryAxiomProof :
    CertifiedPAProof (∀⁰ equalitySymmetryOuterBody) := by
  simpa [equalitySymmetryOuterBody, PAAxiomCertificate.sentence] using
    (ofAxiom .eqSymm)

def equalitySymmetryAfterFirst
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :=
  specialize equalitySymmetryAxiomProof left

def equalitySymmetryInnerBody
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!!(Rew.bShift left) = #0 → #0 = !!(Rew.bShift left)”

theorem equalitySymmetryAfterFirst_formula
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    equalitySymmetryOuterBody/[left] =
      ∀⁰ equalitySymmetryInnerBody left := by
  have hterm :
      ((Rew.subst ![left]).q)
          (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) =
        Rew.bShift left := by
    simpa using
      (Rew.q_bvar_succ (Rew.subst ![left]) (0 : Fin 1))
  simp [equalitySymmetryOuterBody, equalitySymmetryInnerBody, hterm]

def equalitySymmetryAfterFirstAsUniversal
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof (∀⁰ equalitySymmetryInnerBody left) :=
  cast (equalitySymmetryAfterFirst_formula left)
    (equalitySymmetryAfterFirst left)

def equalitySymmetryImplicationRaw
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof ((equalitySymmetryInnerBody left)/[right]) :=
  specialize (equalitySymmetryAfterFirstAsUniversal left) right

theorem equalitySymmetryImplicationRaw_formula
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (equalitySymmetryInnerBody left)/[right] =
      (“!!left = !!right → !!right = !!left” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [equalitySymmetryInnerBody]

def equalitySymmetryImplication
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!left = !!right → !!right = !!left” :
        LO.FirstOrder.ArithmeticProposition) :=
  cast (equalitySymmetryImplicationRaw_formula left right)
    (equalitySymmetryImplicationRaw left right)

theorem equalitySymmetryImplication_payloadLength_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (equalitySymmetryImplication left right).payloadLength <=
      equalitySymmetryAxiomProof.payloadLength +
        specializationCost equalitySymmetryOuterBody left +
        specializationCost (equalitySymmetryInnerBody left) right := by
  have hfirst := specialize_payloadLength_le_cost
    equalitySymmetryAxiomProof left
  have hsecond := specialize_payloadLength_le_cost
    (equalitySymmetryAfterFirstAsUniversal left) right
  have himplicationCast :
      (equalitySymmetryImplication left right).payloadLength =
        (equalitySymmetryImplicationRaw left right).payloadLength := by
    change
      (cast (equalitySymmetryImplicationRaw_formula left right)
        (equalitySymmetryImplicationRaw left right)).payloadLength = _
    exact cast_payloadLength _ _
  rw [himplicationCast]
  change
    (specialize (equalitySymmetryAfterFirstAsUniversal left)
        right).payloadLength <= _
  have hfirstCast :
      (equalitySymmetryAfterFirstAsUniversal left).payloadLength =
        (equalitySymmetryAfterFirst left).payloadLength := by
    change
      (cast (equalitySymmetryAfterFirst_formula left)
        (equalitySymmetryAfterFirst left)).payloadLength = _
    exact cast_payloadLength _ _
  have hfirstUniversal :
      (equalitySymmetryAfterFirstAsUniversal left).payloadLength <=
        equalitySymmetryAxiomProof.payloadLength +
          specializationCost equalitySymmetryOuterBody left := by
    calc
      (equalitySymmetryAfterFirstAsUniversal left).payloadLength =
          (equalitySymmetryAfterFirst left).payloadLength := hfirstCast
      _ = (specialize equalitySymmetryAxiomProof left).payloadLength := rfl
      _ <= _ := hfirst
  calc
    (equalitySymmetryImplicationRaw left right).payloadLength =
        (specialize (equalitySymmetryAfterFirstAsUniversal left)
          right).payloadLength := rfl
    _ <= (equalitySymmetryAfterFirstAsUniversal left).payloadLength +
        specializationCost (equalitySymmetryInnerBody left) right := hsecond
    _ <= (equalitySymmetryAxiomProof.payloadLength +
          specializationCost equalitySymmetryOuterBody left) +
        specializationCost (equalitySymmetryInnerBody left) right :=
      Nat.add_le_add_right hfirstUniversal _
    _ = _ := by omega

/-- Turn any certified proof of `left = right` into one of `right = left`. -/
def proveEqualitySymmetry
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (equalityProof : CertifiedPAProof
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!right = !!left” : LO.FirstOrder.ArithmeticProposition) :=
  modusPonens (equalitySymmetryImplication left right) equalityProof

theorem proveEqualitySymmetry_verifier_eq_true
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (equalityProof : CertifiedPAProof
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    listedCompactCertifiedPAProofVerifier
      (proveEqualitySymmetry left right equalityProof).code
      (compactFormulaCode (“!!right = !!left” :
        LO.FirstOrder.ArithmeticProposition)) = true :=
  (proveEqualitySymmetry left right equalityProof).verifier_eq_true

theorem proveEqualitySymmetry_payloadLength_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (equalityProof : CertifiedPAProof
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    (proveEqualitySymmetry left right equalityProof).payloadLength <=
      (equalitySymmetryImplication left right).payloadLength +
        equalityProof.payloadLength + 240 +
        34 * modusPonensSyntaxBudget
          (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
          (“!!right = !!left” : LO.FirstOrder.ArithmeticProposition) := by
  exact modusPonens_payloadLength_le
    (equalitySymmetryImplication left right) equalityProof

def addZeroBody : LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 + 0 = #0”

def addZeroAxiomProof : CertifiedPAProof (∀⁰ addZeroBody) := by
  simpa [addZeroBody, PAAxiomCertificate.sentence] using
    (ofAxiom .addZero)

/-- For every concrete term, emit a real certified PA proof of `t + 0 = t`. -/
def proveAddZero
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof (addZeroBody/[term]) :=
  specialize addZeroAxiomProof term

theorem proveAddZero_verifier_eq_true
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier (proveAddZero term).code
      (compactFormulaCode (“!!term + 0 = !!term” :
        LO.FirstOrder.ArithmeticProposition)) = true :=
  by
    simpa [addZeroBody] using (proveAddZero term).verifier_eq_true

theorem proveAddZero_payloadLength_le
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveAddZero term).payloadLength <=
      addZeroAxiomProof.payloadLength + 192 +
        2048 * specializationScale addZeroBody term *
          specializationScale addZeroBody term *
          specializationScale addZeroBody term := by
  simpa [proveAddZero] using
    specialize_payloadLength_le addZeroAxiomProof term

def mulZeroBody : LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 * 0 = 0”

def mulZeroAxiomProof : CertifiedPAProof (∀⁰ mulZeroBody) := by
  simpa [mulZeroBody, PAAxiomCertificate.sentence] using
    (ofAxiom .mulZero)

def proveMulZero
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof (mulZeroBody/[term]) :=
  specialize mulZeroAxiomProof term

theorem proveMulZero_verifier_eq_true
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier (proveMulZero term).code
      (compactFormulaCode (“!!term * 0 = 0” :
        LO.FirstOrder.ArithmeticProposition)) = true := by
  simpa [mulZeroBody] using (proveMulZero term).verifier_eq_true

theorem proveMulZero_payloadLength_le
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveMulZero term).payloadLength <=
      mulZeroAxiomProof.payloadLength +
        specializationCost mulZeroBody term := by
  simpa [proveMulZero] using
    specialize_payloadLength_le_cost mulZeroAxiomProof term

def mulOneBody : LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 * 1 = #0”

def mulOneAxiomProof : CertifiedPAProof (∀⁰ mulOneBody) := by
  simpa [mulOneBody, PAAxiomCertificate.sentence] using
    (ofAxiom .mulOne)

def proveMulOne
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof (mulOneBody/[term]) :=
  specialize mulOneAxiomProof term

theorem proveMulOne_verifier_eq_true
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier (proveMulOne term).code
      (compactFormulaCode (“!!term * 1 = !!term” :
        LO.FirstOrder.ArithmeticProposition)) = true := by
  simpa [mulOneBody] using (proveMulOne term).verifier_eq_true

theorem proveMulOne_payloadLength_le
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveMulOne term).payloadLength <=
      mulOneAxiomProof.payloadLength +
        specializationCost mulOneBody term := by
  simpa [proveMulOne] using
    specialize_payloadLength_le_cost mulOneAxiomProof term

end CertifiedPAProof

#print axioms CertifiedPAProof.verifier_eq_true
#print axioms CertifiedPAProof.ofAxiom
#print axioms CertifiedPAProof.specialize
#print axioms CertifiedPAProof.modusPonens
#print axioms CertifiedPAProof.conjunction
#print axioms CertifiedPAProof.existsIntro
#print axioms CertifiedPAProof.ofAxiom_payloadLength_le
#print axioms CertifiedPAProof.verumProof_payloadLength_le
#print axioms CertifiedPAProof.verumProof_verifier_eq_true
#print axioms CertifiedPAProof.specialize_payloadLength_le
#print axioms CertifiedPAProof.modusPonens_payloadLength_le
#print axioms CertifiedPAProof.conjunction_payloadLength_le
#print axioms CertifiedPAProof.existsIntro_payloadLength_le
#print axioms CertifiedPAProof.proveEqualityReflexivity_verifier_eq_true
#print axioms CertifiedPAProof.proveEqualityReflexivity_payloadLength_le
#print axioms CertifiedPAProof.proveEqualitySymmetry_verifier_eq_true
#print axioms CertifiedPAProof.proveEqualitySymmetry_payloadLength_le
#print axioms CertifiedPAProof.proveAddZero_verifier_eq_true
#print axioms CertifiedPAProof.proveAddZero_payloadLength_le
#print axioms CertifiedPAProof.proveMulZero_verifier_eq_true
#print axioms CertifiedPAProof.proveMulZero_payloadLength_le
#print axioms CertifiedPAProof.proveMulOne_verifier_eq_true
#print axioms CertifiedPAProof.proveMulOne_payloadLength_le

end FoundationCompactPAQuantitativeCompilerCore
