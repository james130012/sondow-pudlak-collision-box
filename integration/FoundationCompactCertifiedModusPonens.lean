import integration.FoundationCompactCertifiedDerivationSpecialization
import integration.FoundationCompactCertificateCanonicalDecodeLength

/-!
# Explicit certified modus ponens for concrete PA derivations

The compiler below emits the real sequent-calculus proof tree
`cut(wk(implication), and(wk(argument), closed))`.  It is the first bounded
proof-assembly primitive needed in Pudlak's quantitative diagonal argument.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertifiedModusPonens

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationComputableCompactPAProofEncoder
open FoundationCompactListedCertifiedVerifier
open FoundationCompactListedCertifiedEncoder
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactCertificateCanonicalDecodeLength
open FoundationCompactCertifiedDerivationSpecialization
open FoundationCompactCanonicalDecodeLength

theorem binarySequentCode_length_le_six_formula_budget
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (first second third fourth fifth sixth :
      LO.FirstOrder.ArithmeticProposition)
    (hmem : ∀ formula ∈ Gamma,
      formula = first ∨ formula = second ∨ formula = third ∨
        formula = fourth ∨ formula = fifth ∨ formula = sixth) :
    (binarySequentCode Gamma).length <=
      (binaryNatCode 6).length +
        6 * ((binaryFormulaCode first).length +
          (binaryFormulaCode second).length +
          (binaryFormulaCode third).length +
          (binaryFormulaCode fourth).length +
          (binaryFormulaCode fifth).length +
          (binaryFormulaCode sixth).length) := by
  let formulaBudget :=
    (binaryFormulaCode first).length +
      (binaryFormulaCode second).length +
      (binaryFormulaCode third).length +
      (binaryFormulaCode fourth).length +
      (binaryFormulaCode fifth).length +
      (binaryFormulaCode sixth).length
  have hsubset : Gamma ⊆ {first, second, third, fourth, fifth, sixth} := by
    intro formula hformula
    rcases hmem formula hformula with h | h | h | h | h | h <;> simp [h]
  have hcardSet : ({first, second, third, fourth, fifth, sixth} :
      Finset LO.FirstOrder.ArithmeticProposition).card <= 6 := by
    have hfirst :=
      Finset.card_insert_le first {second, third, fourth, fifth, sixth}
    have hsecond :=
      Finset.card_insert_le second {third, fourth, fifth, sixth}
    have hthird := Finset.card_insert_le third {fourth, fifth, sixth}
    have hfourth := Finset.card_insert_le fourth {fifth, sixth}
    have hfifth := Finset.card_insert_le fifth {sixth}
    simp only [Finset.card_singleton] at hfifth
    omega
  have hcard : Gamma.card <= 6 :=
    (Finset.card_le_card hsubset).trans hcardSet
  have hheader := binaryNatCode_length_mono hcard
  have hformula
      (formula : LO.FirstOrder.ArithmeticProposition)
      (hformulaMem : formula ∈ Gamma) :
      (binaryFormulaCode formula).length <= formulaBudget := by
    rcases hmem formula hformulaMem with h | h | h | h | h | h <;>
      subst formula <;> simp [formulaBudget] <;> omega
  have hpayload :
      Gamma.sum (fun formula => (binaryFormulaCode formula).length) <=
        Gamma.card * formulaBudget := by
    simpa [nsmul_eq_mul] using
      Gamma.sum_le_card_nsmul
        (fun formula => (binaryFormulaCode formula).length)
        formulaBudget hformula
  have hpayloadBound :
      Gamma.sum (fun formula => (binaryFormulaCode formula).length) <=
        6 * formulaBudget :=
    hpayload.trans (Nat.mul_le_mul_right formulaBudget hcard)
  have hflat :
      (Gamma.toList.flatMap binaryFormulaCode).length =
        Gamma.sum (fun formula => (binaryFormulaCode formula).length) := by
    rw [List.length_flatMap]
    simp
  simp only [binarySequentCode, List.length_append, hflat]
  exact Nat.add_le_add hheader hpayloadBound

def modusPonensSyntaxBudget
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) : Nat :=
  (binaryFormulaCode antecedent).length +
    (binaryFormulaCode consequent).length +
    (binaryFormulaCode (antecedent 🡒 consequent)).length +
    (binaryFormulaCode (∼(antecedent 🡒 consequent))).length +
    (binaryFormulaCode (antecedent ⋏ (∼consequent))).length +
    (binaryFormulaCode (∼consequent)).length

/-- Concrete PA modus ponens with no proof-existence or length parameter. -/
def modusPonensDerivation
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof :
      LO.FirstOrder.Derivation2 PA {antecedent 🡒 consequent})
    (antecedentProof : LO.FirstOrder.Derivation2 PA {antecedent}) :
    LO.FirstOrder.Derivation2 PA {consequent} :=
  LO.FirstOrder.Derivation2.cut
    (φ := antecedent 🡒 consequent)
    (LO.FirstOrder.Derivation2.wk implicationProof (by simp))
    (LO.FirstOrder.Derivation2.and
      (φ := antecedent) (ψ := ∼consequent)
      (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        left
        simp [DeMorgan.imply])
      (LO.FirstOrder.Derivation2.wk antecedentProof (by simp))
      (LO.FirstOrder.Derivation2.closed _ consequent (by simp) (by simp)))

theorem modusPonensDerivation_tree_valid
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof :
      LO.FirstOrder.Derivation2 PA {antecedent 🡒 consequent})
    (antecedentProof : LO.FirstOrder.Derivation2 PA {antecedent}) :
    (CheckedPAProofTree.ofDerivation
      (modusPonensDerivation implicationProof antecedentProof)).Valid :=
  CheckedPAProofTree.valid_ofDerivation _

@[simp] theorem modusPonensDerivation_tree_conclusion
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof :
      LO.FirstOrder.Derivation2 PA {antecedent 🡒 consequent})
    (antecedentProof : LO.FirstOrder.Derivation2 PA {antecedent}) :
    (CheckedPAProofTree.ofDerivation
      (modusPonensDerivation implicationProof antecedentProof)).conclusion =
        {consequent} := by
  simp

/-- Exact code-length accounting for the fixed five-node modus-ponens tree. -/
theorem modusPonensDerivation_binaryProofLength_eq
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof :
      LO.FirstOrder.Derivation2 PA {antecedent 🡒 consequent})
    (antecedentProof : LO.FirstOrder.Derivation2 PA {antecedent}) :
    let implication := antecedent 🡒 consequent
    let negatedImplication := ∼implication
    let negatedConsequent := ∼consequent
    binaryProofLength
        (modusPonensDerivation implicationProof antecedentProof) =
      (binaryNatCode 9).length +
        (binarySequentCode {consequent}).length +
        (binaryFormulaCode implication).length +
        ((binaryNatCode 7).length +
          (binarySequentCode (insert implication {consequent})).length +
          binaryProofLength implicationProof) +
        ((binaryNatCode 3).length +
          (binarySequentCode
            (insert negatedImplication {consequent})).length +
          (binaryFormulaCode antecedent).length +
          (binaryFormulaCode negatedConsequent).length +
          ((binaryNatCode 7).length +
            (binarySequentCode
              (insert antecedent
                (insert negatedImplication {consequent}))).length +
            binaryProofLength antecedentProof) +
          ((binaryNatCode 0).length +
            (binarySequentCode
              (insert negatedConsequent
                (insert negatedImplication {consequent}))).length +
            (binaryFormulaCode consequent).length)) := by
  simp only [modusPonensDerivation, binaryProofLength,
    binaryDerivationCode, List.length_append]

theorem modusPonensDerivation_binaryProofLength_le
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof :
      LO.FirstOrder.Derivation2 PA {antecedent 🡒 consequent})
    (antecedentProof : LO.FirstOrder.Derivation2 PA {antecedent}) :
    binaryProofLength
        (modusPonensDerivation implicationProof antecedentProof) <=
      binaryProofLength implicationProof +
        binaryProofLength antecedentProof + 160 +
        34 * modusPonensSyntaxBudget antecedent consequent := by
  let implication := antecedent 🡒 consequent
  let negatedImplication := ∼implication
  let conjunction := antecedent ⋏ (∼consequent)
  let negatedConsequent := ∼consequent
  let syntaxBudget := modusPonensSyntaxBudget antecedent consequent
  have hbudget : syntaxBudget =
      (binaryFormulaCode antecedent).length +
        (binaryFormulaCode consequent).length +
        (binaryFormulaCode implication).length +
        (binaryFormulaCode negatedImplication).length +
        (binaryFormulaCode conjunction).length +
        (binaryFormulaCode negatedConsequent).length := by
    rfl
  have hseq
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (hmem : ∀ candidate ∈ Gamma,
        candidate = antecedent ∨ candidate = consequent ∨
          candidate = implication ∨ candidate = negatedImplication ∨
          candidate = conjunction ∨ candidate = negatedConsequent) :
      (binarySequentCode Gamma).length <=
        (binaryNatCode 6).length + 6 * syntaxBudget := by
    simpa [hbudget] using
      binarySequentCode_length_le_six_formula_budget Gamma
        antecedent consequent implication negatedImplication
        conjunction negatedConsequent hmem
  have hseqFinal := hseq {consequent} (by simp)
  have hseqImplication := hseq (insert implication {consequent}) (by simp)
  have hseqNegatedImplication :=
    hseq (insert negatedImplication {consequent}) (by simp)
  have hseqAntecedent :=
    hseq (insert antecedent
      (insert negatedImplication {consequent})) (by simp)
  have hseqNegatedConsequent :=
    hseq (insert negatedConsequent
      (insert negatedImplication {consequent})) (by simp)
  have htag0 : (binaryNatCode 0).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  have htag6 : (binaryNatCode 6).length <= 16 := by decide
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  have htag9 : (binaryNatCode 9).length <= 16 := by decide
  have hantecedent :
      (binaryFormulaCode antecedent).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  have hconsequent :
      (binaryFormulaCode consequent).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  have himplication :
      (binaryFormulaCode implication).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  have hnegatedConsequent :
      (binaryFormulaCode negatedConsequent).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
  rw [modusPonensDerivation_binaryProofLength_eq]
  dsimp only [implication, negatedImplication, conjunction,
    negatedConsequent] at hseqFinal hseqImplication hseqNegatedImplication hseqAntecedent hseqNegatedConsequent himplication hnegatedConsequent
  change _ <= binaryProofLength implicationProof +
    binaryProofLength antecedentProof + 160 + 34 * syntaxBudget
  omega

/-- Certificate shape matching the five-node modus-ponens tree. -/
def modusPonensCertificate
    (implicationCertificate antecedentCertificate :
      StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .binary (.unary implicationCertificate)
    (.binary (.unary antecedentCertificate) .leaf)

theorem modusPonensCertificate_valid
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof :
      LO.FirstOrder.Derivation2 PA {antecedent 🡒 consequent})
    (antecedentProof : LO.FirstOrder.Derivation2 PA {antecedent})
    (implicationCertificate antecedentCertificate :
      StructuralValidityCertificate)
    (himplication :
      certificateValid (CheckedPAProofTree.ofDerivation implicationProof)
        implicationCertificate)
    (hantecedent :
      certificateValid (CheckedPAProofTree.ofDerivation antecedentProof)
        antecedentCertificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (modusPonensDerivation implicationProof antecedentProof))
      (modusPonensCertificate
        implicationCertificate antecedentCertificate) := by
  have himplicationConclusion :
      (CheckedPAProofTree.ofDerivation implicationProof).conclusion =
        {antecedent 🡒 consequent} :=
    CheckedPAProofTree.conclusion_ofDerivation implicationProof
  have hantecedentConclusion :
      (CheckedPAProofTree.ofDerivation antecedentProof).conclusion =
        {antecedent} :=
    CheckedPAProofTree.conclusion_ofDerivation antecedentProof
  simp [modusPonensDerivation, modusPonensCertificate,
    CheckedPAProofTree.ofDerivation, CheckedPAProofTree.conclusion,
    certificateValid, himplication, hantecedent,
    DeMorgan.imply]
  constructor
  · change
      (CheckedPAProofTree.ofDerivation implicationProof).conclusion ⊆ _
    rw [himplicationConclusion]
    simp [LO.FirstOrder.Semiformula.imp_eq]
  · change
      (CheckedPAProofTree.ofDerivation antecedentProof).conclusion ⊆ _
    rw [hantecedentConclusion]
    simp

theorem modusPonensCertificate_code_length_le
    (implicationCertificate antecedentCertificate :
      StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (modusPonensCertificate
        implicationCertificate antecedentCertificate)).length <=
      (binaryStructuralValidityCertificateCode
        implicationCertificate).length +
      (binaryStructuralValidityCertificateCode
        antecedentCertificate).length + 80 := by
  have htag0 : (binaryNatCode 0).length <= 16 := by decide
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  simp only [modusPonensCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

/-- The same compiler directly on decoded checked trees.  This is the form
needed to compose arbitrary codes accepted by the public verifier. -/
def checkedModusPonensTree
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (implicationTree antecedentTree : CheckedPAProofTree) :
    CheckedPAProofTree :=
  .cut {consequent} (antecedent 🡒 consequent)
    (.wk (insert (antecedent 🡒 consequent) {consequent})
      implicationTree)
    (.and (insert (∼(antecedent 🡒 consequent)) {consequent})
      antecedent (∼consequent)
      (.wk
        (insert antecedent
          (insert (∼(antecedent 🡒 consequent)) {consequent}))
        antecedentTree)
      (.closed
        (insert (∼consequent)
          (insert (∼(antecedent 🡒 consequent)) {consequent}))
        consequent))

@[simp] theorem checkedModusPonensTree_conclusion
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (implicationTree antecedentTree : CheckedPAProofTree) :
    (checkedModusPonensTree antecedent consequent
      implicationTree antecedentTree).conclusion = {consequent} :=
  rfl

theorem checkedModusPonensCertificate_valid
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationTree antecedentTree : CheckedPAProofTree)
    (implicationCertificate antecedentCertificate :
      StructuralValidityCertificate)
    (himplicationConclusion :
      implicationTree.conclusion = {antecedent 🡒 consequent})
    (hantecedentConclusion :
      antecedentTree.conclusion = {antecedent})
    (himplication :
      certificateValid implicationTree implicationCertificate)
    (hantecedent :
      certificateValid antecedentTree antecedentCertificate) :
    certificateValid
      (checkedModusPonensTree antecedent consequent
        implicationTree antecedentTree)
      (modusPonensCertificate
        implicationCertificate antecedentCertificate) := by
  simp [checkedModusPonensTree, modusPonensCertificate,
    CheckedPAProofTree.conclusion, certificateValid,
    himplication, hantecedent, DeMorgan.imply]
  change implicationTree.conclusion ⊆ _ ∧
    antecedentTree.conclusion ⊆ _
  constructor
  · rw [himplicationConclusion]
    simp [LO.FirstOrder.Semiformula.imp_eq]
  · rw [hantecedentConclusion]
    simp

theorem checkedModusPonensTree_code_length_le
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (implicationTree antecedentTree : CheckedPAProofTree) :
    (canonicalBinaryProofCode
      (checkedModusPonensTree antecedent consequent
        implicationTree antecedentTree)).length <=
      (canonicalBinaryProofCode implicationTree).length +
        (canonicalBinaryProofCode antecedentTree).length + 160 +
        34 * modusPonensSyntaxBudget antecedent consequent := by
  let implication := antecedent 🡒 consequent
  let negatedImplication := ∼implication
  let conjunction := antecedent ⋏ (∼consequent)
  let negatedConsequent := ∼consequent
  let syntaxBudget := modusPonensSyntaxBudget antecedent consequent
  have hbudget : syntaxBudget =
      (binaryFormulaCode antecedent).length +
        (binaryFormulaCode consequent).length +
        (binaryFormulaCode implication).length +
        (binaryFormulaCode negatedImplication).length +
        (binaryFormulaCode conjunction).length +
        (binaryFormulaCode negatedConsequent).length := by
    rfl
  have hseq
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (hmem : ∀ candidate ∈ Gamma,
        candidate = antecedent ∨ candidate = consequent ∨
          candidate = implication ∨ candidate = negatedImplication ∨
          candidate = conjunction ∨ candidate = negatedConsequent) :
      (canonicalBinarySequentCode Gamma).length <=
        (binaryNatCode 6).length + 6 * syntaxBudget := by
    rw [canonicalBinarySequentCode_length]
    simpa [hbudget] using
      binarySequentCode_length_le_six_formula_budget Gamma
        antecedent consequent implication negatedImplication
        conjunction negatedConsequent hmem
  have hseqFinal := hseq {consequent} (by simp)
  have hseqImplication := hseq (insert implication {consequent}) (by simp)
  have hseqNegatedImplication :=
    hseq (insert negatedImplication {consequent}) (by simp)
  have hseqAntecedent :=
    hseq (insert antecedent
      (insert negatedImplication {consequent})) (by simp)
  have hseqNegatedConsequent :=
    hseq (insert negatedConsequent
      (insert negatedImplication {consequent})) (by simp)
  have htag0 : (binaryNatCode 0).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  have htag6 : (binaryNatCode 6).length <= 16 := by decide
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  have htag9 : (binaryNatCode 9).length <= 16 := by decide
  have hantecedent :
      (binaryFormulaCode antecedent).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  have hconsequent :
      (binaryFormulaCode consequent).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  have himplication :
      (binaryFormulaCode implication).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  have hnegatedConsequent :
      (binaryFormulaCode negatedConsequent).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
  simp only [checkedModusPonensTree,
    canonicalBinaryProofCode, List.length_append]
  dsimp only [implication, negatedImplication, conjunction,
    negatedConsequent] at hseqFinal hseqImplication hseqNegatedImplication hseqAntecedent hseqNegatedConsequent himplication hnegatedConsequent
  change _ <=
    (canonicalBinaryProofCode implicationTree).length +
      (canonicalBinaryProofCode antecedentTree).length + 160 +
      34 * syntaxBudget
  omega

theorem checkedModusPonensCertifiedCode_length_le
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (implicationTree antecedentTree : CheckedPAProofTree)
    (implicationCertificate antecedentCertificate :
      StructuralValidityCertificate) :
    (canonicalBinaryCertifiedPAProofCode
      (checkedModusPonensTree antecedent consequent
        implicationTree antecedentTree)
      (modusPonensCertificate
        implicationCertificate antecedentCertificate)).length <=
      (canonicalBinaryCertifiedPAProofCode
        implicationTree implicationCertificate).length +
      (canonicalBinaryCertifiedPAProofCode
        antecedentTree antecedentCertificate).length + 240 +
      34 * modusPonensSyntaxBudget antecedent consequent := by
  have hproof := checkedModusPonensTree_code_length_le
    antecedent consequent implicationTree antecedentTree
  have hcertificate := modusPonensCertificate_code_length_le
    implicationCertificate antecedentCertificate
  simp only [canonicalBinaryCertifiedPAProofCode,
    List.length_append] at hproof hcertificate ⊢
  omega

/-- Public-code form of bounded modus ponens.  The compiler decodes both
accepted full payloads, reuses their complete certificates, and emits a
canonical accepted payload whose length is bounded by the two actual input
payload lengths plus explicit local syntax overhead. -/
theorem acceptedCodes_modusPonens_exists
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    {implicationCode antecedentCode : Nat}
    (himplication :
      listedCompactCertifiedPAProofVerifier implicationCode
        (compactFormulaCode (antecedent 🡒 consequent)) = true)
    (hantecedent :
      listedCompactCertifiedPAProofVerifier antecedentCode
        (compactFormulaCode antecedent) = true) :
    exists outputCode : Nat,
      listedCompactCertifiedPAProofVerifier outputCode
          (compactFormulaCode consequent) = true ∧
        packedPayloadLength outputCode <=
          packedPayloadLength implicationCode +
            packedPayloadLength antecedentCode + 240 +
            34 * modusPonensSyntaxBudget antecedent consequent := by
  rcases
      (listedCompactCertifiedPAProofVerifier_eq_true_iff _ _).mp
        himplication with
    ⟨implicationListedTree, implicationCertificate,
      implicationFormula, himplicationDecode,
      himplicationCertificate, himplicationConclusion,
      himplicationFormulaCode⟩
  have himplicationFormula :
      implicationFormula = antecedent 🡒 consequent :=
    compactFormulaCode_injective himplicationFormulaCode
  subst implicationFormula
  rcases
      (listedCompactCertifiedPAProofVerifier_eq_true_iff _ _).mp
        hantecedent with
    ⟨antecedentListedTree, antecedentCertificate,
      antecedentFormula, hantecedentDecode,
      hantecedentCertificate, hantecedentConclusion,
      hantecedentFormulaCode⟩
  have hantecedentFormula :
      antecedentFormula = antecedent :=
    compactFormulaCode_injective hantecedentFormulaCode
  subst antecedentFormula
  let implicationTree := implicationListedTree.toChecked
  let antecedentTree := antecedentListedTree.toChecked
  let outputTree :=
    checkedModusPonensTree antecedent consequent
      implicationTree antecedentTree
  let outputCertificate :=
    modusPonensCertificate
      implicationCertificate antecedentCertificate
  let outputCode :=
    canonicalPackedCertifiedPAProofCode outputTree outputCertificate
  have himplicationCheckedCertificate :
      certificateValid implicationTree implicationCertificate := by
    exact (listedCertificateValid_toChecked_iff
      implicationListedTree implicationCertificate).mp
      himplicationCertificate
  have hantecedentCheckedCertificate :
      certificateValid antecedentTree antecedentCertificate := by
    exact (listedCertificateValid_toChecked_iff
      antecedentListedTree antecedentCertificate).mp
      hantecedentCertificate
  have himplicationCheckedConclusion :
      implicationTree.conclusion = {antecedent 🡒 consequent} := by
    change implicationListedTree.toChecked.conclusion =
      {antecedent 🡒 consequent}
    rw [ListedCheckedPAProofTree.toChecked_conclusion]
    exact himplicationConclusion
  have hantecedentCheckedConclusion :
      antecedentTree.conclusion = {antecedent} := by
    change antecedentListedTree.toChecked.conclusion = {antecedent}
    rw [ListedCheckedPAProofTree.toChecked_conclusion]
    exact hantecedentConclusion
  have houtputCertificate :
      certificateValid outputTree outputCertificate := by
    exact checkedModusPonensCertificate_valid
      implicationTree antecedentTree
      implicationCertificate antecedentCertificate
      himplicationCheckedConclusion hantecedentCheckedConclusion
      himplicationCheckedCertificate hantecedentCheckedCertificate
  have himplicationCheckedDecode :
      decodeCompactPackedCertifiedPAProof implicationCode =
        some (implicationTree, implicationCertificate) := by
    exact decodeCompactPackedListedCertifiedPAProof_toChecked
      himplicationDecode
  have hantecedentCheckedDecode :
      decodeCompactPackedCertifiedPAProof antecedentCode =
        some (antecedentTree, antecedentCertificate) := by
    exact decodeCompactPackedListedCertifiedPAProof_toChecked
      hantecedentDecode
  have himplicationInputLength :
      (canonicalBinaryCertifiedPAProofCode
        implicationTree implicationCertificate).length <=
          packedPayloadLength implicationCode := by
    rw [canonicalBinaryCertifiedPAProofCode_length]
    exact decodeCompactPackedCertifiedPAProof_binaryLength_le
      himplicationCheckedDecode
  have hantecedentInputLength :
      (canonicalBinaryCertifiedPAProofCode
        antecedentTree antecedentCertificate).length <=
          packedPayloadLength antecedentCode := by
    rw [canonicalBinaryCertifiedPAProofCode_length]
    exact decodeCompactPackedCertifiedPAProof_binaryLength_le
      hantecedentCheckedDecode
  have houtputLength :=
    checkedModusPonensCertifiedCode_length_le
      antecedent consequent implicationTree antecedentTree
      implicationCertificate antecedentCertificate
  refine ⟨outputCode, ?_, ?_⟩
  · apply listedCompactCertifiedPAProofVerifier_eq_true_of_certifiedTree
      outputTree outputCertificate consequent
    · exact houtputCertificate
    · simp [outputTree]
  · calc
      packedPayloadLength outputCode =
          (canonicalBinaryCertifiedPAProofCode
            outputTree outputCertificate).length := by
        simp [outputCode]
      _ <=
          (canonicalBinaryCertifiedPAProofCode
            implicationTree implicationCertificate).length +
          (canonicalBinaryCertifiedPAProofCode
            antecedentTree antecedentCertificate).length + 240 +
          34 * modusPonensSyntaxBudget antecedent consequent := by
        simpa [outputTree, outputCertificate] using houtputLength
      _ <= packedPayloadLength implicationCode +
          packedPayloadLength antecedentCode + 240 +
          34 * modusPonensSyntaxBudget antecedent consequent := by
        omega

def modusPonensTree
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof :
      LO.FirstOrder.Derivation2 PA {antecedent 🡒 consequent})
    (antecedentProof : LO.FirstOrder.Derivation2 PA {antecedent}) :
    CheckedPAProofTree :=
  CheckedPAProofTree.ofDerivation
    (modusPonensDerivation implicationProof antecedentProof)

def modusPonensCertifiedCode
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof :
      LO.FirstOrder.Derivation2 PA {antecedent 🡒 consequent})
    (antecedentProof : LO.FirstOrder.Derivation2 PA {antecedent})
    (implicationCertificate antecedentCertificate :
      StructuralValidityCertificate) : Nat :=
  canonicalPackedCertifiedPAProofCode
    (modusPonensTree implicationProof antecedentProof)
    (modusPonensCertificate
      implicationCertificate antecedentCertificate)

/-- The public checker accepts the assembled proof with both input
certificates reused verbatim. -/
theorem modusPonensCertifiedCode_verifier_eq_true
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof :
      LO.FirstOrder.Derivation2 PA {antecedent 🡒 consequent})
    (antecedentProof : LO.FirstOrder.Derivation2 PA {antecedent})
    (implicationCertificate antecedentCertificate :
      StructuralValidityCertificate)
    (himplication :
      certificateValid (CheckedPAProofTree.ofDerivation implicationProof)
        implicationCertificate)
    (hantecedent :
      certificateValid (CheckedPAProofTree.ofDerivation antecedentProof)
        antecedentCertificate) :
    listedCompactCertifiedPAProofVerifier
      (modusPonensCertifiedCode implicationProof antecedentProof
        implicationCertificate antecedentCertificate)
      (compactFormulaCode consequent) = true := by
  apply listedCompactCertifiedPAProofVerifier_eq_true_of_certifiedTree
    (modusPonensTree implicationProof antecedentProof)
    (modusPonensCertificate
      implicationCertificate antecedentCertificate)
    consequent
  · exact modusPonensCertificate_valid
      implicationProof antecedentProof
      implicationCertificate antecedentCertificate
      himplication hantecedent
  · simp [modusPonensTree]

/-- Linear overhead on the complete proof-plus-certificate payload. -/
theorem modusPonensCertifiedCode_payloadLength_le
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof :
      LO.FirstOrder.Derivation2 PA {antecedent 🡒 consequent})
    (antecedentProof : LO.FirstOrder.Derivation2 PA {antecedent})
    (implicationCertificate antecedentCertificate :
      StructuralValidityCertificate) :
    packedPayloadLength
        (modusPonensCertifiedCode implicationProof antecedentProof
          implicationCertificate antecedentCertificate) <=
      binaryProofLength implicationProof +
        binaryProofLength antecedentProof +
        (binaryStructuralValidityCertificateCode
          implicationCertificate).length +
        (binaryStructuralValidityCertificateCode
          antecedentCertificate).length + 240 +
        34 * modusPonensSyntaxBudget antecedent consequent := by
  have hproof :=
    modusPonensDerivation_binaryProofLength_le
      implicationProof antecedentProof
  have hcertificate :=
    modusPonensCertificate_code_length_le
      implicationCertificate antecedentCertificate
  calc
    packedPayloadLength
        (modusPonensCertifiedCode implicationProof antecedentProof
          implicationCertificate antecedentCertificate) =
      binaryProofLength
          (modusPonensDerivation implicationProof antecedentProof) +
        (binaryStructuralValidityCertificateCode
          (modusPonensCertificate
            implicationCertificate antecedentCertificate)).length := by
      simp [modusPonensCertifiedCode, modusPonensTree,
        canonicalBinaryCertifiedPAProofCode,
        canonicalBinaryProofCode_length, binaryProofLength]
    _ <=
        (binaryProofLength implicationProof +
          binaryProofLength antecedentProof + 160 +
          34 * modusPonensSyntaxBudget antecedent consequent) +
        ((binaryStructuralValidityCertificateCode
            implicationCertificate).length +
          (binaryStructuralValidityCertificateCode
            antecedentCertificate).length + 80) :=
      Nat.add_le_add hproof hcertificate
    _ = binaryProofLength implicationProof +
          binaryProofLength antecedentProof +
          (binaryStructuralValidityCertificateCode
            implicationCertificate).length +
          (binaryStructuralValidityCertificateCode
            antecedentCertificate).length + 240 +
          34 * modusPonensSyntaxBudget antecedent consequent := by
      omega

#print axioms modusPonensDerivation
#print axioms modusPonensDerivation_tree_valid
#print axioms modusPonensDerivation_tree_conclusion
#print axioms binarySequentCode_length_le_six_formula_budget
#print axioms modusPonensDerivation_binaryProofLength_eq
#print axioms modusPonensDerivation_binaryProofLength_le
#print axioms modusPonensCertificate_valid
#print axioms modusPonensCertificate_code_length_le
#print axioms checkedModusPonensCertificate_valid
#print axioms checkedModusPonensTree_code_length_le
#print axioms checkedModusPonensCertifiedCode_length_le
#print axioms acceptedCodes_modusPonens_exists
#print axioms modusPonensCertifiedCode_verifier_eq_true
#print axioms modusPonensCertifiedCode_payloadLength_le

end FoundationCompactCertifiedModusPonens
