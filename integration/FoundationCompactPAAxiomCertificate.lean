import integration.FoundationCompactPAProofVerifier

/-!
# Explicit certificates for Foundation PA axioms

An induction axiom carries its body; every other PA-minus/equality axiom has a
fixed constructor.  Thus axiom membership is witnessed locally rather than
left as an opaque theory-membership premise.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAAxiomCertificate

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions

inductive PAAxiomCertificate where
  | eqRefl
  | eqSymm
  | eqTrans
  | eqFuncExt {arity : Nat} (functionSymbol :
      LO.FirstOrder.Language.Func ℒₒᵣ arity)
  | eqRelExt {arity : Nat} (relationSymbol :
      LO.FirstOrder.Language.Rel ℒₒᵣ arity)
  | addZero
  | addAssoc
  | addComm
  | addEqOfLt
  | zeroLe
  | zeroLtOne
  | oneLeOfZeroLt
  | addLtAdd
  | mulZero
  | mulOne
  | mulAssoc
  | mulComm
  | mulLtMul
  | distr
  | ltIrrefl
  | ltTrans
  | ltTri
  | induction (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)

def PAAxiomCertificate.sentence :
    PAAxiomCertificate → LO.FirstOrder.ArithmeticSentence
  | .eqRefl => LO.FirstOrder.Theory.Eq.refl ℒₒᵣ
  | .eqSymm => LO.FirstOrder.Theory.Eq.symm ℒₒᵣ
  | .eqTrans => LO.FirstOrder.Theory.Eq.trans ℒₒᵣ
  | .eqFuncExt functionSymbol =>
      LO.FirstOrder.Theory.Eq.funcExt functionSymbol
  | .eqRelExt relationSymbol =>
      LO.FirstOrder.Theory.Eq.relExt relationSymbol
  | .addZero => PeanoMinus.Axiom.addZero
  | .addAssoc => PeanoMinus.Axiom.addAssoc
  | .addComm => PeanoMinus.Axiom.addComm
  | .addEqOfLt => PeanoMinus.Axiom.addEqOfLt
  | .zeroLe => PeanoMinus.Axiom.zeroLe
  | .zeroLtOne => PeanoMinus.Axiom.zeroLtOne
  | .oneLeOfZeroLt => PeanoMinus.Axiom.oneLeOfZeroLt
  | .addLtAdd => PeanoMinus.Axiom.addLtAdd
  | .mulZero => PeanoMinus.Axiom.mulZero
  | .mulOne => PeanoMinus.Axiom.mulOne
  | .mulAssoc => PeanoMinus.Axiom.mulAssoc
  | .mulComm => PeanoMinus.Axiom.mulComm
  | .mulLtMul => PeanoMinus.Axiom.mulLtMul
  | .distr => PeanoMinus.Axiom.distr
  | .ltIrrefl => PeanoMinus.Axiom.ltIrrefl
  | .ltTrans => PeanoMinus.Axiom.ltTrans
  | .ltTri => PeanoMinus.Axiom.ltTri
  | .induction body => (succInd body).univCl

theorem PAAxiomCertificate.sentence_mem_PA
    (certificate : PAAxiomCertificate) :
    certificate.sentence ∈ PA := by
  cases certificate with
  | eqRefl =>
      exact Or.inl (PeanoMinus.equal _
        (LO.FirstOrder.Theory.eqAxiom.refl))
  | eqSymm =>
      exact Or.inl (PeanoMinus.equal _
        (LO.FirstOrder.Theory.eqAxiom.symm))
  | eqTrans =>
      exact Or.inl (PeanoMinus.equal _
        (LO.FirstOrder.Theory.eqAxiom.trans))
  | eqFuncExt functionSymbol =>
      exact Or.inl (PeanoMinus.equal _
        (LO.FirstOrder.Theory.eqAxiom.funcExt functionSymbol))
  | eqRelExt relationSymbol =>
      exact Or.inl (PeanoMinus.equal _
        (LO.FirstOrder.Theory.eqAxiom.relExt relationSymbol))
  | addZero => exact Or.inl PeanoMinus.addZero
  | addAssoc => exact Or.inl PeanoMinus.addAssoc
  | addComm => exact Or.inl PeanoMinus.addComm
  | addEqOfLt => exact Or.inl PeanoMinus.addEqOfLt
  | zeroLe => exact Or.inl PeanoMinus.zeroLe
  | zeroLtOne => exact Or.inl PeanoMinus.zeroLtOne
  | oneLeOfZeroLt => exact Or.inl PeanoMinus.oneLeOfZeroLt
  | addLtAdd => exact Or.inl PeanoMinus.addLtAdd
  | mulZero => exact Or.inl PeanoMinus.mulZero
  | mulOne => exact Or.inl PeanoMinus.mulOne
  | mulAssoc => exact Or.inl PeanoMinus.mulAssoc
  | mulComm => exact Or.inl PeanoMinus.mulComm
  | mulLtMul => exact Or.inl PeanoMinus.mulLtMul
  | distr => exact Or.inl PeanoMinus.distr
  | ltIrrefl => exact Or.inl PeanoMinus.ltIrrefl
  | ltTrans => exact Or.inl PeanoMinus.ltTrans
  | ltTri => exact Or.inl PeanoMinus.ltTri
  | induction body =>
      exact Or.inr ⟨body, Set.mem_univ body, rfl⟩

theorem exists_axiomCertificate_iff
    (sigma : LO.FirstOrder.ArithmeticSentence) :
    (∃ certificate : PAAxiomCertificate,
      certificate.sentence = sigma) ↔ sigma ∈ PA := by
  constructor
  · rintro ⟨certificate, rfl⟩
    exact certificate.sentence_mem_PA
  · intro hsigma
    rcases hsigma with hminus | hinduction
    · cases hminus with
      | equal formula hformula =>
          cases hformula with
          | refl => exact ⟨.eqRefl, rfl⟩
          | symm => exact ⟨.eqSymm, rfl⟩
          | trans => exact ⟨.eqTrans, rfl⟩
          | funcExt functionSymbol =>
              exact ⟨.eqFuncExt functionSymbol, rfl⟩
          | relExt relationSymbol =>
              exact ⟨.eqRelExt relationSymbol, rfl⟩
      | addZero => exact ⟨.addZero, rfl⟩
      | addAssoc => exact ⟨.addAssoc, rfl⟩
      | addComm => exact ⟨.addComm, rfl⟩
      | addEqOfLt => exact ⟨.addEqOfLt, rfl⟩
      | zeroLe => exact ⟨.zeroLe, rfl⟩
      | zeroLtOne => exact ⟨.zeroLtOne, rfl⟩
      | oneLeOfZeroLt => exact ⟨.oneLeOfZeroLt, rfl⟩
      | addLtAdd => exact ⟨.addLtAdd, rfl⟩
      | mulZero => exact ⟨.mulZero, rfl⟩
      | mulOne => exact ⟨.mulOne, rfl⟩
      | mulAssoc => exact ⟨.mulAssoc, rfl⟩
      | mulComm => exact ⟨.mulComm, rfl⟩
      | mulLtMul => exact ⟨.mulLtMul, rfl⟩
      | distr => exact ⟨.distr, rfl⟩
      | ltIrrefl => exact ⟨.ltIrrefl, rfl⟩
      | ltTrans => exact ⟨.ltTrans, rfl⟩
      | ltTri => exact ⟨.ltTri, rfl⟩
    · rcases hinduction with ⟨body, _, rfl⟩
      exact ⟨.induction body, rfl⟩

inductive StructuralValidityCertificate where
  | leaf
  | axiomCert (certificate : PAAxiomCertificate)
  | unary (premise : StructuralValidityCertificate)
  | binary
      (left right : StructuralValidityCertificate)

def certificateValid :
    CheckedPAProofTree → StructuralValidityCertificate → Prop
  | .closed Gamma formula, .leaf =>
      formula ∈ Gamma ∧ ∼formula ∈ Gamma
  | .axm Gamma sigma, .axiomCert certificate =>
      certificate.sentence = sigma ∧
        (Rewriting.emb sigma : LO.FirstOrder.ArithmeticProposition) ∈ Gamma
  | .verum Gamma, .leaf =>
      (⊤ : LO.FirstOrder.ArithmeticProposition) ∈ Gamma
  | .and Gamma leftFormula rightFormula left right,
      .binary leftCertificate rightCertificate =>
      leftFormula ⋏ rightFormula ∈ Gamma ∧
        left.conclusion = insert leftFormula Gamma ∧
        right.conclusion = insert rightFormula Gamma ∧
        certificateValid left leftCertificate ∧
        certificateValid right rightCertificate
  | .or Gamma leftFormula rightFormula premise,
      .unary premiseCertificate =>
      leftFormula ⋎ rightFormula ∈ Gamma ∧
        premise.conclusion =
          insert leftFormula (insert rightFormula Gamma) ∧
        certificateValid premise premiseCertificate
  | .all Gamma formula premise, .unary premiseCertificate =>
      ∀⁰ formula ∈ Gamma ∧
        premise.conclusion =
          insert (Rewriting.free formula)
            (Gamma.image Rewriting.shift) ∧
        certificateValid premise premiseCertificate
  | .exs Gamma formula witness premise,
      .unary premiseCertificate =>
      ∃⁰ formula ∈ Gamma ∧
        premise.conclusion = insert (formula/[witness]) Gamma ∧
        certificateValid premise premiseCertificate
  | .wk Gamma premise, .unary premiseCertificate =>
      premise.conclusion ⊆ Gamma ∧
        certificateValid premise premiseCertificate
  | .shift Gamma premise, .unary premiseCertificate =>
      Gamma = premise.conclusion.image Rewriting.shift ∧
        certificateValid premise premiseCertificate
  | .cut Gamma formula left right,
      .binary leftCertificate rightCertificate =>
      left.conclusion = insert formula Gamma ∧
        right.conclusion = insert (∼formula) Gamma ∧
        certificateValid left leftCertificate ∧
        certificateValid right rightCertificate
  | _, _ => False

/-- Computable local checker for the structural certificate.  Unlike the
`Decidable` proof below, this definition exposes every recursive check as a
Boolean operation and can be compiled and costed. -/
def certificateValidBool :
    CheckedPAProofTree → StructuralValidityCertificate → Bool
  | .closed Gamma formula, .leaf =>
      decide (formula ∈ Gamma) && decide (∼formula ∈ Gamma)
  | .axm Gamma sigma, .axiomCert certificate =>
      decide (certificate.sentence = sigma) &&
        decide
          ((Rewriting.emb sigma : LO.FirstOrder.ArithmeticProposition) ∈ Gamma)
  | .verum Gamma, .leaf =>
      decide ((⊤ : LO.FirstOrder.ArithmeticProposition) ∈ Gamma)
  | .and Gamma leftFormula rightFormula left right,
      .binary leftCertificate rightCertificate =>
      decide (leftFormula ⋏ rightFormula ∈ Gamma) &&
        decide (left.conclusion = insert leftFormula Gamma) &&
        decide (right.conclusion = insert rightFormula Gamma) &&
        certificateValidBool left leftCertificate &&
        certificateValidBool right rightCertificate
  | .or Gamma leftFormula rightFormula premise,
      .unary premiseCertificate =>
      decide (leftFormula ⋎ rightFormula ∈ Gamma) &&
        decide
          (premise.conclusion =
            insert leftFormula (insert rightFormula Gamma)) &&
        certificateValidBool premise premiseCertificate
  | .all Gamma formula premise, .unary premiseCertificate =>
      decide (∀⁰ formula ∈ Gamma) &&
        decide
          (premise.conclusion =
            insert (Rewriting.free formula)
              (Gamma.image Rewriting.shift)) &&
        certificateValidBool premise premiseCertificate
  | .exs Gamma formula witness premise,
      .unary premiseCertificate =>
      decide (∃⁰ formula ∈ Gamma) &&
        decide
          (premise.conclusion = insert (formula/[witness]) Gamma) &&
        certificateValidBool premise premiseCertificate
  | .wk Gamma premise, .unary premiseCertificate =>
      decide (premise.conclusion ⊆ Gamma) &&
        certificateValidBool premise premiseCertificate
  | .shift Gamma premise, .unary premiseCertificate =>
      decide (Gamma = premise.conclusion.image Rewriting.shift) &&
        certificateValidBool premise premiseCertificate
  | .cut Gamma formula left right,
      .binary leftCertificate rightCertificate =>
      decide (left.conclusion = insert formula Gamma) &&
        decide (right.conclusion = insert (∼formula) Gamma) &&
        certificateValidBool left leftCertificate &&
        certificateValidBool right rightCertificate
  | _, _ => false

theorem certificateValidBool_eq_true_iff
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    certificateValidBool tree certificate = true ↔
      certificateValid tree certificate := by
  induction tree generalizing certificate <;>
    cases certificate <;>
    simp [certificateValidBool, certificateValid, and_assoc, *]

def certificateValid_decidable
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    Decidable (certificateValid tree certificate) := by
  induction tree generalizing certificate <;>
    cases certificate <;>
    simp only [certificateValid] <;>
    infer_instance

theorem certificateValid_sound
    {tree : CheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    (hcertificate : certificateValid tree certificate) :
    structurallyValid tree := by
  induction tree generalizing certificate with
  | closed Gamma formula =>
      cases certificate <;>
        simp [certificateValid, structurallyValid] at hcertificate ⊢ <;>
        assumption
  | axm Gamma sigma =>
      cases certificate with
      | axiomCert axiomCertificate =>
          rcases hcertificate with ⟨hformula, hmember⟩
          exact ⟨hformula ▸ axiomCertificate.sentence_mem_PA, hmember⟩
      | leaf => simp [certificateValid] at hcertificate
      | unary premise => simp [certificateValid] at hcertificate
      | binary left right => simp [certificateValid] at hcertificate
  | verum Gamma =>
      cases certificate <;>
        simp [certificateValid, structurallyValid] at hcertificate ⊢ <;>
        assumption
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      cases certificate with
      | binary leftCertificate rightCertificate =>
          rcases hcertificate with
            ⟨hprincipal, hleftConclusion, hrightConclusion,
              hleft, hright⟩
          exact ⟨hprincipal, hleftConclusion, hrightConclusion,
            ihLeft hleft, ihRight hright⟩
      | leaf => simp [certificateValid] at hcertificate
      | axiomCert axiomCertificate => simp [certificateValid] at hcertificate
      | unary premise => simp [certificateValid] at hcertificate
  | or Gamma leftFormula rightFormula premise ih =>
      cases certificate with
      | unary premiseCertificate =>
          rcases hcertificate with
            ⟨hprincipal, hpremiseConclusion, hpremise⟩
          exact ⟨hprincipal, hpremiseConclusion, ih hpremise⟩
      | leaf => simp [certificateValid] at hcertificate
      | axiomCert axiomCertificate => simp [certificateValid] at hcertificate
      | binary left right => simp [certificateValid] at hcertificate
  | all Gamma formula premise ih =>
      cases certificate with
      | unary premiseCertificate =>
          rcases hcertificate with
            ⟨hprincipal, hpremiseConclusion, hpremise⟩
          exact ⟨hprincipal, hpremiseConclusion, ih hpremise⟩
      | leaf => simp [certificateValid] at hcertificate
      | axiomCert axiomCertificate => simp [certificateValid] at hcertificate
      | binary left right => simp [certificateValid] at hcertificate
  | exs Gamma formula witness premise ih =>
      cases certificate with
      | unary premiseCertificate =>
          rcases hcertificate with
            ⟨hprincipal, hpremiseConclusion, hpremise⟩
          exact ⟨hprincipal, hpremiseConclusion, ih hpremise⟩
      | leaf => simp [certificateValid] at hcertificate
      | axiomCert axiomCertificate => simp [certificateValid] at hcertificate
      | binary left right => simp [certificateValid] at hcertificate
  | wk Gamma premise ih =>
      cases certificate with
      | unary premiseCertificate =>
          exact ⟨hcertificate.1, ih hcertificate.2⟩
      | leaf => simp [certificateValid] at hcertificate
      | axiomCert axiomCertificate => simp [certificateValid] at hcertificate
      | binary left right => simp [certificateValid] at hcertificate
  | shift Gamma premise ih =>
      cases certificate with
      | unary premiseCertificate =>
          exact ⟨hcertificate.1, ih hcertificate.2⟩
      | leaf => simp [certificateValid] at hcertificate
      | axiomCert axiomCertificate => simp [certificateValid] at hcertificate
      | binary left right => simp [certificateValid] at hcertificate
  | cut Gamma formula left right ihLeft ihRight =>
      cases certificate with
      | binary leftCertificate rightCertificate =>
          rcases hcertificate with
            ⟨hleftConclusion, hrightConclusion, hleft, hright⟩
          exact ⟨hleftConclusion, hrightConclusion,
            ihLeft hleft, ihRight hright⟩
      | leaf => simp [certificateValid] at hcertificate
      | axiomCert axiomCertificate => simp [certificateValid] at hcertificate
      | unary premise => simp [certificateValid] at hcertificate

theorem exists_certificateValid
    (tree : CheckedPAProofTree)
    (hvalid : structurallyValid tree) :
    ∃ certificate : StructuralValidityCertificate,
      certificateValid tree certificate := by
  induction tree with
  | closed Gamma formula =>
      exact ⟨.leaf, hvalid⟩
  | axm Gamma sigma =>
      rcases (exists_axiomCertificate_iff sigma).mpr hvalid.1 with
        ⟨axiomCertificate, hformula⟩
      exact ⟨.axiomCert axiomCertificate, hformula, hvalid.2⟩
  | verum Gamma =>
      exact ⟨.leaf, hvalid⟩
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      rcases hvalid with
        ⟨hprincipal, hleftConclusion, hrightConclusion,
          hleft, hright⟩
      rcases ihLeft hleft with ⟨leftCertificate, hleftCertificate⟩
      rcases ihRight hright with ⟨rightCertificate, hrightCertificate⟩
      exact ⟨.binary leftCertificate rightCertificate,
        hprincipal, hleftConclusion, hrightConclusion,
        hleftCertificate, hrightCertificate⟩
  | or Gamma leftFormula rightFormula premise ih =>
      rcases hvalid with ⟨hprincipal, hpremiseConclusion, hpremise⟩
      rcases ih hpremise with ⟨premiseCertificate, hpremiseCertificate⟩
      exact ⟨.unary premiseCertificate,
        hprincipal, hpremiseConclusion, hpremiseCertificate⟩
  | all Gamma formula premise ih =>
      rcases hvalid with ⟨hprincipal, hpremiseConclusion, hpremise⟩
      rcases ih hpremise with ⟨premiseCertificate, hpremiseCertificate⟩
      exact ⟨.unary premiseCertificate,
        hprincipal, hpremiseConclusion, hpremiseCertificate⟩
  | exs Gamma formula witness premise ih =>
      rcases hvalid with ⟨hprincipal, hpremiseConclusion, hpremise⟩
      rcases ih hpremise with ⟨premiseCertificate, hpremiseCertificate⟩
      exact ⟨.unary premiseCertificate,
        hprincipal, hpremiseConclusion, hpremiseCertificate⟩
  | wk Gamma premise ih =>
      rcases hvalid with ⟨hsubset, hpremise⟩
      rcases ih hpremise with ⟨premiseCertificate, hpremiseCertificate⟩
      exact ⟨.unary premiseCertificate, hsubset, hpremiseCertificate⟩
  | shift Gamma premise ih =>
      rcases hvalid with ⟨hconclusion, hpremise⟩
      rcases ih hpremise with ⟨premiseCertificate, hpremiseCertificate⟩
      exact ⟨.unary premiseCertificate,
        hconclusion, hpremiseCertificate⟩
  | cut Gamma formula left right ihLeft ihRight =>
      rcases hvalid with
        ⟨hleftConclusion, hrightConclusion, hleft, hright⟩
      rcases ihLeft hleft with ⟨leftCertificate, hleftCertificate⟩
      rcases ihRight hright with ⟨rightCertificate, hrightCertificate⟩
      exact ⟨.binary leftCertificate rightCertificate,
        hleftConclusion, hrightConclusion,
        hleftCertificate, hrightCertificate⟩

theorem structurallyValid_iff_exists_certificate
    (tree : CheckedPAProofTree) :
    structurallyValid tree ↔
      ∃ certificate : StructuralValidityCertificate,
        certificateValid tree certificate := by
  constructor
  · exact exists_certificateValid tree
  · rintro ⟨certificate, hcertificate⟩
    exact certificateValid_sound hcertificate

def binaryPAAxiomCertificateCode :
    PAAxiomCertificate → List Bool
  | .eqRefl => binaryNatCode 0
  | .eqSymm => binaryNatCode 1
  | .eqTrans => binaryNatCode 2
  | .eqFuncExt (arity := arity) functionSymbol =>
      binaryNatCode 3 ++ binaryNatCode arity ++
        binaryNatCode (Encodable.encode functionSymbol)
  | .eqRelExt (arity := arity) relationSymbol =>
      binaryNatCode 4 ++ binaryNatCode arity ++
        binaryNatCode (Encodable.encode relationSymbol)
  | .addZero => binaryNatCode 5
  | .addAssoc => binaryNatCode 6
  | .addComm => binaryNatCode 7
  | .addEqOfLt => binaryNatCode 8
  | .zeroLe => binaryNatCode 9
  | .zeroLtOne => binaryNatCode 10
  | .oneLeOfZeroLt => binaryNatCode 11
  | .addLtAdd => binaryNatCode 12
  | .mulZero => binaryNatCode 13
  | .mulOne => binaryNatCode 14
  | .mulAssoc => binaryNatCode 15
  | .mulComm => binaryNatCode 16
  | .mulLtMul => binaryNatCode 17
  | .distr => binaryNatCode 18
  | .ltIrrefl => binaryNatCode 19
  | .ltTrans => binaryNatCode 20
  | .ltTri => binaryNatCode 21
  | .induction body =>
      binaryNatCode 22 ++ binaryFormulaCode body

def axiomCertificateParseWeight : PAAxiomCertificate → Nat
  | .induction body => 1 + formulaSymbolCount body
  | _ => 1

theorem axiomCertificateParseWeight_le_binaryCode_length
    (certificate : PAAxiomCertificate) :
    axiomCertificateParseWeight certificate ≤
      (binaryPAAxiomCertificateCode certificate).length := by
  cases certificate <;>
    simp [axiomCertificateParseWeight,
      binaryPAAxiomCertificateCode, binaryNatCode]
  case induction body =>
    have hbody := formulaSymbolCount_le_binaryFormulaCode_length body
    omega
  all_goals omega

def decodePAAxiomCertificate :
    Nat → List Bool → Option (PAAxiomCertificate × List Bool)
  | 0, _ => none
  | fuel + 1, bits => do
      let (tag, bits) ← decodeBinaryNat bits
      match tag with
      | 0 => pure (.eqRefl, bits)
      | 1 => pure (.eqSymm, bits)
      | 2 => pure (.eqTrans, bits)
      | 3 => do
          let (arity, bits) ← decodeBinaryNat bits
          let (functionCode, bits) ← decodeBinaryNat bits
          let functionSymbol ←
            (Encodable.decode₂ _ functionCode :
              Option (LO.FirstOrder.Language.Func ℒₒᵣ arity))
          pure (.eqFuncExt functionSymbol, bits)
      | 4 => do
          let (arity, bits) ← decodeBinaryNat bits
          let (relationCode, bits) ← decodeBinaryNat bits
          let relationSymbol ←
            (Encodable.decode₂ _ relationCode :
              Option (LO.FirstOrder.Language.Rel ℒₒᵣ arity))
          pure (.eqRelExt relationSymbol, bits)
      | 5 => pure (.addZero, bits)
      | 6 => pure (.addAssoc, bits)
      | 7 => pure (.addComm, bits)
      | 8 => pure (.addEqOfLt, bits)
      | 9 => pure (.zeroLe, bits)
      | 10 => pure (.zeroLtOne, bits)
      | 11 => pure (.oneLeOfZeroLt, bits)
      | 12 => pure (.addLtAdd, bits)
      | 13 => pure (.mulZero, bits)
      | 14 => pure (.mulOne, bits)
      | 15 => pure (.mulAssoc, bits)
      | 16 => pure (.mulComm, bits)
      | 17 => pure (.mulLtMul, bits)
      | 18 => pure (.distr, bits)
      | 19 => pure (.ltIrrefl, bits)
      | 20 => pure (.ltTrans, bits)
      | 21 => pure (.ltTri, bits)
      | 22 => do
          let (body, bits) ←
            FoundationCompactPAProofVerifier.decodeCompactFormula
              1 fuel bits
          pure (.induction body, bits)
      | _ => none

theorem decodePAAxiomCertificate_binaryCode_append
    (certificate : PAAxiomCertificate)
    (fuel : Nat)
    (hfuel : axiomCertificateParseWeight certificate < fuel)
    (suffix : List Bool) :
    decodePAAxiomCertificate fuel
        (binaryPAAxiomCertificateCode certificate ++ suffix) =
      some (certificate, suffix) := by
  cases fuel with
  | zero =>
      simp [axiomCertificateParseWeight] at hfuel
  | succ fuel =>
      cases certificate with
      | induction body =>
          have hbody : formulaSymbolCount body < fuel := by
            simp [axiomCertificateParseWeight] at hfuel
            omega
          simp [binaryPAAxiomCertificateCode,
            decodePAAxiomCertificate,
            FoundationCompactPAProofVerifier.decodeCompactFormula_binaryFormulaCode_append
              body fuel hbody]
      | eqRefl => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | eqSymm => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | eqTrans => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | eqFuncExt functionSymbol =>
          simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | eqRelExt relationSymbol =>
          simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | addZero => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | addAssoc => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | addComm => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | addEqOfLt => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | zeroLe => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | zeroLtOne => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | oneLeOfZeroLt => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | addLtAdd => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | mulZero => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | mulOne => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | mulAssoc => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | mulComm => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | mulLtMul => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | distr => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | ltIrrefl => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | ltTrans => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]
      | ltTri => simp [binaryPAAxiomCertificateCode, decodePAAxiomCertificate]

def binaryStructuralValidityCertificateCode :
    StructuralValidityCertificate → List Bool
  | .leaf => binaryNatCode 0
  | .axiomCert certificate =>
      binaryNatCode 1 ++ binaryPAAxiomCertificateCode certificate
  | .unary premise =>
      binaryNatCode 2 ++
        binaryStructuralValidityCertificateCode premise
  | .binary left right =>
      binaryNatCode 3 ++
        binaryStructuralValidityCertificateCode left ++
        binaryStructuralValidityCertificateCode right

def structuralCertificateParseWeight :
    StructuralValidityCertificate → Nat
  | .leaf => 1
  | .axiomCert certificate =>
      1 + axiomCertificateParseWeight certificate
  | .unary premise =>
      1 + structuralCertificateParseWeight premise
  | .binary left right =>
      1 + structuralCertificateParseWeight left +
        structuralCertificateParseWeight right

def decodeStructuralValidityCertificate :
    Nat → List Bool →
      Option (StructuralValidityCertificate × List Bool)
  | 0, _ => none
  | fuel + 1, bits => do
      let (tag, bits) ← decodeBinaryNat bits
      match tag with
      | 0 => pure (.leaf, bits)
      | 1 => do
          let (certificate, bits) ←
            decodePAAxiomCertificate fuel bits
          pure (.axiomCert certificate, bits)
      | 2 => do
          let (premise, bits) ←
            decodeStructuralValidityCertificate fuel bits
          pure (.unary premise, bits)
      | 3 => do
          let (left, bits) ←
            decodeStructuralValidityCertificate fuel bits
          let (right, bits) ←
            decodeStructuralValidityCertificate fuel bits
          pure (.binary left right, bits)
      | _ => none

theorem decodeStructuralValidityCertificate_binaryCode_append
    (certificate : StructuralValidityCertificate)
    (fuel : Nat)
    (hfuel : structuralCertificateParseWeight certificate < fuel)
    (suffix : List Bool) :
    decodeStructuralValidityCertificate fuel
        (binaryStructuralValidityCertificateCode certificate ++ suffix) =
      some (certificate, suffix) := by
  induction certificate generalizing fuel suffix with
  | leaf =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [binaryStructuralValidityCertificateCode,
            decodeStructuralValidityCertificate]
  | axiomCert axiomCertificate =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have haxiom :
              axiomCertificateParseWeight axiomCertificate < fuel := by
            simp [structuralCertificateParseWeight] at hfuel
            omega
          simp [binaryStructuralValidityCertificateCode,
            decodeStructuralValidityCertificate,
            decodePAAxiomCertificate_binaryCode_append
              axiomCertificate fuel haxiom]
  | unary premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hpremise :
              structuralCertificateParseWeight premise < fuel := by
            simp [structuralCertificateParseWeight] at hfuel
            omega
          simp [binaryStructuralValidityCertificateCode,
            decodeStructuralValidityCertificate,
            ih fuel hpremise]
  | binary left right ihLeft ihRight =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hleft :
              structuralCertificateParseWeight left < fuel := by
            simp [structuralCertificateParseWeight] at hfuel
            omega
          have hright :
              structuralCertificateParseWeight right < fuel := by
            simp [structuralCertificateParseWeight] at hfuel
            omega
          simp [binaryStructuralValidityCertificateCode,
            decodeStructuralValidityCertificate,
            ihLeft fuel hleft, ihRight fuel hright]

theorem structuralCertificateParseWeight_le_binaryCode_length
    (certificate : StructuralValidityCertificate) :
    structuralCertificateParseWeight certificate ≤
      (binaryStructuralValidityCertificateCode certificate).length := by
  induction certificate with
  | leaf =>
      simp [structuralCertificateParseWeight,
        binaryStructuralValidityCertificateCode, binaryNatCode]
  | axiomCert axiomCertificate =>
      have haxiom :=
        axiomCertificateParseWeight_le_binaryCode_length axiomCertificate
      simp only [structuralCertificateParseWeight,
        binaryStructuralValidityCertificateCode, List.length_append]
      have htag := two_le_binaryNatCode_length 1
      omega
  | unary premise ih =>
      simp only [structuralCertificateParseWeight,
        binaryStructuralValidityCertificateCode, List.length_append]
      have htag := two_le_binaryNatCode_length 2
      omega
  | binary left right ihLeft ihRight =>
      simp only [structuralCertificateParseWeight,
        binaryStructuralValidityCertificateCode, List.length_append]
      have htag := two_le_binaryNatCode_length 3
      omega

def StructuralValidityCertificate.packedCode
    (certificate : StructuralValidityCertificate) : Nat :=
  packBinaryString (binaryStructuralValidityCertificateCode certificate)

def decodePackedStructuralValidityCertificate
    (code : Nat) : Option StructuralValidityCertificate := do
  let bits := code.bits
  guard (bits.getLast? = some true)
  let payload := bits.dropLast
  let (certificate, suffix) ←
    decodeStructuralValidityCertificate (payload.length + 1) payload
  guard suffix.isEmpty
  pure certificate

theorem decodeStructuralValidityCertificate_binaryCode
    (certificate : StructuralValidityCertificate) :
    decodeStructuralValidityCertificate
        ((binaryStructuralValidityCertificateCode certificate).length + 1)
        (binaryStructuralValidityCertificateCode certificate) =
      some (certificate, []) := by
  have hfuel :
      structuralCertificateParseWeight certificate <
        (binaryStructuralValidityCertificateCode certificate).length + 1 := by
    have hweight :=
      structuralCertificateParseWeight_le_binaryCode_length certificate
    omega
  simpa using
    decodeStructuralValidityCertificate_binaryCode_append certificate
      ((binaryStructuralValidityCertificateCode certificate).length + 1)
      hfuel []

@[simp] theorem decodePackedStructuralValidityCertificate_packedCode
    (certificate : StructuralValidityCertificate) :
    decodePackedStructuralValidityCertificate certificate.packedCode =
      some certificate := by
  simp [decodePackedStructuralValidityCertificate,
    StructuralValidityCertificate.packedCode,
    decodeStructuralValidityCertificate_binaryCode]

@[simp] theorem StructuralValidityCertificate.size_packedCode
    (certificate : StructuralValidityCertificate) :
    Nat.size certificate.packedCode =
      (binaryStructuralValidityCertificateCode certificate).length + 1 := by
  simp [StructuralValidityCertificate.packedCode]

@[simp] theorem StructuralValidityCertificate.packedPayloadLength_packedCode
    (certificate : StructuralValidityCertificate) :
    packedPayloadLength certificate.packedCode =
      (binaryStructuralValidityCertificateCode certificate).length := by
  simp [packedPayloadLength]

end FoundationCompactPAAxiomCertificate
