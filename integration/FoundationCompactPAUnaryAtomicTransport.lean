import integration.FoundationCompactPAUnaryTermEqualityImplication
import integration.FoundationCompactPAQuantitativeRelationCongruence

/-!
# Atomic formula transport under a parameter equality

Positive relation atoms use PA relation extensionality.  Negative atoms use
the reversed positive implication and contextual modus tollens.  The shared
parameter equality remains a real local sequent assumption throughout.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAUnaryAtomicTransport

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAUnaryTermSubstitutionEquality
open FoundationCompactPAUnaryTermEqualityImplication

def unaryRelationFormula
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  LO.FirstOrder.Semiformula.rel relationSymbol
    ![instantiateUnaryTerm (arguments 0) witness,
      instantiateUnaryTerm (arguments 1) witness]

theorem unaryRelationFormula_substitution
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (LO.FirstOrder.Semiformula.rel relationSymbol arguments)/[witness] =
      unaryRelationFormula relationSymbol arguments witness := by
  unfold unaryRelationFormula instantiateUnaryTerm
  simp only [Semiformula.rew_rel]
  rw [Matrix.fun_eq_vec_two
    (fun index => (Rew.subst ![witness]) (arguments index))]

theorem unaryNegatedRelationFormula_substitution
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (LO.FirstOrder.Semiformula.nrel relationSymbol arguments)/[witness] =
      ∼unaryRelationFormula relationSymbol arguments witness := by
  unfold unaryRelationFormula instantiateUnaryTerm
  simp only [Semiformula.rew_nrel]
  rw [Matrix.fun_eq_vec_two
    (fun index => (Rew.subst ![witness]) (arguments index))]
  rw [Semiformula.neg_rel]

def relationTransportImplicationFromEqualities
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstEquality : CertifiedPAContextProof Gamma
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondEquality : CertifiedPAContextProof Gamma
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAContextProof Gamma
      (binaryRelationFormula relationSymbol leftFirst leftSecond 🡒
        binaryRelationFormula relationSymbol rightFirst rightSecond) := by
  let truthProof := CertifiedPAContextProof.weakenCertified Gamma
    CertifiedPAProof.verumProof
  let innerProof := CertifiedPAContextProof.conjunction
    secondEquality truthProof
  let antecedentRaw := CertifiedPAContextProof.conjunction
    firstEquality innerProof
  have hantecedent :
      (“!!leftFirst = !!rightFirst” :
          LO.FirstOrder.ArithmeticProposition) ⋏
          ((“!!leftSecond = !!rightSecond” :
            LO.FirstOrder.ArithmeticProposition) ⋏ ⊤) =
        binaryRelationCongruenceAntecedent
          leftFirst leftSecond rightFirst rightSecond := by
    simp [binaryRelationCongruenceAntecedent]
  let antecedentProof := CertifiedPAContextProof.cast
    hantecedent antecedentRaw
  let implicationTheorem := binaryRelationExtImplication
    relationSymbol leftFirst leftSecond rightFirst rightSecond
  let implicationProof := CertifiedPAContextProof.weakenCertified
    Gamma implicationTheorem
  exact CertifiedPAContextProof.modusPonens
    implicationProof antecedentProof

def relationTransportImplicationStructuralPayloadBound
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstPayloadLength secondPayloadLength : Nat) : Nat :=
  let firstFormula :=
    (“!!leftFirst = !!rightFirst” :
      LO.FirstOrder.ArithmeticProposition)
  let secondFormula :=
    (“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition)
  let truthFormula := (⊤ : LO.FirstOrder.ArithmeticProposition)
  let innerFormula := secondFormula ⋏ truthFormula
  let antecedentFormula := binaryRelationCongruenceAntecedent
    leftFirst leftSecond rightFirst rightSecond
  let conclusionFormula := binaryRelationCongruenceConclusion relationSymbol
    leftFirst leftSecond rightFirst rightSecond
  let implicationFormula := antecedentFormula 🡒 conclusionFormula
  let truthBound := CertifiedPAProof.verumProof.payloadLength +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert truthFormula Gamma)
  let innerBound := secondPayloadLength + truthBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost
      Gamma secondFormula truthFormula
  let antecedentBound := firstPayloadLength + innerBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost
      Gamma firstFormula innerFormula
  let implicationTheorem := binaryRelationExtImplication relationSymbol
    leftFirst leftSecond rightFirst rightSecond
  let implicationBound := implicationTheorem.payloadLength +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert implicationFormula Gamma)
  implicationBound + antecedentBound +
    FoundationCompactCertifiedContextualModusPonens.contextualModusPonensFullAssemblyCost
      Gamma antecedentFormula conclusionFormula

theorem relationTransportImplicationStructuralPayloadBound_mono
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {firstPayloadLength secondPayloadLength firstBound secondBound : Nat}
    (hfirst : firstPayloadLength <= firstBound)
    (hsecond : secondPayloadLength <= secondBound) :
    relationTransportImplicationStructuralPayloadBound Gamma relationSymbol
        leftFirst leftSecond rightFirst rightSecond
        firstPayloadLength secondPayloadLength <=
      relationTransportImplicationStructuralPayloadBound Gamma relationSymbol
        leftFirst leftSecond rightFirst rightSecond
        firstBound secondBound := by
  unfold relationTransportImplicationStructuralPayloadBound
  dsimp only
  omega

theorem relationTransportImplicationFromEqualities_payloadLength_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstEquality : CertifiedPAContextProof Gamma
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondEquality : CertifiedPAContextProof Gamma
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    (relationTransportImplicationFromEqualities relationSymbol
      leftFirst leftSecond rightFirst rightSecond
      firstEquality secondEquality).payloadLength <=
      relationTransportImplicationStructuralPayloadBound Gamma
        relationSymbol leftFirst leftSecond rightFirst rightSecond
        firstEquality.payloadLength secondEquality.payloadLength := by
  let firstFormula :=
    (“!!leftFirst = !!rightFirst” :
      LO.FirstOrder.ArithmeticProposition)
  let secondFormula :=
    (“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition)
  let truthFormula := (⊤ : LO.FirstOrder.ArithmeticProposition)
  let innerFormula := secondFormula ⋏ truthFormula
  let antecedentFormula := binaryRelationCongruenceAntecedent
    leftFirst leftSecond rightFirst rightSecond
  let conclusionFormula := binaryRelationCongruenceConclusion relationSymbol
    leftFirst leftSecond rightFirst rightSecond
  let implicationFormula := antecedentFormula 🡒 conclusionFormula
  let truthProof := CertifiedPAContextProof.weakenCertified Gamma
    CertifiedPAProof.verumProof
  let innerProof := CertifiedPAContextProof.conjunction
    secondEquality truthProof
  let antecedentRaw := CertifiedPAContextProof.conjunction
    firstEquality innerProof
  have hantecedent : firstFormula ⋏ innerFormula =
      antecedentFormula := by
    simp [firstFormula, secondFormula, truthFormula, innerFormula,
      antecedentFormula, binaryRelationCongruenceAntecedent]
  let antecedentProof := CertifiedPAContextProof.cast
    hantecedent antecedentRaw
  let implicationTheorem := binaryRelationExtImplication relationSymbol
    leftFirst leftSecond rightFirst rightSecond
  let implicationProof := CertifiedPAContextProof.weakenCertified
    Gamma implicationTheorem
  let result := CertifiedPAContextProof.modusPonens
    implicationProof antecedentProof
  let truthBound := CertifiedPAProof.verumProof.payloadLength +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert truthFormula Gamma)
  let innerBound := secondEquality.payloadLength + truthBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost
      Gamma secondFormula truthFormula
  let antecedentBound := firstEquality.payloadLength + innerBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost
      Gamma firstFormula innerFormula
  let implicationBound := implicationTheorem.payloadLength +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert implicationFormula Gamma)
  have htruth := CertifiedPAContextProof.weakenCertified_payloadLength_le
    Gamma CertifiedPAProof.verumProof
  have hinner := CertifiedPAContextProof.conjunction_payloadLength_le
    secondEquality truthProof
  have hantecedentRaw := CertifiedPAContextProof.conjunction_payloadLength_le
    firstEquality innerProof
  have himplication :=
    CertifiedPAContextProof.weakenCertified_payloadLength_le
      Gamma implicationTheorem
  have hmp := CertifiedPAContextProof.modusPonens_payloadLength_le
    implicationProof antecedentProof
  have hantecedentPayload : antecedentProof.payloadLength =
      antecedentRaw.payloadLength := by
    dsimp only [antecedentProof]
    exact CertifiedPAContextProof.cast_payloadLength _ _
  have htruthPayload : truthProof.payloadLength <= truthBound := by
    simpa only [truthProof, truthBound, truthFormula] using htruth
  have hinnerPayload : innerProof.payloadLength <= innerBound := by
    calc
      innerProof.payloadLength <= secondEquality.payloadLength +
          truthProof.payloadLength +
          CertifiedPAContextProof.conjunctionFullAssemblyCost
            Gamma secondFormula truthFormula := by
        simpa only [innerProof] using hinner
      _ <= secondEquality.payloadLength + truthBound +
          CertifiedPAContextProof.conjunctionFullAssemblyCost
            Gamma secondFormula truthFormula :=
        Nat.add_le_add_right
          (Nat.add_le_add_left htruthPayload secondEquality.payloadLength) _
      _ = innerBound := by rfl
  have hantecedentRawPayload : antecedentRaw.payloadLength <=
      antecedentBound := by
    calc
      antecedentRaw.payloadLength <= firstEquality.payloadLength +
          innerProof.payloadLength +
          CertifiedPAContextProof.conjunctionFullAssemblyCost
            Gamma firstFormula innerFormula := by
        simpa only [antecedentRaw] using hantecedentRaw
      _ <= firstEquality.payloadLength + innerBound +
          CertifiedPAContextProof.conjunctionFullAssemblyCost
            Gamma firstFormula innerFormula :=
        Nat.add_le_add_right
          (Nat.add_le_add_left hinnerPayload firstEquality.payloadLength) _
      _ = antecedentBound := by rfl
  have hantecedentProofPayload : antecedentProof.payloadLength <=
      antecedentBound := by
    rw [hantecedentPayload]
    exact hantecedentRawPayload
  have himplicationPayload : implicationProof.payloadLength <=
      implicationBound := by
    simpa only [implicationProof, implicationBound,
      implicationFormula] using himplication
  have hresult :
      relationTransportImplicationFromEqualities relationSymbol
        leftFirst leftSecond rightFirst rightSecond
        firstEquality secondEquality = result := by
    rfl
  rw [hresult]
  calc
    result.payloadLength <= implicationProof.payloadLength +
        antecedentProof.payloadLength +
        FoundationCompactCertifiedContextualModusPonens.contextualModusPonensFullAssemblyCost
          Gamma antecedentFormula conclusionFormula := by
      simpa only [result] using hmp
    _ <= implicationBound + antecedentBound +
        FoundationCompactCertifiedContextualModusPonens.contextualModusPonensFullAssemblyCost
          Gamma antecedentFormula conclusionFormula :=
      Nat.add_le_add_right
        (Nat.add_le_add himplicationPayload hantecedentProofPayload) _
    _ = relationTransportImplicationStructuralPayloadBound Gamma
        relationSymbol leftFirst leftSecond rightFirst rightSecond
        firstEquality.payloadLength secondEquality.payloadLength := by
      simp only [relationTransportImplicationStructuralPayloadBound]
      rfl

def positiveTransportImplicationUnderAssumption
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAContextProof (parameterEqualityContext left right)
      (unaryRelationFormula relationSymbol arguments left 🡒
        unaryRelationFormula relationSymbol arguments right) :=
  relationTransportImplicationFromEqualities relationSymbol
    (instantiateUnaryTerm (arguments 0) left)
    (instantiateUnaryTerm (arguments 1) left)
    (instantiateUnaryTerm (arguments 0) right)
    (instantiateUnaryTerm (arguments 1) right)
    (compileUnaryTermEqualityUnderAssumption (arguments 0) left right)
    (compileUnaryTermEqualityUnderAssumption (arguments 1) left right)

def positiveTransportImplicationStructuralPayloadBound
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  relationTransportImplicationStructuralPayloadBound
    (parameterEqualityContext left right) relationSymbol
    (instantiateUnaryTerm (arguments 0) left)
    (instantiateUnaryTerm (arguments 1) left)
    (instantiateUnaryTerm (arguments 0) right)
    (instantiateUnaryTerm (arguments 1) right)
    (unaryTermEqualityUnderAssumptionStructuralPayloadBound
      (arguments 0) left right)
    (unaryTermEqualityUnderAssumptionStructuralPayloadBound
      (arguments 1) left right)

theorem positiveTransportImplicationUnderAssumption_payloadLength_le
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (positiveTransportImplicationUnderAssumption relationSymbol
      arguments left right).payloadLength <=
      positiveTransportImplicationStructuralPayloadBound
        relationSymbol arguments left right := by
  have htransport :=
    relationTransportImplicationFromEqualities_payloadLength_le
      relationSymbol
      (instantiateUnaryTerm (arguments 0) left)
      (instantiateUnaryTerm (arguments 1) left)
      (instantiateUnaryTerm (arguments 0) right)
      (instantiateUnaryTerm (arguments 1) right)
      (compileUnaryTermEqualityUnderAssumption (arguments 0) left right)
      (compileUnaryTermEqualityUnderAssumption (arguments 1) left right)
  have hfirst :=
    compileUnaryTermEqualityUnderAssumption_payloadLength_le
      (arguments 0) left right
  have hsecond :=
    compileUnaryTermEqualityUnderAssumption_payloadLength_le
      (arguments 1) left right
  exact htransport.trans
    (relationTransportImplicationStructuralPayloadBound_mono
      (parameterEqualityContext left right) relationSymbol
      (instantiateUnaryTerm (arguments 0) left)
      (instantiateUnaryTerm (arguments 1) left)
      (instantiateUnaryTerm (arguments 0) right)
      (instantiateUnaryTerm (arguments 1) right)
      hfirst hsecond)

def positiveTransportUnderAssumption
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourceProof : CertifiedPAProof
      (unaryRelationFormula relationSymbol arguments left)) :
    CertifiedPAContextProof (parameterEqualityContext left right)
      (unaryRelationFormula relationSymbol arguments right) :=
  CertifiedPAContextProof.modusPonens
    (positiveTransportImplicationUnderAssumption
      relationSymbol arguments left right)
    (CertifiedPAContextProof.weakenCertified
      (parameterEqualityContext left right) sourceProof)

def positiveTransportUnderAssumptionStructuralPayloadBound
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourcePayloadLength : Nat) : Nat :=
  let Gamma := parameterEqualityContext left right
  let sourceFormula := unaryRelationFormula relationSymbol arguments left
  let targetFormula := unaryRelationFormula relationSymbol arguments right
  positiveTransportImplicationStructuralPayloadBound
      relationSymbol arguments left right +
    (sourcePayloadLength +
      FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
        (insert sourceFormula Gamma)) +
    FoundationCompactCertifiedContextualModusPonens.contextualModusPonensFullAssemblyCost
      Gamma sourceFormula targetFormula

theorem positiveTransportUnderAssumptionStructuralPayloadBound_mono_source
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {sourcePayloadLength sourcePayloadBound : Nat}
    (hsource : sourcePayloadLength <= sourcePayloadBound) :
    positiveTransportUnderAssumptionStructuralPayloadBound
        relationSymbol arguments left right sourcePayloadLength <=
      positiveTransportUnderAssumptionStructuralPayloadBound
        relationSymbol arguments left right sourcePayloadBound := by
  unfold positiveTransportUnderAssumptionStructuralPayloadBound
  dsimp only
  omega

theorem positiveTransportUnderAssumption_payloadLength_le
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourceProof : CertifiedPAProof
      (unaryRelationFormula relationSymbol arguments left)) :
    (positiveTransportUnderAssumption relationSymbol arguments
      left right sourceProof).payloadLength <=
      positiveTransportUnderAssumptionStructuralPayloadBound
        relationSymbol arguments left right sourceProof.payloadLength := by
  have himplication :=
    positiveTransportImplicationUnderAssumption_payloadLength_le
      relationSymbol arguments left right
  have hsource := CertifiedPAContextProof.weakenCertified_payloadLength_le
    (parameterEqualityContext left right) sourceProof
  have hmp := CertifiedPAContextProof.modusPonens_payloadLength_le
    (positiveTransportImplicationUnderAssumption
      relationSymbol arguments left right)
    (CertifiedPAContextProof.weakenCertified
      (parameterEqualityContext left right) sourceProof)
  unfold positiveTransportUnderAssumption
  unfold positiveTransportUnderAssumptionStructuralPayloadBound
  dsimp only at hsource hmp ⊢
  omega

def contextualEqualitySymmetryStructuralPayloadBound
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourcePayloadBound : Nat) : Nat :=
  (equalitySymmetryImplication left right).payloadLength +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert
        (“!!left = !!right → !!right = !!left” :
          LO.FirstOrder.ArithmeticProposition) Gamma) +
    sourcePayloadBound +
    FoundationCompactCertifiedContextualModusPonens.contextualModusPonensFullAssemblyCost
      Gamma
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
      (“!!right = !!left” : LO.FirstOrder.ArithmeticProposition)

theorem contextualEqualitySymmetry_payloadLength_le_structuralBound
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (proof : CertifiedPAContextProof Gamma
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition))
    (sourcePayloadBound : Nat)
    (hsource : proof.payloadLength <= sourcePayloadBound) :
    (CertifiedPAContextProof.equalitySymmetry
      left right proof).payloadLength <=
      contextualEqualitySymmetryStructuralPayloadBound
        Gamma left right sourcePayloadBound := by
  have hsymmetry := CertifiedPAContextProof.equalitySymmetry_payloadLength_le
    left right proof
  exact hsymmetry.trans (by
    unfold contextualEqualitySymmetryStructuralPayloadBound
    omega)

def negativeTransportUnderAssumption
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourceProof : CertifiedPAProof
      (∼unaryRelationFormula relationSymbol arguments left)) :
    CertifiedPAContextProof (parameterEqualityContext left right)
      (∼unaryRelationFormula relationSymbol arguments right) := by
  let firstForward := compileUnaryTermEqualityUnderAssumption
    (arguments 0) left right
  let secondForward := compileUnaryTermEqualityUnderAssumption
    (arguments 1) left right
  let firstReverse := CertifiedPAContextProof.equalitySymmetry
    (instantiateUnaryTerm (arguments 0) left)
    (instantiateUnaryTerm (arguments 0) right) firstForward
  let secondReverse := CertifiedPAContextProof.equalitySymmetry
    (instantiateUnaryTerm (arguments 1) left)
    (instantiateUnaryTerm (arguments 1) right) secondForward
  let reverseImplication := relationTransportImplicationFromEqualities
    relationSymbol
    (instantiateUnaryTerm (arguments 0) right)
    (instantiateUnaryTerm (arguments 1) right)
    (instantiateUnaryTerm (arguments 0) left)
    (instantiateUnaryTerm (arguments 1) left)
    firstReverse secondReverse
  let contextualSource := CertifiedPAContextProof.weakenCertified
    (parameterEqualityContext left right) sourceProof
  exact CertifiedPAContextProof.modusTollens
    reverseImplication contextualSource

def negativeTransportUnderAssumptionStructuralPayloadBound
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourcePayloadLength : Nat) : Nat :=
  let Gamma := parameterEqualityContext left right
  let leftFirst := instantiateUnaryTerm (arguments 0) left
  let leftSecond := instantiateUnaryTerm (arguments 1) left
  let rightFirst := instantiateUnaryTerm (arguments 0) right
  let rightSecond := instantiateUnaryTerm (arguments 1) right
  let firstForwardBound :=
    unaryTermEqualityUnderAssumptionStructuralPayloadBound
      (arguments 0) left right
  let secondForwardBound :=
    unaryTermEqualityUnderAssumptionStructuralPayloadBound
      (arguments 1) left right
  let firstReverseBound :=
    contextualEqualitySymmetryStructuralPayloadBound
      Gamma leftFirst rightFirst firstForwardBound
  let secondReverseBound :=
    contextualEqualitySymmetryStructuralPayloadBound
      Gamma leftSecond rightSecond secondForwardBound
  let reverseImplicationBound :=
    relationTransportImplicationStructuralPayloadBound Gamma relationSymbol
      rightFirst rightSecond leftFirst leftSecond
      firstReverseBound secondReverseBound
  let leftAtom := unaryRelationFormula relationSymbol arguments left
  let rightAtom := unaryRelationFormula relationSymbol arguments right
  let contextualSourceBound := sourcePayloadLength +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert (∼leftAtom) Gamma)
  reverseImplicationBound + contextualSourceBound +
    CertifiedPAContextProof.modusTollensFullAssemblyCost
      Gamma rightAtom leftAtom

theorem negativeTransportUnderAssumptionStructuralPayloadBound_mono_source
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {sourcePayloadLength sourcePayloadBound : Nat}
    (hsource : sourcePayloadLength <= sourcePayloadBound) :
    negativeTransportUnderAssumptionStructuralPayloadBound
        relationSymbol arguments left right sourcePayloadLength <=
      negativeTransportUnderAssumptionStructuralPayloadBound
        relationSymbol arguments left right sourcePayloadBound := by
  unfold negativeTransportUnderAssumptionStructuralPayloadBound
  dsimp only
  omega

theorem negativeTransportUnderAssumption_payloadLength_le
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourceProof : CertifiedPAProof
      (∼unaryRelationFormula relationSymbol arguments left)) :
    (negativeTransportUnderAssumption relationSymbol arguments
      left right sourceProof).payloadLength <=
      negativeTransportUnderAssumptionStructuralPayloadBound
        relationSymbol arguments left right sourceProof.payloadLength := by
  let Gamma := parameterEqualityContext left right
  let leftFirst := instantiateUnaryTerm (arguments 0) left
  let leftSecond := instantiateUnaryTerm (arguments 1) left
  let rightFirst := instantiateUnaryTerm (arguments 0) right
  let rightSecond := instantiateUnaryTerm (arguments 1) right
  let firstForward := compileUnaryTermEqualityUnderAssumption
    (arguments 0) left right
  let secondForward := compileUnaryTermEqualityUnderAssumption
    (arguments 1) left right
  let firstReverse := CertifiedPAContextProof.equalitySymmetry
    leftFirst rightFirst firstForward
  let secondReverse := CertifiedPAContextProof.equalitySymmetry
    leftSecond rightSecond secondForward
  let reverseImplication := relationTransportImplicationFromEqualities
    relationSymbol rightFirst rightSecond leftFirst leftSecond
    firstReverse secondReverse
  let contextualSource := CertifiedPAContextProof.weakenCertified
    Gamma sourceProof
  let result := CertifiedPAContextProof.modusTollens
    reverseImplication contextualSource
  let firstForwardBound :=
    unaryTermEqualityUnderAssumptionStructuralPayloadBound
      (arguments 0) left right
  let secondForwardBound :=
    unaryTermEqualityUnderAssumptionStructuralPayloadBound
      (arguments 1) left right
  let firstReverseBound :=
    contextualEqualitySymmetryStructuralPayloadBound
      Gamma leftFirst rightFirst firstForwardBound
  let secondReverseBound :=
    contextualEqualitySymmetryStructuralPayloadBound
      Gamma leftSecond rightSecond secondForwardBound
  let reverseImplicationBound :=
    relationTransportImplicationStructuralPayloadBound Gamma relationSymbol
      rightFirst rightSecond leftFirst leftSecond
      firstReverseBound secondReverseBound
  let leftAtom := unaryRelationFormula relationSymbol arguments left
  let rightAtom := unaryRelationFormula relationSymbol arguments right
  let contextualSourceBound := sourceProof.payloadLength +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert (∼leftAtom) Gamma)
  have hfirstForward :=
    compileUnaryTermEqualityUnderAssumption_payloadLength_le
      (arguments 0) left right
  have hsecondForward :=
    compileUnaryTermEqualityUnderAssumption_payloadLength_le
      (arguments 1) left right
  have hfirstReverse : firstReverse.payloadLength <= firstReverseBound :=
    contextualEqualitySymmetry_payloadLength_le_structuralBound
      leftFirst rightFirst firstForward firstForwardBound hfirstForward
  have hsecondReverse : secondReverse.payloadLength <= secondReverseBound :=
    contextualEqualitySymmetry_payloadLength_le_structuralBound
      leftSecond rightSecond secondForward secondForwardBound hsecondForward
  have hreverseRaw :=
    relationTransportImplicationFromEqualities_payloadLength_le
      relationSymbol rightFirst rightSecond leftFirst leftSecond
      firstReverse secondReverse
  have hreverse : reverseImplication.payloadLength <=
      reverseImplicationBound :=
    hreverseRaw.trans
      (relationTransportImplicationStructuralPayloadBound_mono
        Gamma relationSymbol rightFirst rightSecond leftFirst leftSecond
        hfirstReverse hsecondReverse)
  have hsourceRaw := CertifiedPAContextProof.weakenCertified_payloadLength_le
    Gamma sourceProof
  have hsource : contextualSource.payloadLength <=
      contextualSourceBound := by
    simpa only [contextualSource, contextualSourceBound, leftAtom] using
      hsourceRaw
  have hmodusTollens := CertifiedPAContextProof.modusTollens_payloadLength_le
    reverseImplication contextualSource
  have hresult :
      negativeTransportUnderAssumption relationSymbol arguments
        left right sourceProof = result := by
    rfl
  rw [hresult]
  calc
    result.payloadLength <= reverseImplication.payloadLength +
        contextualSource.payloadLength +
        CertifiedPAContextProof.modusTollensFullAssemblyCost
          Gamma rightAtom leftAtom := by
      simpa only [result, rightAtom, leftAtom, unaryRelationFormula,
        binaryRelationFormula] using hmodusTollens
    _ <= reverseImplicationBound + contextualSourceBound +
        CertifiedPAContextProof.modusTollensFullAssemblyCost
          Gamma rightAtom leftAtom :=
      Nat.add_le_add_right (Nat.add_le_add hreverse hsource) _
    _ = negativeTransportUnderAssumptionStructuralPayloadBound
        relationSymbol arguments left right sourceProof.payloadLength := by
      rfl

def provePositiveAtomicTransport
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourceProof : CertifiedPAProof
      (unaryRelationFormula relationSymbol arguments left)) :
    CertifiedPAProof
      (parameterEqualityFormula left right 🡒
        unaryRelationFormula relationSymbol arguments right) :=
  CertifiedPAContextProof.discharge
    (parameterEqualityFormula left right)
    (unaryRelationFormula relationSymbol arguments right)
    (positiveTransportUnderAssumption
      relationSymbol arguments left right sourceProof)

def proveNegativeAtomicTransport
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourceProof : CertifiedPAProof
      (∼unaryRelationFormula relationSymbol arguments left)) :
    CertifiedPAProof
      (parameterEqualityFormula left right 🡒
        ∼unaryRelationFormula relationSymbol arguments right) :=
  CertifiedPAContextProof.discharge
    (parameterEqualityFormula left right)
    (∼unaryRelationFormula relationSymbol arguments right)
    (negativeTransportUnderAssumption
      relationSymbol arguments left right sourceProof)

def positiveAtomicTransportStructuralPayloadBound
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourcePayloadLength : Nat) : Nat :=
  positiveTransportUnderAssumptionStructuralPayloadBound
      relationSymbol arguments left right sourcePayloadLength +
    CertifiedPAContextProof.dischargeFullAssemblyCost
      (parameterEqualityFormula left right)
      (unaryRelationFormula relationSymbol arguments right)

def negativeAtomicTransportStructuralPayloadBound
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourcePayloadLength : Nat) : Nat :=
  negativeTransportUnderAssumptionStructuralPayloadBound
      relationSymbol arguments left right sourcePayloadLength +
    CertifiedPAContextProof.dischargeFullAssemblyCost
      (parameterEqualityFormula left right)
      (∼unaryRelationFormula relationSymbol arguments right)

theorem provePositiveAtomicTransport_payloadLength_le
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourceProof : CertifiedPAProof
      (unaryRelationFormula relationSymbol arguments left)) :
    (provePositiveAtomicTransport relationSymbol arguments
      left right sourceProof).payloadLength <=
      positiveAtomicTransportStructuralPayloadBound
        relationSymbol arguments left right sourceProof.payloadLength := by
  have hcontext := positiveTransportUnderAssumption_payloadLength_le
    relationSymbol arguments left right sourceProof
  have hdischarge := CertifiedPAContextProof.discharge_payloadLength_le
    (parameterEqualityFormula left right)
    (unaryRelationFormula relationSymbol arguments right)
    (positiveTransportUnderAssumption
      relationSymbol arguments left right sourceProof)
  unfold provePositiveAtomicTransport
  unfold positiveAtomicTransportStructuralPayloadBound
  exact hdischarge.trans (Nat.add_le_add_right hcontext _)

theorem proveNegativeAtomicTransport_payloadLength_le
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourceProof : CertifiedPAProof
      (∼unaryRelationFormula relationSymbol arguments left)) :
    (proveNegativeAtomicTransport relationSymbol arguments
      left right sourceProof).payloadLength <=
      negativeAtomicTransportStructuralPayloadBound
        relationSymbol arguments left right sourceProof.payloadLength := by
  have hcontext := negativeTransportUnderAssumption_payloadLength_le
    relationSymbol arguments left right sourceProof
  have hdischarge := CertifiedPAContextProof.discharge_payloadLength_le
    (parameterEqualityFormula left right)
    (∼unaryRelationFormula relationSymbol arguments right)
    (negativeTransportUnderAssumption
      relationSymbol arguments left right sourceProof)
  unfold proveNegativeAtomicTransport
  unfold negativeAtomicTransportStructuralPayloadBound
  exact hdischarge.trans (Nat.add_le_add_right hcontext _)

theorem provePositiveAtomicTransport_verifier_eq_true
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourceProof : CertifiedPAProof
      (unaryRelationFormula relationSymbol arguments left)) :
    listedCompactCertifiedPAProofVerifier
      (provePositiveAtomicTransport relationSymbol arguments
        left right sourceProof).code
      (compactFormulaCode
        (parameterEqualityFormula left right 🡒
          unaryRelationFormula relationSymbol arguments right)) = true :=
  (provePositiveAtomicTransport relationSymbol arguments
    left right sourceProof).verifier_eq_true

theorem proveNegativeAtomicTransport_verifier_eq_true
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourceProof : CertifiedPAProof
      (∼unaryRelationFormula relationSymbol arguments left)) :
    listedCompactCertifiedPAProofVerifier
      (proveNegativeAtomicTransport relationSymbol arguments
        left right sourceProof).code
      (compactFormulaCode
        (parameterEqualityFormula left right 🡒
          ∼unaryRelationFormula relationSymbol arguments right)) = true :=
  (proveNegativeAtomicTransport relationSymbol arguments
    left right sourceProof).verifier_eq_true

theorem provePositiveAtomicTransport_checked_structuralBound
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourceProof : CertifiedPAProof
      (unaryRelationFormula relationSymbol arguments left)) :
    listedCompactCertifiedPAProofVerifier
        (provePositiveAtomicTransport relationSymbol arguments
          left right sourceProof).code
        (compactFormulaCode
          (parameterEqualityFormula left right 🡒
            unaryRelationFormula relationSymbol arguments right)) = true ∧
      (provePositiveAtomicTransport relationSymbol arguments
        left right sourceProof).payloadLength <=
        positiveAtomicTransportStructuralPayloadBound
          relationSymbol arguments left right sourceProof.payloadLength :=
  ⟨provePositiveAtomicTransport_verifier_eq_true
      relationSymbol arguments left right sourceProof,
    provePositiveAtomicTransport_payloadLength_le
      relationSymbol arguments left right sourceProof⟩

theorem proveNegativeAtomicTransport_checked_structuralBound
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourceProof : CertifiedPAProof
      (∼unaryRelationFormula relationSymbol arguments left)) :
    listedCompactCertifiedPAProofVerifier
        (proveNegativeAtomicTransport relationSymbol arguments
          left right sourceProof).code
        (compactFormulaCode
          (parameterEqualityFormula left right 🡒
            ∼unaryRelationFormula relationSymbol arguments right)) = true ∧
      (proveNegativeAtomicTransport relationSymbol arguments
        left right sourceProof).payloadLength <=
        negativeAtomicTransportStructuralPayloadBound
          relationSymbol arguments left right sourceProof.payloadLength :=
  ⟨proveNegativeAtomicTransport_verifier_eq_true
      relationSymbol arguments left right sourceProof,
    proveNegativeAtomicTransport_payloadLength_le
      relationSymbol arguments left right sourceProof⟩

#print axioms relationTransportImplicationFromEqualities
#print axioms positiveTransportUnderAssumption
#print axioms negativeTransportUnderAssumption
#print axioms provePositiveAtomicTransport_verifier_eq_true
#print axioms proveNegativeAtomicTransport_verifier_eq_true
#print axioms provePositiveAtomicTransport_checked_structuralBound
#print axioms proveNegativeAtomicTransport_checked_structuralBound

end FoundationCompactPAUnaryAtomicTransport
