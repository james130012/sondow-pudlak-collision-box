import integration.FoundationCompactPAQuantitativeEqualityTransitivity
import integration.FoundationCompactPAQuantitativeFunctionCongruence
import integration.FoundationCompactCertifiedContextProof

/-!
# Quantitative equality operations under a finite PA context

The closed equality compiler is not enough inside nested bounded quantifiers:
the current eigenvariables are pinned to concrete numerals by local equality
assumptions.  This module lifts equality transitivity and binary function
congruence to that retained context.  Every constructor emits a real
`Derivation2 PA`, reuses explicit structural certificates, and carries a
full-payload assembly bound.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPACertifiedContextEquality

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

def contextualEqualityTransitivity
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftProof : CertifiedPAContextProof Gamma
      (“!!left = !!middle” : LO.FirstOrder.ArithmeticProposition))
    (rightProof : CertifiedPAContextProof Gamma
      (“!!middle = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAContextProof Gamma
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition) :=
  CertifiedPAContextProof.modusPonens
    (CertifiedPAContextProof.modusPonens
      (CertifiedPAContextProof.weakenCertified Gamma
        (equalityTransitivityImplication left middle right))
      leftProof)
    rightProof

def contextualEqualityTransitivityStructuralPayloadBound
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftPayloadLength rightPayloadLength : Nat) : Nat :=
  let firstFormula :=
    (“!!left = !!middle” : LO.FirstOrder.ArithmeticProposition)
  let secondFormula :=
    (“!!middle = !!right” : LO.FirstOrder.ArithmeticProposition)
  let resultFormula :=
    (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
  let afterFirstFormula := LO.Arrow.arrow secondFormula resultFormula
  let theoremFormula := LO.Arrow.arrow firstFormula afterFirstFormula
  let theoremProof := equalityTransitivityImplication left middle right
  let weakenedTheoremBound := theoremProof.payloadLength +
    weakeningFullAssemblyCost (insert theoremFormula Gamma)
  let afterFirstBound := weakenedTheoremBound + leftPayloadLength +
    contextualModusPonensFullAssemblyCost
      Gamma firstFormula afterFirstFormula
  afterFirstBound + rightPayloadLength +
    contextualModusPonensFullAssemblyCost
      Gamma secondFormula resultFormula

theorem contextualEqualityTransitivity_payloadLength_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftProof : CertifiedPAContextProof Gamma
      (“!!left = !!middle” : LO.FirstOrder.ArithmeticProposition))
    (rightProof : CertifiedPAContextProof Gamma
      (“!!middle = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    (contextualEqualityTransitivity
      left middle right leftProof rightProof).payloadLength ≤
      contextualEqualityTransitivityStructuralPayloadBound
        Gamma left middle right
        leftProof.payloadLength rightProof.payloadLength := by
  let theoremProof := equalityTransitivityImplication left middle right
  let contextualTheorem :=
    CertifiedPAContextProof.weakenCertified Gamma theoremProof
  let afterFirst :=
    CertifiedPAContextProof.modusPonens contextualTheorem leftProof
  let firstFormula :=
    (“!!left = !!middle” : LO.FirstOrder.ArithmeticProposition)
  let secondFormula :=
    (“!!middle = !!right” : LO.FirstOrder.ArithmeticProposition)
  let resultFormula :=
    (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
  let afterFirstFormula := LO.Arrow.arrow secondFormula resultFormula
  let theoremFormula := LO.Arrow.arrow firstFormula afterFirstFormula
  let weakenedTheoremBound := theoremProof.payloadLength +
    weakeningFullAssemblyCost (insert theoremFormula Gamma)
  let afterFirstBound := weakenedTheoremBound + leftProof.payloadLength +
    contextualModusPonensFullAssemblyCost
      Gamma firstFormula afterFirstFormula
  have htheorem := CertifiedPAContextProof.weakenCertified_payloadLength_le
    Gamma theoremProof
  have hfirst := CertifiedPAContextProof.modusPonens_payloadLength_le
    contextualTheorem leftProof
  have hsecond := CertifiedPAContextProof.modusPonens_payloadLength_le
    afterFirst rightProof
  have hcontextualTheorem : contextualTheorem.payloadLength ≤
      weakenedTheoremBound := by
    simpa only [contextualTheorem, weakenedTheoremBound,
      theoremFormula] using htheorem
  have hafterFirst : afterFirst.payloadLength ≤ afterFirstBound := by
    calc
      afterFirst.payloadLength ≤ contextualTheorem.payloadLength +
          leftProof.payloadLength +
          contextualModusPonensFullAssemblyCost
            Gamma firstFormula afterFirstFormula := by
        simpa only [afterFirst, firstFormula, afterFirstFormula] using hfirst
      _ ≤ weakenedTheoremBound + leftProof.payloadLength +
          contextualModusPonensFullAssemblyCost
            Gamma firstFormula afterFirstFormula :=
        Nat.add_le_add_right
          (Nat.add_le_add_right hcontextualTheorem
            leftProof.payloadLength) _
      _ = afterFirstBound := by rfl
  calc
    (contextualEqualityTransitivity
        left middle right leftProof rightProof).payloadLength =
        (CertifiedPAContextProof.modusPonens
          afterFirst rightProof).payloadLength := by rfl
    _ ≤ afterFirst.payloadLength + rightProof.payloadLength +
        contextualModusPonensFullAssemblyCost
          Gamma secondFormula resultFormula := by
      simpa only [secondFormula, resultFormula] using hsecond
    _ ≤ afterFirstBound + rightProof.payloadLength +
        contextualModusPonensFullAssemblyCost
          Gamma secondFormula resultFormula :=
      Nat.add_le_add_right
        (Nat.add_le_add_right hafterFirst rightProof.payloadLength) _
    _ = contextualEqualityTransitivityStructuralPayloadBound
        Gamma left middle right
          leftProof.payloadLength rightProof.payloadLength := by
      simp only [contextualEqualityTransitivityStructuralPayloadBound]
      rfl

def contextualBinaryFunctionCongruenceFromEqualities
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAContextProof Gamma
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAContextProof Gamma
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAContextProof Gamma
      (binaryFunctionCongruenceConclusion functionSymbol
        leftFirst leftSecond rightFirst rightSecond) := by
  let truthProof := CertifiedPAContextProof.weakenCertified Gamma
    CertifiedPAProof.verumProof
  let innerProof := CertifiedPAContextProof.conjunction
    secondProof truthProof
  let antecedentRaw := CertifiedPAContextProof.conjunction
    firstProof innerProof
  have hantecedent :
      (“!!leftFirst = !!rightFirst” :
          LO.FirstOrder.ArithmeticProposition) ⋏
          ((“!!leftSecond = !!rightSecond” :
            LO.FirstOrder.ArithmeticProposition) ⋏ ⊤) =
        binaryFunctionCongruenceAntecedent
          leftFirst leftSecond rightFirst rightSecond := by
    simp [binaryFunctionCongruenceAntecedent]
  let antecedentProof := CertifiedPAContextProof.cast
    hantecedent antecedentRaw
  let implicationProof := CertifiedPAContextProof.weakenCertified Gamma
    (binaryFunctionExtImplication functionSymbol
      leftFirst leftSecond rightFirst rightSecond)
  exact CertifiedPAContextProof.modusPonens
    implicationProof antecedentProof

def contextualBinaryFunctionCongruenceStructuralPayloadBound
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
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
  let antecedentFormula := binaryFunctionCongruenceAntecedent
    leftFirst leftSecond rightFirst rightSecond
  let conclusionFormula := binaryFunctionCongruenceConclusion functionSymbol
    leftFirst leftSecond rightFirst rightSecond
  let implicationFormula :=
    LO.Arrow.arrow antecedentFormula conclusionFormula
  let truthBound := CertifiedPAProof.verumProof.payloadLength +
    weakeningFullAssemblyCost (insert truthFormula Gamma)
  let innerBound := secondPayloadLength + truthBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost
      Gamma secondFormula truthFormula
  let antecedentBound := firstPayloadLength + innerBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost
      Gamma firstFormula innerFormula
  let implicationTheorem := binaryFunctionExtImplication functionSymbol
    leftFirst leftSecond rightFirst rightSecond
  let implicationBound := implicationTheorem.payloadLength +
    weakeningFullAssemblyCost (insert implicationFormula Gamma)
  implicationBound + antecedentBound +
    contextualModusPonensFullAssemblyCost
      Gamma antecedentFormula conclusionFormula

theorem contextualBinaryFunctionCongruence_payloadLength_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAContextProof Gamma
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAContextProof Gamma
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    (contextualBinaryFunctionCongruenceFromEqualities functionSymbol
      leftFirst leftSecond rightFirst rightSecond
      firstProof secondProof).payloadLength ≤
      contextualBinaryFunctionCongruenceStructuralPayloadBound
        Gamma functionSymbol leftFirst leftSecond rightFirst rightSecond
        firstProof.payloadLength secondProof.payloadLength := by
  let firstFormula :=
    (“!!leftFirst = !!rightFirst” :
      LO.FirstOrder.ArithmeticProposition)
  let secondFormula :=
    (“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition)
  let truthFormula := (⊤ : LO.FirstOrder.ArithmeticProposition)
  let innerFormula := secondFormula ⋏ truthFormula
  let antecedentFormula := binaryFunctionCongruenceAntecedent
    leftFirst leftSecond rightFirst rightSecond
  let conclusionFormula := binaryFunctionCongruenceConclusion functionSymbol
    leftFirst leftSecond rightFirst rightSecond
  let implicationFormula :=
    LO.Arrow.arrow antecedentFormula conclusionFormula
  let truthProof := CertifiedPAContextProof.weakenCertified Gamma
    CertifiedPAProof.verumProof
  let innerProof := CertifiedPAContextProof.conjunction
    secondProof truthProof
  let antecedentRaw := CertifiedPAContextProof.conjunction
    firstProof innerProof
  have hantecedent : firstFormula ⋏ innerFormula = antecedentFormula := by
    simp [firstFormula, secondFormula, truthFormula, innerFormula,
      antecedentFormula, binaryFunctionCongruenceAntecedent]
  let antecedentProof := CertifiedPAContextProof.cast
    hantecedent antecedentRaw
  let implicationTheorem := binaryFunctionExtImplication functionSymbol
    leftFirst leftSecond rightFirst rightSecond
  let implicationProof := CertifiedPAContextProof.weakenCertified
    Gamma implicationTheorem
  let truthBound := CertifiedPAProof.verumProof.payloadLength +
    weakeningFullAssemblyCost (insert truthFormula Gamma)
  let innerBound := secondProof.payloadLength + truthBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost
      Gamma secondFormula truthFormula
  let antecedentBound := firstProof.payloadLength + innerBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost
      Gamma firstFormula innerFormula
  let implicationBound := implicationTheorem.payloadLength +
    weakeningFullAssemblyCost (insert implicationFormula Gamma)
  have htruth := CertifiedPAContextProof.weakenCertified_payloadLength_le
    Gamma CertifiedPAProof.verumProof
  have hinner := CertifiedPAContextProof.conjunction_payloadLength_le
    secondProof truthProof
  have hantecedentRaw := CertifiedPAContextProof.conjunction_payloadLength_le
    firstProof innerProof
  have himplication := CertifiedPAContextProof.weakenCertified_payloadLength_le
    Gamma implicationTheorem
  have hmp := CertifiedPAContextProof.modusPonens_payloadLength_le
    implicationProof antecedentProof
  have hantecedentPayload : antecedentProof.payloadLength =
      antecedentRaw.payloadLength :=
    CertifiedPAContextProof.cast_payloadLength _ _
  have htruthPayload : truthProof.payloadLength ≤ truthBound := by
    simpa only [truthProof, truthBound, truthFormula] using htruth
  have hinnerPayload : innerProof.payloadLength ≤ innerBound := by
    calc
      innerProof.payloadLength ≤ secondProof.payloadLength +
          truthProof.payloadLength +
          CertifiedPAContextProof.conjunctionFullAssemblyCost
            Gamma secondFormula truthFormula := by
        simpa only [innerProof, secondFormula, truthFormula] using hinner
      _ ≤ secondProof.payloadLength + truthBound +
          CertifiedPAContextProof.conjunctionFullAssemblyCost
            Gamma secondFormula truthFormula :=
        Nat.add_le_add_right
          (Nat.add_le_add_left htruthPayload secondProof.payloadLength) _
      _ = innerBound := by rfl
  have hantecedentRawPayload : antecedentRaw.payloadLength ≤
      antecedentBound := by
    calc
      antecedentRaw.payloadLength ≤ firstProof.payloadLength +
          innerProof.payloadLength +
          CertifiedPAContextProof.conjunctionFullAssemblyCost
            Gamma firstFormula innerFormula := by
        simpa only [antecedentRaw, firstFormula, innerFormula]
          using hantecedentRaw
      _ ≤ firstProof.payloadLength + innerBound +
          CertifiedPAContextProof.conjunctionFullAssemblyCost
            Gamma firstFormula innerFormula :=
        Nat.add_le_add_right
          (Nat.add_le_add_left hinnerPayload firstProof.payloadLength) _
      _ = antecedentBound := by rfl
  have hantecedentProofPayload : antecedentProof.payloadLength ≤
      antecedentBound := by
    rw [hantecedentPayload]
    exact hantecedentRawPayload
  have himplicationPayload : implicationProof.payloadLength ≤
      implicationBound := by
    simpa only [implicationProof, implicationBound,
      implicationFormula] using himplication
  calc
    (contextualBinaryFunctionCongruenceFromEqualities functionSymbol
        leftFirst leftSecond rightFirst rightSecond
        firstProof secondProof).payloadLength =
        (CertifiedPAContextProof.modusPonens
          implicationProof antecedentProof).payloadLength := by rfl
    _ ≤ implicationProof.payloadLength + antecedentProof.payloadLength +
        contextualModusPonensFullAssemblyCost
          Gamma antecedentFormula conclusionFormula := by
      simpa only [antecedentFormula, conclusionFormula] using hmp
    _ ≤ implicationBound + antecedentBound +
        contextualModusPonensFullAssemblyCost
          Gamma antecedentFormula conclusionFormula :=
      Nat.add_le_add_right
        (Nat.add_le_add himplicationPayload hantecedentProofPayload) _
    _ = contextualBinaryFunctionCongruenceStructuralPayloadBound
        Gamma functionSymbol leftFirst leftSecond rightFirst rightSecond
          firstProof.payloadLength secondProof.payloadLength := by
      simp only [contextualBinaryFunctionCongruenceStructuralPayloadBound]
      rfl

def contextualAddCongruence
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAContextProof Gamma
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAContextProof Gamma
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAContextProof Gamma
      (“!!leftFirst + !!leftSecond = !!rightFirst + !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition) :=
  CertifiedPAContextProof.cast
    (binaryFunctionCongruenceConclusion_add_formula
      leftFirst leftSecond rightFirst rightSecond)
    (contextualBinaryFunctionCongruenceFromEqualities Language.Add.add
      leftFirst leftSecond rightFirst rightSecond firstProof secondProof)

def contextualMulCongruence
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAContextProof Gamma
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAContextProof Gamma
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAContextProof Gamma
      (“!!leftFirst * !!leftSecond = !!rightFirst * !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition) :=
  CertifiedPAContextProof.cast
    (binaryFunctionCongruenceConclusion_mul_formula
      leftFirst leftSecond rightFirst rightSecond)
    (contextualBinaryFunctionCongruenceFromEqualities Language.Mul.mul
      leftFirst leftSecond rightFirst rightSecond firstProof secondProof)

#print axioms contextualEqualityTransitivity
#print axioms contextualEqualityTransitivity_payloadLength_le
#print axioms contextualBinaryFunctionCongruenceFromEqualities
#print axioms contextualBinaryFunctionCongruence_payloadLength_le
#print axioms contextualAddCongruence
#print axioms contextualMulCongruence

end FoundationCompactPACertifiedContextEquality
