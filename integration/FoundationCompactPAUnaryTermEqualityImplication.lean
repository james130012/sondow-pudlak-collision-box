import integration.FoundationCompactCertifiedContextProof
import integration.FoundationCompactPAUnaryTermSubstitutionEquality
import integration.FoundationCompactPAQuantitativeFunctionCongruence

/-!
# Conditional equality transport through unary arithmetic terms

This compiler proves `(left = right) -> (t(left) = t(right))`.  The parameter
equality is a genuine local sequent assumption.  The detailed compiler emits
the actual contextual proof together with a structural full-payload bound
assembled from the checked costs of every constructor it uses.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAUnaryTermEqualityImplication

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAUnaryTermSubstitutionEquality

def parameterEqualityFormula
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)

def parameterEqualityContext
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    Finset LO.FirstOrder.ArithmeticProposition :=
  {∼parameterEqualityFormula left right}

def unaryTermEqualityFormula
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  (“!!(instantiateUnaryTerm term left) =
    !!(instantiateUnaryTerm term right)” :
    LO.FirstOrder.ArithmeticProposition)

structure UnaryTermEqualityUnderAssumptionCompilation
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) where
  proof : CertifiedPAContextProof (parameterEqualityContext left right)
    (unaryTermEqualityFormula term left right)
  structuralPayloadBound : Nat
  payloadLength_le : proof.payloadLength <= structuralPayloadBound

noncomputable def compileUnaryTermEqualityUnderAssumptionDetailed :
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1) →
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) →
    UnaryTermEqualityUnderAssumptionCompilation term left right
  | .bvar index, left, right => by
      have hindex : index = 0 := Fin.eq_zero index
      subst index
      let assumptionProof := CertifiedPAContextProof.assumption
        (parameterEqualityContext left right)
        (parameterEqualityFormula left right) (by
          simp [parameterEqualityContext])
      have hformula : parameterEqualityFormula left right =
          unaryTermEqualityFormula (#0) left right := by
        simp [parameterEqualityFormula, unaryTermEqualityFormula,
          instantiateUnaryTerm]
      let proof := CertifiedPAContextProof.cast hformula assumptionProof
      refine
        { proof := proof
          structuralPayloadBound := assumptionFullPayloadCost
            (parameterEqualityContext left right)
            (parameterEqualityFormula left right)
          payloadLength_le := ?_ }
      rw [CertifiedPAContextProof.cast_payloadLength]
      rw [assumption_payloadLength_eq]
  | .fvar index, left, right => by
      let Gamma := parameterEqualityContext left right
      let baseFormula :=
        (“!!(&index : LO.FirstOrder.ArithmeticSemiterm Nat 0) =
          !!(&index : LO.FirstOrder.ArithmeticSemiterm Nat 0)” :
          LO.FirstOrder.ArithmeticProposition)
      let baseProof := proveEqualityReflexivityAtTerm
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      let contextualProof := CertifiedPAContextProof.weakenCertified
        Gamma baseProof
      have hformula : baseFormula =
          unaryTermEqualityFormula (&index) left right := by
        simp [baseFormula, unaryTermEqualityFormula, instantiateUnaryTerm]
      let proof := CertifiedPAContextProof.cast hformula contextualProof
      refine
        { proof := proof
          structuralPayloadBound := baseProof.payloadLength +
            weakeningFullAssemblyCost (insert baseFormula Gamma)
          payloadLength_le := ?_ }
      rw [CertifiedPAContextProof.cast_payloadLength]
      simpa [baseFormula, baseProof, contextualProof] using
        (CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma baseProof)
  | .func Language.Zero.zero arguments, left, right => by
      let Gamma := parameterEqualityContext left right
      let zeroTerm : LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
        Semiterm.func Language.Zero.zero ![]
      let baseFormula :=
        (“!!zeroTerm = !!zeroTerm” :
          LO.FirstOrder.ArithmeticProposition)
      let baseProof := proveEqualityReflexivityAtTerm zeroTerm
      let contextualProof := CertifiedPAContextProof.weakenCertified
        Gamma baseProof
      have hformula : baseFormula =
          unaryTermEqualityFormula
            (Semiterm.func Language.Zero.zero arguments) left right := by
        simp [baseFormula, zeroTerm, unaryTermEqualityFormula,
          instantiateUnaryTerm, Matrix.empty_eq]
      let proof := CertifiedPAContextProof.cast hformula contextualProof
      refine
        { proof := proof
          structuralPayloadBound := baseProof.payloadLength +
            weakeningFullAssemblyCost (insert baseFormula Gamma)
          payloadLength_le := ?_ }
      rw [CertifiedPAContextProof.cast_payloadLength]
      simpa [baseFormula, baseProof, contextualProof] using
        (CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma baseProof)
  | .func Language.One.one arguments, left, right => by
      let Gamma := parameterEqualityContext left right
      let oneTerm : LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
        Semiterm.func Language.One.one ![]
      let baseFormula :=
        (“!!oneTerm = !!oneTerm” :
          LO.FirstOrder.ArithmeticProposition)
      let baseProof := proveEqualityReflexivityAtTerm oneTerm
      let contextualProof := CertifiedPAContextProof.weakenCertified
        Gamma baseProof
      have hformula : baseFormula =
          unaryTermEqualityFormula
            (Semiterm.func Language.One.one arguments) left right := by
        simp [baseFormula, oneTerm, unaryTermEqualityFormula,
          instantiateUnaryTerm, Matrix.empty_eq]
      let proof := CertifiedPAContextProof.cast hformula contextualProof
      refine
        { proof := proof
          structuralPayloadBound := baseProof.payloadLength +
            weakeningFullAssemblyCost (insert baseFormula Gamma)
          payloadLength_le := ?_ }
      rw [CertifiedPAContextProof.cast_payloadLength]
      simpa [baseFormula, baseProof, contextualProof] using
        (CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma baseProof)
  | .func Language.Add.add arguments, left, right => by
      let Gamma := parameterEqualityContext left right
      let leftFirst := instantiateUnaryTerm (arguments 0) left
      let leftSecond := instantiateUnaryTerm (arguments 1) left
      let rightFirst := instantiateUnaryTerm (arguments 0) right
      let rightSecond := instantiateUnaryTerm (arguments 1) right
      let firstCompilation :=
        compileUnaryTermEqualityUnderAssumptionDetailed
          (arguments 0) left right
      let secondCompilation :=
        compileUnaryTermEqualityUnderAssumptionDetailed
          (arguments 1) left right
      let firstFormula := unaryTermEqualityFormula
        (arguments 0) left right
      let secondFormula := unaryTermEqualityFormula
        (arguments 1) left right
      let truthFormula := (⊤ : LO.FirstOrder.ArithmeticProposition)
      let innerFormula := secondFormula ⋏ truthFormula
      let antecedentFormula := binaryFunctionCongruenceAntecedent
        leftFirst leftSecond rightFirst rightSecond
      let conclusionFormula := binaryFunctionCongruenceConclusion
        Language.Add.add leftFirst leftSecond rightFirst rightSecond
      let implicationFormula := antecedentFormula 🡒 conclusionFormula
      let truthProof := CertifiedPAContextProof.weakenCertified Gamma
        CertifiedPAProof.verumProof
      let innerProof := CertifiedPAContextProof.conjunction
        secondCompilation.proof truthProof
      let antecedentRaw := CertifiedPAContextProof.conjunction
        firstCompilation.proof innerProof
      have hantecedent : firstFormula ⋏ innerFormula =
          antecedentFormula := by
        simp [firstFormula, secondFormula, truthFormula, innerFormula,
          antecedentFormula, unaryTermEqualityFormula,
          binaryFunctionCongruenceAntecedent,
          leftFirst, leftSecond, rightFirst, rightSecond]
      let antecedentProof := CertifiedPAContextProof.cast
        hantecedent antecedentRaw
      let implicationTheorem := binaryFunctionExtImplication
        Language.Add.add leftFirst leftSecond rightFirst rightSecond
      let implicationProof := CertifiedPAContextProof.weakenCertified
        Gamma implicationTheorem
      let resultRaw := CertifiedPAContextProof.modusPonens
        implicationProof antecedentProof
      have hresult : conclusionFormula =
          unaryTermEqualityFormula
            (Semiterm.func Language.Add.add arguments) left right := by
        dsimp only [conclusionFormula]
        rw [binaryFunctionCongruenceConclusion_add_formula]
        rw [addEqualityAsTerm_formula]
        simp only [unaryTermEqualityFormula]
        rw [instantiateUnaryTerm_add, instantiateUnaryTerm_add]
      let proof := CertifiedPAContextProof.cast hresult resultRaw
      let truthBound := CertifiedPAProof.verumProof.payloadLength +
        weakeningFullAssemblyCost (insert truthFormula Gamma)
      let innerBound := secondCompilation.structuralPayloadBound +
        truthBound +
        CertifiedPAContextProof.conjunctionFullAssemblyCost
          Gamma secondFormula truthFormula
      let antecedentBound := firstCompilation.structuralPayloadBound +
        innerBound +
        CertifiedPAContextProof.conjunctionFullAssemblyCost
          Gamma firstFormula innerFormula
      let implicationBound := implicationTheorem.payloadLength +
        weakeningFullAssemblyCost (insert implicationFormula Gamma)
      let resultBound := implicationBound + antecedentBound +
        contextualModusPonensFullAssemblyCost
          Gamma antecedentFormula conclusionFormula
      refine
        { proof := proof
          structuralPayloadBound := resultBound
          payloadLength_le := ?_ }
      have htruth :=
        CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma CertifiedPAProof.verumProof
      have hinner := CertifiedPAContextProof.conjunction_payloadLength_le
        secondCompilation.proof truthProof
      have hantecedentBound :=
        CertifiedPAContextProof.conjunction_payloadLength_le
          firstCompilation.proof innerProof
      have himplication :=
        CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma implicationTheorem
      have hmp := CertifiedPAContextProof.modusPonens_payloadLength_le
        implicationProof antecedentProof
      have hproofPayload : proof.payloadLength = resultRaw.payloadLength := by
        dsimp only [proof]
        exact CertifiedPAContextProof.cast_payloadLength _ _
      have hantecedentPayload : antecedentProof.payloadLength =
          antecedentRaw.payloadLength := by
        dsimp only [antecedentProof]
        exact CertifiedPAContextProof.cast_payloadLength _ _
      have htruthPayload : truthProof.payloadLength <= truthBound := by
        simpa only [truthProof, truthBound, truthFormula] using htruth
      have hfirstCompilationPayload :
          firstCompilation.proof.payloadLength <=
            firstCompilation.structuralPayloadBound :=
        firstCompilation.payloadLength_le
      have hsecondCompilationPayload :
          secondCompilation.proof.payloadLength <=
            secondCompilation.structuralPayloadBound :=
        secondCompilation.payloadLength_le
      have hinnerRaw : innerProof.payloadLength <=
          secondCompilation.proof.payloadLength + truthProof.payloadLength +
            CertifiedPAContextProof.conjunctionFullAssemblyCost
              Gamma secondFormula truthFormula := by
        simpa only [innerProof] using hinner
      have hinnerPayload : innerProof.payloadLength <= innerBound := by
        calc
          innerProof.payloadLength <=
              secondCompilation.proof.payloadLength +
                truthProof.payloadLength +
                CertifiedPAContextProof.conjunctionFullAssemblyCost
                  Gamma secondFormula truthFormula := hinnerRaw
          _ <= secondCompilation.structuralPayloadBound + truthBound +
                CertifiedPAContextProof.conjunctionFullAssemblyCost
                  Gamma secondFormula truthFormula := by
              exact Nat.add_le_add_right
                (Nat.add_le_add hsecondCompilationPayload htruthPayload) _
          _ = innerBound := by rfl
      have hantecedentRaw : antecedentRaw.payloadLength <=
          firstCompilation.proof.payloadLength + innerProof.payloadLength +
            CertifiedPAContextProof.conjunctionFullAssemblyCost
              Gamma firstFormula innerFormula := by
        simpa only [antecedentRaw] using hantecedentBound
      have hantecedentRawPayload : antecedentRaw.payloadLength <=
          antecedentBound := by
        calc
          antecedentRaw.payloadLength <=
              firstCompilation.proof.payloadLength +
                innerProof.payloadLength +
                CertifiedPAContextProof.conjunctionFullAssemblyCost
                  Gamma firstFormula innerFormula := hantecedentRaw
          _ <= firstCompilation.structuralPayloadBound + innerBound +
                CertifiedPAContextProof.conjunctionFullAssemblyCost
                  Gamma firstFormula innerFormula := by
              exact Nat.add_le_add_right
                (Nat.add_le_add hfirstCompilationPayload hinnerPayload) _
          _ = antecedentBound := by rfl
      have hantecedentProofPayload : antecedentProof.payloadLength <=
          antecedentBound := by
        rw [hantecedentPayload]
        exact hantecedentRawPayload
      have himplicationPayload : implicationProof.payloadLength <=
          implicationBound := by
        simpa only [implicationProof, implicationBound,
          implicationFormula] using himplication
      have hmpRaw : resultRaw.payloadLength <=
          implicationProof.payloadLength + antecedentProof.payloadLength +
            contextualModusPonensFullAssemblyCost
              Gamma antecedentFormula conclusionFormula := by
        simpa only [resultRaw] using hmp
      calc
        proof.payloadLength = resultRaw.payloadLength := hproofPayload
        _ <= implicationProof.payloadLength + antecedentProof.payloadLength +
              contextualModusPonensFullAssemblyCost
                Gamma antecedentFormula conclusionFormula := hmpRaw
        _ <= implicationBound + antecedentBound +
              contextualModusPonensFullAssemblyCost
                Gamma antecedentFormula conclusionFormula := by
              exact Nat.add_le_add_right
                (Nat.add_le_add himplicationPayload
                  hantecedentProofPayload) _
        _ = resultBound := by rfl
  | .func Language.Mul.mul arguments, left, right => by
      let Gamma := parameterEqualityContext left right
      let leftFirst := instantiateUnaryTerm (arguments 0) left
      let leftSecond := instantiateUnaryTerm (arguments 1) left
      let rightFirst := instantiateUnaryTerm (arguments 0) right
      let rightSecond := instantiateUnaryTerm (arguments 1) right
      let firstCompilation :=
        compileUnaryTermEqualityUnderAssumptionDetailed
          (arguments 0) left right
      let secondCompilation :=
        compileUnaryTermEqualityUnderAssumptionDetailed
          (arguments 1) left right
      let firstFormula := unaryTermEqualityFormula
        (arguments 0) left right
      let secondFormula := unaryTermEqualityFormula
        (arguments 1) left right
      let truthFormula := (⊤ : LO.FirstOrder.ArithmeticProposition)
      let innerFormula := secondFormula ⋏ truthFormula
      let antecedentFormula := binaryFunctionCongruenceAntecedent
        leftFirst leftSecond rightFirst rightSecond
      let conclusionFormula := binaryFunctionCongruenceConclusion
        Language.Mul.mul leftFirst leftSecond rightFirst rightSecond
      let implicationFormula := antecedentFormula 🡒 conclusionFormula
      let truthProof := CertifiedPAContextProof.weakenCertified Gamma
        CertifiedPAProof.verumProof
      let innerProof := CertifiedPAContextProof.conjunction
        secondCompilation.proof truthProof
      let antecedentRaw := CertifiedPAContextProof.conjunction
        firstCompilation.proof innerProof
      have hantecedent : firstFormula ⋏ innerFormula =
          antecedentFormula := by
        simp [firstFormula, secondFormula, truthFormula, innerFormula,
          antecedentFormula, unaryTermEqualityFormula,
          binaryFunctionCongruenceAntecedent,
          leftFirst, leftSecond, rightFirst, rightSecond]
      let antecedentProof := CertifiedPAContextProof.cast
        hantecedent antecedentRaw
      let implicationTheorem := binaryFunctionExtImplication
        Language.Mul.mul leftFirst leftSecond rightFirst rightSecond
      let implicationProof := CertifiedPAContextProof.weakenCertified
        Gamma implicationTheorem
      let resultRaw := CertifiedPAContextProof.modusPonens
        implicationProof antecedentProof
      have hresult : conclusionFormula =
          unaryTermEqualityFormula
            (Semiterm.func Language.Mul.mul arguments) left right := by
        dsimp only [conclusionFormula]
        rw [binaryFunctionCongruenceConclusion_mul_formula]
        rw [mulEqualityAsTerm_formula]
        simp only [unaryTermEqualityFormula]
        rw [instantiateUnaryTerm_mul, instantiateUnaryTerm_mul]
      let proof := CertifiedPAContextProof.cast hresult resultRaw
      let truthBound := CertifiedPAProof.verumProof.payloadLength +
        weakeningFullAssemblyCost (insert truthFormula Gamma)
      let innerBound := secondCompilation.structuralPayloadBound +
        truthBound +
        CertifiedPAContextProof.conjunctionFullAssemblyCost
          Gamma secondFormula truthFormula
      let antecedentBound := firstCompilation.structuralPayloadBound +
        innerBound +
        CertifiedPAContextProof.conjunctionFullAssemblyCost
          Gamma firstFormula innerFormula
      let implicationBound := implicationTheorem.payloadLength +
        weakeningFullAssemblyCost (insert implicationFormula Gamma)
      let resultBound := implicationBound + antecedentBound +
        contextualModusPonensFullAssemblyCost
          Gamma antecedentFormula conclusionFormula
      refine
        { proof := proof
          structuralPayloadBound := resultBound
          payloadLength_le := ?_ }
      have htruth :=
        CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma CertifiedPAProof.verumProof
      have hinner := CertifiedPAContextProof.conjunction_payloadLength_le
        secondCompilation.proof truthProof
      have hantecedentBound :=
        CertifiedPAContextProof.conjunction_payloadLength_le
          firstCompilation.proof innerProof
      have himplication :=
        CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma implicationTheorem
      have hmp := CertifiedPAContextProof.modusPonens_payloadLength_le
        implicationProof antecedentProof
      have hproofPayload : proof.payloadLength = resultRaw.payloadLength := by
        dsimp only [proof]
        exact CertifiedPAContextProof.cast_payloadLength _ _
      have hantecedentPayload : antecedentProof.payloadLength =
          antecedentRaw.payloadLength := by
        dsimp only [antecedentProof]
        exact CertifiedPAContextProof.cast_payloadLength _ _
      have htruthPayload : truthProof.payloadLength <= truthBound := by
        simpa only [truthProof, truthBound, truthFormula] using htruth
      have hfirstCompilationPayload :
          firstCompilation.proof.payloadLength <=
            firstCompilation.structuralPayloadBound :=
        firstCompilation.payloadLength_le
      have hsecondCompilationPayload :
          secondCompilation.proof.payloadLength <=
            secondCompilation.structuralPayloadBound :=
        secondCompilation.payloadLength_le
      have hinnerRaw : innerProof.payloadLength <=
          secondCompilation.proof.payloadLength + truthProof.payloadLength +
            CertifiedPAContextProof.conjunctionFullAssemblyCost
              Gamma secondFormula truthFormula := by
        simpa only [innerProof] using hinner
      have hinnerPayload : innerProof.payloadLength <= innerBound := by
        calc
          innerProof.payloadLength <=
              secondCompilation.proof.payloadLength +
                truthProof.payloadLength +
                CertifiedPAContextProof.conjunctionFullAssemblyCost
                  Gamma secondFormula truthFormula := hinnerRaw
          _ <= secondCompilation.structuralPayloadBound + truthBound +
                CertifiedPAContextProof.conjunctionFullAssemblyCost
                  Gamma secondFormula truthFormula := by
              exact Nat.add_le_add_right
                (Nat.add_le_add hsecondCompilationPayload htruthPayload) _
          _ = innerBound := by rfl
      have hantecedentRaw : antecedentRaw.payloadLength <=
          firstCompilation.proof.payloadLength + innerProof.payloadLength +
            CertifiedPAContextProof.conjunctionFullAssemblyCost
              Gamma firstFormula innerFormula := by
        simpa only [antecedentRaw] using hantecedentBound
      have hantecedentRawPayload : antecedentRaw.payloadLength <=
          antecedentBound := by
        calc
          antecedentRaw.payloadLength <=
              firstCompilation.proof.payloadLength +
                innerProof.payloadLength +
                CertifiedPAContextProof.conjunctionFullAssemblyCost
                  Gamma firstFormula innerFormula := hantecedentRaw
          _ <= firstCompilation.structuralPayloadBound + innerBound +
                CertifiedPAContextProof.conjunctionFullAssemblyCost
                  Gamma firstFormula innerFormula := by
              exact Nat.add_le_add_right
                (Nat.add_le_add hfirstCompilationPayload hinnerPayload) _
          _ = antecedentBound := by rfl
      have hantecedentProofPayload : antecedentProof.payloadLength <=
          antecedentBound := by
        rw [hantecedentPayload]
        exact hantecedentRawPayload
      have himplicationPayload : implicationProof.payloadLength <=
          implicationBound := by
        simpa only [implicationProof, implicationBound,
          implicationFormula] using himplication
      have hmpRaw : resultRaw.payloadLength <=
          implicationProof.payloadLength + antecedentProof.payloadLength +
            contextualModusPonensFullAssemblyCost
              Gamma antecedentFormula conclusionFormula := by
        simpa only [resultRaw] using hmp
      calc
        proof.payloadLength = resultRaw.payloadLength := hproofPayload
        _ <= implicationProof.payloadLength + antecedentProof.payloadLength +
              contextualModusPonensFullAssemblyCost
                Gamma antecedentFormula conclusionFormula := hmpRaw
        _ <= implicationBound + antecedentBound +
              contextualModusPonensFullAssemblyCost
                Gamma antecedentFormula conclusionFormula := by
              exact Nat.add_le_add_right
                (Nat.add_le_add himplicationPayload
                  hantecedentProofPayload) _
        _ = resultBound := by rfl
termination_by term => term.complexity
decreasing_by
  all_goals exact Semiterm.complexity_func_lt _ _ _

def compileUnaryTermEqualityUnderAssumption
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAContextProof (parameterEqualityContext left right)
      (unaryTermEqualityFormula term left right) :=
  (compileUnaryTermEqualityUnderAssumptionDetailed term left right).proof

def unaryTermEqualityUnderAssumptionStructuralPayloadBound
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  (compileUnaryTermEqualityUnderAssumptionDetailed
    term left right).structuralPayloadBound

theorem compileUnaryTermEqualityUnderAssumption_payloadLength_le
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (compileUnaryTermEqualityUnderAssumption
      term left right).payloadLength <=
      unaryTermEqualityUnderAssumptionStructuralPayloadBound
        term left right :=
  (compileUnaryTermEqualityUnderAssumptionDetailed
    term left right).payloadLength_le

def proveUnaryTermEqualityImplication
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (parameterEqualityFormula left right 🡒
        unaryTermEqualityFormula term left right) :=
  CertifiedPAContextProof.discharge
    (parameterEqualityFormula left right)
    (unaryTermEqualityFormula term left right)
    (compileUnaryTermEqualityUnderAssumption term left right)

def unaryTermEqualityImplicationStructuralPayloadBound
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  unaryTermEqualityUnderAssumptionStructuralPayloadBound term left right +
    CertifiedPAContextProof.dischargeFullAssemblyCost
      (parameterEqualityFormula left right)
      (unaryTermEqualityFormula term left right)

theorem proveUnaryTermEqualityImplication_payloadLength_le
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveUnaryTermEqualityImplication term left right).payloadLength <=
      unaryTermEqualityImplicationStructuralPayloadBound
        term left right := by
  have hcontext :=
    compileUnaryTermEqualityUnderAssumption_payloadLength_le
      term left right
  have hdischarge := CertifiedPAContextProof.discharge_payloadLength_le
    (parameterEqualityFormula left right)
    (unaryTermEqualityFormula term left right)
    (compileUnaryTermEqualityUnderAssumption term left right)
  unfold proveUnaryTermEqualityImplication
  unfold unaryTermEqualityImplicationStructuralPayloadBound
  exact hdischarge.trans (Nat.add_le_add_right hcontext _)

theorem proveUnaryTermEqualityImplication_verifier_eq_true
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier
      (proveUnaryTermEqualityImplication term left right).code
      (compactFormulaCode
        (parameterEqualityFormula left right 🡒
          unaryTermEqualityFormula term left right)) = true :=
  (proveUnaryTermEqualityImplication term left right).verifier_eq_true

theorem proveUnaryTermEqualityImplication_checked_structuralBound
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier
        (proveUnaryTermEqualityImplication term left right).code
        (compactFormulaCode
          (parameterEqualityFormula left right 🡒
            unaryTermEqualityFormula term left right)) = true ∧
      (proveUnaryTermEqualityImplication term left right).payloadLength <=
        unaryTermEqualityImplicationStructuralPayloadBound
          term left right :=
  ⟨proveUnaryTermEqualityImplication_verifier_eq_true term left right,
    proveUnaryTermEqualityImplication_payloadLength_le term left right⟩

#print axioms compileUnaryTermEqualityUnderAssumptionDetailed
#print axioms compileUnaryTermEqualityUnderAssumption_payloadLength_le
#print axioms proveUnaryTermEqualityImplication_payloadLength_le
#print axioms proveUnaryTermEqualityImplication_checked_structuralBound

end FoundationCompactPAUnaryTermEqualityImplication
