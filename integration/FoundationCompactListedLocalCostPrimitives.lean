import integration.FoundationCompactListedProofHonestWeight
import integration.FoundationCompactSyntaxTransformationCodeBounds
import integration.FoundationCompactListedCertificateVerifier

/-!
# Uniform local bit-cost bounds for list-preserving proof checks

The existing executable traces expose exact costs for formula equality,
membership, inclusion, and extensional list equality.  This file bounds all
four operations by one explicit quadratic in the complete formula-code weight
of their inputs.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedLocalCostPrimitives

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAAxiomCertificate
open FoundationCompactVerifierBitCostPrimitives
open FoundationCompactVerifierFormulaListChecks
open FoundationCompactListedProofDecoder
open FoundationCompactListedProofHonestWeight
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxTransformationTrace
open FoundationCompactListedCertificateVerifier

def formulaCheckPolynomial (weight : Nat) : Nat :=
  4 + 2 * ((weight + 3) * (weight + 3)) + weight

theorem formulaCheckPolynomial_mono
    {left right : Nat} (h : left <= right) :
    formulaCheckPolynomial left <= formulaCheckPolynomial right := by
  unfold formulaCheckPolynomial
  have hshift : left + 3 <= right + 3 := by omega
  have hsquare := Nat.mul_le_mul hshift hshift
  have hscaled := Nat.mul_le_mul_left 2 hsquare
  exact Nat.add_le_add (Nat.add_le_add_left hscaled 4) h

theorem formulaEqTrace_cost_le_polynomial
    (left right : LO.FirstOrder.ArithmeticProposition) :
    (formulaEqTrace left right).2 <=
      formulaCheckPolynomial
        ((binaryFormulaCode left).length +
          (binaryFormulaCode right).length) := by
  have hcost := formulaEqTrace_cost_le left right
  let weight := (binaryFormulaCode left).length +
    (binaryFormulaCode right).length
  change (formulaEqTrace left right).2 <= formulaCheckPolynomial weight
  have hpositive : 1 <= weight + 3 := by omega
  have hsquare :
      weight + 3 <= (weight + 3) * (weight + 3) := by
    simpa using Nat.mul_le_mul_right (weight + 3) hpositive
  have hscaled := Nat.mul_le_mul_left 2 hsquare
  calc
    (formulaEqTrace left right).2 <=
        2 * (binaryFormulaCode left).length +
          (binaryFormulaCode right).length + 2 := hcost
    _ <= 2 * (weight + 3) := by
      dsimp [weight]
      omega
    _ <= 2 * ((weight + 3) * (weight + 3)) := hscaled
    _ <= formulaCheckPolynomial weight := by
      unfold formulaCheckPolynomial
      omega

theorem formulaMemTrace_cost_le_polynomial
    (formula : LO.FirstOrder.ArithmeticProposition)
    (formulas : List LO.FirstOrder.ArithmeticProposition) :
    (formulaMemTrace formula formulas).2 <=
      formulaCheckPolynomial
        ((binaryFormulaCode formula).length +
          formulaListCodeWeight formulas) := by
  have hcost := formulaMemTrace_cost_le formula formulas
  have hlength := formulaList_length_le_codeWeight formulas
  let weight := (binaryFormulaCode formula).length +
    formulaListCodeWeight formulas
  have hleft : (binaryFormulaCode formula).length + 2 <= weight + 3 := by
    dsimp [weight]
    omega
  have hright : formulas.length + 1 <= weight + 3 := by
    dsimp [weight]
    omega
  have hproduct := Nat.mul_le_mul hleft hright
  unfold formulaCheckPolynomial
  dsimp [weight] at hproduct
  omega

theorem formulaSubsetTrace_cost_le_polynomial
    (left right : List LO.FirstOrder.ArithmeticProposition) :
    (formulaSubsetTrace left right).2 <=
      formulaCheckPolynomial
        (formulaListCodeWeight left + formulaListCodeWeight right) := by
  have hcost := formulaSubsetTrace_cost_le left right
  have hleftLength := formulaList_length_le_codeWeight left
  have hrightLength := formulaList_length_le_codeWeight right
  let weight := formulaListCodeWeight left + formulaListCodeWeight right
  have hfactor : right.length + 1 <= weight + 3 := by
    dsimp [weight]
    omega
  have hleftWeight : formulaListCodeWeight left <= weight + 3 := by
    dsimp [weight]
    omega
  have hproduct := Nat.mul_le_mul hfactor hleftWeight
  unfold formulaCheckPolynomial
  dsimp [weight] at hproduct
  omega

theorem formulaSetEqTrace_cost_le_polynomial
    (left right : List LO.FirstOrder.ArithmeticProposition) :
    (formulaSetEqTrace left right).2 <=
      formulaCheckPolynomial
        (formulaListCodeWeight left + formulaListCodeWeight right) := by
  have hcost := formulaSetEqTrace_cost_le left right
  have hleftLength := formulaList_length_le_codeWeight left
  have hrightLength := formulaList_length_le_codeWeight right
  let weight := formulaListCodeWeight left + formulaListCodeWeight right
  have hrightFactor : right.length + 1 <= weight + 3 := by
    dsimp [weight]
    omega
  have hleftFactor : left.length + 1 <= weight + 3 := by
    dsimp [weight]
    omega
  have hleftWeight : formulaListCodeWeight left <= weight + 3 := by
    dsimp [weight]
    omega
  have hrightWeight : formulaListCodeWeight right <= weight + 3 := by
    dsimp [weight]
    omega
  have hleftProduct := Nat.mul_le_mul hrightFactor hleftWeight
  have hrightProduct := Nat.mul_le_mul hleftFactor hrightWeight
  unfold formulaCheckPolynomial
  dsimp [weight] at hleftProduct hrightProduct
  omega

theorem binaryFormulaCode_and_length_le
    (left right : LO.FirstOrder.ArithmeticProposition) :
    (binaryFormulaCode (left ⋏ right)).length <=
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length + 8 := by
  have htag : (binaryNatCode 4).length <= 8 := by decide
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem binaryFormulaCode_or_length_le
    (left right : LO.FirstOrder.ArithmeticProposition) :
    (binaryFormulaCode (left ⋎ right)).length <=
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length + 8 := by
  have htag : (binaryNatCode 5).length <= 8 := by decide
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem binaryFormulaCode_all_length_le
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaCode (∀⁰ formula)).length <=
      (binaryFormulaCode formula).length + 8 := by
  have htag : (binaryNatCode 6).length <= 8 := by decide
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem binaryFormulaCode_exs_length_le
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaCode (∃⁰ formula)).length <=
      (binaryFormulaCode formula).length + 8 := by
  have htag : (binaryNatCode 7).length <= 8 := by decide
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem formulaListCodeWeight_neg_cons_le
    (formula : LO.FirstOrder.ArithmeticProposition)
    (formulas : List LO.FirstOrder.ArithmeticProposition) :
    formulaListCodeWeight ((∼formula) :: formulas) <=
      2 * (binaryFormulaCode formula).length + 3 +
        formulaListCodeWeight formulas := by
  have hneg := binaryFormulaCode_neg_length_le formula
  simp only [formulaListCodeWeight_cons]
  omega

theorem formulaListCodeWeight_two_cons
    (left right : LO.FirstOrder.ArithmeticProposition)
    (formulas : List LO.FirstOrder.ArithmeticProposition) :
    formulaListCodeWeight (left :: right :: formulas) =
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length + 6 +
          formulaListCodeWeight formulas := by
  simp [formulaListCodeWeight_cons]
  omega

theorem formulaListCodeWeight_free_cons_map_shift_le
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (formulas : List LO.FirstOrder.ArithmeticProposition) :
    formulaListCodeWeight
        (Rewriting.free formula :: formulas.map Rewriting.shift) <=
      2 * (binaryFormulaCode formula).length + 3 +
        2 * formulaListCodeWeight formulas := by
  have hfree := binaryFormulaCode_free_length_le formula
  have hshift := formulaListCodeWeight_map_shift_le formulas
  simp only [formulaListCodeWeight_cons]
  omega

theorem formulaListCodeWeight_substitution_cons_le
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (formulas : List LO.FirstOrder.ArithmeticProposition) :
    formulaListCodeWeight (formula/[witness] :: formulas) <=
      3 * ((binaryFormulaCode formula).length + 1) *
          ((binaryTermCode witness).length + 1) *
          (binaryFormulaCode formula).length + 3 +
        formulaListCodeWeight formulas := by
  have hsubstitution :=
    binaryFormulaCode_substitution_one_length_le formula witness
  simp only [formulaListCodeWeight_cons]
  omega

def listedProofNodeCount : ListedCheckedPAProofTree -> Nat
  | .closed _ _ => 1
  | .axm _ _ => 1
  | .verum _ => 1
  | .and _ _ _ left right =>
      1 + listedProofNodeCount left + listedProofNodeCount right
  | .or _ _ _ premise => 1 + listedProofNodeCount premise
  | .all _ _ premise => 1 + listedProofNodeCount premise
  | .exs _ _ _ premise => 1 + listedProofNodeCount premise
  | .wk _ premise => 1 + listedProofNodeCount premise
  | .shift _ premise => 1 + listedProofNodeCount premise
  | .cut _ _ left right =>
      1 + listedProofNodeCount left + listedProofNodeCount right

theorem listedProofNodeCount_pos
    (tree : ListedCheckedPAProofTree) :
    1 <= listedProofNodeCount tree := by
  cases tree <;> simp [listedProofNodeCount] <;> omega

theorem listedProofNodeCount_le_honestBitWeight
    (tree : ListedCheckedPAProofTree) :
    listedProofNodeCount tree <= listedProofHonestBitWeight tree := by
  induction tree with
  | closed Gamma formula =>
      simp [listedProofNodeCount, listedProofHonestBitWeight]
      omega
  | axm Gamma sentence =>
      simp [listedProofNodeCount, listedProofHonestBitWeight]
      omega
  | verum Gamma =>
      simp [listedProofNodeCount, listedProofHonestBitWeight]
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      simp only [listedProofNodeCount, listedProofHonestBitWeight]
      omega
  | or Gamma leftFormula rightFormula premise ih =>
      simp only [listedProofNodeCount, listedProofHonestBitWeight]
      omega
  | all Gamma formula premise ih =>
      simp only [listedProofNodeCount, listedProofHonestBitWeight]
      omega
  | exs Gamma formula witness premise ih =>
      simp only [listedProofNodeCount, listedProofHonestBitWeight]
      omega
  | wk Gamma premise ih =>
      simp only [listedProofNodeCount, listedProofHonestBitWeight]
      omega
  | shift Gamma premise ih =>
      simp only [listedProofNodeCount, listedProofHonestBitWeight]
      omega
  | cut Gamma formula left right ihLeft ihRight =>
      simp only [listedProofNodeCount, listedProofHonestBitWeight]
      omega

def generatedFormulaWeightPolynomial (weight : Nat) : Nat :=
  3 * (weight + 1) * (weight + 1) * (weight + 1) +
    4 * weight + 32

theorem generatedFormulaWeightPolynomial_mono
    {left right : Nat} (h : left <= right) :
    generatedFormulaWeightPolynomial left <=
      generatedFormulaWeightPolynomial right := by
  have hshift : left + 1 <= right + 1 := by omega
  have hfirst := Nat.mul_le_mul_left 3 hshift
  have hsecond := Nat.mul_le_mul hfirst hshift
  have hthird := Nat.mul_le_mul hsecond hshift
  have hlinear := Nat.mul_le_mul_left 4 h
  unfold generatedFormulaWeightPolynomial
  omega

theorem linearGeneratedWeight_le_polynomial
    (weight : Nat) :
    4 * weight + 32 <= generatedFormulaWeightPolynomial weight := by
  unfold generatedFormulaWeightPolynomial
  omega

theorem substitutionGeneratedWeight_le_polynomial
    {formulaLength witnessLength contextWeight weight : Nat}
    (hformula : formulaLength <= weight)
    (hwitness : witnessLength <= weight)
    (hcontext : contextWeight <= weight) :
    3 * (formulaLength + 1) * (witnessLength + 1) *
          formulaLength + 3 + contextWeight <=
      generatedFormulaWeightPolynomial weight := by
  have hformulaSucc : formulaLength + 1 <= weight + 1 := by omega
  have hwitnessSucc : witnessLength + 1 <= weight + 1 := by omega
  have hformulaFinal : formulaLength <= weight + 1 := by omega
  have hfirst := Nat.mul_le_mul_left 3 hformulaSucc
  have hsecond := Nat.mul_le_mul hfirst hwitnessSucc
  have hthird := Nat.mul_le_mul hsecond hformulaFinal
  unfold generatedFormulaWeightPolynomial
  omega

theorem substitutionGeneratedWithPremiseWeight_le_polynomial
    {formulaLength witnessLength contextWeight premiseWeight weight : Nat}
    (hformula : formulaLength <= weight)
    (hwitness : witnessLength <= weight)
    (hcontext : contextWeight <= weight)
    (hpremise : premiseWeight <= weight) :
    premiseWeight +
        (3 * (formulaLength + 1) * (witnessLength + 1) *
          formulaLength + 3 + contextWeight) <=
      generatedFormulaWeightPolynomial weight := by
  have hformulaSucc : formulaLength + 1 <= weight + 1 := by omega
  have hwitnessSucc : witnessLength + 1 <= weight + 1 := by omega
  have hformulaFinal : formulaLength <= weight + 1 := by omega
  have hfirst := Nat.mul_le_mul_left 3 hformulaSucc
  have hsecond := Nat.mul_le_mul hfirst hwitnessSucc
  have hthird := Nat.mul_le_mul hsecond hformulaFinal
  unfold generatedFormulaWeightPolynomial
  omega

def guardedAxiomCostEnvelope (weight : Nat) : Nat :=
  guardedAxiomSentenceEqTraceCoefficient *
    (2 * weight + 1) ^ 12

def perProofNodeFormulaCostPolynomial (weight : Nat) : Nat :=
  8 * formulaCheckPolynomial (generatedFormulaWeightPolynomial weight) + 16 +
    guardedAxiomCostEnvelope weight

def listedLocalCostPolynomial (weight : Nat) : Nat :=
  weight * perProofNodeFormulaCostPolynomial weight

def localStructuralCertificateHonestBitWeight
    (certificate : StructuralValidityCertificate) : Nat :=
  8 * (binaryStructuralValidityCertificateCode certificate).length

def listedLocalJointHonestBitWeight
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) : Nat :=
  listedProofHonestBitWeight tree +
    localStructuralCertificateHonestBitWeight certificate

def listedJointLocalCostPolynomial (weight : Nat) : Nat :=
  weight * perProofNodeFormulaCostPolynomial (2 * weight)

theorem perProofNodeFormulaCostPolynomial_pos
    (weight : Nat) :
    1 <= perProofNodeFormulaCostPolynomial weight := by
  unfold perProofNodeFormulaCostPolynomial
  omega

theorem perProofNodeFormulaCostPolynomial_mono
    {left right : Nat} (h : left <= right) :
    perProofNodeFormulaCostPolynomial left <=
      perProofNodeFormulaCostPolynomial right := by
  have hgenerated := generatedFormulaWeightPolynomial_mono h
  have hcheck := formulaCheckPolynomial_mono hgenerated
  have hscaled := Nat.mul_le_mul_left 8 hcheck
  have hguardBase : 2 * left + 1 <= 2 * right + 1 := by omega
  have hguardPow := Nat.pow_le_pow_left hguardBase 12
  have hguard := Nat.mul_le_mul_left
    guardedAxiomSentenceEqTraceCoefficient hguardPow
  unfold perProofNodeFormulaCostPolynomial guardedAxiomCostEnvelope
  omega

theorem listedLocalCostPolynomial_mono
    {left right : Nat} (h : left <= right) :
    listedLocalCostPolynomial left <= listedLocalCostPolynomial right := by
  have hnode := perProofNodeFormulaCostPolynomial_mono h
  unfold listedLocalCostPolynomial
  exact Nat.mul_le_mul h hnode

theorem listedJointLocalCostPolynomial_mono
    {left right : Nat} (h : left <= right) :
    listedJointLocalCostPolynomial left <=
      listedJointLocalCostPolynomial right := by
  have hdouble : 2 * left <= 2 * right := Nat.mul_le_mul_left 2 h
  have hnode := perProofNodeFormulaCostPolynomial_mono hdouble
  unfold listedJointLocalCostPolynomial
  exact Nat.mul_le_mul h hnode

theorem localStructuralCertificateHonestBitWeight_unary_le
    (certificate : StructuralValidityCertificate) :
    localStructuralCertificateHonestBitWeight certificate <=
      localStructuralCertificateHonestBitWeight (.unary certificate) := by
  simp only [localStructuralCertificateHonestBitWeight,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

theorem localStructuralCertificateHonestBitWeight_binary_left_le
    (left right : StructuralValidityCertificate) :
    localStructuralCertificateHonestBitWeight left <=
      localStructuralCertificateHonestBitWeight (.binary left right) := by
  simp only [localStructuralCertificateHonestBitWeight,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

theorem localStructuralCertificateHonestBitWeight_binary_right_le
    (left right : StructuralValidityCertificate) :
    localStructuralCertificateHonestBitWeight right <=
      localStructuralCertificateHonestBitWeight (.binary left right) := by
  simp only [localStructuralCertificateHonestBitWeight,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

theorem listedProofHonestBitWeight_le_joint
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    listedProofHonestBitWeight tree <=
      listedLocalJointHonestBitWeight tree certificate := by
  simp [listedLocalJointHonestBitWeight]

theorem localStructuralCertificateHonestBitWeight_le_joint
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    localStructuralCertificateHonestBitWeight certificate <=
      listedLocalJointHonestBitWeight tree certificate := by
  simp [listedLocalJointHonestBitWeight]

theorem nodeCount_mul_jointPerNode_le_listedJointLocalCostPolynomial
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    listedProofNodeCount tree *
        perProofNodeFormulaCostPolynomial
          (2 * listedLocalJointHonestBitWeight tree certificate) <=
      listedJointLocalCostPolynomial
        (listedLocalJointHonestBitWeight tree certificate) := by
  unfold listedJointLocalCostPolynomial
  apply Nat.mul_le_mul_right
  exact (listedProofNodeCount_le_honestBitWeight tree).trans
    (listedProofHonestBitWeight_le_joint tree certificate)

theorem nodeCount_mul_perNode_le_listedLocalCostPolynomial
    (tree : ListedCheckedPAProofTree) :
    listedProofNodeCount tree *
        perProofNodeFormulaCostPolynomial
          (listedProofHonestBitWeight tree) <=
      listedLocalCostPolynomial (listedProofHonestBitWeight tree) := by
  unfold listedLocalCostPolynomial
  exact Nat.mul_le_mul_right _
    (listedProofNodeCount_le_honestBitWeight tree)

theorem listedCertificateValidTrace_closed_cost_le
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition) :
    (listedCertificateValidTrace (.closed Gamma formula) .leaf).2 <=
      perProofNodeFormulaCostPolynomial
        (listedProofHonestBitWeight (.closed Gamma formula)) := by
  let weight := listedProofHonestBitWeight
    (ListedCheckedPAProofTree.closed Gamma formula)
  have hlinear := linearGeneratedWeight_le_polynomial weight
  have hformulaInput :
      (binaryFormulaCode formula).length +
          formulaListCodeWeight Gamma <=
        generatedFormulaWeightPolynomial weight := by
    apply (show (binaryFormulaCode formula).length +
        formulaListCodeWeight Gamma <= 4 * weight + 32 by
      dsimp [weight]
      simp only [listedProofHonestBitWeight]
      omega).trans
    exact hlinear
  have hnegLength := binaryFormulaCode_neg_length_le formula
  have hnegInput :
      (binaryFormulaCode (∼formula)).length +
          formulaListCodeWeight Gamma <=
        generatedFormulaWeightPolynomial weight := by
    apply (show (binaryFormulaCode (∼formula)).length +
        formulaListCodeWeight Gamma <= 4 * weight + 32 by
      dsimp [weight]
      simp only [listedProofHonestBitWeight]
      omega).trans
    exact hlinear
  have hformulaCost :=
    (formulaMemTrace_cost_le_polynomial formula Gamma).trans
      (formulaCheckPolynomial_mono hformulaInput)
  have hnegCost :=
    (formulaMemTrace_cost_le_polynomial (∼formula) Gamma).trans
      (formulaCheckPolynomial_mono hnegInput)
  simp only [listedCertificateValidTrace, traceAnd_cost]
  change _ <= perProofNodeFormulaCostPolynomial weight
  unfold perProofNodeFormulaCostPolynomial
  omega

theorem listedCertificateValidTrace_verum_cost_le
    (Gamma : List LO.FirstOrder.ArithmeticProposition) :
    (listedCertificateValidTrace
        (.verum Gamma) (.leaf : StructuralValidityCertificate)).2 <=
      perProofNodeFormulaCostPolynomial
        (listedProofHonestBitWeight (.verum Gamma)) := by
  let weight := listedProofHonestBitWeight
    (ListedCheckedPAProofTree.verum Gamma)
  have htop :
      (binaryFormulaCode
        (⊤ : LO.FirstOrder.ArithmeticProposition)).length <= 8 := by
    decide
  have hlinear := linearGeneratedWeight_le_polynomial weight
  have hinput :
      (binaryFormulaCode
          (⊤ : LO.FirstOrder.ArithmeticProposition)).length +
          formulaListCodeWeight Gamma <=
        generatedFormulaWeightPolynomial weight := by
    apply (show (binaryFormulaCode
          (⊤ : LO.FirstOrder.ArithmeticProposition)).length +
        formulaListCodeWeight Gamma <= 4 * weight + 32 by
      dsimp [weight]
      simp only [listedProofHonestBitWeight]
      omega).trans
    exact hlinear
  have hcost :=
    (formulaMemTrace_cost_le_polynomial
      (⊤ : LO.FirstOrder.ArithmeticProposition) Gamma).trans
        (formulaCheckPolynomial_mono hinput)
  simp only [listedCertificateValidTrace]
  change _ <= perProofNodeFormulaCostPolynomial weight
  unfold perProofNodeFormulaCostPolynomial
  omega

theorem listedCertificateValidTrace_and_cost_le
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate) :
    (listedCertificateValidTrace
        (.and Gamma leftFormula rightFormula left right)
        (.binary leftCertificate rightCertificate)).2 <=
      (listedCertificateValidTrace left leftCertificate).2 +
        (listedCertificateValidTrace right rightCertificate).2 +
        perProofNodeFormulaCostPolynomial
          (listedProofHonestBitWeight
            (.and Gamma leftFormula rightFormula left right)) := by
  let weight := listedProofHonestBitWeight
    (ListedCheckedPAProofTree.and Gamma leftFormula rightFormula left right)
  have hlinear := linearGeneratedWeight_le_polynomial weight
  have hprincipalLength :=
    binaryFormulaCode_and_length_le leftFormula rightFormula
  have hprincipalInput :
      (binaryFormulaCode (leftFormula ⋏ rightFormula)).length +
          formulaListCodeWeight Gamma <=
        generatedFormulaWeightPolynomial weight := by
    apply (show (binaryFormulaCode (leftFormula ⋏ rightFormula)).length +
        formulaListCodeWeight Gamma <= 4 * weight + 32 by
      dsimp [weight]
      simp only [listedProofHonestBitWeight]
      omega).trans
    exact hlinear
  have hleftConclusion :=
    conclusionList_codeWeight_le_honestBitWeight left
  have hleftInput :
      formulaListCodeWeight left.conclusionList +
          formulaListCodeWeight (leftFormula :: Gamma) <=
        generatedFormulaWeightPolynomial weight := by
    apply (show formulaListCodeWeight left.conclusionList +
        formulaListCodeWeight (leftFormula :: Gamma) <=
          4 * weight + 32 by
      dsimp [weight]
      simp only [listedProofHonestBitWeight, formulaListCodeWeight_cons]
      omega).trans
    exact hlinear
  have hrightConclusion :=
    conclusionList_codeWeight_le_honestBitWeight right
  have hrightInput :
      formulaListCodeWeight right.conclusionList +
          formulaListCodeWeight (rightFormula :: Gamma) <=
        generatedFormulaWeightPolynomial weight := by
    apply (show formulaListCodeWeight right.conclusionList +
        formulaListCodeWeight (rightFormula :: Gamma) <=
          4 * weight + 32 by
      dsimp [weight]
      simp only [listedProofHonestBitWeight, formulaListCodeWeight_cons]
      omega).trans
    exact hlinear
  have hprincipalCost :=
    (formulaMemTrace_cost_le_polynomial
      (leftFormula ⋏ rightFormula) Gamma).trans
        (formulaCheckPolynomial_mono hprincipalInput)
  have hleftCost :=
    (formulaSetEqTrace_cost_le_polynomial
      left.conclusionList (leftFormula :: Gamma)).trans
        (formulaCheckPolynomial_mono hleftInput)
  have hrightCost :=
    (formulaSetEqTrace_cost_le_polynomial
      right.conclusionList (rightFormula :: Gamma)).trans
        (formulaCheckPolynomial_mono hrightInput)
  simp only [listedCertificateValidTrace, traceAnd_cost]
  change _ <= _ + _ + perProofNodeFormulaCostPolynomial weight
  unfold perProofNodeFormulaCostPolynomial
  omega

theorem listedCertificateValidTrace_or_cost_le
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate) :
    (listedCertificateValidTrace
        (.or Gamma leftFormula rightFormula premise)
        (.unary premiseCertificate)).2 <=
      (listedCertificateValidTrace premise premiseCertificate).2 +
        perProofNodeFormulaCostPolynomial
          (listedProofHonestBitWeight
            (.or Gamma leftFormula rightFormula premise)) := by
  let weight := listedProofHonestBitWeight
    (ListedCheckedPAProofTree.or Gamma leftFormula rightFormula premise)
  have hlinear := linearGeneratedWeight_le_polynomial weight
  have hprincipalLength :=
    binaryFormulaCode_or_length_le leftFormula rightFormula
  have hprincipalInput :
      (binaryFormulaCode (leftFormula ⋎ rightFormula)).length +
          formulaListCodeWeight Gamma <=
        generatedFormulaWeightPolynomial weight := by
    apply (show (binaryFormulaCode (leftFormula ⋎ rightFormula)).length +
        formulaListCodeWeight Gamma <= 4 * weight + 32 by
      dsimp [weight]
      simp only [listedProofHonestBitWeight]
      omega).trans
    exact hlinear
  have hpremiseConclusion :=
    conclusionList_codeWeight_le_honestBitWeight premise
  have hpremiseInput :
      formulaListCodeWeight premise.conclusionList +
          formulaListCodeWeight (leftFormula :: rightFormula :: Gamma) <=
        generatedFormulaWeightPolynomial weight := by
    have htwo := formulaListCodeWeight_two_cons
      leftFormula rightFormula Gamma
    apply (show formulaListCodeWeight premise.conclusionList +
        formulaListCodeWeight (leftFormula :: rightFormula :: Gamma) <=
          4 * weight + 32 by
      rw [htwo]
      dsimp [weight]
      simp only [listedProofHonestBitWeight]
      omega).trans
    exact hlinear
  have hprincipalCost :=
    (formulaMemTrace_cost_le_polynomial
      (leftFormula ⋎ rightFormula) Gamma).trans
        (formulaCheckPolynomial_mono hprincipalInput)
  have hpremiseCost :=
    (formulaSetEqTrace_cost_le_polynomial premise.conclusionList
      (leftFormula :: rightFormula :: Gamma)).trans
        (formulaCheckPolynomial_mono hpremiseInput)
  simp only [listedCertificateValidTrace, traceAnd_cost]
  change _ <= _ + perProofNodeFormulaCostPolynomial weight
  unfold perProofNodeFormulaCostPolynomial
  omega

theorem listedCertificateValidTrace_all_cost_le
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate) :
    (listedCertificateValidTrace
        (.all Gamma formula premise) (.unary premiseCertificate)).2 <=
      (listedCertificateValidTrace premise premiseCertificate).2 +
        perProofNodeFormulaCostPolynomial
          (listedProofHonestBitWeight (.all Gamma formula premise)) := by
  let weight := listedProofHonestBitWeight
    (ListedCheckedPAProofTree.all Gamma formula premise)
  have hlinear := linearGeneratedWeight_le_polynomial weight
  have hprincipalLength := binaryFormulaCode_all_length_le formula
  have hprincipalInput :
      (binaryFormulaCode (∀⁰ formula)).length +
          formulaListCodeWeight Gamma <=
        generatedFormulaWeightPolynomial weight := by
    apply (show (binaryFormulaCode (∀⁰ formula)).length +
        formulaListCodeWeight Gamma <= 4 * weight + 32 by
      dsimp [weight]
      simp only [listedProofHonestBitWeight]
      omega).trans
    exact hlinear
  have hpremiseConclusion :=
    conclusionList_codeWeight_le_honestBitWeight premise
  have hgeneratedList :=
    formulaListCodeWeight_free_cons_map_shift_le formula Gamma
  have hpremiseInput :
      formulaListCodeWeight premise.conclusionList +
          formulaListCodeWeight
            (Rewriting.free formula :: Gamma.map Rewriting.shift) <=
        generatedFormulaWeightPolynomial weight := by
    apply (show formulaListCodeWeight premise.conclusionList +
        formulaListCodeWeight
          (Rewriting.free formula :: Gamma.map Rewriting.shift) <=
          4 * weight + 32 by
      dsimp [weight]
      simp only [listedProofHonestBitWeight]
      omega).trans
    exact hlinear
  have hprincipalCost :=
    (formulaMemTrace_cost_le_polynomial (∀⁰ formula) Gamma).trans
      (formulaCheckPolynomial_mono hprincipalInput)
  have hpremiseCost :=
    (formulaSetEqTrace_cost_le_polynomial premise.conclusionList
      (Rewriting.free formula :: Gamma.map Rewriting.shift)).trans
        (formulaCheckPolynomial_mono hpremiseInput)
  simp only [listedCertificateValidTrace, traceAnd_cost]
  change _ <= _ + perProofNodeFormulaCostPolynomial weight
  unfold perProofNodeFormulaCostPolynomial
  omega

theorem listedCertificateValidTrace_exs_cost_le
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate) :
    (listedCertificateValidTrace
        (.exs Gamma formula witness premise)
        (.unary premiseCertificate)).2 <=
      (listedCertificateValidTrace premise premiseCertificate).2 +
        perProofNodeFormulaCostPolynomial
          (listedProofHonestBitWeight
            (.exs Gamma formula witness premise)) := by
  let weight := listedProofHonestBitWeight
    (ListedCheckedPAProofTree.exs Gamma formula witness premise)
  have hlinear := linearGeneratedWeight_le_polynomial weight
  have hprincipalLength := binaryFormulaCode_exs_length_le formula
  have hprincipalInput :
      (binaryFormulaCode (∃⁰ formula)).length +
          formulaListCodeWeight Gamma <=
        generatedFormulaWeightPolynomial weight := by
    apply (show (binaryFormulaCode (∃⁰ formula)).length +
        formulaListCodeWeight Gamma <= 4 * weight + 32 by
      dsimp [weight]
      simp only [listedProofHonestBitWeight]
      omega).trans
    exact hlinear
  have hpremiseConclusion :=
    conclusionList_codeWeight_le_honestBitWeight premise
  have hgeneratedList :=
    formulaListCodeWeight_substitution_cons_le formula witness Gamma
  have hformulaBound : (binaryFormulaCode formula).length <= weight := by
    dsimp [weight]
    simp only [listedProofHonestBitWeight]
    omega
  have hwitnessBound : (binaryTermCode witness).length <= weight := by
    dsimp [weight]
    simp only [listedProofHonestBitWeight]
    omega
  have hcontextBound : formulaListCodeWeight Gamma <= weight := by
    dsimp [weight]
    simp only [listedProofHonestBitWeight]
    omega
  have hpremiseBound :
      formulaListCodeWeight premise.conclusionList <= weight := by
    calc
      formulaListCodeWeight premise.conclusionList <=
          listedProofHonestBitWeight premise := hpremiseConclusion
      _ <= weight := by
        dsimp [weight]
        simp only [listedProofHonestBitWeight]
        omega
  have hcombined := substitutionGeneratedWithPremiseWeight_le_polynomial
    hformulaBound hwitnessBound hcontextBound hpremiseBound
  have hpremiseInput :
      formulaListCodeWeight premise.conclusionList +
          formulaListCodeWeight (formula/[witness] :: Gamma) <=
        generatedFormulaWeightPolynomial weight := by
    calc
      formulaListCodeWeight premise.conclusionList +
          formulaListCodeWeight (formula/[witness] :: Gamma) <=
        formulaListCodeWeight premise.conclusionList +
          (3 * ((binaryFormulaCode formula).length + 1) *
              ((binaryTermCode witness).length + 1) *
              (binaryFormulaCode formula).length + 3 +
            formulaListCodeWeight Gamma) :=
        Nat.add_le_add_left hgeneratedList _
      _ <= generatedFormulaWeightPolynomial weight := hcombined
  have hprincipalCost :=
    (formulaMemTrace_cost_le_polynomial (∃⁰ formula) Gamma).trans
      (formulaCheckPolynomial_mono hprincipalInput)
  have hpremiseCost :=
    (formulaSetEqTrace_cost_le_polynomial premise.conclusionList
      (formula/[witness] :: Gamma)).trans
        (formulaCheckPolynomial_mono hpremiseInput)
  simp only [listedCertificateValidTrace, traceAnd_cost]
  change _ <= _ + perProofNodeFormulaCostPolynomial weight
  unfold perProofNodeFormulaCostPolynomial
  omega

theorem listedCertificateValidTrace_wk_cost_le
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate) :
    (listedCertificateValidTrace
        (.wk Gamma premise) (.unary premiseCertificate)).2 <=
      (listedCertificateValidTrace premise premiseCertificate).2 +
        perProofNodeFormulaCostPolynomial
          (listedProofHonestBitWeight (.wk Gamma premise)) := by
  let weight := listedProofHonestBitWeight
    (ListedCheckedPAProofTree.wk Gamma premise)
  have hlinear := linearGeneratedWeight_le_polynomial weight
  have hpremiseConclusion :=
    conclusionList_codeWeight_le_honestBitWeight premise
  have hinput :
      formulaListCodeWeight premise.conclusionList +
          formulaListCodeWeight Gamma <=
        generatedFormulaWeightPolynomial weight := by
    apply (show formulaListCodeWeight premise.conclusionList +
        formulaListCodeWeight Gamma <= 4 * weight + 32 by
      dsimp [weight]
      simp only [listedProofHonestBitWeight]
      omega).trans
    exact hlinear
  have hlocalCost :=
    (formulaSubsetTrace_cost_le_polynomial premise.conclusionList Gamma).trans
      (formulaCheckPolynomial_mono hinput)
  simp only [listedCertificateValidTrace, traceAnd_cost]
  change _ <= _ + perProofNodeFormulaCostPolynomial weight
  unfold perProofNodeFormulaCostPolynomial
  omega

theorem listedCertificateValidTrace_shift_cost_le
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate) :
    (listedCertificateValidTrace
        (.shift Gamma premise) (.unary premiseCertificate)).2 <=
      (listedCertificateValidTrace premise premiseCertificate).2 +
        perProofNodeFormulaCostPolynomial
          (listedProofHonestBitWeight (.shift Gamma premise)) := by
  let weight := listedProofHonestBitWeight
    (ListedCheckedPAProofTree.shift Gamma premise)
  have hlinear := linearGeneratedWeight_le_polynomial weight
  have hpremiseConclusion :=
    conclusionList_codeWeight_le_honestBitWeight premise
  have hshifted :=
    formulaListCodeWeight_map_shift_le premise.conclusionList
  have hinput :
      formulaListCodeWeight Gamma +
          formulaListCodeWeight
            (premise.conclusionList.map Rewriting.shift) <=
        generatedFormulaWeightPolynomial weight := by
    apply (show formulaListCodeWeight Gamma +
        formulaListCodeWeight
          (premise.conclusionList.map Rewriting.shift) <=
          4 * weight + 32 by
      dsimp [weight]
      simp only [listedProofHonestBitWeight]
      omega).trans
    exact hlinear
  have hlocalCost :=
    (formulaSetEqTrace_cost_le_polynomial Gamma
      (premise.conclusionList.map Rewriting.shift)).trans
        (formulaCheckPolynomial_mono hinput)
  simp only [listedCertificateValidTrace, traceAnd_cost]
  change _ <= _ + perProofNodeFormulaCostPolynomial weight
  unfold perProofNodeFormulaCostPolynomial
  omega

theorem listedCertificateValidTrace_cut_cost_le
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate) :
    (listedCertificateValidTrace
        (.cut Gamma formula left right)
        (.binary leftCertificate rightCertificate)).2 <=
      (listedCertificateValidTrace left leftCertificate).2 +
        (listedCertificateValidTrace right rightCertificate).2 +
        perProofNodeFormulaCostPolynomial
          (listedProofHonestBitWeight (.cut Gamma formula left right)) := by
  let weight := listedProofHonestBitWeight
    (ListedCheckedPAProofTree.cut Gamma formula left right)
  have hlinear := linearGeneratedWeight_le_polynomial weight
  have hleftConclusion :=
    conclusionList_codeWeight_le_honestBitWeight left
  have hleftInput :
      formulaListCodeWeight left.conclusionList +
          formulaListCodeWeight (formula :: Gamma) <=
        generatedFormulaWeightPolynomial weight := by
    apply (show formulaListCodeWeight left.conclusionList +
        formulaListCodeWeight (formula :: Gamma) <=
          4 * weight + 32 by
      dsimp [weight]
      simp only [listedProofHonestBitWeight, formulaListCodeWeight_cons]
      omega).trans
    exact hlinear
  have hrightConclusion :=
    conclusionList_codeWeight_le_honestBitWeight right
  have hnegList := formulaListCodeWeight_neg_cons_le formula Gamma
  have hrightInput :
      formulaListCodeWeight right.conclusionList +
          formulaListCodeWeight ((∼formula) :: Gamma) <=
        generatedFormulaWeightPolynomial weight := by
    apply (show formulaListCodeWeight right.conclusionList +
        formulaListCodeWeight ((∼formula) :: Gamma) <=
          4 * weight + 32 by
      dsimp [weight]
      simp only [listedProofHonestBitWeight]
      omega).trans
    exact hlinear
  have hleftCost :=
    (formulaSetEqTrace_cost_le_polynomial left.conclusionList
      (formula :: Gamma)).trans
        (formulaCheckPolynomial_mono hleftInput)
  have hrightCost :=
    (formulaSetEqTrace_cost_le_polynomial right.conclusionList
      ((∼formula) :: Gamma)).trans
        (formulaCheckPolynomial_mono hrightInput)
  simp only [listedCertificateValidTrace, traceAnd_cost]
  change _ <= _ + _ + perProofNodeFormulaCostPolynomial weight
  unfold perProofNodeFormulaCostPolynomial
  omega

theorem one_le_nodeCount_mul_perNode
    (tree : ListedCheckedPAProofTree) :
    1 <= listedProofNodeCount tree *
      perProofNodeFormulaCostPolynomial
        (listedProofHonestBitWeight tree) := by
  have hnodes := listedProofNodeCount_pos tree
  have hnodeCost := perProofNodeFormulaCostPolynomial_pos
    (listedProofHonestBitWeight tree)
  simpa using Nat.mul_le_mul hnodes hnodeCost

theorem perNodeCost_le_doubleBudget
    {tree : ListedCheckedPAProofTree} {budget : Nat}
    (htree : listedProofHonestBitWeight tree <= budget) :
    perProofNodeFormulaCostPolynomial
        (listedProofHonestBitWeight tree) <=
      perProofNodeFormulaCostPolynomial (2 * budget) := by
  apply perProofNodeFormulaCostPolynomial_mono
  omega

theorem one_le_nodeCount_mul_doubleBudgetPerNode
    (tree : ListedCheckedPAProofTree) (budget : Nat) :
    1 <= listedProofNodeCount tree *
      perProofNodeFormulaCostPolynomial (2 * budget) := by
  have hnodes := listedProofNodeCount_pos tree
  have hnodeCost := perProofNodeFormulaCostPolynomial_pos (2 * budget)
  simpa using Nat.mul_le_mul hnodes hnodeCost

theorem listedCertificateValidTrace_cost_le_of_axm
    (haxm : forall
      (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (sentence : LO.FirstOrder.ArithmeticSentence)
      (axiomCertificate : PAAxiomCertificate),
      (listedCertificateValidTrace (.axm Gamma sentence)
        (.axiomCert axiomCertificate)).2 <=
        perProofNodeFormulaCostPolynomial
          (listedProofHonestBitWeight (.axm Gamma sentence)))
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    (listedCertificateValidTrace tree certificate).2 <=
      listedProofNodeCount tree *
        perProofNodeFormulaCostPolynomial
          (listedProofHonestBitWeight tree) := by
  induction tree generalizing certificate with
  | closed Gamma formula =>
      cases certificate with
      | leaf =>
          simpa [listedProofNodeCount] using
            listedCertificateValidTrace_closed_cost_le Gamma formula
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.closed Gamma formula)
      | unary premiseCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.closed Gamma formula)
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.closed Gamma formula)
  | axm Gamma sentence =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.axm Gamma sentence)
      | axiomCert axiomCertificate =>
          simpa [listedProofNodeCount] using
            haxm Gamma sentence axiomCertificate
      | unary premiseCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.axm Gamma sentence)
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.axm Gamma sentence)
  | verum Gamma =>
      cases certificate with
      | leaf =>
          simpa [listedProofNodeCount] using
            listedCertificateValidTrace_verum_cost_le Gamma
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.verum Gamma)
      | unary premiseCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.verum Gamma)
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.verum Gamma)
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.and Gamma leftFormula rightFormula
                left right)
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.and Gamma leftFormula rightFormula
                left right)
      | unary premiseCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.and Gamma leftFormula rightFormula
                left right)
      | binary leftCertificate rightCertificate =>
          let weight := listedProofHonestBitWeight
            (ListedCheckedPAProofTree.and Gamma leftFormula rightFormula
              left right)
          have hleftWeight : listedProofHonestBitWeight left <= weight := by
            dsimp [weight]
            simp only [listedProofHonestBitWeight]
            omega
          have hrightWeight : listedProofHonestBitWeight right <= weight := by
            dsimp [weight]
            simp only [listedProofHonestBitWeight]
            omega
          have hleftNode :=
            perProofNodeFormulaCostPolynomial_mono hleftWeight
          have hrightNode :=
            perProofNodeFormulaCostPolynomial_mono hrightWeight
          have hleftScaled :=
            Nat.mul_le_mul_left (listedProofNodeCount left) hleftNode
          have hrightScaled :=
            Nat.mul_le_mul_left (listedProofNodeCount right) hrightNode
          have hleftCost := (ihLeft leftCertificate).trans hleftScaled
          have hrightCost := (ihRight rightCertificate).trans hrightScaled
          have hlocal := listedCertificateValidTrace_and_cost_le
            Gamma leftFormula rightFormula left right
              leftCertificate rightCertificate
          dsimp [weight] at hleftCost hrightCost hlocal
          simp only [listedProofNodeCount, Nat.add_mul, one_mul]
          omega
  | or Gamma leftFormula rightFormula premise ih =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.or Gamma leftFormula rightFormula premise)
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.or Gamma leftFormula rightFormula premise)
      | unary premiseCertificate =>
          let weight := listedProofHonestBitWeight
            (ListedCheckedPAProofTree.or Gamma leftFormula rightFormula premise)
          have hpremiseWeight :
              listedProofHonestBitWeight premise <= weight := by
            dsimp [weight]
            simp only [listedProofHonestBitWeight]
            omega
          have hpremiseNode :=
            perProofNodeFormulaCostPolynomial_mono hpremiseWeight
          have hpremiseScaled :=
            Nat.mul_le_mul_left (listedProofNodeCount premise) hpremiseNode
          have hpremiseCost := (ih premiseCertificate).trans hpremiseScaled
          have hlocal := listedCertificateValidTrace_or_cost_le
            Gamma leftFormula rightFormula premise premiseCertificate
          dsimp [weight] at hpremiseCost hlocal
          simp only [listedProofNodeCount, Nat.add_mul, one_mul]
          omega
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.or Gamma leftFormula rightFormula premise)
  | all Gamma formula premise ih =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.all Gamma formula premise)
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.all Gamma formula premise)
      | unary premiseCertificate =>
          let weight := listedProofHonestBitWeight
            (ListedCheckedPAProofTree.all Gamma formula premise)
          have hpremiseWeight :
              listedProofHonestBitWeight premise <= weight := by
            dsimp [weight]
            simp only [listedProofHonestBitWeight]
            omega
          have hpremiseNode :=
            perProofNodeFormulaCostPolynomial_mono hpremiseWeight
          have hpremiseScaled :=
            Nat.mul_le_mul_left (listedProofNodeCount premise) hpremiseNode
          have hpremiseCost := (ih premiseCertificate).trans hpremiseScaled
          have hlocal := listedCertificateValidTrace_all_cost_le
            Gamma formula premise premiseCertificate
          dsimp [weight] at hpremiseCost hlocal
          simp only [listedProofNodeCount, Nat.add_mul, one_mul]
          omega
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.all Gamma formula premise)
  | exs Gamma formula witness premise ih =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.exs Gamma formula witness premise)
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.exs Gamma formula witness premise)
      | unary premiseCertificate =>
          let weight := listedProofHonestBitWeight
            (ListedCheckedPAProofTree.exs Gamma formula witness premise)
          have hpremiseWeight :
              listedProofHonestBitWeight premise <= weight := by
            dsimp [weight]
            simp only [listedProofHonestBitWeight]
            omega
          have hpremiseNode :=
            perProofNodeFormulaCostPolynomial_mono hpremiseWeight
          have hpremiseScaled :=
            Nat.mul_le_mul_left (listedProofNodeCount premise) hpremiseNode
          have hpremiseCost := (ih premiseCertificate).trans hpremiseScaled
          have hlocal := listedCertificateValidTrace_exs_cost_le
            Gamma formula witness premise premiseCertificate
          dsimp [weight] at hpremiseCost hlocal
          simp only [listedProofNodeCount, Nat.add_mul, one_mul]
          omega
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.exs Gamma formula witness premise)
  | wk Gamma premise ih =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.wk Gamma premise)
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.wk Gamma premise)
      | unary premiseCertificate =>
          let weight := listedProofHonestBitWeight
            (ListedCheckedPAProofTree.wk Gamma premise)
          have hpremiseWeight :
              listedProofHonestBitWeight premise <= weight := by
            dsimp [weight]
            simp only [listedProofHonestBitWeight]
            omega
          have hpremiseNode :=
            perProofNodeFormulaCostPolynomial_mono hpremiseWeight
          have hpremiseScaled :=
            Nat.mul_le_mul_left (listedProofNodeCount premise) hpremiseNode
          have hpremiseCost := (ih premiseCertificate).trans hpremiseScaled
          have hlocal := listedCertificateValidTrace_wk_cost_le
            Gamma premise premiseCertificate
          dsimp [weight] at hpremiseCost hlocal
          simp only [listedProofNodeCount, Nat.add_mul, one_mul]
          omega
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.wk Gamma premise)
  | shift Gamma premise ih =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.shift Gamma premise)
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.shift Gamma premise)
      | unary premiseCertificate =>
          let weight := listedProofHonestBitWeight
            (ListedCheckedPAProofTree.shift Gamma premise)
          have hpremiseWeight :
              listedProofHonestBitWeight premise <= weight := by
            dsimp [weight]
            simp only [listedProofHonestBitWeight]
            omega
          have hpremiseNode :=
            perProofNodeFormulaCostPolynomial_mono hpremiseWeight
          have hpremiseScaled :=
            Nat.mul_le_mul_left (listedProofNodeCount premise) hpremiseNode
          have hpremiseCost := (ih premiseCertificate).trans hpremiseScaled
          have hlocal := listedCertificateValidTrace_shift_cost_le
            Gamma premise premiseCertificate
          dsimp [weight] at hpremiseCost hlocal
          simp only [listedProofNodeCount, Nat.add_mul, one_mul]
          omega
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.shift Gamma premise)
  | cut Gamma formula left right ihLeft ihRight =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.cut Gamma formula left right)
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.cut Gamma formula left right)
      | unary premiseCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_perNode
              (ListedCheckedPAProofTree.cut Gamma formula left right)
      | binary leftCertificate rightCertificate =>
          let weight := listedProofHonestBitWeight
            (ListedCheckedPAProofTree.cut Gamma formula left right)
          have hleftWeight : listedProofHonestBitWeight left <= weight := by
            dsimp [weight]
            simp only [listedProofHonestBitWeight]
            omega
          have hrightWeight : listedProofHonestBitWeight right <= weight := by
            dsimp [weight]
            simp only [listedProofHonestBitWeight]
            omega
          have hleftNode :=
            perProofNodeFormulaCostPolynomial_mono hleftWeight
          have hrightNode :=
            perProofNodeFormulaCostPolynomial_mono hrightWeight
          have hleftScaled :=
            Nat.mul_le_mul_left (listedProofNodeCount left) hleftNode
          have hrightScaled :=
            Nat.mul_le_mul_left (listedProofNodeCount right) hrightNode
          have hleftCost := (ihLeft leftCertificate).trans hleftScaled
          have hrightCost := (ihRight rightCertificate).trans hrightScaled
          have hlocal := listedCertificateValidTrace_cut_cost_le
            Gamma formula left right leftCertificate rightCertificate
          dsimp [weight] at hleftCost hrightCost hlocal
          simp only [listedProofNodeCount, Nat.add_mul, one_mul]
          omega

theorem listedCertificateValidTrace_cost_le_polynomial_of_axm
    (haxm : forall
      (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (sentence : LO.FirstOrder.ArithmeticSentence)
      (axiomCertificate : PAAxiomCertificate),
      (listedCertificateValidTrace (.axm Gamma sentence)
        (.axiomCert axiomCertificate)).2 <=
        perProofNodeFormulaCostPolynomial
          (listedProofHonestBitWeight (.axm Gamma sentence)))
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    (listedCertificateValidTrace tree certificate).2 <=
      listedLocalCostPolynomial (listedProofHonestBitWeight tree) := by
  exact (listedCertificateValidTrace_cost_le_of_axm haxm tree certificate).trans
    (nodeCount_mul_perNode_le_listedLocalCostPolynomial tree)

theorem listedCertificateValidTrace_jointBudget_cost_le_of_axm
    (haxm : forall
      (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (sentence : LO.FirstOrder.ArithmeticSentence)
      (axiomCertificate : PAAxiomCertificate),
      (listedCertificateValidTrace (.axm Gamma sentence)
        (.axiomCert axiomCertificate)).2 <=
        perProofNodeFormulaCostPolynomial
          (listedLocalJointHonestBitWeight (.axm Gamma sentence)
            (.axiomCert axiomCertificate)))
    {budget : Nat}
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (htree : listedProofHonestBitWeight tree <= budget)
    (hcertificate :
      localStructuralCertificateHonestBitWeight certificate <= budget) :
    (listedCertificateValidTrace tree certificate).2 <=
      listedProofNodeCount tree *
        perProofNodeFormulaCostPolynomial (2 * budget) := by
  induction tree generalizing certificate with
  | closed Gamma formula =>
      cases certificate with
      | leaf =>
          have hlocal := listedCertificateValidTrace_closed_cost_le Gamma formula
          have hlift := perNodeCost_le_doubleBudget htree
          simpa [listedProofNodeCount] using hlocal.trans hlift
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.closed Gamma formula) budget
      | unary premiseCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.closed Gamma formula) budget
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.closed Gamma formula) budget
  | axm Gamma sentence =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.axm Gamma sentence) budget
      | axiomCert axiomCertificate =>
          have hlocal := haxm Gamma sentence axiomCertificate
          have hjoint :
              listedLocalJointHonestBitWeight
                  (ListedCheckedPAProofTree.axm Gamma sentence)
                  (.axiomCert axiomCertificate) <=
                2 * budget := by
            unfold listedLocalJointHonestBitWeight
            omega
          have hlift := perProofNodeFormulaCostPolynomial_mono hjoint
          simpa [listedProofNodeCount] using hlocal.trans hlift
      | unary premiseCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.axm Gamma sentence) budget
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.axm Gamma sentence) budget
  | verum Gamma =>
      cases certificate with
      | leaf =>
          have hlocal := listedCertificateValidTrace_verum_cost_le Gamma
          have hlift := perNodeCost_le_doubleBudget htree
          simpa [listedProofNodeCount] using hlocal.trans hlift
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.verum Gamma) budget
      | unary premiseCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.verum Gamma) budget
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.verum Gamma) budget
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.and Gamma leftFormula rightFormula
                left right) budget
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.and Gamma leftFormula rightFormula
                left right) budget
      | unary premiseCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.and Gamma leftFormula rightFormula
                left right) budget
      | binary leftCertificate rightCertificate =>
          have hleftTree : listedProofHonestBitWeight left <= budget := by
            apply (show listedProofHonestBitWeight left <=
                listedProofHonestBitWeight
                  (ListedCheckedPAProofTree.and Gamma leftFormula rightFormula
                    left right) by
              simp only [listedProofHonestBitWeight]
              omega).trans htree
          have hrightTree : listedProofHonestBitWeight right <= budget := by
            apply (show listedProofHonestBitWeight right <=
                listedProofHonestBitWeight
                  (ListedCheckedPAProofTree.and Gamma leftFormula rightFormula
                    left right) by
              simp only [listedProofHonestBitWeight]
              omega).trans htree
          have hleftCertificate :=
            (localStructuralCertificateHonestBitWeight_binary_left_le
              leftCertificate rightCertificate).trans hcertificate
          have hrightCertificate :=
            (localStructuralCertificateHonestBitWeight_binary_right_le
              leftCertificate rightCertificate).trans hcertificate
          have hleftCost := ihLeft leftCertificate hleftTree hleftCertificate
          have hrightCost :=
            ihRight rightCertificate hrightTree hrightCertificate
          have hlocal := listedCertificateValidTrace_and_cost_le
            Gamma leftFormula rightFormula left right
              leftCertificate rightCertificate
          have hlift := perNodeCost_le_doubleBudget htree
          have hlocal' := hlocal.trans
            (Nat.add_le_add_left hlift
              ((listedCertificateValidTrace left leftCertificate).2 +
                (listedCertificateValidTrace right rightCertificate).2))
          simp only [listedProofNodeCount, Nat.add_mul, one_mul]
          omega
  | or Gamma leftFormula rightFormula premise ih =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.or Gamma leftFormula rightFormula premise)
              budget
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.or Gamma leftFormula rightFormula premise)
              budget
      | unary premiseCertificate =>
          have hpremiseTree : listedProofHonestBitWeight premise <= budget := by
            apply (show listedProofHonestBitWeight premise <=
                listedProofHonestBitWeight
                  (ListedCheckedPAProofTree.or Gamma leftFormula rightFormula
                    premise) by
              simp only [listedProofHonestBitWeight]
              omega).trans htree
          have hpremiseCertificate :=
            (localStructuralCertificateHonestBitWeight_unary_le
              premiseCertificate).trans hcertificate
          have hpremiseCost :=
            ih premiseCertificate hpremiseTree hpremiseCertificate
          have hlocal := listedCertificateValidTrace_or_cost_le
            Gamma leftFormula rightFormula premise premiseCertificate
          have hlift := perNodeCost_le_doubleBudget htree
          have hlocal' := hlocal.trans
            (Nat.add_le_add_left hlift
              (listedCertificateValidTrace premise premiseCertificate).2)
          simp only [listedProofNodeCount, Nat.add_mul, one_mul]
          omega
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.or Gamma leftFormula rightFormula premise)
              budget
  | all Gamma formula premise ih =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.all Gamma formula premise) budget
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.all Gamma formula premise) budget
      | unary premiseCertificate =>
          have hpremiseTree : listedProofHonestBitWeight premise <= budget := by
            apply (show listedProofHonestBitWeight premise <=
                listedProofHonestBitWeight
                  (ListedCheckedPAProofTree.all Gamma formula premise) by
              simp only [listedProofHonestBitWeight]
              omega).trans htree
          have hpremiseCertificate :=
            (localStructuralCertificateHonestBitWeight_unary_le
              premiseCertificate).trans hcertificate
          have hpremiseCost :=
            ih premiseCertificate hpremiseTree hpremiseCertificate
          have hlocal := listedCertificateValidTrace_all_cost_le
            Gamma formula premise premiseCertificate
          have hlift := perNodeCost_le_doubleBudget htree
          have hlocal' := hlocal.trans
            (Nat.add_le_add_left hlift
              (listedCertificateValidTrace premise premiseCertificate).2)
          simp only [listedProofNodeCount, Nat.add_mul, one_mul]
          omega
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.all Gamma formula premise) budget
  | exs Gamma formula witness premise ih =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.exs Gamma formula witness premise) budget
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.exs Gamma formula witness premise) budget
      | unary premiseCertificate =>
          have hpremiseTree : listedProofHonestBitWeight premise <= budget := by
            apply (show listedProofHonestBitWeight premise <=
                listedProofHonestBitWeight
                  (ListedCheckedPAProofTree.exs Gamma formula witness premise) by
              simp only [listedProofHonestBitWeight]
              omega).trans htree
          have hpremiseCertificate :=
            (localStructuralCertificateHonestBitWeight_unary_le
              premiseCertificate).trans hcertificate
          have hpremiseCost :=
            ih premiseCertificate hpremiseTree hpremiseCertificate
          have hlocal := listedCertificateValidTrace_exs_cost_le
            Gamma formula witness premise premiseCertificate
          have hlift := perNodeCost_le_doubleBudget htree
          have hlocal' := hlocal.trans
            (Nat.add_le_add_left hlift
              (listedCertificateValidTrace premise premiseCertificate).2)
          simp only [listedProofNodeCount, Nat.add_mul, one_mul]
          omega
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.exs Gamma formula witness premise) budget
  | wk Gamma premise ih =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.wk Gamma premise) budget
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.wk Gamma premise) budget
      | unary premiseCertificate =>
          have hpremiseTree : listedProofHonestBitWeight premise <= budget := by
            apply (show listedProofHonestBitWeight premise <=
                listedProofHonestBitWeight
                  (ListedCheckedPAProofTree.wk Gamma premise) by
              simp only [listedProofHonestBitWeight]
              omega).trans htree
          have hpremiseCertificate :=
            (localStructuralCertificateHonestBitWeight_unary_le
              premiseCertificate).trans hcertificate
          have hpremiseCost :=
            ih premiseCertificate hpremiseTree hpremiseCertificate
          have hlocal := listedCertificateValidTrace_wk_cost_le
            Gamma premise premiseCertificate
          have hlift := perNodeCost_le_doubleBudget htree
          have hlocal' := hlocal.trans
            (Nat.add_le_add_left hlift
              (listedCertificateValidTrace premise premiseCertificate).2)
          simp only [listedProofNodeCount, Nat.add_mul, one_mul]
          omega
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.wk Gamma premise) budget
  | shift Gamma premise ih =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.shift Gamma premise) budget
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.shift Gamma premise) budget
      | unary premiseCertificate =>
          have hpremiseTree : listedProofHonestBitWeight premise <= budget := by
            apply (show listedProofHonestBitWeight premise <=
                listedProofHonestBitWeight
                  (ListedCheckedPAProofTree.shift Gamma premise) by
              simp only [listedProofHonestBitWeight]
              omega).trans htree
          have hpremiseCertificate :=
            (localStructuralCertificateHonestBitWeight_unary_le
              premiseCertificate).trans hcertificate
          have hpremiseCost :=
            ih premiseCertificate hpremiseTree hpremiseCertificate
          have hlocal := listedCertificateValidTrace_shift_cost_le
            Gamma premise premiseCertificate
          have hlift := perNodeCost_le_doubleBudget htree
          have hlocal' := hlocal.trans
            (Nat.add_le_add_left hlift
              (listedCertificateValidTrace premise premiseCertificate).2)
          simp only [listedProofNodeCount, Nat.add_mul, one_mul]
          omega
      | binary leftCertificate rightCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.shift Gamma premise) budget
  | cut Gamma formula left right ihLeft ihRight =>
      cases certificate with
      | leaf =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.cut Gamma formula left right) budget
      | axiomCert axiomCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.cut Gamma formula left right) budget
      | unary premiseCertificate =>
          simpa [listedCertificateValidTrace] using
            one_le_nodeCount_mul_doubleBudgetPerNode
              (ListedCheckedPAProofTree.cut Gamma formula left right) budget
      | binary leftCertificate rightCertificate =>
          have hleftTree : listedProofHonestBitWeight left <= budget := by
            apply (show listedProofHonestBitWeight left <=
                listedProofHonestBitWeight
                  (ListedCheckedPAProofTree.cut Gamma formula left right) by
              simp only [listedProofHonestBitWeight]
              omega).trans htree
          have hrightTree : listedProofHonestBitWeight right <= budget := by
            apply (show listedProofHonestBitWeight right <=
                listedProofHonestBitWeight
                  (ListedCheckedPAProofTree.cut Gamma formula left right) by
              simp only [listedProofHonestBitWeight]
              omega).trans htree
          have hleftCertificate :=
            (localStructuralCertificateHonestBitWeight_binary_left_le
              leftCertificate rightCertificate).trans hcertificate
          have hrightCertificate :=
            (localStructuralCertificateHonestBitWeight_binary_right_le
              leftCertificate rightCertificate).trans hcertificate
          have hleftCost := ihLeft leftCertificate hleftTree hleftCertificate
          have hrightCost :=
            ihRight rightCertificate hrightTree hrightCertificate
          have hlocal := listedCertificateValidTrace_cut_cost_le
            Gamma formula left right leftCertificate rightCertificate
          have hlift := perNodeCost_le_doubleBudget htree
          have hlocal' := hlocal.trans
            (Nat.add_le_add_left hlift
              ((listedCertificateValidTrace left leftCertificate).2 +
                (listedCertificateValidTrace right rightCertificate).2))
          simp only [listedProofNodeCount, Nat.add_mul, one_mul]
          omega

theorem listedCertificateValidTrace_jointCost_le_polynomial_of_axm
    (haxm : forall
      (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (sentence : LO.FirstOrder.ArithmeticSentence)
      (axiomCertificate : PAAxiomCertificate),
      (listedCertificateValidTrace (.axm Gamma sentence)
        (.axiomCert axiomCertificate)).2 <=
        perProofNodeFormulaCostPolynomial
          (listedLocalJointHonestBitWeight (.axm Gamma sentence)
            (.axiomCert axiomCertificate)))
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    (listedCertificateValidTrace tree certificate).2 <=
      listedJointLocalCostPolynomial
        (listedLocalJointHonestBitWeight tree certificate) := by
  let budget := listedLocalJointHonestBitWeight tree certificate
  have htree : listedProofHonestBitWeight tree <= budget := by
    dsimp [budget]
    exact listedProofHonestBitWeight_le_joint tree certificate
  have hcertificate :
      localStructuralCertificateHonestBitWeight certificate <= budget := by
    dsimp [budget]
    exact localStructuralCertificateHonestBitWeight_le_joint tree certificate
  have htotal := listedCertificateValidTrace_jointBudget_cost_le_of_axm
    haxm tree certificate htree hcertificate
  exact htotal.trans
    (nodeCount_mul_jointPerNode_le_listedJointLocalCostPolynomial
      tree certificate)

#print axioms formulaCheckPolynomial_mono
#print axioms formulaEqTrace_cost_le_polynomial
#print axioms formulaMemTrace_cost_le_polynomial
#print axioms formulaSubsetTrace_cost_le_polynomial
#print axioms formulaSetEqTrace_cost_le_polynomial
#print axioms binaryFormulaCode_and_length_le
#print axioms binaryFormulaCode_or_length_le
#print axioms binaryFormulaCode_all_length_le
#print axioms binaryFormulaCode_exs_length_le
#print axioms formulaListCodeWeight_neg_cons_le
#print axioms formulaListCodeWeight_two_cons
#print axioms formulaListCodeWeight_free_cons_map_shift_le
#print axioms formulaListCodeWeight_substitution_cons_le
#print axioms listedProofNodeCount_le_honestBitWeight
#print axioms generatedFormulaWeightPolynomial_mono
#print axioms substitutionGeneratedWeight_le_polynomial
#print axioms listedLocalCostPolynomial_mono
#print axioms nodeCount_mul_perNode_le_listedLocalCostPolynomial
#print axioms listedCertificateValidTrace_closed_cost_le
#print axioms listedCertificateValidTrace_verum_cost_le
#print axioms listedCertificateValidTrace_and_cost_le
#print axioms listedCertificateValidTrace_or_cost_le
#print axioms listedCertificateValidTrace_all_cost_le
#print axioms listedCertificateValidTrace_exs_cost_le
#print axioms listedCertificateValidTrace_wk_cost_le
#print axioms listedCertificateValidTrace_shift_cost_le
#print axioms listedCertificateValidTrace_cut_cost_le
#print axioms listedCertificateValidTrace_cost_le_of_axm
#print axioms listedCertificateValidTrace_cost_le_polynomial_of_axm
#print axioms listedCertificateValidTrace_jointBudget_cost_le_of_axm
#print axioms listedCertificateValidTrace_jointCost_le_polynomial_of_axm

end FoundationCompactListedLocalCostPrimitives
