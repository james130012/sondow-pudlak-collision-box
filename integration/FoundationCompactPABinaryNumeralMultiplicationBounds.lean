import integration.FoundationCompactPABinaryNumeralMultiplication

/-!
# Polynomial payload bound for binary-numeral multiplication

This module derives a closed payload polynomial for the checked multiplication
normalizer.  Every envelope is defined from concrete syntax encoders, fixed PA
axioms, and previously checked proof constructors.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABinaryNumeralMultiplicationBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAAxiomCertificate
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABinaryNumeralMultiplication

/-! ## Numeric and term-code work widths -/

theorem natSize_mul_le (left right : Nat) :
    Nat.size (left * right) <= Nat.size left + Nat.size right := by
  by_cases hright : right = 0
  · subst right
    simp
  rw [Nat.size_le]
  have hleftLt : left < 2 ^ Nat.size left := Nat.lt_size_self left
  have hrightLt : right < 2 ^ Nat.size right := Nat.lt_size_self right
  have hrightPos : 0 < right := Nat.pos_of_ne_zero hright
  have hrightPowerPos : 0 < 2 ^ Nat.size right :=
    Nat.pow_pos (by decide)
  calc
    left * right < 2 ^ Nat.size left * right :=
      Nat.mul_lt_mul_of_pos_right hleftLt hrightPos
    _ < 2 ^ Nat.size left * 2 ^ Nat.size right :=
      Nat.mul_lt_mul_of_pos_left hrightLt
        (Nat.pow_pos (by decide))
    _ = 2 ^ (Nat.size left + Nat.size right) := by rw [pow_add]

def paMultiplicationWorkWidth (inputWidth : Nat) : Nat :=
  2 * inputWidth + 4

def paMultiplicationTermCodeEnvelope (inputWidth : Nat) : Nat :=
  paGeneratedTermCodeEnvelope (paMultiplicationWorkWidth inputWidth)

theorem multiplication_left_size_le_work
    (left right inputWidth : Nat)
    (hwidth : Nat.size left + Nat.size right <= inputWidth) :
    Nat.size left <= paMultiplicationWorkWidth inputWidth := by
  unfold paMultiplicationWorkWidth
  omega

theorem multiplication_right_size_le_work
    (left right inputWidth : Nat)
    (hwidth : Nat.size left + Nat.size right <= inputWidth) :
    Nat.size right <= paMultiplicationWorkWidth inputWidth := by
  unfold paMultiplicationWorkWidth
  omega

theorem multiplication_product_size_le_work
    (left right inputWidth : Nat)
    (hwidth : Nat.size left + Nat.size right <= inputWidth) :
    Nat.size (left * right) <= paMultiplicationWorkWidth inputWidth := by
  have hproduct := natSize_mul_le left right
  unfold paMultiplicationWorkWidth
  omega

theorem multiplication_doubled_product_size_le_work
    (left right inputWidth : Nat)
    (hwidth : Nat.size left + Nat.size right <= inputWidth) :
    Nat.size (Nat.bit false (left * right)) <=
      paMultiplicationWorkWidth inputWidth := by
  by_cases hproduct : left * right = 0
  · simp [hproduct, Nat.bit_val]
  have hbit : Nat.bit false (left * right) ≠ 0 :=
    Nat.bit_ne_zero_iff.mpr (fun hz => (hproduct hz).elim)
  have hsize := Nat.size_bit hbit
  have hproductSize := natSize_mul_le left right
  rw [hsize]
  unfold paMultiplicationWorkWidth
  omega

/-! ## Formula-code envelopes for multiplication axioms -/

def multiplicationFormulaSeed : Nat :=
  (binaryFormulaCode mulCommutativityOuterBody).length +
    (binaryFormulaCode mulAssociativityOuterBody).length + 1

def multiplicationFormulaStage0 : Nat := multiplicationFormulaSeed

def multiplicationFormulaStage1 (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope multiplicationFormulaStage0 termBound

def multiplicationFormulaStage2 (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (multiplicationFormulaStage1 termBound) termBound

def multiplicationFormulaCodeEnvelope (termBound : Nat) : Nat :=
  multiplicationFormulaStage0 + multiplicationFormulaStage1 termBound +
    multiplicationFormulaStage2 termBound + 1

theorem mulCommutativityOuterBody_code_le_seed :
    (binaryFormulaCode mulCommutativityOuterBody).length <=
      multiplicationFormulaSeed := by
  unfold multiplicationFormulaSeed
  omega

theorem mulAssociativityOuterBody_code_le_seed :
    (binaryFormulaCode mulAssociativityOuterBody).length <=
      multiplicationFormulaSeed := by
  unfold multiplicationFormulaSeed
  omega

theorem multiplicationFormulaStage0_le_envelope (termBound : Nat) :
    multiplicationFormulaStage0 <=
      multiplicationFormulaCodeEnvelope termBound := by
  unfold multiplicationFormulaCodeEnvelope
  omega

theorem multiplicationFormulaStage1_le_envelope (termBound : Nat) :
    multiplicationFormulaStage1 termBound <=
      multiplicationFormulaCodeEnvelope termBound := by
  unfold multiplicationFormulaCodeEnvelope
  omega

theorem multiplicationFormulaStage2_le_envelope (termBound : Nat) :
    multiplicationFormulaStage2 termBound <=
      multiplicationFormulaCodeEnvelope termBound := by
  unfold multiplicationFormulaCodeEnvelope
  omega

theorem mulCommutativityInnerBody_code_le_stage1
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound) :
    (binaryFormulaCode (mulCommutativityInnerBody left)).length <=
      multiplicationFormulaStage1 termBound := by
  have hbody := instantiatedBodyCode_le_nextStage
    mulCommutativityOuterBody (mulCommutativityInnerBody left)
    left multiplicationFormulaStage0 termBound
    (by simpa [multiplicationFormulaStage0] using
      mulCommutativityOuterBody_code_le_seed)
    hleft (mulCommutativityAfterFirst_formula left)
  simpa [multiplicationFormulaStage1] using hbody

theorem mulAssociativityMiddleBody_code_le_stage1
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound) :
    (binaryFormulaCode (mulAssociativityMiddleBody left)).length <=
      multiplicationFormulaStage1 termBound := by
  have hbody := instantiatedBodyCode_le_nextStage
    mulAssociativityOuterBody (mulAssociativityMiddleBody left)
    left multiplicationFormulaStage0 termBound
    (by simpa [multiplicationFormulaStage0] using
      mulAssociativityOuterBody_code_le_seed)
    hleft (mulAssociativityAfterFirst_formula left)
  simpa [multiplicationFormulaStage1] using hbody

theorem mulAssociativityInnerBody_code_le_stage2
    (left middle : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hmiddle : (binaryTermCode middle).length <= termBound) :
    (binaryFormulaCode
      (mulAssociativityInnerBody left middle)).length <=
      multiplicationFormulaStage2 termBound := by
  have hbody := instantiatedBodyCode_le_nextStage
    (mulAssociativityMiddleBody left)
    (mulAssociativityInnerBody left middle)
    middle (multiplicationFormulaStage1 termBound) termBound
    (mulAssociativityMiddleBody_code_le_stage1 left termBound hleft)
    hmiddle (mulAssociativityAfterSecond_formula left middle)
  simpa [multiplicationFormulaStage2] using hbody

def multiplicationSpecializationScaleEnvelope (termBound : Nat) : Nat :=
  multiplicationFormulaCodeEnvelope termBound + termBound + 1

def multiplicationSpecializationCostEnvelope (termBound : Nat) : Nat :=
  192 + 2048 * multiplicationSpecializationScaleEnvelope termBound *
    multiplicationSpecializationScaleEnvelope termBound *
    multiplicationSpecializationScaleEnvelope termBound

theorem specializationCost_le_multiplicationEnvelope
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hformula : (binaryFormulaCode formula).length <=
      multiplicationFormulaCodeEnvelope termBound)
    (hwitness : (binaryTermCode witness).length <= termBound) :
    specializationCost formula witness <=
      multiplicationSpecializationCostEnvelope termBound := by
  have hscale : specializationScale formula witness <=
      multiplicationSpecializationScaleEnvelope termBound := by
    simp [specializationScale, multiplicationSpecializationScaleEnvelope]
    omega
  simp only [specializationCost, multiplicationSpecializationCostEnvelope]
  gcongr

def fixedMultiplicationAxiomPayloadEnvelope : Nat :=
  (32 + 10 * axiomSyntaxBudget .mulComm) +
    (32 + 10 * axiomSyntaxBudget .mulAssoc) + 1

def paMultiplicationPrimitiveCostEnvelope (inputWidth : Nat) : Nat :=
  let termBound := paMultiplicationTermCodeEnvelope inputWidth
  fixedMultiplicationAxiomPayloadEnvelope +
    16 * multiplicationSpecializationCostEnvelope termBound +
    16 * paPrimitiveCostEnvelope termBound + 1

theorem paPrimitiveCost_le_multiplicationPrimitive (inputWidth : Nat) :
    paPrimitiveCostEnvelope (paMultiplicationTermCodeEnvelope inputWidth) <=
      paMultiplicationPrimitiveCostEnvelope inputWidth := by
  simp [paMultiplicationPrimitiveCostEnvelope]
  omega

theorem proveMulCommutativity_payloadLength_le_primitive
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (inputWidth : Nat)
    (hleft : (binaryTermCode left).length <=
      paMultiplicationTermCodeEnvelope inputWidth)
    (hright : (binaryTermCode right).length <=
      paMultiplicationTermCodeEnvelope inputWidth) :
    (proveMulCommutativity left right).payloadLength <=
      paMultiplicationPrimitiveCostEnvelope inputWidth := by
  let termBound := paMultiplicationTermCodeEnvelope inputWidth
  have hproof := proveMulCommutativity_payloadLength_le left right
  have haxiom := mulCommutativityAxiomProof_payloadLength_le
  have hfirst := specializationCost_le_multiplicationEnvelope
    mulCommutativityOuterBody left termBound
    ((mulCommutativityOuterBody_code_le_seed.trans
      (multiplicationFormulaStage0_le_envelope termBound))) hleft
  have hsecond := specializationCost_le_multiplicationEnvelope
    (mulCommutativityInnerBody left) right termBound
    ((mulCommutativityInnerBody_code_le_stage1 left termBound hleft).trans
      (multiplicationFormulaStage1_le_envelope termBound)) hright
  simp only [paMultiplicationPrimitiveCostEnvelope]
  dsimp only [termBound] at *
  unfold fixedMultiplicationAxiomPayloadEnvelope at haxiom ⊢
  omega

theorem proveMulAssociativity_payloadLength_le_primitive
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (inputWidth : Nat)
    (hleft : (binaryTermCode left).length <=
      paMultiplicationTermCodeEnvelope inputWidth)
    (hmiddle : (binaryTermCode middle).length <=
      paMultiplicationTermCodeEnvelope inputWidth)
    (hright : (binaryTermCode right).length <=
      paMultiplicationTermCodeEnvelope inputWidth) :
    (proveMulAssociativity left middle right).payloadLength <=
      paMultiplicationPrimitiveCostEnvelope inputWidth := by
  let termBound := paMultiplicationTermCodeEnvelope inputWidth
  have hproof := proveMulAssociativity_payloadLength_le left middle right
  have haxiom := mulAssociativityAxiomProof_payloadLength_le
  have hfirst := specializationCost_le_multiplicationEnvelope
    mulAssociativityOuterBody left termBound
    ((mulAssociativityOuterBody_code_le_seed.trans
      (multiplicationFormulaStage0_le_envelope termBound))) hleft
  have hsecond := specializationCost_le_multiplicationEnvelope
    (mulAssociativityMiddleBody left) middle termBound
    ((mulAssociativityMiddleBody_code_le_stage1 left termBound hleft).trans
      (multiplicationFormulaStage1_le_envelope termBound)) hmiddle
  have hthird := specializationCost_le_multiplicationEnvelope
    (mulAssociativityInnerBody left middle) right termBound
    ((mulAssociativityInnerBody_code_le_stage2
      left middle termBound hleft hmiddle).trans
      (multiplicationFormulaStage2_le_envelope termBound)) hright
  simp only [paMultiplicationPrimitiveCostEnvelope]
  dsimp only [termBound] at *
  unfold fixedMultiplicationAxiomPayloadEnvelope at haxiom ⊢
  omega

/-! ## Uniform local cost and base branches -/

def paMultiplicationLocalCostEnvelope (inputWidth : Nat) : Nat :=
  4096 *
    (paMultiplicationPrimitiveCostEnvelope inputWidth +
      binaryNumeralAdditionPayloadPolynomial
        (paMultiplicationWorkWidth inputWidth) +
      paBinaryOneBaseCostEnvelope
        (paMultiplicationWorkWidth inputWidth) + 1)

theorem paMultiplicationPrimitive_le_local (inputWidth : Nat) :
    paMultiplicationPrimitiveCostEnvelope inputWidth <=
      paMultiplicationLocalCostEnvelope inputWidth := by
  unfold paMultiplicationLocalCostEnvelope
  omega

theorem additionPolynomial_le_multiplicationLocal (inputWidth : Nat) :
    binaryNumeralAdditionPayloadPolynomial
        (paMultiplicationWorkWidth inputWidth) <=
      paMultiplicationLocalCostEnvelope inputWidth := by
  unfold paMultiplicationLocalCostEnvelope
  omega

theorem binaryOneCost_le_multiplicationLocal (inputWidth : Nat) :
    paBinaryOneBaseCostEnvelope
        (paMultiplicationWorkWidth inputWidth) <=
      paMultiplicationLocalCostEnvelope inputWidth := by
  unfold paMultiplicationLocalCostEnvelope
  omega

theorem multiplicationGeneratedTerm_code_length_le
    {inputWidth budget : Nat}
    {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    (hterm : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) budget term)
    (hbudget : budget <= 64) :
    (binaryTermCode term).length <=
      paMultiplicationTermCodeEnvelope inputWidth := by
  unfold paMultiplicationTermCodeEnvelope
  exact generatedTerm_code_length_le_compiler hterm hbudget

theorem proveZeroMul_payloadLength_le_local
    {inputWidth budget : Nat}
    {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    (hterm : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) budget term)
    (hbudget : budget <= 32) :
    (proveZeroMul term).payloadLength <=
      paMultiplicationLocalCostEnvelope inputWidth := by
  let source := paMulTerm paZeroTerm term
  let middle := paMulTerm term paZeroTerm
  have hzero : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 paZeroTerm := .zero
  have hsource : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) (1 + budget + 1) source :=
    .mul hzero hterm
  have hmiddle : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) (budget + 1 + 1) middle :=
    .mul hterm hzero
  have htermCode := multiplicationGeneratedTerm_code_length_le
    hterm (by omega)
  have hzeroCode := multiplicationGeneratedTerm_code_length_le
    hzero (by omega)
  have hsourceCode := multiplicationGeneratedTerm_code_length_le
    hsource (by omega)
  have hmiddleCode := multiplicationGeneratedTerm_code_length_le
    hmiddle (by omega)
  have hcomm := proveMulCommutativity_payloadLength_le_primitive
    paZeroTerm term inputWidth hzeroCode htermCode
  have hmulZeroRaw :=
    proveMulZeroAtPaZero_payloadLength_le_primitive
      term (paMultiplicationTermCodeEnvelope inputWidth) htermCode
  have hmulZero : (proveMulZeroAtPaZero term).payloadLength <=
      paMultiplicationPrimitiveCostEnvelope inputWidth :=
    hmulZeroRaw.trans (paPrimitiveCost_le_multiplicationPrimitive inputWidth)
  have htrans :=
    proveEqualityTransitivity_payloadLength_le_primitive
      source middle paZeroTerm
      (proveMulCommutativity paZeroTerm term)
      (proveMulZeroAtPaZero term)
      (paMultiplicationTermCodeEnvelope inputWidth)
      hsourceCode hmiddleCode hzeroCode
  change
    (proveEqualityTransitivity source middle paZeroTerm
      (proveMulCommutativity paZeroTerm term)
      (proveMulZeroAtPaZero term)).payloadLength <= _
  have hprimitive := paPrimitiveCost_le_multiplicationPrimitive inputWidth
  calc
    _ <= (proveMulCommutativity paZeroTerm term).payloadLength +
        (proveMulZeroAtPaZero term).payloadLength +
        paPrimitiveCostEnvelope
          (paMultiplicationTermCodeEnvelope inputWidth) := htrans
    _ <= 3 * paMultiplicationPrimitiveCostEnvelope inputWidth := by omega
    _ <= paMultiplicationLocalCostEnvelope inputWidth := by
      unfold paMultiplicationLocalCostEnvelope
      omega

theorem proveShortBinaryOneEqualsPaOne_payloadLength_le_local
    (inputWidth : Nat) :
    proveShortBinaryOneEqualsPaOne.payloadLength <=
      paMultiplicationLocalCostEnvelope inputWidth := by
  have hcast : proveShortBinaryOneEqualsPaOne.payloadLength =
      proveBinaryOneAlgebraEqualsOne.payloadLength := by
    have hformula :
        (“!!binaryOneAlgebraTerm = !!paOneTerm” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(shortBinaryNumeralTerm 1) = !!paOneTerm” :
          LO.FirstOrder.ArithmeticProposition) := by
      rw [binaryNumeralTerm_one_formula]
    change (CertifiedPAProof.cast hformula
      proveBinaryOneAlgebraEqualsOne).payloadLength = _
    exact cast_payloadLength _ _
  rw [hcast]
  exact (proveBinaryOneAlgebraEqualsOne_payloadLength_le_incrementLocal
    (paMultiplicationWorkWidth inputWidth)).trans
      (binaryOneCost_le_multiplicationLocal inputWidth)

theorem proveBinaryNumeralMultiplicationZeroLeft_payloadLength_le
    (right inputWidth : Nat)
    (hright : Nat.size right <= paMultiplicationWorkWidth inputWidth) :
    (proveBinaryNumeralMultiplicationZeroLeft right).payloadLength <=
      paMultiplicationLocalCostEnvelope inputWidth := by
  let rightTerm := shortBinaryNumeralTerm right
  have hrightTerm : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 rightTerm :=
    .numeral right hright
  have hraw := proveZeroMul_payloadLength_le_local
    (inputWidth := inputWidth) hrightTerm (by omega)
  have hcast :
      (proveBinaryNumeralMultiplicationZeroLeft right).payloadLength =
        (proveZeroMul rightTerm).payloadLength := by
    change (CertifiedPAProof.cast _ (proveZeroMul rightTerm)).payloadLength = _
    exact cast_payloadLength _ _
  rw [hcast]
  exact hraw

theorem proveBinaryNumeralMultiplicationZeroRight_payloadLength_le
    (left inputWidth : Nat)
    (hleft : Nat.size left <= paMultiplicationWorkWidth inputWidth) :
    (proveBinaryNumeralMultiplicationZeroRight left).payloadLength <=
      paMultiplicationLocalCostEnvelope inputWidth := by
  let leftTerm := shortBinaryNumeralTerm left
  have hleftTerm : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 leftTerm :=
    .numeral left hleft
  have hleftCode := multiplicationGeneratedTerm_code_length_le
    hleftTerm (by omega)
  have hraw :=
    proveMulZeroAtPaZero_payloadLength_le_primitive
      leftTerm (paMultiplicationTermCodeEnvelope inputWidth) hleftCode
  have hcast :
      (proveBinaryNumeralMultiplicationZeroRight left).payloadLength =
        (proveMulZeroAtPaZero leftTerm).payloadLength := by
    have hformula :
        (“!!(paMulTerm leftTerm paZeroTerm) = !!paZeroTerm” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paMulTerm (shortBinaryNumeralTerm left)
            (shortBinaryNumeralTerm 0)) =
          !!(shortBinaryNumeralTerm (left * 0))” :
          LO.FirstOrder.ArithmeticProposition) := by
      simp [leftTerm, paZeroTerm,
        FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero]
    change (CertifiedPAProof.cast hformula
      (proveMulZeroAtPaZero leftTerm)).payloadLength = _
    exact cast_payloadLength _ _
  rw [hcast]
  exact (hraw.trans
    (paPrimitiveCost_le_multiplicationPrimitive inputWidth)).trans
      (paMultiplicationPrimitive_le_local inputWidth)

theorem proveBinaryNumeralMultiplicationOneRight_payloadLength_le
    (left inputWidth : Nat)
    (hleft : Nat.size left <= paMultiplicationWorkWidth inputWidth) :
    (proveBinaryNumeralMultiplicationOneRight left).payloadLength <=
      8 * paMultiplicationLocalCostEnvelope inputWidth := by
  let leftTerm := shortBinaryNumeralTerm left
  let source := paMulTerm leftTerm (shortBinaryNumeralTerm 1)
  let middle := paMulTerm leftTerm paOneTerm
  let rewriteRightRaw := proveMulCongruence
    leftTerm (shortBinaryNumeralTerm 1) leftTerm paOneTerm
    (proveEqualityReflexivityAtTerm leftTerm)
    proveShortBinaryOneEqualsPaOne
  let rewriteRight : CertifiedPAProof
      (“!!source = !!middle” : LO.FirstOrder.ArithmeticProposition) := by
    have hformula := mulEqualityAsTerm_formula
      leftTerm (shortBinaryNumeralTerm 1) leftTerm paOneTerm
    simpa [source, middle] using
      (CertifiedPAProof.cast hformula rewriteRightRaw)
  let collapseOne := proveMulOneAtPaOne leftTerm
  let through := proveEqualityTransitivity source middle leftTerm
    rewriteRight collapseOne
  have hleftTerm : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 leftTerm :=
    .numeral left hleft
  have honeNumeral : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1
      (shortBinaryNumeralTerm 1) := .numeral 1 (by
        unfold paMultiplicationWorkWidth
        simp)
  have hone : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 paOneTerm := .one
  have hsource : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 3 source :=
    .mul hleftTerm honeNumeral
  have hmiddle : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 3 middle :=
    .mul hleftTerm hone
  have hleftCode := multiplicationGeneratedTerm_code_length_le
    hleftTerm (by omega)
  have honeNumeralCode := multiplicationGeneratedTerm_code_length_le
    honeNumeral (by omega)
  have honeCode := multiplicationGeneratedTerm_code_length_le
    hone (by omega)
  have hsourceCode := multiplicationGeneratedTerm_code_length_le
    hsource (by omega)
  have hmiddleCode := multiplicationGeneratedTerm_code_length_le
    hmiddle (by omega)
  have hreflexivityRaw :=
    proveEqualityReflexivityAtTerm_payloadLength_le_primitive
      leftTerm (paMultiplicationTermCodeEnvelope inputWidth) hleftCode
  have hshortOne :=
    proveShortBinaryOneEqualsPaOne_payloadLength_le_local inputWidth
  have hrewriteRaw :=
    proveMulCongruence_payloadLength_le_primitive
      leftTerm (shortBinaryNumeralTerm 1) leftTerm paOneTerm
      (proveEqualityReflexivityAtTerm leftTerm)
      proveShortBinaryOneEqualsPaOne
      (paMultiplicationTermCodeEnvelope inputWidth)
      hleftCode honeNumeralCode hleftCode honeCode
  have hrewrite : rewriteRight.payloadLength <=
      4 * paMultiplicationLocalCostEnvelope inputWidth := by
    have hcast : rewriteRight.payloadLength = rewriteRightRaw.payloadLength := by
      dsimp only [rewriteRight]
      change (CertifiedPAProof.cast _ rewriteRightRaw).payloadLength = _
      exact cast_payloadLength _ _
    have hprimitive := paPrimitiveCost_le_multiplicationPrimitive inputWidth
    have hlocal := paMultiplicationPrimitive_le_local inputWidth
    calc
      rewriteRight.payloadLength = rewriteRightRaw.payloadLength := hcast
      _ <= (proveEqualityReflexivityAtTerm leftTerm).payloadLength +
          proveShortBinaryOneEqualsPaOne.payloadLength +
          paPrimitiveCostEnvelope
            (paMultiplicationTermCodeEnvelope inputWidth) := hrewriteRaw
      _ <= 4 * paMultiplicationLocalCostEnvelope inputWidth := by omega
  have hcollapseRaw :=
    proveMulOneAtPaOne_payloadLength_le_primitive
      leftTerm (paMultiplicationTermCodeEnvelope inputWidth) hleftCode
  have hcollapse : collapseOne.payloadLength <=
      paMultiplicationLocalCostEnvelope inputWidth := by
    dsimp only [collapseOne]
    exact (hcollapseRaw.trans
        (paPrimitiveCost_le_multiplicationPrimitive inputWidth)).trans
      (paMultiplicationPrimitive_le_local inputWidth)
  have htrans :=
    proveEqualityTransitivity_payloadLength_le_primitive
      source middle leftTerm rewriteRight collapseOne
      (paMultiplicationTermCodeEnvelope inputWidth)
      hsourceCode hmiddleCode hleftCode
  have houter :
      (proveBinaryNumeralMultiplicationOneRight left).payloadLength =
        through.payloadLength := by
    change (CertifiedPAProof.cast _ through).payloadLength = _
    exact cast_payloadLength _ _
  rw [houter]
  have hprimitive := paPrimitiveCost_le_multiplicationPrimitive inputWidth
  have hlocal := paMultiplicationPrimitive_le_local inputWidth
  dsimp only [through]
  calc
    (proveEqualityTransitivity source middle leftTerm
        rewriteRight collapseOne).payloadLength <=
        rewriteRight.payloadLength + collapseOne.payloadLength +
          paPrimitiveCostEnvelope
            (paMultiplicationTermCodeEnvelope inputWidth) := htrans
    _ <= 8 * paMultiplicationLocalCostEnvelope inputWidth := by omega

/-! ## Recursive-product doubling -/

theorem proveBinaryMultiplicationDoubleHighAlgebra_payloadLength_le
    (left high inputWidth : Nat)
    (highProof : CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm high)) =
        !!(shortBinaryNumeralTerm (left * high))” :
        LO.FirstOrder.ArithmeticProposition))
    (hwidth : Nat.size left + Nat.size high <= inputWidth) :
    (proveBinaryMultiplicationDoubleHighAlgebra
      left high highProof).payloadLength <=
      highProof.payloadLength +
        64 * paMultiplicationLocalCostEnvelope inputWidth := by
  let leftTerm := shortBinaryNumeralTerm left
  let highTerm := shortBinaryNumeralTerm high
  let productTerm := shortBinaryNumeralTerm (left * high)
  let source := paMulTerm leftTerm (paMulTerm arithmeticTwoTerm highTerm)
  let leftTwoHigh := paMulTerm
    (paMulTerm leftTerm arithmeticTwoTerm) highTerm
  let twoLeftHigh := paMulTerm
    (paMulTerm arithmeticTwoTerm leftTerm) highTerm
  let grouped := paMulTerm arithmeticTwoTerm
    (paMulTerm leftTerm highTerm)
  let result := paMulTerm arithmeticTwoTerm productTerm
  let associationReverse : CertifiedPAProof
      (“!!source = !!leftTwoHigh” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula :
        (“!!leftTerm * (!!arithmeticTwoTerm * !!highTerm) =
          (!!leftTerm * !!arithmeticTwoTerm) * !!highTerm” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!source = !!leftTwoHigh” :
          LO.FirstOrder.ArithmeticProposition) := by
      simp [source, leftTwoHigh, paMulTerm]
    exact CertifiedPAProof.cast hformula
      (proveMulAssociativityReverse
        leftTerm arithmeticTwoTerm highTerm)
  let commuteRaw := proveMulCongruence
    (paMulTerm leftTerm arithmeticTwoTerm) highTerm
    (paMulTerm arithmeticTwoTerm leftTerm) highTerm
    (proveMulCommutativity leftTerm arithmeticTwoTerm)
    (proveEqualityReflexivityAtTerm highTerm)
  let commute : CertifiedPAProof
      (“!!leftTwoHigh = !!twoLeftHigh” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := mulEqualityAsTerm_formula
      (paMulTerm leftTerm arithmeticTwoTerm) highTerm
      (paMulTerm arithmeticTwoTerm leftTerm) highTerm
    simpa [leftTwoHigh, twoLeftHigh] using
      (CertifiedPAProof.cast hformula commuteRaw)
  let association : CertifiedPAProof
      (“!!twoLeftHigh = !!grouped” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula :
        (“(!!arithmeticTwoTerm * !!leftTerm) * !!highTerm =
          !!arithmeticTwoTerm * (!!leftTerm * !!highTerm)” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!twoLeftHigh = !!grouped” :
          LO.FirstOrder.ArithmeticProposition) := by
      simp [twoLeftHigh, grouped, paMulTerm]
    exact CertifiedPAProof.cast hformula
      (proveMulAssociativity arithmeticTwoTerm leftTerm highTerm)
  let recurseRaw := proveMulCongruence
    arithmeticTwoTerm (paMulTerm leftTerm highTerm)
    arithmeticTwoTerm productTerm
    (proveEqualityReflexivityAtTerm arithmeticTwoTerm) highProof
  let recurse : CertifiedPAProof
      (“!!grouped = !!result” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := mulEqualityAsTerm_formula
      arithmeticTwoTerm (paMulTerm leftTerm highTerm)
      arithmeticTwoTerm productTerm
    simpa [grouped, result] using
      (CertifiedPAProof.cast hformula recurseRaw)
  let first := proveEqualityTransitivity source leftTwoHigh twoLeftHigh
    associationReverse commute
  let second := proveEqualityTransitivity source twoLeftHigh grouped
    first association
  let third := proveEqualityTransitivity source grouped result
    second recurse
  have hleftSize := multiplication_left_size_le_work
    left high inputWidth hwidth
  have hhighSize := multiplication_right_size_le_work
    left high inputWidth hwidth
  have hproductSize := multiplication_product_size_le_work
    left high inputWidth hwidth
  have hleftTerm : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 leftTerm :=
    .numeral left hleftSize
  have hhighTerm : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 highTerm :=
    .numeral high hhighSize
  have hproductTerm : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 productTerm :=
    .numeral (left * high) hproductSize
  have htwo : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 arithmeticTwoTerm := .two
  have htwoHigh : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 3
      (paMulTerm arithmeticTwoTerm highTerm) := .mul htwo hhighTerm
  have hleftTwo : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 3
      (paMulTerm leftTerm arithmeticTwoTerm) := .mul hleftTerm htwo
  have htwoLeft : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 3
      (paMulTerm arithmeticTwoTerm leftTerm) := .mul htwo hleftTerm
  have hleftHigh : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 3
      (paMulTerm leftTerm highTerm) := .mul hleftTerm hhighTerm
  have hsource : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 5 source :=
    .mul hleftTerm htwoHigh
  have hleftTwoHigh : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 5 leftTwoHigh :=
    .mul hleftTwo hhighTerm
  have htwoLeftHigh : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 5 twoLeftHigh :=
    .mul htwoLeft hhighTerm
  have hgrouped : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 5 grouped :=
    .mul htwo hleftHigh
  have hresult : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 3 result :=
    .mul htwo hproductTerm
  have hleftCode := multiplicationGeneratedTerm_code_length_le
    hleftTerm (by omega)
  have hhighCode := multiplicationGeneratedTerm_code_length_le
    hhighTerm (by omega)
  have hproductCode := multiplicationGeneratedTerm_code_length_le
    hproductTerm (by omega)
  have htwoCode := multiplicationGeneratedTerm_code_length_le
    htwo (by omega)
  have hleftTwoCode := multiplicationGeneratedTerm_code_length_le
    hleftTwo (by omega)
  have htwoLeftCode := multiplicationGeneratedTerm_code_length_le
    htwoLeft (by omega)
  have hleftHighCode := multiplicationGeneratedTerm_code_length_le
    hleftHigh (by omega)
  have hsourceCode := multiplicationGeneratedTerm_code_length_le
    hsource (by omega)
  have hleftTwoHighCode := multiplicationGeneratedTerm_code_length_le
    hleftTwoHigh (by omega)
  have htwoLeftHighCode := multiplicationGeneratedTerm_code_length_le
    htwoLeftHigh (by omega)
  have hgroupedCode := multiplicationGeneratedTerm_code_length_le
    hgrouped (by omega)
  have hresultCode := multiplicationGeneratedTerm_code_length_le
    hresult (by omega)
  have hassocRaw := proveMulAssociativity_payloadLength_le_primitive
    leftTerm arithmeticTwoTerm highTerm inputWidth
    hleftCode htwoCode hhighCode
  have hassocReverseRaw :=
    proveEqualitySymmetry_payloadLength_le_primitive
      leftTwoHigh source
      (proveMulAssociativity leftTerm arithmeticTwoTerm highTerm)
      (paMultiplicationTermCodeEnvelope inputWidth)
      hleftTwoHighCode hsourceCode
  have hassocReverseBase :
      (proveMulAssociativityReverse
        leftTerm arithmeticTwoTerm highTerm).payloadLength <=
        2 * paMultiplicationLocalCostEnvelope inputWidth := by
    change
      (proveEqualitySymmetry leftTwoHigh source
        (proveMulAssociativity leftTerm arithmeticTwoTerm highTerm)).payloadLength
        <= _
    have hprimitive := paPrimitiveCost_le_multiplicationPrimitive inputWidth
    have hlocal := paMultiplicationPrimitive_le_local inputWidth
    calc
      (proveEqualitySymmetry leftTwoHigh source
          (proveMulAssociativity
            leftTerm arithmeticTwoTerm highTerm)).payloadLength <=
          (proveMulAssociativity
            leftTerm arithmeticTwoTerm highTerm).payloadLength +
            paPrimitiveCostEnvelope
              (paMultiplicationTermCodeEnvelope inputWidth) :=
        hassocReverseRaw
      _ <= 2 * paMultiplicationLocalCostEnvelope inputWidth := by omega
  have hassociationReverse : associationReverse.payloadLength <=
      2 * paMultiplicationLocalCostEnvelope inputWidth := by
    have hcast : associationReverse.payloadLength =
        (proveMulAssociativityReverse
          leftTerm arithmeticTwoTerm highTerm).payloadLength := by
      dsimp only [associationReverse]
      exact cast_payloadLength _ _
    rw [hcast]
    exact hassocReverseBase
  have hcommBase := proveMulCommutativity_payloadLength_le_primitive
    leftTerm arithmeticTwoTerm inputWidth hleftCode htwoCode
  have hreflexiveHigh :=
    proveEqualityReflexivityAtTerm_payloadLength_le_primitive
      highTerm (paMultiplicationTermCodeEnvelope inputWidth) hhighCode
  have hcommuteRaw := proveMulCongruence_payloadLength_le_primitive
    (paMulTerm leftTerm arithmeticTwoTerm) highTerm
    (paMulTerm arithmeticTwoTerm leftTerm) highTerm
    (proveMulCommutativity leftTerm arithmeticTwoTerm)
    (proveEqualityReflexivityAtTerm highTerm)
    (paMultiplicationTermCodeEnvelope inputWidth)
    hleftTwoCode hhighCode htwoLeftCode hhighCode
  have hcommute : commute.payloadLength <=
      4 * paMultiplicationLocalCostEnvelope inputWidth := by
    have hcast : commute.payloadLength = commuteRaw.payloadLength := by
      dsimp only [commute]
      change (CertifiedPAProof.cast _ commuteRaw).payloadLength = _
      exact cast_payloadLength _ _
    have hprimitive := paPrimitiveCost_le_multiplicationPrimitive inputWidth
    have hlocal := paMultiplicationPrimitive_le_local inputWidth
    calc
      commute.payloadLength = commuteRaw.payloadLength := hcast
      _ <= (proveMulCommutativity
            leftTerm arithmeticTwoTerm).payloadLength +
          (proveEqualityReflexivityAtTerm highTerm).payloadLength +
          paPrimitiveCostEnvelope
            (paMultiplicationTermCodeEnvelope inputWidth) := hcommuteRaw
      _ <= 4 * paMultiplicationLocalCostEnvelope inputWidth := by omega
  have hassociationBase := proveMulAssociativity_payloadLength_le_primitive
    arithmeticTwoTerm leftTerm highTerm inputWidth
    htwoCode hleftCode hhighCode
  have hassociation : association.payloadLength <=
      paMultiplicationLocalCostEnvelope inputWidth := by
    have hcast : association.payloadLength =
        (proveMulAssociativity
          arithmeticTwoTerm leftTerm highTerm).payloadLength := by
      dsimp only [association]
      exact cast_payloadLength _ _
    rw [hcast]
    exact hassociationBase.trans
      (paMultiplicationPrimitive_le_local inputWidth)
  have hreflexiveTwo :=
    proveEqualityReflexivityAtTerm_payloadLength_le_primitive
      arithmeticTwoTerm (paMultiplicationTermCodeEnvelope inputWidth) htwoCode
  have hrecurseRaw := proveMulCongruence_payloadLength_le_primitive
    arithmeticTwoTerm (paMulTerm leftTerm highTerm)
    arithmeticTwoTerm productTerm
    (proveEqualityReflexivityAtTerm arithmeticTwoTerm) highProof
    (paMultiplicationTermCodeEnvelope inputWidth)
    htwoCode hleftHighCode htwoCode hproductCode
  have hrecurse : recurse.payloadLength <= highProof.payloadLength +
      3 * paMultiplicationLocalCostEnvelope inputWidth := by
    have hcast : recurse.payloadLength = recurseRaw.payloadLength := by
      dsimp only [recurse]
      change (CertifiedPAProof.cast _ recurseRaw).payloadLength = _
      exact cast_payloadLength _ _
    have hprimitive := paPrimitiveCost_le_multiplicationPrimitive inputWidth
    have hlocal := paMultiplicationPrimitive_le_local inputWidth
    calc
      recurse.payloadLength = recurseRaw.payloadLength := hcast
      _ <= (proveEqualityReflexivityAtTerm arithmeticTwoTerm).payloadLength +
          highProof.payloadLength +
          paPrimitiveCostEnvelope
            (paMultiplicationTermCodeEnvelope inputWidth) := hrecurseRaw
      _ <= highProof.payloadLength +
          3 * paMultiplicationLocalCostEnvelope inputWidth := by omega
  have hfirst := proveEqualityTransitivity_payloadLength_le_primitive
    source leftTwoHigh twoLeftHigh associationReverse commute
    (paMultiplicationTermCodeEnvelope inputWidth)
    hsourceCode hleftTwoHighCode htwoLeftHighCode
  have hsecond := proveEqualityTransitivity_payloadLength_le_primitive
    source twoLeftHigh grouped first association
    (paMultiplicationTermCodeEnvelope inputWidth)
    hsourceCode htwoLeftHighCode hgroupedCode
  have hthird := proveEqualityTransitivity_payloadLength_le_primitive
    source grouped result second recurse
      (paMultiplicationTermCodeEnvelope inputWidth)
      hsourceCode hgroupedCode hresultCode
  have hfirstBound : first.payloadLength <=
      associationReverse.payloadLength + commute.payloadLength +
        paPrimitiveCostEnvelope
          (paMultiplicationTermCodeEnvelope inputWidth) := by
    dsimp only [first]
    exact hfirst
  have hsecondBound : second.payloadLength <=
      first.payloadLength + association.payloadLength +
        paPrimitiveCostEnvelope
          (paMultiplicationTermCodeEnvelope inputWidth) := by
    dsimp only [second]
    exact hsecond
  have hthirdBound : third.payloadLength <=
      second.payloadLength + recurse.payloadLength +
        paPrimitiveCostEnvelope
          (paMultiplicationTermCodeEnvelope inputWidth) := by
    dsimp only [third]
    exact hthird
  have houter :
      (proveBinaryMultiplicationDoubleHighAlgebra
        left high highProof).payloadLength = third.payloadLength := by
    have hformula :
        (“!!source = !!result” : LO.FirstOrder.ArithmeticProposition) =
        (“!!(paMulTerm (shortBinaryNumeralTerm left)
            (paMulTerm arithmeticTwoTerm
              (shortBinaryNumeralTerm high))) =
          !!(paMulTerm arithmeticTwoTerm
            (shortBinaryNumeralTerm (left * high)))” :
          LO.FirstOrder.ArithmeticProposition) := by
      simp [source, result, leftTerm, highTerm, productTerm]
    change (CertifiedPAProof.cast hformula third).payloadLength = _
    exact cast_payloadLength _ _
  have hprimitive := paPrimitiveCost_le_multiplicationPrimitive inputWidth
  have hlocal := paMultiplicationPrimitive_le_local inputWidth
  have hfirstLocal : first.payloadLength <=
      8 * paMultiplicationLocalCostEnvelope inputWidth := by omega
  have hsecondLocal : second.payloadLength <=
      12 * paMultiplicationLocalCostEnvelope inputWidth := by omega
  have hthirdLocal : third.payloadLength <= highProof.payloadLength +
      20 * paMultiplicationLocalCostEnvelope inputWidth := by omega
  rw [houter]
  exact hthirdLocal.trans (by omega)

/-! ## Odd-bit algebra -/

theorem proveBinaryMultiplicationOddAlgebra_payloadLength_le
    (left high inputWidth : Nat)
    (highProof : CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm high)) =
        !!(shortBinaryNumeralTerm (left * high))” :
        LO.FirstOrder.ArithmeticProposition))
    (hwidth : Nat.size left + Nat.size high <= inputWidth) :
    (proveBinaryMultiplicationOddAlgebra left high highProof).payloadLength <=
      highProof.payloadLength +
        128 * paMultiplicationLocalCostEnvelope inputWidth := by
  let leftTerm := shortBinaryNumeralTerm left
  let highTerm := shortBinaryNumeralTerm high
  let productTerm := shortBinaryNumeralTerm (left * high)
  let doubleHigh := paMulTerm arithmeticTwoTerm highTerm
  let source := paMulTerm leftTerm (paAddTerm doubleHigh paOneTerm)
  let distributed := paAddTerm
    (paMulTerm leftTerm doubleHigh) (paMulTerm leftTerm paOneTerm)
  let doubledProduct := paMulTerm arithmeticTwoTerm productTerm
  let result := paAddTerm doubledProduct leftTerm
  let distributionRaw :=
    proveLeftDistributivity leftTerm doubleHigh paOneTerm
  let distribution : CertifiedPAProof
      (“!!source = !!distributed” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula :
        (“!!leftTerm * (!!doubleHigh + !!paOneTerm) =
          !!leftTerm * !!doubleHigh + !!leftTerm * !!paOneTerm” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!source = !!distributed” :
          LO.FirstOrder.ArithmeticProposition) := by
      simp [source, distributed, paAddTerm, paMulTerm]
    exact CertifiedPAProof.cast hformula distributionRaw
  let doubled :=
    proveBinaryMultiplicationDoubleHighAlgebra left high highProof
  let collapseOne := proveMulOneAtPaOne leftTerm
  let normalizeRaw := proveAddCongruence
    (paMulTerm leftTerm doubleHigh) (paMulTerm leftTerm paOneTerm)
    doubledProduct leftTerm doubled collapseOne
  let normalize : CertifiedPAProof
      (“!!distributed = !!result” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      (paMulTerm leftTerm doubleHigh) (paMulTerm leftTerm paOneTerm)
      doubledProduct leftTerm
    simpa [distributed, result] using
      (CertifiedPAProof.cast hformula normalizeRaw)
  let through := proveEqualityTransitivity source distributed result
    distribution normalize
  have hleftSize := multiplication_left_size_le_work
    left high inputWidth hwidth
  have hhighSize := multiplication_right_size_le_work
    left high inputWidth hwidth
  have hproductSize := multiplication_product_size_le_work
    left high inputWidth hwidth
  have hleftTerm : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 leftTerm :=
    .numeral left hleftSize
  have hhighTerm : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 highTerm :=
    .numeral high hhighSize
  have hproductTerm : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 productTerm :=
    .numeral (left * high) hproductSize
  have htwo : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 arithmeticTwoTerm := .two
  have hone : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 paOneTerm := .one
  have hdoubleHigh : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 3 doubleHigh :=
    .mul htwo hhighTerm
  have hdoubleHighPlusOne : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 5
      (paAddTerm doubleHigh paOneTerm) := .add hdoubleHigh hone
  have hsource : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 7 source :=
    .mul hleftTerm hdoubleHighPlusOne
  have hleftDouble : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 5
      (paMulTerm leftTerm doubleHigh) := .mul hleftTerm hdoubleHigh
  have hleftOne : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 3
      (paMulTerm leftTerm paOneTerm) := .mul hleftTerm hone
  have hdistributed : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 9 distributed :=
    .add hleftDouble hleftOne
  have hdoubledProduct : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 3 doubledProduct :=
    .mul htwo hproductTerm
  have hresult : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 5 result :=
    .add hdoubledProduct hleftTerm
  have hleftCode := multiplicationGeneratedTerm_code_length_le
    hleftTerm (by omega)
  have hhighCode := multiplicationGeneratedTerm_code_length_le
    hhighTerm (by omega)
  have htwoCode := multiplicationGeneratedTerm_code_length_le
    htwo (by omega)
  have honeCode := multiplicationGeneratedTerm_code_length_le
    hone (by omega)
  have hdoubleHighCode := multiplicationGeneratedTerm_code_length_le
    hdoubleHigh (by omega)
  have hsourceCode := multiplicationGeneratedTerm_code_length_le
    hsource (by omega)
  have hleftDoubleCode := multiplicationGeneratedTerm_code_length_le
    hleftDouble (by omega)
  have hleftOneCode := multiplicationGeneratedTerm_code_length_le
    hleftOne (by omega)
  have hdistributedCode := multiplicationGeneratedTerm_code_length_le
    hdistributed (by omega)
  have hdoubledProductCode := multiplicationGeneratedTerm_code_length_le
    hdoubledProduct (by omega)
  have hresultCode := multiplicationGeneratedTerm_code_length_le
    hresult (by omega)
  have hdistributionRaw :=
    proveLeftDistributivity_payloadLength_le_primitive
      leftTerm doubleHigh paOneTerm
      (paMultiplicationTermCodeEnvelope inputWidth)
      hleftCode hdoubleHighCode honeCode
  have hdistribution : distribution.payloadLength <=
      paMultiplicationLocalCostEnvelope inputWidth := by
    have hcast : distribution.payloadLength = distributionRaw.payloadLength := by
      dsimp only [distribution]
      exact cast_payloadLength _ _
    rw [hcast]
    exact (hdistributionRaw.trans
      (paPrimitiveCost_le_multiplicationPrimitive inputWidth)).trans
        (paMultiplicationPrimitive_le_local inputWidth)
  have hdoubled :=
    proveBinaryMultiplicationDoubleHighAlgebra_payloadLength_le
      left high inputWidth highProof hwidth
  have hdoubledLocal : doubled.payloadLength <= highProof.payloadLength +
      64 * paMultiplicationLocalCostEnvelope inputWidth := by
    dsimp only [doubled]
    exact hdoubled
  have hcollapseRaw := proveMulOneAtPaOne_payloadLength_le_primitive
    leftTerm (paMultiplicationTermCodeEnvelope inputWidth) hleftCode
  have hcollapse : collapseOne.payloadLength <=
      paMultiplicationLocalCostEnvelope inputWidth := by
    dsimp only [collapseOne]
    exact (hcollapseRaw.trans
      (paPrimitiveCost_le_multiplicationPrimitive inputWidth)).trans
        (paMultiplicationPrimitive_le_local inputWidth)
  have hnormalizeRaw := proveAddCongruence_payloadLength_le_primitive
    (paMulTerm leftTerm doubleHigh) (paMulTerm leftTerm paOneTerm)
    doubledProduct leftTerm doubled collapseOne
    (paMultiplicationTermCodeEnvelope inputWidth)
    hleftDoubleCode hleftOneCode hdoubledProductCode hleftCode
  have hnormalize : normalize.payloadLength <= highProof.payloadLength +
      68 * paMultiplicationLocalCostEnvelope inputWidth := by
    have hcast : normalize.payloadLength = normalizeRaw.payloadLength := by
      dsimp only [normalize]
      change (CertifiedPAProof.cast _ normalizeRaw).payloadLength = _
      exact cast_payloadLength _ _
    have hprimitive := paPrimitiveCost_le_multiplicationPrimitive inputWidth
    have hlocal := paMultiplicationPrimitive_le_local inputWidth
    calc
      normalize.payloadLength = normalizeRaw.payloadLength := hcast
      _ <= doubled.payloadLength + collapseOne.payloadLength +
          paPrimitiveCostEnvelope
            (paMultiplicationTermCodeEnvelope inputWidth) := hnormalizeRaw
      _ <= highProof.payloadLength +
          68 * paMultiplicationLocalCostEnvelope inputWidth := by omega
  have hthrough := proveEqualityTransitivity_payloadLength_le_primitive
    source distributed result distribution normalize
    (paMultiplicationTermCodeEnvelope inputWidth)
    hsourceCode hdistributedCode hresultCode
  have houter :
      (proveBinaryMultiplicationOddAlgebra
        left high highProof).payloadLength = through.payloadLength := by
    have hformula :
        (“!!source = !!result” : LO.FirstOrder.ArithmeticProposition) =
        (“!!(paMulTerm (shortBinaryNumeralTerm left)
            (paAddTerm
              (paMulTerm arithmeticTwoTerm
                (shortBinaryNumeralTerm high)) paOneTerm)) =
          !!(paAddTerm
            (paMulTerm arithmeticTwoTerm
              (shortBinaryNumeralTerm (left * high)))
            (shortBinaryNumeralTerm left))” :
          LO.FirstOrder.ArithmeticProposition) := by
      simp [source, result, leftTerm, highTerm, productTerm,
        doubleHigh, doubledProduct]
    change (CertifiedPAProof.cast hformula through).payloadLength = _
    exact cast_payloadLength _ _
  rw [houter]
  have hprimitive := paPrimitiveCost_le_multiplicationPrimitive inputWidth
  have hlocal := paMultiplicationPrimitive_le_local inputWidth
  dsimp only [through]
  calc
    (proveEqualityTransitivity source distributed result
        distribution normalize).payloadLength <=
        distribution.payloadLength + normalize.payloadLength +
          paPrimitiveCostEnvelope
            (paMultiplicationTermCodeEnvelope inputWidth) := hthrough
    _ <= highProof.payloadLength +
        128 * paMultiplicationLocalCostEnvelope inputWidth := by omega

/-! ## Certified even and odd branches -/

theorem proveBinaryNumeralAddition_payloadLength_le_multiplicationWork
    (first second inputWidth : Nat)
    (hwidth : Nat.size first + Nat.size second <=
      paMultiplicationWorkWidth inputWidth) :
    (proveBinaryNumeralAddition first second).payloadLength <=
      binaryNumeralAdditionPayloadPolynomial
        (paMultiplicationWorkWidth inputWidth) := by
  have hproof := proveBinaryNumeralAddition_payloadLength_le_external
    first second (paMultiplicationWorkWidth inputWidth) hwidth
  unfold binaryNumeralAdditionPayloadPolynomial
  exact hproof.trans (Nat.mul_le_mul_right
    (paAdditionLocalCostEnvelope
      (paMultiplicationWorkWidth inputWidth))
    (Nat.add_le_add_right
      ((Nat.le_add_right (Nat.size first) (Nat.size second)).trans hwidth) 1))

theorem doubled_product_plus_left_width
    (left high inputWidth : Nat)
    (hleft : left ≠ 0) (hhigh : high ≠ 0)
    (hwidth : Nat.size left + Nat.size high <= inputWidth) :
    Nat.size (Nat.bit false (left * high)) + Nat.size left <=
      paMultiplicationWorkWidth inputWidth := by
  have hproduct : left * high ≠ 0 := Nat.mul_ne_zero hleft hhigh
  have hbit : Nat.bit false (left * high) ≠ 0 :=
    Nat.bit_ne_zero_iff.mpr (fun hz => (hproduct hz).elim)
  have hbitSize := Nat.size_bit hbit
  have hproductSize := natSize_mul_le left high
  rw [hbitSize]
  unfold paMultiplicationWorkWidth
  omega

theorem proveBinaryNumeralMultiplicationEven_payloadLength_le
    (left high inputWidth : Nat)
    (hleft : left ≠ 0) (hhigh : high ≠ 0)
    (highProof : CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm high)) =
        !!(shortBinaryNumeralTerm (left * high))” :
        LO.FirstOrder.ArithmeticProposition))
    (hwidth : Nat.size left + Nat.size high <= inputWidth) :
    (proveBinaryNumeralMultiplicationEven
      left high hleft hhigh highProof).payloadLength <=
      highProof.payloadLength +
        64 * paMultiplicationLocalCostEnvelope inputWidth := by
  have hproduct : left * high ≠ 0 := Nat.mul_ne_zero hleft hhigh
  let algebra :=
    proveBinaryMultiplicationDoubleHighAlgebra left high highProof
  have hformula :
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (paMulTerm arithmeticTwoTerm
            (shortBinaryNumeralTerm high))) =
        !!(paMulTerm arithmeticTwoTerm
          (shortBinaryNumeralTerm (left * high)))” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paMulTerm (shortBinaryNumeralTerm left)
            (shortBinaryNumeralTerm (Nat.bit false high))) =
          !!(shortBinaryNumeralTerm
            (left * Nat.bit false high))” :
          LO.FirstOrder.ArithmeticProposition) := by
    rw [shortBinaryNumeralTerm_bit_false high hhigh,
      nat_mul_bit_false,
      shortBinaryNumeralTerm_bit_false (left * high) hproduct]
  have hcast :
      (proveBinaryNumeralMultiplicationEven
        left high hleft hhigh highProof).payloadLength =
        algebra.payloadLength := by
    change (CertifiedPAProof.cast hformula algebra).payloadLength = _
    exact cast_payloadLength _ _
  rw [hcast]
  dsimp only [algebra]
  exact proveBinaryMultiplicationDoubleHighAlgebra_payloadLength_le
    left high inputWidth highProof hwidth

theorem proveBinaryNumeralMultiplicationOdd_payloadLength_le
    (left high inputWidth : Nat)
    (hleft : left ≠ 0) (hhigh : high ≠ 0)
    (highProof : CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm high)) =
        !!(shortBinaryNumeralTerm (left * high))” :
        LO.FirstOrder.ArithmeticProposition))
    (hwidth : Nat.size left + Nat.size high <= inputWidth) :
    (proveBinaryNumeralMultiplicationOdd
      left high hleft hhigh highProof).payloadLength <=
      highProof.payloadLength +
        256 * paMultiplicationLocalCostEnvelope inputWidth := by
  have hproduct : left * high ≠ 0 := Nat.mul_ne_zero hleft hhigh
  let doubledProductValue := Nat.bit false (left * high)
  let algebra := proveBinaryMultiplicationOddAlgebra left high highProof
  let additionRaw := proveBinaryNumeralAddition doubledProductValue left
  let addition : CertifiedPAProof
      (“!!(paAddTerm
          (paMulTerm arithmeticTwoTerm
            (shortBinaryNumeralTerm (left * high)))
          (shortBinaryNumeralTerm left)) =
        !!(shortBinaryNumeralTerm (doubledProductValue + left))” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula :
        (“!!(paAddTerm (shortBinaryNumeralTerm doubledProductValue)
            (shortBinaryNumeralTerm left)) =
          !!(shortBinaryNumeralTerm (doubledProductValue + left))” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paAddTerm
            (paMulTerm arithmeticTwoTerm
              (shortBinaryNumeralTerm (left * high)))
            (shortBinaryNumeralTerm left)) =
          !!(shortBinaryNumeralTerm (doubledProductValue + left))” :
          LO.FirstOrder.ArithmeticProposition) := by
      simp only [doubledProductValue]
      rw [shortBinaryNumeralTerm_bit_false (left * high) hproduct]
    exact CertifiedPAProof.cast hformula additionRaw
  let middle := paAddTerm
    (paMulTerm arithmeticTwoTerm
      (shortBinaryNumeralTerm (left * high)))
    (shortBinaryNumeralTerm left)
  let through := proveEqualityTransitivity
    (paMulTerm (shortBinaryNumeralTerm left)
      (paAddTerm
        (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high))
        paOneTerm))
    middle
    (shortBinaryNumeralTerm (doubledProductValue + left))
    algebra addition
  have hleftSize := multiplication_left_size_le_work
    left high inputWidth hwidth
  have hhighSize := multiplication_right_size_le_work
    left high inputWidth hwidth
  have hproductSize := multiplication_product_size_le_work
    left high inputWidth hwidth
  have hdoubledWidth := doubled_product_plus_left_width
    left high inputWidth hleft hhigh hwidth
  have hbit : Nat.bit false (left * high) ≠ 0 :=
    Nat.bit_ne_zero_iff.mpr (fun hz => (hproduct hz).elim)
  have hbitSize := Nat.size_bit hbit
  have hfinalSizeRaw := natSize_add_le doubledProductValue left
  have hfinalSize : Nat.size (doubledProductValue + left) <=
      paMultiplicationWorkWidth inputWidth := by
    dsimp only [doubledProductValue] at hfinalSizeRaw ⊢
    rw [hbitSize] at hfinalSizeRaw
    have hproductRaw := natSize_mul_le left high
    unfold paMultiplicationWorkWidth
    omega
  have hleftTerm : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1
      (shortBinaryNumeralTerm left) := .numeral left hleftSize
  have hhighTerm : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1
      (shortBinaryNumeralTerm high) := .numeral high hhighSize
  have hproductTerm : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1
      (shortBinaryNumeralTerm (left * high)) :=
    .numeral (left * high) hproductSize
  have hfinalTerm : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1
      (shortBinaryNumeralTerm (doubledProductValue + left)) :=
    .numeral (doubledProductValue + left) hfinalSize
  have htwo : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 arithmeticTwoTerm := .two
  have hone : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 1 paOneTerm := .one
  have hdoubleHigh : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 3
      (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high)) :=
    .mul htwo hhighTerm
  have hrightAlgebra : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 5
      (paAddTerm
        (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high))
        paOneTerm) := .add hdoubleHigh hone
  have hsource : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 7
      (paMulTerm (shortBinaryNumeralTerm left)
        (paAddTerm
          (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high))
          paOneTerm)) := .mul hleftTerm hrightAlgebra
  have hdoubledProduct : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 3
      (paMulTerm arithmeticTwoTerm
        (shortBinaryNumeralTerm (left * high))) :=
    .mul htwo hproductTerm
  have hmiddle : PACompilerGeneratedTerm
      (paMultiplicationWorkWidth inputWidth) 5 middle :=
    .add hdoubledProduct hleftTerm
  have hsourceCode := multiplicationGeneratedTerm_code_length_le
    hsource (by omega)
  have hmiddleCode := multiplicationGeneratedTerm_code_length_le
    hmiddle (by omega)
  have hfinalCode := multiplicationGeneratedTerm_code_length_le
    hfinalTerm (by omega)
  have halgebraRaw :=
    proveBinaryMultiplicationOddAlgebra_payloadLength_le
      left high inputWidth highProof hwidth
  have halgebra : algebra.payloadLength <= highProof.payloadLength +
      128 * paMultiplicationLocalCostEnvelope inputWidth := by
    dsimp only [algebra]
    exact halgebraRaw
  have hadditionRaw :=
    proveBinaryNumeralAddition_payloadLength_le_multiplicationWork
      doubledProductValue left inputWidth hdoubledWidth
  have haddition : addition.payloadLength <=
      paMultiplicationLocalCostEnvelope inputWidth := by
    have hcast : addition.payloadLength = additionRaw.payloadLength := by
      dsimp only [addition]
      exact cast_payloadLength _ _
    rw [hcast]
    exact hadditionRaw.trans
      (additionPolynomial_le_multiplicationLocal inputWidth)
  have htrans := proveEqualityTransitivity_payloadLength_le_primitive
    (paMulTerm (shortBinaryNumeralTerm left)
      (paAddTerm
        (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high))
        paOneTerm))
    middle (shortBinaryNumeralTerm (doubledProductValue + left))
    algebra addition (paMultiplicationTermCodeEnvelope inputWidth)
    hsourceCode hmiddleCode hfinalCode
  have hformula :
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (paAddTerm
            (paMulTerm arithmeticTwoTerm
              (shortBinaryNumeralTerm high)) paOneTerm)) =
        !!(shortBinaryNumeralTerm (doubledProductValue + left))” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paMulTerm (shortBinaryNumeralTerm left)
            (shortBinaryNumeralTerm (Nat.bit true high))) =
          !!(shortBinaryNumeralTerm
            (left * Nat.bit true high))” :
          LO.FirstOrder.ArithmeticProposition) := by
    rw [shortBinaryNumeralTerm_bit_true high, nat_mul_bit_true]
  have houter :
      (proveBinaryNumeralMultiplicationOdd
        left high hleft hhigh highProof).payloadLength = through.payloadLength := by
    change (CertifiedPAProof.cast hformula through).payloadLength = _
    exact cast_payloadLength _ _
  rw [houter]
  have hprimitive := paPrimitiveCost_le_multiplicationPrimitive inputWidth
  have hlocal := paMultiplicationPrimitive_le_local inputWidth
  dsimp only [through]
  calc
    (proveEqualityTransitivity
        (paMulTerm (shortBinaryNumeralTerm left)
          (paAddTerm
            (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high))
            paOneTerm))
        middle (shortBinaryNumeralTerm (doubledProductValue + left))
        algebra addition).payloadLength <=
        algebra.payloadLength + addition.payloadLength +
          paPrimitiveCostEnvelope
            (paMultiplicationTermCodeEnvelope inputWidth) := htrans
    _ <= highProof.payloadLength +
        256 * paMultiplicationLocalCostEnvelope inputWidth := by omega

/-! ## Bit step, recursion, and public polynomial endpoint -/

def paMultiplicationStepCostEnvelope (inputWidth : Nat) : Nat :=
  256 * paMultiplicationLocalCostEnvelope inputWidth

theorem proveBinaryNumeralMultiplicationBitStep_payloadLength_le
    (left : Nat) (rightBit : Bool) (rightHigh inputWidth : Nat)
    (hrightCanonical : rightHigh = 0 → rightBit = true)
    (highProof : CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(shortBinaryNumeralTerm (left * rightHigh))” :
        LO.FirstOrder.ArithmeticProposition))
    (hwidth : Nat.size left + Nat.size rightHigh <= inputWidth) :
    (proveBinaryNumeralMultiplicationBitStep
      left rightBit rightHigh hrightCanonical highProof).payloadLength <=
      highProof.payloadLength +
        paMultiplicationStepCostEnvelope inputWidth := by
  by_cases hleft : left = 0
  · subst left
    have hrightNonzero : Nat.bit rightBit rightHigh ≠ 0 :=
      Nat.bit_ne_zero_iff.mpr hrightCanonical
    have hrightSizeEq := Nat.size_bit hrightNonzero
    have hrightSize : Nat.size (Nat.bit rightBit rightHigh) <=
        paMultiplicationWorkWidth inputWidth := by
      rw [hrightSizeEq]
      unfold paMultiplicationWorkWidth
      omega
    rw [proveBinaryNumeralMultiplicationBitStep_left_zero]
    have hbase :=
      proveBinaryNumeralMultiplicationZeroLeft_payloadLength_le
        (Nat.bit rightBit rightHigh) inputWidth hrightSize
    unfold paMultiplicationStepCostEnvelope
    omega
  · cases rightBit with
    | false =>
        have hhigh : rightHigh ≠ 0 := by
          intro hz
          exact Bool.false_eq_true.mp (hrightCanonical hz)
        rw [proveBinaryNumeralMultiplicationBitStep_false
          left rightHigh hleft hrightCanonical highProof]
        have heven :=
          proveBinaryNumeralMultiplicationEven_payloadLength_le
            left rightHigh inputWidth hleft hhigh highProof hwidth
        unfold paMultiplicationStepCostEnvelope
        omega
    | true =>
        by_cases hhigh : rightHigh = 0
        · subst rightHigh
          rw [proveBinaryNumeralMultiplicationBitStep_true_zero
            left hleft hrightCanonical highProof]
          have hleftSize : Nat.size left <=
              paMultiplicationWorkWidth inputWidth := by
            unfold paMultiplicationWorkWidth
            omega
          have hone :=
            proveBinaryNumeralMultiplicationOneRight_payloadLength_le
              left inputWidth hleftSize
          calc
            (proveBinaryNumeralMultiplicationOneRight left).payloadLength <=
                8 * paMultiplicationLocalCostEnvelope inputWidth := hone
            _ <= highProof.payloadLength +
                paMultiplicationStepCostEnvelope inputWidth := by
              unfold paMultiplicationStepCostEnvelope
              omega
        · rw [proveBinaryNumeralMultiplicationBitStep_true_nonzero
            left rightHigh hleft hhigh hrightCanonical highProof]
          have hodd :=
            proveBinaryNumeralMultiplicationOdd_payloadLength_le
              left rightHigh inputWidth hleft hhigh highProof hwidth
          unfold paMultiplicationStepCostEnvelope
          omega

theorem proveBinaryNumeralMultiplication_payloadLength_le_external
    (left right inputWidth : Nat)
    (hwidth : Nat.size left + Nat.size right <= inputWidth) :
    (proveBinaryNumeralMultiplication left right).payloadLength <=
      (Nat.size right + 1) *
        paMultiplicationStepCostEnvelope inputWidth := by
  induction right using Nat.binaryRec' generalizing inputWidth with
  | zero =>
      rw [proveBinaryNumeralMultiplication_zero]
      have hleftSize : Nat.size left <=
          paMultiplicationWorkWidth inputWidth := by
        unfold paMultiplicationWorkWidth
        omega
      have hbase :=
        proveBinaryNumeralMultiplicationZeroRight_payloadLength_le
          left inputWidth hleftSize
      unfold paMultiplicationStepCostEnvelope
      simpa using hbase.trans (by omega)
  | bit rightBit rightHigh hrightCanonical ih =>
      have hrightNonzero : Nat.bit rightBit rightHigh ≠ 0 :=
        Nat.bit_ne_zero_iff.mpr hrightCanonical
      have hrightSizeEq :
          Nat.size (Nat.bit rightBit rightHigh) =
            Nat.size rightHigh + 1 := Nat.size_bit hrightNonzero
      have hhighWidth :
          Nat.size left + Nat.size rightHigh <= inputWidth := by
        omega
      have hrecursive := ih inputWidth hhighWidth
      have hstep :=
        proveBinaryNumeralMultiplicationBitStep_payloadLength_le
          left rightBit rightHigh inputWidth hrightCanonical
          (proveBinaryNumeralMultiplication left rightHigh) hhighWidth
      rw [proveBinaryNumeralMultiplication_bit
        left rightBit rightHigh hrightCanonical]
      rw [hrightSizeEq]
      calc
        (proveBinaryNumeralMultiplicationBitStep
            left rightBit rightHigh hrightCanonical
            (proveBinaryNumeralMultiplication left rightHigh)).payloadLength <=
            (proveBinaryNumeralMultiplication
              left rightHigh).payloadLength +
              paMultiplicationStepCostEnvelope inputWidth := hstep
        _ <= (Nat.size rightHigh + 1) *
              paMultiplicationStepCostEnvelope inputWidth +
              paMultiplicationStepCostEnvelope inputWidth :=
          Nat.add_le_add_right hrecursive _
        _ = (Nat.size rightHigh + 1 + 1) *
              paMultiplicationStepCostEnvelope inputWidth := by ring

def binaryNumeralMultiplicationPayloadPolynomial
    (inputWidth : Nat) : Nat :=
  (inputWidth + 1) * paMultiplicationStepCostEnvelope inputWidth

theorem proveBinaryNumeralMultiplication_payloadLength_le_polynomial
    (left right : Nat) :
    (proveBinaryNumeralMultiplication left right).payloadLength <=
      binaryNumeralMultiplicationPayloadPolynomial
        (Nat.size left + Nat.size right) := by
  let inputWidth := Nat.size left + Nat.size right
  have hproof := proveBinaryNumeralMultiplication_payloadLength_le_external
    left right inputWidth le_rfl
  unfold binaryNumeralMultiplicationPayloadPolynomial
  dsimp only [inputWidth] at hproof ⊢
  exact hproof.trans (Nat.mul_le_mul_right
    (paMultiplicationStepCostEnvelope
      (Nat.size left + Nat.size right))
    (Nat.add_le_add_right
      (Nat.le_add_left (Nat.size right) (Nat.size left)) 1))

/-- Single public endpoint for `A04.15`: checker acceptance and a fixed
polynomial payload bound in the total binary input width. -/
theorem proveBinaryNumeralMultiplication_checked_polynomial
    (left right : Nat) :
    listedCompactCertifiedPAProofVerifier
        (proveBinaryNumeralMultiplication left right).code
        (compactFormulaCode
          (“!!(paMulTerm (shortBinaryNumeralTerm left)
              (shortBinaryNumeralTerm right)) =
            !!(shortBinaryNumeralTerm (left * right))” :
            LO.FirstOrder.ArithmeticProposition)) = true ∧
      (proveBinaryNumeralMultiplication left right).payloadLength <=
        binaryNumeralMultiplicationPayloadPolynomial
          (Nat.size left + Nat.size right) := by
  exact ⟨proveBinaryNumeralMultiplication_verifier_eq_true left right,
    proveBinaryNumeralMultiplication_payloadLength_le_polynomial left right⟩

#print axioms natSize_mul_le
#print axioms proveMulCommutativity_payloadLength_le_primitive
#print axioms proveMulAssociativity_payloadLength_le_primitive
#print axioms proveBinaryMultiplicationDoubleHighAlgebra_payloadLength_le
#print axioms proveBinaryMultiplicationOddAlgebra_payloadLength_le
#print axioms proveBinaryNumeralMultiplication_payloadLength_le_polynomial
#print axioms proveBinaryNumeralMultiplication_checked_polynomial

end FoundationCompactPABinaryNumeralMultiplicationBounds
