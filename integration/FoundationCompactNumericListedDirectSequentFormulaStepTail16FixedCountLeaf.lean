import integration.FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransport
import integration.FoundationCompactPABinaryNumeralAdditionBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds
import integration.FoundationCompactPAContextCostPolynomialBounds

/-! # Direct fixed successor-count leaf 21 -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedCountLeaf

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransport

private theorem certifiedPAProof_conclusionCodeLength_le_payloadLength
    {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof formula) :
    (binaryFormulaCode formula).length <= proof.payloadLength := by
  have hformula : formula ∈ ({formula} :
      Finset LO.FirstOrder.ArithmeticProposition) := by simp
  have hsequent :=
    binaryFormulaCode_length_le_binarySequentCode_length_of_mem
      {formula} formula hformula
  have hproof := binarySequentCode_length_le_binaryProofLength proof.derivation
  have hpayload : binaryProofLength proof.derivation <= proof.payloadLength := by
    rw [CertifiedPAProof.payloadLength_eq]
    omega
  exact hsequent.trans (hproof.trans hpayload)

def compactSequentFormulaStepTail16CountBitBound
    (suffixCount valueCount : Nat) : Nat :=
  Nat.size suffixCount + Nat.size valueCount + 1

def compactSequentFormulaStepTail16CountTermCodePolynomial
    (bitBound : Nat) : Nat :=
  3 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode compactParserSyntaxExactNativeOneTerm).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 16

def compactSequentFormulaStepTail16CountCorePayloadPolynomial
    (suffixCount valueCount : Nat) : Nat :=
  let bitBound :=
    compactSequentFormulaStepTail16CountBitBound suffixCount valueCount
  let termBound :=
    compactSequentFormulaStepTail16CountTermCodePolynomial bitBound
  binaryNumeralAdditionPayloadPolynomial
      (Nat.size valueCount + Nat.size 1) +
    compactParserSyntaxExactShortOneEqualsNativeOneProof.payloadLength +
    4 * paPrimitiveCostEnvelope termBound

def compactSequentFormulaStepTail16CountDirectPayloadPolynomial
    (suffixCount valueCount : Nat) : Nat :=
  let core :=
    compactSequentFormulaStepTail16CountCorePayloadPolynomial suffixCount
      valueCount
  core + smallContextAssemblyEnvelope core

theorem exists_compactSequentFormulaStepTail16FixedCountLeaf
    (suffixCount valueCount : Nat)
    (hcount : suffixCount = valueCount + 1) :
    ∃ proof : CertifiedPAContextProof ∅
        (“!!(shortBinaryNumeralTerm suffixCount) =
          !!(shortBinaryNumeralTerm valueCount) + 1” : ValuationFormula),
      proof.payloadLength <=
        compactSequentFormulaStepTail16CountDirectPayloadPolynomial suffixCount
          valueCount := by
  let bitBound :=
    compactSequentFormulaStepTail16CountBitBound suffixCount valueCount
  let termBound :=
    compactSequentFormulaStepTail16CountTermCodePolynomial bitBound
  let valueTerm := shortBinaryNumeralTerm valueCount
  let shortOneTerm := shortBinaryNumeralTerm 1
  let nativeOneTerm := compactParserSyntaxExactNativeOneTerm
  let resultTerm := shortBinaryNumeralTerm (valueCount + 1)
  let shortSumTerm := paAddTerm valueTerm shortOneTerm
  let nativeSumTerm := paAddTerm valueTerm nativeOneTerm
  have hvalueSize : Nat.size valueCount <= bitBound := by
    unfold bitBound compactSequentFormulaStepTail16CountBitBound
    omega
  have honeSize : Nat.size 1 <= bitBound := by
    unfold bitBound compactSequentFormulaStepTail16CountBitBound
    norm_num [Nat.size]
  have hsuffixSize : Nat.size suffixCount <= bitBound := by
    unfold bitBound compactSequentFormulaStepTail16CountBitBound
    omega
  have hvalueBase : (binaryTermCode valueTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound := by
    exact binaryNumeralTerm_code_length_le_envelope valueCount bitBound
      hvalueSize
  have hshortOneBase : (binaryTermCode shortOneTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound := by
    exact binaryNumeralTerm_code_length_le_envelope 1 bitBound honeSize
  have hvalueCode : (binaryTermCode valueTerm).length <= termBound := by
    unfold valueTerm termBound
      compactSequentFormulaStepTail16CountTermCodePolynomial
    exact hvalueBase.trans (by omega)
  have hshortOneCode : (binaryTermCode shortOneTerm).length <= termBound := by
    unfold shortOneTerm termBound
      compactSequentFormulaStepTail16CountTermCodePolynomial
    exact hshortOneBase.trans (by omega)
  have hnativeOneCode :
      (binaryTermCode nativeOneTerm).length <= termBound := by
    unfold nativeOneTerm termBound
      compactSequentFormulaStepTail16CountTermCodePolynomial
    omega
  have hnativeOneExact :
      (binaryTermCode nativeOneTerm).length =
        (binaryTermCode compactParserSyntaxExactNativeOneTerm).length := by
    rfl
  have hresultCode : (binaryTermCode resultTerm).length <= termBound := by
    have hraw := binaryNumeralTerm_code_length_le_envelope suffixCount bitBound
      hsuffixSize
    have hresult : valueCount + 1 = suffixCount := hcount.symm
    unfold resultTerm
    rw [hresult]
    unfold termBound compactSequentFormulaStepTail16CountTermCodePolynomial
    omega
  have hshortSumCode :
      (binaryTermCode shortSumTerm).length <= termBound := by
    have hraw := paAddTerm_code_length_le valueTerm shortOneTerm
    unfold termBound
      compactSequentFormulaStepTail16CountTermCodePolynomial
    exact hraw.trans (by omega)
  have hnativeSumCode :
      (binaryTermCode nativeSumTerm).length <= termBound := by
    have hraw := paAddTerm_code_length_le valueTerm nativeOneTerm
    unfold termBound
      compactSequentFormulaStepTail16CountTermCodePolynomial
    exact hraw.trans (by omega)
  let additionProof := proveBinaryNumeralAddition valueCount 1
  let reverseAddition := proveEqualitySymmetry shortSumTerm resultTerm
    additionProof
  let valueReflexivity := proveEqualityReflexivityAtTerm valueTerm
  let replaceOne := proveAddCongruence valueTerm shortOneTerm valueTerm
    nativeOneTerm valueReflexivity
    compactParserSyntaxExactShortOneEqualsNativeOneProof
  let finalRaw := proveEqualityTransitivity resultTerm shortSumTerm
    nativeSumTerm reverseAddition replaceOne
  have hfinalFormula :
      (“!!resultTerm = !!nativeSumTerm” : ArithmeticProposition) =
        (“!!(shortBinaryNumeralTerm suffixCount) =
          !!(shortBinaryNumeralTerm valueCount) + 1” :
          ArithmeticProposition) := by
    subst suffixCount
    simp [resultTerm, nativeSumTerm, valueTerm, nativeOneTerm, paAddTerm,
      compactParserSyntaxExactNativeOneTerm, Semiterm.Operator.operator,
      Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]
  let finalClosed := CertifiedPAProof.cast hfinalFormula finalRaw
  let proof := CertifiedPAContextProof.weakenCertified ∅ finalClosed
  let core :=
    compactSequentFormulaStepTail16CountCorePayloadPolynomial suffixCount
      valueCount
  have haddition : additionProof.payloadLength <=
      binaryNumeralAdditionPayloadPolynomial
        (Nat.size valueCount + Nat.size 1) := by
    exact proveBinaryNumeralAddition_payloadLength_le_polynomial valueCount 1
  have hreverse := proveEqualitySymmetry_payloadLength_le_primitive
    shortSumTerm resultTerm additionProof termBound hshortSumCode hresultCode
  have hreflexivity := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
    valueTerm termBound hvalueCode
  have hreplace := proveAddCongruence_payloadLength_le_primitive valueTerm
    shortOneTerm valueTerm nativeOneTerm valueReflexivity
    compactParserSyntaxExactShortOneEqualsNativeOneProof termBound hvalueCode
    hshortOneCode hvalueCode hnativeOneCode
  have hfinal := proveEqualityTransitivity_payloadLength_le_primitive
    resultTerm shortSumTerm nativeSumTerm reverseAddition replaceOne termBound
    hresultCode hshortSumCode hnativeSumCode
  have hreverseBound : reverseAddition.payloadLength <=
      binaryNumeralAdditionPayloadPolynomial
          (Nat.size valueCount + Nat.size 1) +
        paPrimitiveCostEnvelope termBound := by
    exact hreverse.trans (Nat.add_le_add_right haddition _)
  have hreflexivityBound : valueReflexivity.payloadLength <=
      paPrimitiveCostEnvelope termBound := by
    simpa only [valueReflexivity] using hreflexivity
  have hreplace' : replaceOne.payloadLength <=
      valueReflexivity.payloadLength +
        compactParserSyntaxExactShortOneEqualsNativeOneProof.payloadLength +
        paPrimitiveCostEnvelope termBound := by
    simpa only [replaceOne] using hreplace
  have hreplaceBound : replaceOne.payloadLength <=
      compactParserSyntaxExactShortOneEqualsNativeOneProof.payloadLength +
        2 * paPrimitiveCostEnvelope termBound := by
    exact hreplace'.trans (by omega)
  have hfinal' : finalRaw.payloadLength <=
      reverseAddition.payloadLength + replaceOne.payloadLength +
        paPrimitiveCostEnvelope termBound := by
    change
      (proveEqualityTransitivity resultTerm shortSumTerm nativeSumTerm
        reverseAddition replaceOne).payloadLength <= _
    exact hfinal
  have hfinalBound : finalRaw.payloadLength <=
      binaryNumeralAdditionPayloadPolynomial
          (Nat.size valueCount + Nat.size 1) +
        compactParserSyntaxExactShortOneEqualsNativeOneProof.payloadLength +
        4 * paPrimitiveCostEnvelope termBound := by
    exact hfinal'.trans (by omega)
  have hfinalClosed : finalClosed.payloadLength <= core := by
    rw [show finalClosed.payloadLength = finalRaw.payloadLength by
      exact CertifiedPAProof.cast_payloadLength _ _]
    unfold core compactSequentFormulaStepTail16CountCorePayloadPolynomial
    dsimp only [bitBound, termBound]
    exact hfinalBound
  have hformulaCode :
      (binaryFormulaCode
        (“!!(shortBinaryNumeralTerm suffixCount) =
          !!(shortBinaryNumeralTerm valueCount) + 1” :
          ArithmeticProposition)).length <= core := by
    exact
      (certifiedPAProof_conclusionCodeLength_le_payloadLength finalClosed).trans
        hfinalClosed
  have hweakeningCost := weakeningFullAssemblyCost_le_small
    (insert
      (“!!(shortBinaryNumeralTerm suffixCount) =
        !!(shortBinaryNumeralTerm valueCount) + 1” : ArithmeticProposition)
      ∅) core (by simp) (by
        intro formula hmem
        simp at hmem
        subst formula
        exact hformulaCode)
  have hweakening :=
    CertifiedPAContextProof.weakenCertified_payloadLength_le ∅ finalClosed
  refine ⟨proof, ?_⟩
  have hproof : proof.payloadLength <=
      core + smallContextAssemblyEnvelope core := by
    calc
      proof.payloadLength <= finalClosed.payloadLength +
          weakeningFullAssemblyCost
            (insert
              (“!!(shortBinaryNumeralTerm suffixCount) =
                !!(shortBinaryNumeralTerm valueCount) + 1” :
                ArithmeticProposition) ∅) := by
        simpa only [proof, finalClosed] using hweakening
      _ <= core + smallContextAssemblyEnvelope core :=
        Nat.add_le_add hfinalClosed hweakeningCost
  unfold compactSequentFormulaStepTail16CountDirectPayloadPolynomial
  simpa only [core] using hproof

#print axioms exists_compactSequentFormulaStepTail16FixedCountLeaf

end FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedCountLeaf
