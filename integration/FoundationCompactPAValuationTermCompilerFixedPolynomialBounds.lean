import integration.FoundationCompactPAValuationTermCompilerUniformMonotoneBounds

/-!
# Fixed polynomial bounds for valuation-term compilation

The uniform valuation-term compiler is recursive in the input term.  This file
charges that recursion to the canonical term-code length.  In particular, the
binary width of a semantic value is retained as `Nat.size`; the semantic value
itself never becomes a syntax-cost coordinate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactPAValuationTermCompilerFixedPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABinaryNumeralMultiplicationBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExponentialShortNumeralCompilerBounds
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationTermCompilerUniformBounds
open FoundationCompactPAValuationTermCompilerUniformMonotoneBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds

theorem binaryTermCode_argument_length_le_zero
    {arity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ arity)
    (arguments : Fin arity -> ValuationTerm)
    (index : Fin arity) :
    (binaryTermCode (arguments index)).length <=
      (binaryTermCode
        (LO.FirstOrder.Semiterm.func functionSymbol arguments)).length := by
  have hsingle :
      (binaryTermCode (arguments index)).length <=
        Finset.univ.sum
          (fun child => (binaryTermCode (arguments child)).length) :=
    Finset.single_le_sum
      (fun child _ => Nat.zero_le
        (binaryTermCode (arguments child)).length)
      (Finset.mem_univ index)
  simp only [binaryTermCode, List.length_append]
  rw [length_flatten_ofFn]
  omega

theorem termSymbolCount_binary_function_zero
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (arguments : Fin 2 -> ValuationTerm) :
    termSymbolCount (LO.FirstOrder.Semiterm.func functionSymbol arguments) =
      1 + termSymbolCount (arguments 0) +
        termSymbolCount (arguments 1) := by
  simp [termSymbolCount,
    show (Finset.univ : Finset (Fin 2)) = {0, 1} from by
      ext index
      cases index using Fin.cases <;> simp]
  omega

def valuationTermValueWidthPolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  termCodeBound * (Nat.size numericBound + 1)

theorem valuationTermValueEnvelope_size_le_symbolCount
    (numericBound : Nat) :
    (term : ValuationTerm) ->
      Nat.size (valuationTermValueEnvelope numericBound term) <=
        termSymbolCount term * (Nat.size numericBound + 1)
  | #index => Fin.elim0 index
  | &index => by
      simp only [valuationTermValueEnvelope, termSymbolCount, one_mul]
      omega
  | .func .zero args => by
      simp [valuationTermValueEnvelope, termSymbolCount]
  | .func .one args => by
      simp [valuationTermValueEnvelope, termSymbolCount]
  | .func .add args => by
      have hraw := natSize_add_le
        (valuationTermValueEnvelope numericBound (args 0))
        (valuationTermValueEnvelope numericBound (args 1))
      have hleft := valuationTermValueEnvelope_size_le_symbolCount
        numericBound (args 0)
      have hright := valuationTermValueEnvelope_size_le_symbolCount
        numericBound (args 1)
      calc
        Nat.size (valuationTermValueEnvelope numericBound
            (.func .add args : ValuationTerm)) <=
          Nat.size (valuationTermValueEnvelope numericBound (args 0)) +
            Nat.size (valuationTermValueEnvelope numericBound (args 1)) +
            1 := by
              simpa only [valuationTermValueEnvelope] using hraw
        _ <= termSymbolCount (args 0) * (Nat.size numericBound + 1) +
            termSymbolCount (args 1) * (Nat.size numericBound + 1) +
            (Nat.size numericBound + 1) := by omega
        _ = termSymbolCount (.func .add args : ValuationTerm) *
            (Nat.size numericBound + 1) := by
              rw [termSymbolCount_binary_function_zero]
              ring
  | .func .mul args => by
      have hraw := natSize_mul_le
        (valuationTermValueEnvelope numericBound (args 0))
        (valuationTermValueEnvelope numericBound (args 1))
      have hleft := valuationTermValueEnvelope_size_le_symbolCount
        numericBound (args 0)
      have hright := valuationTermValueEnvelope_size_le_symbolCount
        numericBound (args 1)
      calc
        Nat.size (valuationTermValueEnvelope numericBound
            (.func .mul args : ValuationTerm)) <=
          Nat.size (valuationTermValueEnvelope numericBound (args 0)) +
            Nat.size (valuationTermValueEnvelope numericBound (args 1)) := by
              simpa only [valuationTermValueEnvelope] using hraw
        _ <= termSymbolCount (args 0) * (Nat.size numericBound + 1) +
            termSymbolCount (args 1) * (Nat.size numericBound + 1) :=
          Nat.add_le_add hleft hright
        _ <= (1 + termSymbolCount (args 0) + termSymbolCount (args 1)) *
            (Nat.size numericBound + 1) := by
              nlinarith
        _ = termSymbolCount (.func .mul args : ValuationTerm) *
            (Nat.size numericBound + 1) := by
              rw [termSymbolCount_binary_function_zero]

theorem valuationTermValueEnvelope_size_le_polynomial
    (numericBound termCodeBound : Nat) (term : ValuationTerm)
    (hcode : (binaryTermCode term).length <= termCodeBound) :
    Nat.size (valuationTermValueEnvelope numericBound term) <=
      valuationTermValueWidthPolynomial numericBound termCodeBound := by
  have hsize := valuationTermValueEnvelope_size_le_symbolCount
    numericBound term
  have hsymbols :=
    (termSymbolCount_le_binaryTermCode_length term).trans hcode
  unfold valuationTermValueWidthPolynomial
  exact hsize.trans (Nat.mul_le_mul_right _ hsymbols)

def valuationTermInstantiatedCodeUnit
    (numericBound termCodeBound : Nat) : Nat :=
  iteratedSuccessorTermCodePolynomial 0 numericBound + termCodeBound +
    binaryFunctionTermCodeOverhead Language.Add.add +
    binaryFunctionTermCodeOverhead Language.Mul.mul + 1

def valuationTermInstantiatedCodePolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  termCodeBound *
    valuationTermInstantiatedCodeUnit numericBound termCodeBound

theorem instantiatedValuationTermCodeEnvelope_le_symbolCount
    (numericBound termCodeBound : Nat) :
    (term : ValuationTerm) ->
      (binaryTermCode term).length <= termCodeBound ->
      instantiatedValuationTermCodeEnvelope numericBound term <=
        termSymbolCount term *
          valuationTermInstantiatedCodeUnit numericBound termCodeBound
  | #index, _ => Fin.elim0 index
  | &index, _ => by
      simp only [instantiatedValuationTermCodeEnvelope, termSymbolCount,
        one_mul]
      unfold valuationTermInstantiatedCodeUnit
      omega
  | .func .zero args, hcode => by
      simp only [instantiatedValuationTermCodeEnvelope]
      have hcount : termSymbolCount
          (.func .zero args : ValuationTerm) = 1 := by
        simp [termSymbolCount]
      rw [hcount, one_mul]
      unfold valuationTermInstantiatedCodeUnit
      omega
  | .func .one args, hcode => by
      simp only [instantiatedValuationTermCodeEnvelope]
      have hcount : termSymbolCount
          (.func .one args : ValuationTerm) = 1 := by
        simp [termSymbolCount]
      rw [hcount, one_mul]
      unfold valuationTermInstantiatedCodeUnit
      omega
  | .func .add args, hcode => by
      have hleftCode :=
        (binaryTermCode_argument_length_le_zero Language.Add.add args 0).trans
          hcode
      have hrightCode :=
        (binaryTermCode_argument_length_le_zero Language.Add.add args 1).trans
          hcode
      have hleft := instantiatedValuationTermCodeEnvelope_le_symbolCount
        numericBound termCodeBound (args 0) hleftCode
      have hright := instantiatedValuationTermCodeEnvelope_le_symbolCount
        numericBound termCodeBound (args 1) hrightCode
      let unit := valuationTermInstantiatedCodeUnit numericBound termCodeBound
      change instantiatedValuationTermCodeEnvelope numericBound (args 0) <=
        termSymbolCount (args 0) * unit at hleft
      change instantiatedValuationTermCodeEnvelope numericBound (args 1) <=
        termSymbolCount (args 1) * unit at hright
      have hoverhead : binaryFunctionTermCodeOverhead Language.Add.add <=
          unit := by
        dsimp only [unit]
        unfold valuationTermInstantiatedCodeUnit
        omega
      calc
        instantiatedValuationTermCodeEnvelope numericBound
            (.func .add args : ValuationTerm) =
          instantiatedValuationTermCodeEnvelope numericBound (args 0) +
            instantiatedValuationTermCodeEnvelope numericBound (args 1) +
            binaryFunctionTermCodeOverhead Language.Add.add := rfl
        _ <= termSymbolCount (args 0) * unit +
            termSymbolCount (args 1) * unit + unit := by omega
        _ = termSymbolCount (.func .add args : ValuationTerm) * unit := by
          rw [termSymbolCount_binary_function_zero]
          ring
  | .func .mul args, hcode => by
      have hleftCode :=
        (binaryTermCode_argument_length_le_zero Language.Mul.mul args 0).trans
          hcode
      have hrightCode :=
        (binaryTermCode_argument_length_le_zero Language.Mul.mul args 1).trans
          hcode
      have hleft := instantiatedValuationTermCodeEnvelope_le_symbolCount
        numericBound termCodeBound (args 0) hleftCode
      have hright := instantiatedValuationTermCodeEnvelope_le_symbolCount
        numericBound termCodeBound (args 1) hrightCode
      let unit := valuationTermInstantiatedCodeUnit numericBound termCodeBound
      change instantiatedValuationTermCodeEnvelope numericBound (args 0) <=
        termSymbolCount (args 0) * unit at hleft
      change instantiatedValuationTermCodeEnvelope numericBound (args 1) <=
        termSymbolCount (args 1) * unit at hright
      have hoverhead : binaryFunctionTermCodeOverhead Language.Mul.mul <=
          unit := by
        dsimp only [unit]
        unfold valuationTermInstantiatedCodeUnit
        omega
      calc
        instantiatedValuationTermCodeEnvelope numericBound
            (.func .mul args : ValuationTerm) =
          instantiatedValuationTermCodeEnvelope numericBound (args 0) +
            instantiatedValuationTermCodeEnvelope numericBound (args 1) +
            binaryFunctionTermCodeOverhead Language.Mul.mul := rfl
        _ <= termSymbolCount (args 0) * unit +
            termSymbolCount (args 1) * unit + unit := by omega
        _ = termSymbolCount (.func .mul args : ValuationTerm) * unit := by
          rw [termSymbolCount_binary_function_zero]
          ring

theorem instantiatedValuationTermCodeEnvelope_le_polynomial
    (numericBound termCodeBound : Nat) (term : ValuationTerm)
    (hcode : (binaryTermCode term).length <= termCodeBound) :
    instantiatedValuationTermCodeEnvelope numericBound term <=
      valuationTermInstantiatedCodePolynomial numericBound termCodeBound := by
  have hraw := instantiatedValuationTermCodeEnvelope_le_symbolCount
    numericBound termCodeBound term hcode
  have hsymbols :=
    (termSymbolCount_le_binaryTermCode_length term).trans hcode
  unfold valuationTermInstantiatedCodePolynomial
  exact hraw.trans (Nat.mul_le_mul_right _ hsymbols)

def valuationTermShortNumeralCodePolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope
    (valuationTermValueWidthPolynomial numericBound termCodeBound)

theorem valuationTermShortNumeralCodeEnvelope_le_polynomial
    (numericBound termCodeBound : Nat) (term : ValuationTerm)
    (hcode : (binaryTermCode term).length <= termCodeBound) :
    valuationTermShortNumeralCodeEnvelope numericBound term <=
      valuationTermShortNumeralCodePolynomial numericBound termCodeBound := by
  unfold valuationTermShortNumeralCodeEnvelope
    valuationTermShortNumeralCodePolynomial
  exact binaryNumeralTermCodeEnvelope_mono_short
    (valuationTermValueEnvelope_size_le_polynomial numericBound termCodeBound
      term hcode)

def valuationTermEqualityTermCodePolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  valuationTermShortNumeralCodePolynomial numericBound termCodeBound +
    valuationTermInstantiatedCodePolynomial numericBound termCodeBound +
    termCodeBound + 1

theorem valuationTermEqualityTermCodeEnvelope_le_polynomial
    (numericBound termCodeBound : Nat) (term : ValuationTerm)
    (hcode : (binaryTermCode term).length <= termCodeBound) :
    valuationTermEqualityTermCodeEnvelope numericBound term <=
      valuationTermEqualityTermCodePolynomial numericBound termCodeBound := by
  have hshort := valuationTermShortNumeralCodeEnvelope_le_polynomial
    numericBound termCodeBound term hcode
  have hinstantiated := instantiatedValuationTermCodeEnvelope_le_polynomial
    numericBound termCodeBound term hcode
  unfold valuationTermEqualityTermCodeEnvelope
    valuationTermEqualityTermCodePolynomial
  omega

theorem freeVariableTermCode_length_le_termCode_length
    (index : Nat) :
    (term : ValuationTerm) ->
      index ∈ term.freeVariables ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        (binaryTermCode term).length
  | #boundIndex, _ => Fin.elim0 boundIndex
  | &freeIndex, hmember => by
      simp only [LO.FirstOrder.Semiterm.freeVariables_fvar,
        Finset.mem_singleton] at hmember
      subst index
      exact le_rfl
  | .func functionSymbol arguments, hmember => by
      simp only [LO.FirstOrder.Semiterm.freeVariables_func,
        Finset.mem_biUnion] at hmember
      rcases hmember with ⟨child, _, hchild⟩
      exact (freeVariableTermCode_length_le_termCode_length index
        (arguments child) hchild).trans
          (binaryTermCode_argument_length_le_zero functionSymbol arguments
            child)

theorem valuationTermVariableCodeEnvelope_le_four_mul
    (termCodeBound : Nat) (term : ValuationTerm)
    (hcard : term.freeVariables.card <= 4)
    (hcode : (binaryTermCode term).length <= termCodeBound) :
    valuationTermVariableCodeEnvelope term <= 4 * termCodeBound := by
  have heach : forall index, index ∈ term.freeVariables ->
      (binaryTermCode (&index : ValuationTerm)).length <= termCodeBound := by
    intro index hindex
    exact (freeVariableTermCode_length_le_termCode_length index term hindex).trans
      hcode
  have hsum := term.freeVariables.sum_le_card_nsmul
    (fun index => (binaryTermCode (&index : ValuationTerm)).length)
    termCodeBound heach
  unfold valuationTermVariableCodeEnvelope
  simpa only [nsmul_eq_mul] using
    hsum.trans (Nat.mul_le_mul_right termCodeBound hcard)

def valuationTermContextFormulaCodePolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 4 numericBound
    (4 * termCodeBound)

theorem valuationTermContextFormulaCodeEnvelope_le_polynomial
    (numericBound termCodeBound : Nat) (term : ValuationTerm)
    (hcard : term.freeVariables.card <= 4)
    (hcode : (binaryTermCode term).length <= termCodeBound) :
    valuationTermContextFormulaCodeEnvelope numericBound term <=
      valuationTermContextFormulaCodePolynomial numericBound
        termCodeBound := by
  have hvariables := valuationTermVariableCodeEnvelope_le_four_mul
    termCodeBound term hcard hcode
  have hassumption :
      valuationEqualityAssumptionFormulaCodeEnvelope numericBound
          (valuationTermVariableCodeEnvelope term) <=
        valuationEqualityAssumptionFormulaCodeEnvelope numericBound
          (4 * termCodeBound) := by
    unfold valuationEqualityAssumptionFormulaCodeEnvelope
    omega
  unfold valuationTermContextFormulaCodeEnvelope
    valuationTermContextFormulaCodePolynomial
    valuationContextFormulaCodeSumEnvelope
  exact Nat.mul_le_mul hcard hassumption

def valuationTermEqualityFormulaResourcePolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  valuationTermContextFormulaCodePolynomial numericBound termCodeBound +
    paFormulaCodeEnvelope
      (valuationTermEqualityTermCodePolynomial numericBound termCodeBound) + 1

theorem valuationTermEqualityFormulaResourceEnvelope_le_polynomial
    (numericBound termCodeBound : Nat) (term : ValuationTerm)
    (hcard : term.freeVariables.card <= 4)
    (hcode : (binaryTermCode term).length <= termCodeBound) :
    valuationTermEqualityFormulaResourceEnvelope numericBound term <=
      valuationTermEqualityFormulaResourcePolynomial numericBound
        termCodeBound := by
  have hcontext := valuationTermContextFormulaCodeEnvelope_le_polynomial
    numericBound termCodeBound term hcard hcode
  have hterm := valuationTermEqualityTermCodeEnvelope_le_polynomial
    numericBound termCodeBound term hcode
  have hformula := paFormulaCodeEnvelope_mono_local hterm
  unfold valuationTermEqualityFormulaResourceEnvelope
    valuationTermEqualityFormulaResourcePolynomial
  omega

def valuationTermNormalizationStepTermCodePolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  5 * valuationTermShortNumeralCodePolynomial numericBound termCodeBound +
    4 * valuationTermInstantiatedCodePolynomial numericBound termCodeBound +
    2 * (binaryFunctionTermCodeOverhead Language.Add.add +
      binaryFunctionTermCodeOverhead Language.Mul.mul) + 1

theorem additionNormalizationStepTermCodeUniformEnvelope_le_polynomial
    (numericBound termCodeBound : Nat)
    (args : Fin 2 -> ValuationTerm)
    (hcode : (binaryTermCode
      (.func .add args : ValuationTerm)).length <= termCodeBound) :
    additionNormalizationStepTermCodeUniformEnvelope numericBound args <=
      valuationTermNormalizationStepTermCodePolynomial numericBound
        termCodeBound := by
  have hleftCode :=
    (binaryTermCode_argument_length_le_zero Language.Add.add args 0).trans
      hcode
  have hrightCode :=
    (binaryTermCode_argument_length_le_zero Language.Add.add args 1).trans
      hcode
  have hleftShort := valuationTermShortNumeralCodeEnvelope_le_polynomial
    numericBound termCodeBound (args 0) hleftCode
  have hrightShort := valuationTermShortNumeralCodeEnvelope_le_polynomial
    numericBound termCodeBound (args 1) hrightCode
  have hresultShort := valuationTermShortNumeralCodeEnvelope_le_polynomial
    numericBound termCodeBound (.func .add args : ValuationTerm) hcode
  have hleftInstantiated := instantiatedValuationTermCodeEnvelope_le_polynomial
    numericBound termCodeBound (args 0) hleftCode
  have hrightInstantiated :=
    instantiatedValuationTermCodeEnvelope_le_polynomial numericBound
      termCodeBound (args 1) hrightCode
  unfold additionNormalizationStepTermCodeUniformEnvelope
    valuationTermNormalizationStepTermCodePolynomial
  dsimp only
  omega

theorem multiplicationNormalizationStepTermCodeUniformEnvelope_le_polynomial
    (numericBound termCodeBound : Nat)
    (args : Fin 2 -> ValuationTerm)
    (hcode : (binaryTermCode
      (.func .mul args : ValuationTerm)).length <= termCodeBound) :
    multiplicationNormalizationStepTermCodeUniformEnvelope numericBound args <=
      valuationTermNormalizationStepTermCodePolynomial numericBound
        termCodeBound := by
  have hleftCode :=
    (binaryTermCode_argument_length_le_zero Language.Mul.mul args 0).trans
      hcode
  have hrightCode :=
    (binaryTermCode_argument_length_le_zero Language.Mul.mul args 1).trans
      hcode
  have hleftShort := valuationTermShortNumeralCodeEnvelope_le_polynomial
    numericBound termCodeBound (args 0) hleftCode
  have hrightShort := valuationTermShortNumeralCodeEnvelope_le_polynomial
    numericBound termCodeBound (args 1) hrightCode
  have hresultShort := valuationTermShortNumeralCodeEnvelope_le_polynomial
    numericBound termCodeBound (.func .mul args : ValuationTerm) hcode
  have hleftInstantiated := instantiatedValuationTermCodeEnvelope_le_polynomial
    numericBound termCodeBound (args 0) hleftCode
  have hrightInstantiated :=
    instantiatedValuationTermCodeEnvelope_le_polynomial numericBound
      termCodeBound (args 1) hrightCode
  unfold multiplicationNormalizationStepTermCodeUniformEnvelope
    valuationTermNormalizationStepTermCodePolynomial
  dsimp only
  omega

def valuationTermNormalizationLocalPayloadPolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  shortToIteratedPayloadPolynomial numericBound +
    shortToIteratedPayloadPolynomial 0 +
    paMultiplicationLocalCostEnvelope 0 +
    binaryNumeralAdditionPayloadPolynomial
      (2 * valuationTermValueWidthPolynomial numericBound termCodeBound) +
    binaryNumeralMultiplicationPayloadPolynomial
      (2 * valuationTermValueWidthPolynomial numericBound termCodeBound) +
    3 * paPrimitiveCostEnvelope
      (valuationTermNormalizationStepTermCodePolynomial numericBound
        termCodeBound) + 1

theorem instantiatedTermNormalizationUniformPolynomial_le_symbolCount
    (numericBound termCodeBound : Nat) :
    (term : ValuationTerm) ->
      (binaryTermCode term).length <= termCodeBound ->
      instantiatedTermNormalizationUniformPolynomial numericBound term <=
        termSymbolCount term *
          valuationTermNormalizationLocalPayloadPolynomial numericBound
            termCodeBound
  | #index, _ => Fin.elim0 index
  | &index, _ => by
      simp only [instantiatedTermNormalizationUniformPolynomial,
        termSymbolCount, one_mul]
      unfold valuationTermNormalizationLocalPayloadPolynomial
      omega
  | .func .zero args, _ => by
      simp only [instantiatedTermNormalizationUniformPolynomial]
      have hcount : termSymbolCount
          (.func .zero args : ValuationTerm) = 1 := by
        simp [termSymbolCount]
      rw [hcount, one_mul]
      unfold valuationTermNormalizationLocalPayloadPolynomial
      omega
  | .func .one args, _ => by
      simp only [instantiatedTermNormalizationUniformPolynomial]
      have hcount : termSymbolCount
          (.func .one args : ValuationTerm) = 1 := by
        simp [termSymbolCount]
      rw [hcount, one_mul]
      unfold valuationTermNormalizationLocalPayloadPolynomial
      omega
  | .func .add args, hcode => by
      have hleftCode :=
        (binaryTermCode_argument_length_le_zero Language.Add.add args 0).trans
          hcode
      have hrightCode :=
        (binaryTermCode_argument_length_le_zero Language.Add.add args 1).trans
          hcode
      have hleft := instantiatedTermNormalizationUniformPolynomial_le_symbolCount
        numericBound termCodeBound (args 0) hleftCode
      have hright := instantiatedTermNormalizationUniformPolynomial_le_symbolCount
        numericBound termCodeBound (args 1) hrightCode
      have hleftWidth := valuationTermValueEnvelope_size_le_polynomial
        numericBound termCodeBound (args 0) hleftCode
      have hrightWidth := valuationTermValueEnvelope_size_le_polynomial
        numericBound termCodeBound (args 1) hrightCode
      have harithmetic := binaryNumeralAdditionPayloadPolynomial_mono_uniform
        (show Nat.size (valuationTermValueEnvelope numericBound (args 0)) +
            Nat.size (valuationTermValueEnvelope numericBound (args 1)) <=
          2 * valuationTermValueWidthPolynomial numericBound termCodeBound by
            omega)
      have hstep :=
        additionNormalizationStepTermCodeUniformEnvelope_le_polynomial
          numericBound termCodeBound args hcode
      have hprimitive := paPrimitiveCostEnvelope_mono_short hstep
      let localBound := valuationTermNormalizationLocalPayloadPolynomial
        numericBound termCodeBound
      change instantiatedTermNormalizationUniformPolynomial numericBound
          (args 0) <= termSymbolCount (args 0) * localBound at hleft
      change instantiatedTermNormalizationUniformPolynomial numericBound
          (args 1) <= termSymbolCount (args 1) * localBound at hright
      have hnode :
          binaryNumeralAdditionPayloadPolynomial
              (Nat.size (valuationTermValueEnvelope numericBound (args 0)) +
                Nat.size
                  (valuationTermValueEnvelope numericBound (args 1))) +
            3 * paPrimitiveCostEnvelope
              (additionNormalizationStepTermCodeUniformEnvelope numericBound
                args) <= localBound := by
        dsimp only [localBound]
        unfold valuationTermNormalizationLocalPayloadPolynomial
        omega
      calc
        instantiatedTermNormalizationUniformPolynomial numericBound
            (.func .add args : ValuationTerm) =
          instantiatedTermNormalizationUniformPolynomial numericBound
              (args 0) +
            instantiatedTermNormalizationUniformPolynomial numericBound
              (args 1) +
            (binaryNumeralAdditionPayloadPolynomial
                (Nat.size
                    (valuationTermValueEnvelope numericBound (args 0)) +
                  Nat.size
                    (valuationTermValueEnvelope numericBound (args 1))) +
              3 * paPrimitiveCostEnvelope
                (additionNormalizationStepTermCodeUniformEnvelope numericBound
                  args)) := by
                    simp only [instantiatedTermNormalizationUniformPolynomial]
                    omega
        _ <= termSymbolCount (args 0) * localBound +
            termSymbolCount (args 1) * localBound + localBound := by omega
        _ = termSymbolCount (.func .add args : ValuationTerm) * localBound := by
          rw [termSymbolCount_binary_function_zero]
          ring
  | .func .mul args, hcode => by
      have hleftCode :=
        (binaryTermCode_argument_length_le_zero Language.Mul.mul args 0).trans
          hcode
      have hrightCode :=
        (binaryTermCode_argument_length_le_zero Language.Mul.mul args 1).trans
          hcode
      have hleft := instantiatedTermNormalizationUniformPolynomial_le_symbolCount
        numericBound termCodeBound (args 0) hleftCode
      have hright := instantiatedTermNormalizationUniformPolynomial_le_symbolCount
        numericBound termCodeBound (args 1) hrightCode
      have hleftWidth := valuationTermValueEnvelope_size_le_polynomial
        numericBound termCodeBound (args 0) hleftCode
      have hrightWidth := valuationTermValueEnvelope_size_le_polynomial
        numericBound termCodeBound (args 1) hrightCode
      have harithmetic :=
        binaryNumeralMultiplicationPayloadPolynomial_mono_uniform
          (show Nat.size (valuationTermValueEnvelope numericBound (args 0)) +
              Nat.size (valuationTermValueEnvelope numericBound (args 1)) <=
            2 * valuationTermValueWidthPolynomial numericBound termCodeBound by
              omega)
      have hstep :=
        multiplicationNormalizationStepTermCodeUniformEnvelope_le_polynomial
          numericBound termCodeBound args hcode
      have hprimitive := paPrimitiveCostEnvelope_mono_short hstep
      let localBound := valuationTermNormalizationLocalPayloadPolynomial
        numericBound termCodeBound
      change instantiatedTermNormalizationUniformPolynomial numericBound
          (args 0) <= termSymbolCount (args 0) * localBound at hleft
      change instantiatedTermNormalizationUniformPolynomial numericBound
          (args 1) <= termSymbolCount (args 1) * localBound at hright
      have hnode :
          binaryNumeralMultiplicationPayloadPolynomial
              (Nat.size (valuationTermValueEnvelope numericBound (args 0)) +
                Nat.size
                  (valuationTermValueEnvelope numericBound (args 1))) +
            3 * paPrimitiveCostEnvelope
              (multiplicationNormalizationStepTermCodeUniformEnvelope
                numericBound args) <= localBound := by
        dsimp only [localBound]
        unfold valuationTermNormalizationLocalPayloadPolynomial
        omega
      calc
        instantiatedTermNormalizationUniformPolynomial numericBound
            (.func .mul args : ValuationTerm) =
          instantiatedTermNormalizationUniformPolynomial numericBound
              (args 0) +
            instantiatedTermNormalizationUniformPolynomial numericBound
              (args 1) +
            (binaryNumeralMultiplicationPayloadPolynomial
                (Nat.size
                    (valuationTermValueEnvelope numericBound (args 0)) +
                  Nat.size
                    (valuationTermValueEnvelope numericBound (args 1))) +
              3 * paPrimitiveCostEnvelope
                (multiplicationNormalizationStepTermCodeUniformEnvelope
                  numericBound args)) := by
                    simp only [instantiatedTermNormalizationUniformPolynomial]
                    omega
        _ <= termSymbolCount (args 0) * localBound +
            termSymbolCount (args 1) * localBound + localBound := by omega
        _ = termSymbolCount (.func .mul args : ValuationTerm) * localBound := by
          rw [termSymbolCount_binary_function_zero]
          ring

def instantiatedTermNormalizationFixedPolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  termCodeBound *
    valuationTermNormalizationLocalPayloadPolynomial numericBound
      termCodeBound

theorem instantiatedTermNormalizationUniformPolynomial_le_fixed
    (numericBound termCodeBound : Nat) (term : ValuationTerm)
    (hcode : (binaryTermCode term).length <= termCodeBound) :
    instantiatedTermNormalizationUniformPolynomial numericBound term <=
      instantiatedTermNormalizationFixedPolynomial numericBound
        termCodeBound := by
  have hraw := instantiatedTermNormalizationUniformPolynomial_le_symbolCount
    numericBound termCodeBound term hcode
  have hsymbols :=
    (termSymbolCount_le_binaryTermCode_length term).trans hcode
  unfold instantiatedTermNormalizationFixedPolynomial
  exact hraw.trans (Nat.mul_le_mul_right _ hsymbols)

def contextualizedNormalizationFixedPayloadPolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  instantiatedTermNormalizationFixedPolynomial numericBound termCodeBound +
    smallContextAssemblyEnvelope
      (valuationTermEqualityFormulaResourcePolynomial numericBound
        termCodeBound)

theorem contextualizedNormalizationUniformPayloadPolynomial_le_fixed
    (numericBound termCodeBound : Nat) (term : ValuationTerm)
    (hcard : term.freeVariables.card <= 4)
    (hcode : (binaryTermCode term).length <= termCodeBound) :
    contextualizedNormalizationUniformPayloadPolynomial numericBound term <=
      contextualizedNormalizationFixedPayloadPolynomial numericBound
        termCodeBound := by
  have hnormalization :=
    instantiatedTermNormalizationUniformPolynomial_le_fixed numericBound
      termCodeBound term hcode
  have hformula := valuationTermEqualityFormulaResourceEnvelope_le_polynomial
    numericBound termCodeBound term hcard hcode
  have hassembly := smallContextAssemblyEnvelope_mono_local hformula
  unfold contextualizedNormalizationUniformPayloadPolynomial
    contextualizedNormalizationFixedPayloadPolynomial
  omega

def valuationTermTransportNodeTermCodePolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  2 * valuationTermInstantiatedCodePolynomial numericBound termCodeBound +
    2 * termCodeBound + 1

theorem valuationTermTransportNodeTermCodeEnvelope_le_polynomial
    (numericBound termCodeBound : Nat)
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (hcode : (binaryTermCode
      (.func functionSymbol args : ValuationTerm)).length <= termCodeBound) :
    valuationTermTransportNodeTermCodeEnvelope numericBound args <=
      valuationTermTransportNodeTermCodePolynomial numericBound
        termCodeBound := by
  have hleftCode :=
    (binaryTermCode_argument_length_le_zero functionSymbol args 0).trans hcode
  have hrightCode :=
    (binaryTermCode_argument_length_le_zero functionSymbol args 1).trans hcode
  have hleft := instantiatedValuationTermCodeEnvelope_le_polynomial
    numericBound termCodeBound (args 0) hleftCode
  have hright := instantiatedValuationTermCodeEnvelope_le_polynomial
    numericBound termCodeBound (args 1) hrightCode
  unfold valuationTermTransportNodeTermCodeEnvelope
    valuationTermTransportNodeTermCodePolynomial
  omega

def valuationTermTransportNodeLocalPayloadPolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  let contextBound :=
    valuationTermContextFormulaCodePolynomial numericBound termCodeBound
  let termBound :=
    valuationTermTransportNodeTermCodePolynomial numericBound termCodeBound
  2 * smallContextAssemblyEnvelope
      (valuationTermCongruenceFormulaResourceEnvelope contextBound termBound) +
    contextualBinaryFunctionCongruenceLocalUniformEnvelope contextBound
      termBound

def valuationTermTransportLocalPayloadPolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
      (valuationTermEqualityFormulaResourcePolynomial numericBound
        termCodeBound) +
    paPrimitiveCostEnvelope
      (valuationTermEqualityTermCodePolynomial numericBound termCodeBound) +
    valuationTermTransportNodeLocalPayloadPolynomial numericBound
      termCodeBound + 1

theorem instantiatedTermTransportUniformPolynomial_le_symbolCount
    (numericBound termCodeBound : Nat) :
    (term : ValuationTerm) ->
      term.freeVariables.card <= 4 ->
      (binaryTermCode term).length <= termCodeBound ->
      instantiatedTermTransportUniformPolynomial numericBound term <=
        termSymbolCount term *
          valuationTermTransportLocalPayloadPolynomial numericBound
            termCodeBound
  | #index, _, _ => Fin.elim0 index
  | &index, hcard, hcode => by
      have hformula :=
        valuationTermEqualityFormulaResourceEnvelope_le_polynomial
          numericBound termCodeBound (&index : ValuationTerm) hcard hcode
      have hassembly := smallContextAssemblyEnvelope_mono_local hformula
      simp only [instantiatedTermTransportUniformPolynomial, termSymbolCount,
        one_mul]
      unfold valuationTermTransportLocalPayloadPolynomial
      omega
  | .func .zero args, hcard, hcode => by
      let term := (.func .zero args : ValuationTerm)
      have hterm := valuationTermEqualityTermCodeEnvelope_le_polynomial
        numericBound termCodeBound term hcode
      have hprimitive := paPrimitiveCostEnvelope_mono_short hterm
      have hformula :=
        valuationTermEqualityFormulaResourceEnvelope_le_polynomial
          numericBound termCodeBound term hcard hcode
      have hassembly := smallContextAssemblyEnvelope_mono_local hformula
      have hcount : termSymbolCount term = 1 := by
        simp [term, termSymbolCount]
      simp only [instantiatedTermTransportUniformPolynomial]
      dsimp only [term] at hprimitive hassembly hcount ⊢
      rw [hcount, one_mul]
      unfold valuationTermTransportLocalPayloadPolynomial
      omega
  | .func .one args, hcard, hcode => by
      let term := (.func .one args : ValuationTerm)
      have hterm := valuationTermEqualityTermCodeEnvelope_le_polynomial
        numericBound termCodeBound term hcode
      have hprimitive := paPrimitiveCostEnvelope_mono_short hterm
      have hformula :=
        valuationTermEqualityFormulaResourceEnvelope_le_polynomial
          numericBound termCodeBound term hcard hcode
      have hassembly := smallContextAssemblyEnvelope_mono_local hformula
      have hcount : termSymbolCount term = 1 := by
        simp [term, termSymbolCount]
      simp only [instantiatedTermTransportUniformPolynomial]
      dsimp only [term] at hprimitive hassembly hcount ⊢
      rw [hcount, one_mul]
      unfold valuationTermTransportLocalPayloadPolynomial
      omega
  | .func .add args, hcard, hcode => by
      have hleftCode :=
        (binaryTermCode_argument_length_le_zero Language.Add.add args 0).trans
          hcode
      have hrightCode :=
        (binaryTermCode_argument_length_le_zero Language.Add.add args 1).trans
          hcode
      have hleftSubset := freeVariables_arg_subset_func
        Language.Add.add args 0
      have hrightSubset := freeVariables_arg_subset_func
        Language.Add.add args 1
      have hleftCard : (args 0).freeVariables.card <= 4 :=
        (Finset.card_le_card hleftSubset).trans hcard
      have hrightCard : (args 1).freeVariables.card <= 4 :=
        (Finset.card_le_card hrightSubset).trans hcard
      have hleft := instantiatedTermTransportUniformPolynomial_le_symbolCount
        numericBound termCodeBound (args 0) hleftCard hleftCode
      have hright := instantiatedTermTransportUniformPolynomial_le_symbolCount
        numericBound termCodeBound (args 1) hrightCard hrightCode
      have hcontext := valuationTermContextFormulaCodeEnvelope_le_polynomial
        numericBound termCodeBound (.func .add args : ValuationTerm) hcard
          hcode
      have hterm := valuationTermTransportNodeTermCodeEnvelope_le_polynomial
        numericBound termCodeBound Language.Add.add args hcode
      have hformula := valuationTermCongruenceFormulaResourceEnvelope_mono
        hcontext hterm
      have hassembly := smallContextAssemblyEnvelope_mono_local hformula
      have hcongruence :=
        contextualBinaryFunctionCongruenceLocalUniformEnvelope_mono
          hcontext hterm
      let nodeBound := valuationTermTransportNodeLocalPayloadPolynomial
        numericBound termCodeBound
      have hnode :
          2 * smallContextAssemblyEnvelope
              (valuationTermCongruenceFormulaResourceEnvelope
                (valuationTermContextFormulaCodeEnvelope numericBound
                  (.func .add args : ValuationTerm))
                (valuationTermTransportNodeTermCodeEnvelope numericBound
                  args)) +
            contextualBinaryFunctionCongruenceLocalUniformEnvelope
              (valuationTermContextFormulaCodeEnvelope numericBound
                (.func .add args : ValuationTerm))
              (valuationTermTransportNodeTermCodeEnvelope numericBound args) <=
          nodeBound := by
        dsimp only [nodeBound]
        unfold valuationTermTransportNodeLocalPayloadPolynomial
        dsimp only
        omega
      let localBound := valuationTermTransportLocalPayloadPolynomial
        numericBound termCodeBound
      change instantiatedTermTransportUniformPolynomial numericBound
          (args 0) <= termSymbolCount (args 0) * localBound at hleft
      change instantiatedTermTransportUniformPolynomial numericBound
          (args 1) <= termSymbolCount (args 1) * localBound at hright
      have hnodeLocal : nodeBound <= localBound := by
        dsimp only [nodeBound, localBound]
        unfold valuationTermTransportLocalPayloadPolynomial
        omega
      calc
        instantiatedTermTransportUniformPolynomial numericBound
            (.func .add args : ValuationTerm) =
          instantiatedTermTransportUniformPolynomial numericBound (args 0) +
            instantiatedTermTransportUniformPolynomial numericBound (args 1) +
            (2 * smallContextAssemblyEnvelope
                (valuationTermCongruenceFormulaResourceEnvelope
                  (valuationTermContextFormulaCodeEnvelope numericBound
                    (.func .add args : ValuationTerm))
                  (valuationTermTransportNodeTermCodeEnvelope numericBound
                    args)) +
              contextualBinaryFunctionCongruenceLocalUniformEnvelope
                (valuationTermContextFormulaCodeEnvelope numericBound
                  (.func .add args : ValuationTerm))
                (valuationTermTransportNodeTermCodeEnvelope numericBound
                  args)) := by
                    simp only [instantiatedTermTransportUniformPolynomial,
                      instantiatedTermTransportNodeUniformPolynomial]
                    omega
        _ <= termSymbolCount (args 0) * localBound +
            termSymbolCount (args 1) * localBound + localBound := by omega
        _ = termSymbolCount (.func .add args : ValuationTerm) * localBound := by
          rw [termSymbolCount_binary_function_zero]
          ring
  | .func .mul args, hcard, hcode => by
      have hleftCode :=
        (binaryTermCode_argument_length_le_zero Language.Mul.mul args 0).trans
          hcode
      have hrightCode :=
        (binaryTermCode_argument_length_le_zero Language.Mul.mul args 1).trans
          hcode
      have hleftSubset := freeVariables_arg_subset_func
        Language.Mul.mul args 0
      have hrightSubset := freeVariables_arg_subset_func
        Language.Mul.mul args 1
      have hleftCard : (args 0).freeVariables.card <= 4 :=
        (Finset.card_le_card hleftSubset).trans hcard
      have hrightCard : (args 1).freeVariables.card <= 4 :=
        (Finset.card_le_card hrightSubset).trans hcard
      have hleft := instantiatedTermTransportUniformPolynomial_le_symbolCount
        numericBound termCodeBound (args 0) hleftCard hleftCode
      have hright := instantiatedTermTransportUniformPolynomial_le_symbolCount
        numericBound termCodeBound (args 1) hrightCard hrightCode
      have hcontext := valuationTermContextFormulaCodeEnvelope_le_polynomial
        numericBound termCodeBound (.func .mul args : ValuationTerm) hcard
          hcode
      have hterm := valuationTermTransportNodeTermCodeEnvelope_le_polynomial
        numericBound termCodeBound Language.Mul.mul args hcode
      have hformula := valuationTermCongruenceFormulaResourceEnvelope_mono
        hcontext hterm
      have hassembly := smallContextAssemblyEnvelope_mono_local hformula
      have hcongruence :=
        contextualBinaryFunctionCongruenceLocalUniformEnvelope_mono
          hcontext hterm
      let nodeBound := valuationTermTransportNodeLocalPayloadPolynomial
        numericBound termCodeBound
      have hnode :
          2 * smallContextAssemblyEnvelope
              (valuationTermCongruenceFormulaResourceEnvelope
                (valuationTermContextFormulaCodeEnvelope numericBound
                  (.func .mul args : ValuationTerm))
                (valuationTermTransportNodeTermCodeEnvelope numericBound
                  args)) +
            contextualBinaryFunctionCongruenceLocalUniformEnvelope
              (valuationTermContextFormulaCodeEnvelope numericBound
                (.func .mul args : ValuationTerm))
              (valuationTermTransportNodeTermCodeEnvelope numericBound args) <=
          nodeBound := by
        dsimp only [nodeBound]
        unfold valuationTermTransportNodeLocalPayloadPolynomial
        dsimp only
        omega
      let localBound := valuationTermTransportLocalPayloadPolynomial
        numericBound termCodeBound
      change instantiatedTermTransportUniformPolynomial numericBound
          (args 0) <= termSymbolCount (args 0) * localBound at hleft
      change instantiatedTermTransportUniformPolynomial numericBound
          (args 1) <= termSymbolCount (args 1) * localBound at hright
      have hnodeLocal : nodeBound <= localBound := by
        dsimp only [nodeBound, localBound]
        unfold valuationTermTransportLocalPayloadPolynomial
        omega
      calc
        instantiatedTermTransportUniformPolynomial numericBound
            (.func .mul args : ValuationTerm) =
          instantiatedTermTransportUniformPolynomial numericBound (args 0) +
            instantiatedTermTransportUniformPolynomial numericBound (args 1) +
            (2 * smallContextAssemblyEnvelope
                (valuationTermCongruenceFormulaResourceEnvelope
                  (valuationTermContextFormulaCodeEnvelope numericBound
                    (.func .mul args : ValuationTerm))
                  (valuationTermTransportNodeTermCodeEnvelope numericBound
                    args)) +
              contextualBinaryFunctionCongruenceLocalUniformEnvelope
                (valuationTermContextFormulaCodeEnvelope numericBound
                  (.func .mul args : ValuationTerm))
                (valuationTermTransportNodeTermCodeEnvelope numericBound
                  args)) := by
                    simp only [instantiatedTermTransportUniformPolynomial,
                      instantiatedTermTransportNodeUniformPolynomial]
                    omega
        _ <= termSymbolCount (args 0) * localBound +
            termSymbolCount (args 1) * localBound + localBound := by omega
        _ = termSymbolCount (.func .mul args : ValuationTerm) * localBound := by
          rw [termSymbolCount_binary_function_zero]
          ring

def instantiatedTermTransportFixedPolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  termCodeBound *
    valuationTermTransportLocalPayloadPolynomial numericBound termCodeBound

theorem instantiatedTermTransportUniformPolynomial_le_fixed
    (numericBound termCodeBound : Nat) (term : ValuationTerm)
    (hcard : term.freeVariables.card <= 4)
    (hcode : (binaryTermCode term).length <= termCodeBound) :
    instantiatedTermTransportUniformPolynomial numericBound term <=
      instantiatedTermTransportFixedPolynomial numericBound
        termCodeBound := by
  have hraw := instantiatedTermTransportUniformPolynomial_le_symbolCount
    numericBound termCodeBound term hcard hcode
  have hsymbols :=
    (termSymbolCount_le_binaryTermCode_length term).trans hcode
  unfold instantiatedTermTransportFixedPolynomial
  exact hraw.trans (Nat.mul_le_mul_right _ hsymbols)

def compileTermValueEqualityFixedPayloadPolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  contextualEqualityTransitivityUniformPayloadBound
    (valuationTermContextFormulaCodePolynomial numericBound termCodeBound)
    (valuationTermEqualityTermCodePolynomial numericBound termCodeBound)
    (contextualizedNormalizationFixedPayloadPolynomial numericBound
      termCodeBound)
    (instantiatedTermTransportFixedPolynomial numericBound termCodeBound)

theorem compileTermValueEqualityUniformPayloadPolynomial_le_fixed
    (numericBound termCodeBound : Nat) (term : ValuationTerm)
    (hcard : term.freeVariables.card <= 4)
    (hcode : (binaryTermCode term).length <= termCodeBound) :
    compileTermValueEqualityUniformPayloadPolynomial numericBound term <=
      compileTermValueEqualityFixedPayloadPolynomial numericBound
        termCodeBound := by
  have hcontext := valuationTermContextFormulaCodeEnvelope_le_polynomial
    numericBound termCodeBound term hcard hcode
  have hterm := valuationTermEqualityTermCodeEnvelope_le_polynomial
    numericBound termCodeBound term hcode
  have hnormalization :=
    contextualizedNormalizationUniformPayloadPolynomial_le_fixed
      numericBound termCodeBound term hcard hcode
  have htransport := instantiatedTermTransportUniformPolynomial_le_fixed
    numericBound termCodeBound term hcard hcode
  unfold compileTermValueEqualityUniformPayloadPolynomial
    compileTermValueEqualityFixedPayloadPolynomial
  exact contextualEqualityTransitivityUniformPayloadBound_mono hcontext hterm
    hnormalization htransport

#print axioms valuationTermValueEnvelope_size_le_polynomial
#print axioms instantiatedValuationTermCodeEnvelope_le_polynomial
#print axioms valuationTermEqualityTermCodeEnvelope_le_polynomial
#print axioms valuationTermContextFormulaCodeEnvelope_le_polynomial
#print axioms instantiatedTermNormalizationUniformPolynomial_le_fixed
#print axioms contextualizedNormalizationUniformPayloadPolynomial_le_fixed
#print axioms instantiatedTermTransportUniformPolynomial_le_fixed
#print axioms compileTermValueEqualityUniformPayloadPolynomial_le_fixed

end FoundationCompactPAValuationTermCompilerFixedPolynomialBounds
