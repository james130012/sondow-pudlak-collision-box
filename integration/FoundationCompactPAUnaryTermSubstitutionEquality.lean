import integration.FoundationCompactPABinaryNumeralAdditionBounds
import integration.FoundationCompactSyntaxTransformationCodeBounds

/-!
# Quantitative equality transport through unary arithmetic terms

For an arbitrary one-bound-variable ordered-ring term, this module transports
an explicit proof of `left = right` through every term node.  The recursive
compiler returns the actual certified PA proof together with a complete
proof-and-certificate payload bound; no proof-length premise is accepted.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAUnaryTermSubstitutionEquality

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactSyntaxTransformationCodeBounds

def instantiateUnaryTerm
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  (Rew.subst ![witness]) term

theorem instantiateUnaryTerm_add
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    instantiateUnaryTerm (Semiterm.func Language.Add.add arguments) witness =
      paAddTerm
        (instantiateUnaryTerm (arguments 0) witness)
        (instantiateUnaryTerm (arguments 1) witness) := by
  unfold instantiateUnaryTerm paAddTerm
  rw [Rew.func']
  rw [Matrix.fun_eq_vec_two
    (fun index => (Rew.subst ![witness]) (arguments index))]
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func]
  funext index
  simp [Function.comp_apply]

theorem instantiateUnaryTerm_mul
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    instantiateUnaryTerm (Semiterm.func Language.Mul.mul arguments) witness =
      paMulTerm
        (instantiateUnaryTerm (arguments 0) witness)
        (instantiateUnaryTerm (arguments 1) witness) := by
  unfold instantiateUnaryTerm paMulTerm
  rw [Rew.func']
  rw [Matrix.fun_eq_vec_two
    (fun index => (Rew.subst ![witness]) (arguments index))]
  simp [Semiterm.Operator.operator, Semiterm.Operator.Mul.term_eq,
    Rew.func]
  funext index
  simp [Function.comp_apply]

/-- Every immediate argument code occurs literally inside the canonical code
of its enclosing function term. -/
theorem binaryTermCode_argument_length_le
    {arity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ arity)
    (arguments : Fin arity →
      LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (index : Fin arity) :
    (binaryTermCode (arguments index)).length <=
      (binaryTermCode
        (Semiterm.func functionSymbol arguments)).length := by
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

theorem termSymbolCount_binary_function
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1) :
    termSymbolCount (Semiterm.func functionSymbol arguments) =
      1 + termSymbolCount (arguments 0) +
        termSymbolCount (arguments 1) := by
  simp [termSymbolCount,
    show (Finset.univ : Finset (Fin 2)) = {0, 1} from by
      ext index
      cases index using Fin.cases <;> simp]
  omega

def unaryTermSubstitutionCodeEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (openTermCodeBound : Nat) : Nat :=
  (substitutionCodeFactor left 0 +
    substitutionCodeFactor right 0) * openTermCodeBound

theorem instantiateUnaryTerm_code_length_le_factor
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryTermCode (instantiateUnaryTerm term witness)).length <=
      substitutionCodeFactor witness 0 *
        (binaryTermCode term).length := by
  simpa [instantiateUnaryTerm, Rew.qpow] using
    (binaryTermCode_substitutionOne_qpow_length_le witness 0 term)

theorem instantiateUnaryTerm_left_code_length_le_envelope
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (openTermCodeBound : Nat)
    (hterm : (binaryTermCode term).length <= openTermCodeBound) :
    (binaryTermCode (instantiateUnaryTerm term left)).length <=
      unaryTermSubstitutionCodeEnvelope left right openTermCodeBound := by
  calc
    (binaryTermCode (instantiateUnaryTerm term left)).length <=
        substitutionCodeFactor left 0 *
          (binaryTermCode term).length :=
      instantiateUnaryTerm_code_length_le_factor term left
    _ <= substitutionCodeFactor left 0 * openTermCodeBound :=
      Nat.mul_le_mul_left _ hterm
    _ <= unaryTermSubstitutionCodeEnvelope left right
        openTermCodeBound := by
      unfold unaryTermSubstitutionCodeEnvelope
      rw [Nat.add_mul]
      exact Nat.le_add_right _ _

theorem instantiateUnaryTerm_right_code_length_le_envelope
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (openTermCodeBound : Nat)
    (hterm : (binaryTermCode term).length <= openTermCodeBound) :
    (binaryTermCode (instantiateUnaryTerm term right)).length <=
      unaryTermSubstitutionCodeEnvelope left right openTermCodeBound := by
  calc
    (binaryTermCode (instantiateUnaryTerm term right)).length <=
        substitutionCodeFactor right 0 *
          (binaryTermCode term).length :=
      instantiateUnaryTerm_code_length_le_factor term right
    _ <= substitutionCodeFactor right 0 * openTermCodeBound :=
      Nat.mul_le_mul_left _ hterm
    _ <= unaryTermSubstitutionCodeEnvelope left right
        openTermCodeBound := by
      unfold unaryTermSubstitutionCodeEnvelope
      rw [Nat.add_mul]
      exact Nat.le_add_left _ _

structure UnaryTermSubstitutionEqualityCompilation
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (parameterEquality : CertifiedPAProof
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition))
    (openTermCodeBound : Nat) where
  proof : CertifiedPAProof
    (“!!(instantiateUnaryTerm term left) =
      !!(instantiateUnaryTerm term right)” :
      LO.FirstOrder.ArithmeticProposition)
  payloadLength_le : proof.payloadLength <=
    termSymbolCount term *
      (parameterEquality.payloadLength +
        paPrimitiveCostEnvelope
          (unaryTermSubstitutionCodeEnvelope
            left right openTermCodeBound))

noncomputable def compileUnaryTermSubstitutionEquality :
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1) →
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) →
    (parameterEquality : CertifiedPAProof
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)) →
    (openTermCodeBound : Nat) →
    (binaryTermCode term).length <= openTermCodeBound →
    UnaryTermSubstitutionEqualityCompilation
      term left right parameterEquality openTermCodeBound
  | .bvar index, left, right, parameterEquality,
      openTermCodeBound, _ => by
      have hindex : index = 0 := Fin.eq_zero index
      subst index
      let formulaEq :
          (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition) =
          (“!!(instantiateUnaryTerm (#0) left) =
            !!(instantiateUnaryTerm (#0) right)” :
            LO.FirstOrder.ArithmeticProposition) := by
        simp [instantiateUnaryTerm]
      let proof := CertifiedPAProof.cast formulaEq parameterEquality
      refine { proof := proof, payloadLength_le := ?_ }
      have hpayload : proof.payloadLength =
          parameterEquality.payloadLength := by
        dsimp only [proof]
        exact cast_payloadLength _ _
      rw [hpayload]
      simp only [termSymbolCount, one_mul]
      omega
  | .fvar index, left, right, parameterEquality,
      openTermCodeBound, hterm => by
      let termBound := unaryTermSubstitutionCodeEnvelope
        left right openTermCodeBound
      let baseProof := proveEqualityReflexivityAtTerm
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      let formulaEq :
          (“!!(&index : LO.FirstOrder.ArithmeticSemiterm Nat 0) =
            !!(&index : LO.FirstOrder.ArithmeticSemiterm Nat 0)” :
            LO.FirstOrder.ArithmeticProposition) =
          (“!!(instantiateUnaryTerm (&index) left) =
            !!(instantiateUnaryTerm (&index) right)” :
            LO.FirstOrder.ArithmeticProposition) := by
        simp [instantiateUnaryTerm]
      let proof := CertifiedPAProof.cast formulaEq baseProof
      have hcode := instantiateUnaryTerm_left_code_length_le_envelope
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat 1)
        left right openTermCodeBound hterm
      have hbase := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat 0)
        termBound (by simpa [instantiateUnaryTerm] using hcode)
      refine { proof := proof, payloadLength_le := ?_ }
      change proof.payloadLength <=
        termSymbolCount (&index : LO.FirstOrder.ArithmeticSemiterm Nat 1) *
          (parameterEquality.payloadLength +
            paPrimitiveCostEnvelope termBound)
      have hpayload : proof.payloadLength = baseProof.payloadLength := by
        dsimp only [proof]
        exact cast_payloadLength _ _
      rw [hpayload]
      simp only [termSymbolCount, one_mul]
      exact hbase.trans (Nat.le_add_left _ _)
  | .func Language.Zero.zero arguments, left, right, parameterEquality,
      openTermCodeBound, hterm => by
      let termBound := unaryTermSubstitutionCodeEnvelope
        left right openTermCodeBound
      let zeroTerm : LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
        Semiterm.func Language.Zero.zero ![]
      let baseProof := proveEqualityReflexivityAtTerm zeroTerm
      let formulaEq :
          (“!!zeroTerm = !!zeroTerm” :
            LO.FirstOrder.ArithmeticProposition) =
          (“!!(instantiateUnaryTerm
              (Semiterm.func Language.Zero.zero arguments) left) =
            !!(instantiateUnaryTerm
              (Semiterm.func Language.Zero.zero arguments) right)” :
            LO.FirstOrder.ArithmeticProposition) := by
        simp [zeroTerm, instantiateUnaryTerm, Matrix.empty_eq]
      let proof := CertifiedPAProof.cast formulaEq baseProof
      have hcode := instantiateUnaryTerm_left_code_length_le_envelope
        (Semiterm.func Language.Zero.zero arguments)
        left right openTermCodeBound hterm
      have hzeroCode : (binaryTermCode zeroTerm).length <= termBound := by
        simpa [zeroTerm, instantiateUnaryTerm, Matrix.empty_eq] using hcode
      have hbase := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
        zeroTerm termBound hzeroCode
      refine { proof := proof, payloadLength_le := ?_ }
      change proof.payloadLength <=
        termSymbolCount (Semiterm.func Language.Zero.zero arguments) *
          (parameterEquality.payloadLength +
            paPrimitiveCostEnvelope termBound)
      have hpayload : proof.payloadLength = baseProof.payloadLength := by
        dsimp only [proof]
        exact cast_payloadLength _ _
      rw [hpayload]
      have hcount : termSymbolCount
          (Semiterm.func Language.Zero.zero arguments) = 1 := by
        simp [termSymbolCount]
      rw [hcount, one_mul]
      exact hbase.trans (Nat.le_add_left _ _)
  | .func Language.One.one arguments, left, right, parameterEquality,
      openTermCodeBound, hterm => by
      let termBound := unaryTermSubstitutionCodeEnvelope
        left right openTermCodeBound
      let oneTerm : LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
        Semiterm.func Language.One.one ![]
      let baseProof := proveEqualityReflexivityAtTerm oneTerm
      let formulaEq :
          (“!!oneTerm = !!oneTerm” :
            LO.FirstOrder.ArithmeticProposition) =
          (“!!(instantiateUnaryTerm
              (Semiterm.func Language.One.one arguments) left) =
            !!(instantiateUnaryTerm
              (Semiterm.func Language.One.one arguments) right)” :
            LO.FirstOrder.ArithmeticProposition) := by
        simp [oneTerm, instantiateUnaryTerm, Matrix.empty_eq]
      let proof := CertifiedPAProof.cast formulaEq baseProof
      have hcode := instantiateUnaryTerm_left_code_length_le_envelope
        (Semiterm.func Language.One.one arguments)
        left right openTermCodeBound hterm
      have honeCode : (binaryTermCode oneTerm).length <= termBound := by
        simpa [oneTerm, instantiateUnaryTerm, Matrix.empty_eq] using hcode
      have hbase := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
        oneTerm termBound honeCode
      refine { proof := proof, payloadLength_le := ?_ }
      change proof.payloadLength <=
        termSymbolCount (Semiterm.func Language.One.one arguments) *
          (parameterEquality.payloadLength +
            paPrimitiveCostEnvelope termBound)
      have hpayload : proof.payloadLength = baseProof.payloadLength := by
        dsimp only [proof]
        exact cast_payloadLength _ _
      rw [hpayload]
      have hcount : termSymbolCount
          (Semiterm.func Language.One.one arguments) = 1 := by
        simp [termSymbolCount]
      rw [hcount, one_mul]
      exact hbase.trans (Nat.le_add_left _ _)
  | .func Language.Add.add arguments, left, right, parameterEquality,
      openTermCodeBound, hterm => by
      let termBound := unaryTermSubstitutionCodeEnvelope
        left right openTermCodeBound
      have hfirstOpen : (binaryTermCode (arguments 0)).length <=
          openTermCodeBound :=
        (binaryTermCode_argument_length_le Language.Add.add arguments 0).trans
          hterm
      have hsecondOpen : (binaryTermCode (arguments 1)).length <=
          openTermCodeBound :=
        (binaryTermCode_argument_length_le Language.Add.add arguments 1).trans
          hterm
      let firstCompilation := compileUnaryTermSubstitutionEquality
        (arguments 0) left right parameterEquality
          openTermCodeBound hfirstOpen
      let secondCompilation := compileUnaryTermSubstitutionEquality
        (arguments 1) left right parameterEquality
          openTermCodeBound hsecondOpen
      let leftFirst := instantiateUnaryTerm (arguments 0) left
      let leftSecond := instantiateUnaryTerm (arguments 1) left
      let rightFirst := instantiateUnaryTerm (arguments 0) right
      let rightSecond := instantiateUnaryTerm (arguments 1) right
      let result := proveAddCongruence
        leftFirst leftSecond rightFirst rightSecond
        firstCompilation.proof secondCompilation.proof
      have hleftApplication :
          instantiateUnaryTerm
              (Semiterm.func Language.Add.add arguments) left =
            paAddTerm leftFirst leftSecond := by
        dsimp only [leftFirst, leftSecond]
        unfold instantiateUnaryTerm paAddTerm
        rw [Rew.func']
        rw [Matrix.fun_eq_vec_two
          (fun index => (Rew.subst ![left]) (arguments index))]
        simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
          Rew.func]
        funext index
        simp [Function.comp_apply]
      have hrightApplication :
          instantiateUnaryTerm
              (Semiterm.func Language.Add.add arguments) right =
            paAddTerm rightFirst rightSecond := by
        dsimp only [rightFirst, rightSecond]
        unfold instantiateUnaryTerm paAddTerm
        rw [Rew.func']
        rw [Matrix.fun_eq_vec_two
          (fun index => (Rew.subst ![right]) (arguments index))]
        simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
          Rew.func]
        funext index
        simp [Function.comp_apply]
      let formulaEq :
          (“!!leftFirst + !!leftSecond =
            !!rightFirst + !!rightSecond” :
            LO.FirstOrder.ArithmeticProposition) =
          (“!!(instantiateUnaryTerm
              (Semiterm.func Language.Add.add arguments) left) =
            !!(instantiateUnaryTerm
              (Semiterm.func Language.Add.add arguments) right)” :
            LO.FirstOrder.ArithmeticProposition) := by
        rw [addEqualityAsTerm_formula]
        rw [hleftApplication, hrightApplication]
      let proof := CertifiedPAProof.cast formulaEq result
      have hleftFirst := instantiateUnaryTerm_left_code_length_le_envelope
        (arguments 0) left right openTermCodeBound hfirstOpen
      have hleftSecond := instantiateUnaryTerm_left_code_length_le_envelope
        (arguments 1) left right openTermCodeBound hsecondOpen
      have hrightFirst := instantiateUnaryTerm_right_code_length_le_envelope
        (arguments 0) left right openTermCodeBound hfirstOpen
      have hrightSecond := instantiateUnaryTerm_right_code_length_le_envelope
        (arguments 1) left right openTermCodeBound hsecondOpen
      have hcongruence := proveAddCongruence_payloadLength_le_primitive
        leftFirst leftSecond rightFirst rightSecond
        firstCompilation.proof secondCompilation.proof termBound
        hleftFirst hleftSecond hrightFirst hrightSecond
      refine { proof := proof, payloadLength_le := ?_ }
      change proof.payloadLength <=
        termSymbolCount (Semiterm.func Language.Add.add arguments) *
          (parameterEquality.payloadLength +
            paPrimitiveCostEnvelope termBound)
      have hpayload : proof.payloadLength = result.payloadLength := by
        dsimp only [proof]
        exact cast_payloadLength _ _
      rw [hpayload]
      have hfirstPayload : firstCompilation.proof.payloadLength <=
          termSymbolCount (arguments 0) *
            (parameterEquality.payloadLength +
              paPrimitiveCostEnvelope termBound) := by
        simpa only [termBound] using firstCompilation.payloadLength_le
      have hsecondPayload : secondCompilation.proof.payloadLength <=
          termSymbolCount (arguments 1) *
            (parameterEquality.payloadLength +
              paPrimitiveCostEnvelope termBound) := by
        simpa only [termBound] using secondCompilation.payloadLength_le
      calc
        result.payloadLength <=
            firstCompilation.proof.payloadLength +
              secondCompilation.proof.payloadLength +
              paPrimitiveCostEnvelope termBound := by
                dsimp only [result]
                exact hcongruence
        _ <= termSymbolCount (arguments 0) *
              (parameterEquality.payloadLength +
                paPrimitiveCostEnvelope termBound) +
            termSymbolCount (arguments 1) *
              (parameterEquality.payloadLength +
                paPrimitiveCostEnvelope termBound) +
            paPrimitiveCostEnvelope termBound := by
              omega
        _ <= termSymbolCount (arguments 0) *
              (parameterEquality.payloadLength +
                paPrimitiveCostEnvelope termBound) +
            termSymbolCount (arguments 1) *
              (parameterEquality.payloadLength +
                paPrimitiveCostEnvelope termBound) +
            (parameterEquality.payloadLength +
              paPrimitiveCostEnvelope termBound) :=
          Nat.add_le_add_left
            (Nat.le_add_left
              (paPrimitiveCostEnvelope termBound)
              parameterEquality.payloadLength) _
        _ = (1 + termSymbolCount (arguments 0) +
              termSymbolCount (arguments 1)) *
            (parameterEquality.payloadLength +
              paPrimitiveCostEnvelope termBound) := by
              ring
        _ = termSymbolCount
              (Semiterm.func Language.Add.add arguments) *
            (parameterEquality.payloadLength +
              paPrimitiveCostEnvelope termBound) := by
              rw [termSymbolCount_binary_function]
  | .func Language.Mul.mul arguments, left, right, parameterEquality,
      openTermCodeBound, hterm => by
      let termBound := unaryTermSubstitutionCodeEnvelope
        left right openTermCodeBound
      have hfirstOpen : (binaryTermCode (arguments 0)).length <=
          openTermCodeBound :=
        (binaryTermCode_argument_length_le Language.Mul.mul arguments 0).trans
          hterm
      have hsecondOpen : (binaryTermCode (arguments 1)).length <=
          openTermCodeBound :=
        (binaryTermCode_argument_length_le Language.Mul.mul arguments 1).trans
          hterm
      let firstCompilation := compileUnaryTermSubstitutionEquality
        (arguments 0) left right parameterEquality
          openTermCodeBound hfirstOpen
      let secondCompilation := compileUnaryTermSubstitutionEquality
        (arguments 1) left right parameterEquality
          openTermCodeBound hsecondOpen
      let leftFirst := instantiateUnaryTerm (arguments 0) left
      let leftSecond := instantiateUnaryTerm (arguments 1) left
      let rightFirst := instantiateUnaryTerm (arguments 0) right
      let rightSecond := instantiateUnaryTerm (arguments 1) right
      let result := proveMulCongruence
        leftFirst leftSecond rightFirst rightSecond
        firstCompilation.proof secondCompilation.proof
      have hleftApplication :
          instantiateUnaryTerm
              (Semiterm.func Language.Mul.mul arguments) left =
            paMulTerm leftFirst leftSecond := by
        dsimp only [leftFirst, leftSecond]
        unfold instantiateUnaryTerm paMulTerm
        rw [Rew.func']
        rw [Matrix.fun_eq_vec_two
          (fun index => (Rew.subst ![left]) (arguments index))]
        simp [Semiterm.Operator.operator, Semiterm.Operator.Mul.term_eq,
          Rew.func]
        funext index
        simp [Function.comp_apply]
      have hrightApplication :
          instantiateUnaryTerm
              (Semiterm.func Language.Mul.mul arguments) right =
            paMulTerm rightFirst rightSecond := by
        dsimp only [rightFirst, rightSecond]
        unfold instantiateUnaryTerm paMulTerm
        rw [Rew.func']
        rw [Matrix.fun_eq_vec_two
          (fun index => (Rew.subst ![right]) (arguments index))]
        simp [Semiterm.Operator.operator, Semiterm.Operator.Mul.term_eq,
          Rew.func]
        funext index
        simp [Function.comp_apply]
      let formulaEq :
          (“!!leftFirst * !!leftSecond =
            !!rightFirst * !!rightSecond” :
            LO.FirstOrder.ArithmeticProposition) =
          (“!!(instantiateUnaryTerm
              (Semiterm.func Language.Mul.mul arguments) left) =
            !!(instantiateUnaryTerm
              (Semiterm.func Language.Mul.mul arguments) right)” :
            LO.FirstOrder.ArithmeticProposition) := by
        rw [mulEqualityAsTerm_formula]
        rw [hleftApplication, hrightApplication]
      let proof := CertifiedPAProof.cast formulaEq result
      have hleftFirst := instantiateUnaryTerm_left_code_length_le_envelope
        (arguments 0) left right openTermCodeBound hfirstOpen
      have hleftSecond := instantiateUnaryTerm_left_code_length_le_envelope
        (arguments 1) left right openTermCodeBound hsecondOpen
      have hrightFirst := instantiateUnaryTerm_right_code_length_le_envelope
        (arguments 0) left right openTermCodeBound hfirstOpen
      have hrightSecond := instantiateUnaryTerm_right_code_length_le_envelope
        (arguments 1) left right openTermCodeBound hsecondOpen
      have hcongruence := proveMulCongruence_payloadLength_le_primitive
        leftFirst leftSecond rightFirst rightSecond
        firstCompilation.proof secondCompilation.proof termBound
        hleftFirst hleftSecond hrightFirst hrightSecond
      refine { proof := proof, payloadLength_le := ?_ }
      change proof.payloadLength <=
        termSymbolCount (Semiterm.func Language.Mul.mul arguments) *
          (parameterEquality.payloadLength +
            paPrimitiveCostEnvelope termBound)
      have hpayload : proof.payloadLength = result.payloadLength := by
        dsimp only [proof]
        exact cast_payloadLength _ _
      rw [hpayload]
      have hfirstPayload : firstCompilation.proof.payloadLength <=
          termSymbolCount (arguments 0) *
            (parameterEquality.payloadLength +
              paPrimitiveCostEnvelope termBound) := by
        simpa only [termBound] using firstCompilation.payloadLength_le
      have hsecondPayload : secondCompilation.proof.payloadLength <=
          termSymbolCount (arguments 1) *
            (parameterEquality.payloadLength +
              paPrimitiveCostEnvelope termBound) := by
        simpa only [termBound] using secondCompilation.payloadLength_le
      calc
        result.payloadLength <=
            firstCompilation.proof.payloadLength +
              secondCompilation.proof.payloadLength +
              paPrimitiveCostEnvelope termBound := by
                dsimp only [result]
                exact hcongruence
        _ <= termSymbolCount (arguments 0) *
              (parameterEquality.payloadLength +
                paPrimitiveCostEnvelope termBound) +
            termSymbolCount (arguments 1) *
              (parameterEquality.payloadLength +
                paPrimitiveCostEnvelope termBound) +
            paPrimitiveCostEnvelope termBound := by
              omega
        _ <= termSymbolCount (arguments 0) *
              (parameterEquality.payloadLength +
                paPrimitiveCostEnvelope termBound) +
            termSymbolCount (arguments 1) *
              (parameterEquality.payloadLength +
                paPrimitiveCostEnvelope termBound) +
            (parameterEquality.payloadLength +
              paPrimitiveCostEnvelope termBound) :=
          Nat.add_le_add_left
            (Nat.le_add_left
              (paPrimitiveCostEnvelope termBound)
              parameterEquality.payloadLength) _
        _ = (1 + termSymbolCount (arguments 0) +
              termSymbolCount (arguments 1)) *
            (parameterEquality.payloadLength +
              paPrimitiveCostEnvelope termBound) := by
              ring
        _ = termSymbolCount
              (Semiterm.func Language.Mul.mul arguments) *
            (parameterEquality.payloadLength +
              paPrimitiveCostEnvelope termBound) := by
              rw [termSymbolCount_binary_function]
termination_by term => term.complexity
decreasing_by
  all_goals exact Semiterm.complexity_func_lt _ _ _

def proveUnaryTermSubstitutionEquality
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (parameterEquality : CertifiedPAProof
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(instantiateUnaryTerm term left) =
        !!(instantiateUnaryTerm term right)” :
        LO.FirstOrder.ArithmeticProposition) :=
  (compileUnaryTermSubstitutionEquality term left right parameterEquality
    (binaryTermCode term).length le_rfl).proof

theorem proveUnaryTermSubstitutionEquality_verifier_eq_true
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (parameterEquality : CertifiedPAProof
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    listedCompactCertifiedPAProofVerifier
      (proveUnaryTermSubstitutionEquality
        term left right parameterEquality).code
      (compactFormulaCode
        (“!!(instantiateUnaryTerm term left) =
          !!(instantiateUnaryTerm term right)” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (proveUnaryTermSubstitutionEquality
    term left right parameterEquality).verifier_eq_true

#print axioms compileUnaryTermSubstitutionEquality
#print axioms proveUnaryTermSubstitutionEquality_verifier_eq_true

end FoundationCompactPAUnaryTermSubstitutionEquality
