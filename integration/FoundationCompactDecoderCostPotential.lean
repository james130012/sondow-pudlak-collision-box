import integration.FoundationCompactListedCertifiedDecoderCost
import integration.FoundationCompactCertificateDecoderStructuralBound
import Mathlib.Tactic.Linarith

/-!
# Amortized potential for compact decoder bit costs

Successful parsers are charged against the prefix they consume; the unused
suffix retains its potential.  This is the invariant needed to add the costs
of sequential and branching proof-tree parses without an exponential bound.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactDecoderCostPotential

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactVerifierStructuralBound
open FoundationCompactNatDecoderCost
open FoundationCompactSyntaxDecoderCost

/-- A fixed quartic reserve.  The constant pays for bind nodes and local
administrative operations while the fourth power amortizes quadratic natural
decodes over a linear number of consumed prefixes. -/
def decoderPotential (length : Nat) : Nat :=
  4096 * (length + 1) ^ 4

def parserReserve (length : Nat) : Nat :=
  16 * (length + 1)

def primitiveReserve (length : Nat) : Nat :=
  64 * (length + 1)

@[simp] theorem tracePure_cost {alpha : Type*} (value : alpha) :
    (tracePure value).2 = 1 := rfl

@[simp] theorem traceFailure_cost {alpha : Type*} :
    (traceFailure : OptionTrace alpha).2 = 1 := rfl

@[simp] theorem traceLiftOption_cost {alpha : Type*}
    (value : Option alpha) (cost : Nat) :
    (traceLiftOption value cost).2 = cost + 1 := rfl

theorem traceBind_cost {alpha beta : Type*}
    (source : OptionTrace alpha)
    (next : alpha -> OptionTrace beta) :
    (traceBind source next).2 =
      match source.1 with
      | none => source.2 + 1
      | some value => source.2 + (next value).2 + 1 := by
  cases hsource : source.1 <;> simp [traceBind, hsource]

theorem decoderPotential_mono {left right : Nat}
    (h : left <= right) :
    decoderPotential left <= decoderPotential right := by
  unfold decoderPotential
  exact Nat.mul_le_mul_left 4096
    (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 4)

theorem quadratic_le_decoderPotential (length : Nat) :
    (length + 1) * (length + 1) <= decoderPotential length := by
  have hpow : (length + 1) ^ 2 <= (length + 1) ^ 4 :=
    Nat.pow_le_pow_right (Nat.succ_pos length) (by omega)
  calc
    (length + 1) * (length + 1) = (length + 1) ^ 2 :=
      (pow_two _).symm
    _ <= (length + 1) ^ 4 := hpow
    _ <= decoderPotential length := by
      unfold decoderPotential
      omega

theorem quadratic_plus_sixteen_le_decoderPotential (length : Nat) :
    (length + 1) * (length + 1) + 16 <= decoderPotential length := by
  have hpowTwo : (length + 1) ^ 2 <= (length + 1) ^ 4 :=
    Nat.pow_le_pow_right (Nat.succ_pos length) (by omega)
  have hpowOne : 1 <= (length + 1) ^ 4 := by
    have := Nat.pow_le_pow_left (show 1 <= length + 1 by omega) 4
    norm_num at this ⊢
    exact this
  have hscaledOne := Nat.mul_le_mul_left 16 hpowOne
  unfold decoderPotential
  rw [← pow_two]
  omega

theorem natDecoder_quartic_gap (length : Nat)
    (hlength : 2 <= length) :
    (length + 1) * (length + 1) +
        4096 * length ^ 4 + 16 <=
      decoderPotential length := by
  unfold decoderPotential
  simp only [pow_succ]
  nlinarith

theorem decodeBinaryNatTrace_success_potential
    {bits suffix : List Bool} {value : Nat}
    (htrace : (decodeBinaryNatTrace bits).1 = some (value, suffix)) :
    (decodeBinaryNatTrace bits).2 + decoderPotential suffix.length + 16 <=
      decoderPotential bits.length := by
  have hdecode : decodeBinaryNat bits = some (value, suffix) := by
    rw [← decodeBinaryNatTrace_result bits]
    exact htrace
  have hconsume := decodeBinaryNat_consumes_two hdecode
  have hcost := decodeBinaryNatTrace_cost_le bits
  have hsuffix : suffix.length + 1 <= bits.length := by omega
  have hsuffixPow : (suffix.length + 1) ^ 4 <= bits.length ^ 4 :=
    Nat.pow_le_pow_left hsuffix 4
  have hgap := natDecoder_quartic_gap bits.length (by omega)
  unfold decoderPotential at *
  omega

theorem decodeBinaryNatTrace_failure_potential
    {bits : List Bool}
    (_htrace : (decodeBinaryNatTrace bits).1 = none) :
    (decodeBinaryNatTrace bits).2 + 16 <=
      decoderPotential bits.length := by
  have hcost := decodeBinaryNatTrace_cost_le bits
  have hbound := quadratic_plus_sixteen_le_decoderPotential bits.length
  omega

/-- A whole parser call retains sixteen cost units after either failure or a
successful transition to its unconsumed suffix. -/
def parserCostBoundWith {alpha : Type*}
    (reserve : Nat)
    (trace : OptionTrace (alpha × List Bool))
    (bits : List Bool) : Prop :=
  match trace.1 with
  | none => trace.2 + reserve <= decoderPotential bits.length
  | some (_, suffix) =>
      trace.2 + decoderPotential suffix.length + reserve <=
        decoderPotential bits.length

def parserCostBound {alpha : Type*}
    (trace : OptionTrace (alpha × List Bool))
    (bits : List Bool) : Prop :=
  parserCostBoundWith (parserReserve bits.length) trace bits

theorem linear_plus_quadratic_le_decoderPotential (length : Nat) :
    (length + 1) * (length + 1) + primitiveReserve length <=
      decoderPotential length := by
  have hpowTwo : (length + 1) ^ 2 <= (length + 1) ^ 4 :=
    Nat.pow_le_pow_right (Nat.succ_pos length) (by omega)
  have hpowOne : (length + 1) <= (length + 1) ^ 4 := by
    have hpow : (length + 1) ^ 1 <= (length + 1) ^ 4 :=
      Nat.pow_le_pow_right (Nat.succ_pos length) (by omega)
    simpa using hpow
  have hscaledOne := Nat.mul_le_mul_left 64 hpowOne
  unfold decoderPotential primitiveReserve
  rw [← pow_two]
  omega

theorem natDecoder_quartic_gap_primitive (length : Nat)
    (hlength : 2 <= length) :
    (length + 1) * (length + 1) +
        4096 * length ^ 4 + primitiveReserve length <=
      decoderPotential length := by
  unfold decoderPotential primitiveReserve
  simp only [pow_succ]
  nlinarith

theorem decodeBinaryNatTrace_primitiveCostBound (bits : List Bool) :
    parserCostBoundWith (primitiveReserve bits.length)
      (decodeBinaryNatTrace bits) bits := by
  unfold parserCostBoundWith
  cases htrace : (decodeBinaryNatTrace bits).1 with
  | none =>
      have hcost := decodeBinaryNatTrace_cost_le bits
      have hbound := linear_plus_quadratic_le_decoderPotential bits.length
      omega
  | some result =>
      rcases result with ⟨value, suffix⟩
      have hdecode : decodeBinaryNat bits = some (value, suffix) := by
        rw [← decodeBinaryNatTrace_result bits]
        exact htrace
      have hconsume := decodeBinaryNat_consumes_two hdecode
      have hcost := decodeBinaryNatTrace_cost_le bits
      have hsuffix : suffix.length + 1 <= bits.length := by omega
      have hsuffixPow : (suffix.length + 1) ^ 4 <= bits.length ^ 4 :=
        Nat.pow_le_pow_left hsuffix 4
      have hgap := natDecoder_quartic_gap_primitive bits.length (by omega)
      unfold decoderPotential at *
      omega

theorem decodeBinaryNatTrace_parserCostBound (bits : List Bool) :
    parserCostBound (decodeBinaryNatTrace bits) bits := by
  have hstrong := decodeBinaryNatTrace_primitiveCostBound bits
  unfold parserCostBound parserCostBoundWith at *
  cases htrace : (decodeBinaryNatTrace bits).1 with
  | none =>
      simp [htrace] at hstrong ⊢
      unfold parserReserve primitiveReserve at *
      omega
  | some result =>
      rcases result with ⟨value, suffix⟩
      simp [htrace] at hstrong ⊢
      unfold parserReserve primitiveReserve at *
      omega

/-- Sequential vector parsing is amortized over the disjoint prefixes consumed
by its elements.  A successful empty vector accounts for the single `pure`
step through the additive `+ 1` on the right. -/
theorem decodeManyVectorTrace_potential
    {alpha : Type*}
    (decode : List Bool -> OptionTrace (alpha × List Bool))
    (hdecode : forall bits, parserCostBound (decode bits) bits) :
    forall (count : Nat) (bits : List Bool),
      match (decodeManyVectorTrace decode count bits).1 with
      | none =>
          (decodeManyVectorTrace decode count bits).2 <=
            decoderPotential bits.length
      | some (_, suffix) =>
          (decodeManyVectorTrace decode count bits).2 +
              decoderPotential suffix.length <=
            decoderPotential bits.length + 1
  | 0, bits => by
      simp only [decodeManyVectorTrace, tracePure]
      omega
  | count + 1, bits => by
      cases hheadResult : (decode bits).1 with
      | none =>
          have hheadBound :
              (decode bits).2 + 16 <= decoderPotential bits.length := by
            have hbound := hdecode bits
            simp [parserCostBound, parserCostBoundWith, hheadResult] at hbound
            unfold parserReserve at hbound
            omega
          simp [decodeManyVectorTrace, traceBind, hheadResult]
          omega
      | some headResult =>
          rcases headResult with ⟨head, afterHead⟩
          have hheadBound :
              (decode bits).2 + decoderPotential afterHead.length + 16 <=
                decoderPotential bits.length := by
            have hbound := hdecode bits
            simp [parserCostBound, parserCostBoundWith, hheadResult] at hbound
            unfold parserReserve at hbound
            omega
          have htail :=
            decodeManyVectorTrace_potential decode hdecode count afterHead
          cases htailResult :
              (decodeManyVectorTrace decode count afterHead).1 with
          | none =>
              have htailBound :
                  (decodeManyVectorTrace decode count afterHead).2 <=
                    decoderPotential afterHead.length := by
                simpa [htailResult] using htail
              simp [decodeManyVectorTrace, traceBind, hheadResult,
                htailResult]
              omega

          | some tailResult =>
              rcases tailResult with ⟨tail, suffix⟩
              have htailBound :
                  (decodeManyVectorTrace decode count afterHead).2 +
                      decoderPotential suffix.length <=
                    decoderPotential afterHead.length + 1 := by
                simpa [htailResult] using htail
              simp [decodeManyVectorTrace, traceBind, tracePure,
                hheadResult, htailResult]
              omega

theorem natDecoder_quartic_gap_sixtyFour (length : Nat)
    (hlength : 2 <= length) :
    (length + 1) * (length + 1) +
        4096 * length ^ 4 + 64 <=
      decoderPotential length := by
  unfold decoderPotential
  simp only [pow_succ]
  nlinarith

theorem quadratic_plus_sixtyFour_le_decoderPotential (length : Nat) :
    (length + 1) * (length + 1) + 64 <= decoderPotential length := by
  have hpowTwo : (length + 1) ^ 2 <= (length + 1) ^ 4 :=
    Nat.pow_le_pow_right (Nat.succ_pos length) (by omega)
  have hpowOne : 1 <= (length + 1) ^ 4 := by
    have := Nat.pow_le_pow_left (show 1 <= length + 1 by omega) 4
    norm_num at this ⊢
    exact this
  have hscaledOne := Nat.mul_le_mul_left 64 hpowOne
  unfold decoderPotential
  rw [← pow_two]
  omega

theorem decodeBinaryNatTrace_parserCostBound_sixtyFour
    (bits : List Bool) :
    parserCostBoundWith 64 (decodeBinaryNatTrace bits) bits := by
  unfold parserCostBoundWith
  cases htrace : (decodeBinaryNatTrace bits).1 with
  | none =>
      have hcost := decodeBinaryNatTrace_cost_le bits
      have hbound :=
        quadratic_plus_sixtyFour_le_decoderPotential bits.length
      omega
  | some result =>
      rcases result with ⟨value, suffix⟩
      have hdecode : decodeBinaryNat bits = some (value, suffix) := by
        rw [← decodeBinaryNatTrace_result bits]
        exact htrace
      have hconsume := decodeBinaryNat_consumes_two hdecode
      have hcost := decodeBinaryNatTrace_cost_le bits
      have hsuffix : suffix.length + 1 <= bits.length := by omega
      have hsuffixPow : (suffix.length + 1) ^ 4 <= bits.length ^ 4 :=
        Nat.pow_le_pow_left hsuffix 4
      have hgap :=
        natDecoder_quartic_gap_sixtyFour bits.length (by omega)
      unfold decoderPotential at *
      omega

theorem arithmeticFunc_decode_charge_le
    {arity code : Nat}
    {symbol : LO.FirstOrder.Language.Func ℒₒᵣ arity}
    (hdecode : (Encodable.decode₂ _ code :
      Option (LO.FirstOrder.Language.Func ℒₒᵣ arity)) = some symbol) :
    Nat.size arity + Nat.size code + 2 <= 5 := by
  have hsizeTwo : Nat.size 2 = 2 := by
    simpa using (Nat.size_pow (n := 1))
  rw [Encodable.decode₂_eq_some] at hdecode
  cases symbol with
  | zero =>
      change 0 = code at hdecode
      subst code
      simp
  | one =>
      change 1 = code at hdecode
      subst code
      simp
  | add =>
      change 0 = code at hdecode
      subst code
      simp [hsizeTwo]
  | mul =>
      change 1 = code at hdecode
      subst code
      simp [hsizeTwo]

theorem arithmeticRel_decode_charge_le
    {arity code : Nat}
    {symbol : LO.FirstOrder.Language.Rel ℒₒᵣ arity}
    (hdecode : (Encodable.decode₂ _ code :
      Option (LO.FirstOrder.Language.Rel ℒₒᵣ arity)) = some symbol) :
    Nat.size arity + Nat.size code + 2 <= 5 := by
  have hsizeTwo : Nat.size 2 = 2 := by
    simpa using (Nat.size_pow (n := 1))
  rw [Encodable.decode₂_eq_some] at hdecode
  cases symbol with
  | eq =>
      change 0 = code at hdecode
      subst code
      simp [hsizeTwo]
  | lt =>
      change 1 = code at hdecode
      subst code
      simp [hsizeTwo]

#print axioms decodeBinaryNatTrace_success_potential
#print axioms decodeBinaryNatTrace_failure_potential
#print axioms decodeManyVectorTrace_potential
#print axioms decodeBinaryNatTrace_parserCostBound_sixtyFour
#print axioms arithmeticFunc_decode_charge_le
#print axioms arithmeticRel_decode_charge_le

end FoundationCompactDecoderCostPotential
