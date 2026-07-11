import integration.FoundationCompactNatDecoderCost

/-!
# Cost traces for compact term and formula decoding
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactSyntaxDecoderCost

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactNatDecoderCost

abbrev OptionTrace (alpha : Type*) := Option alpha × Nat

def tracePure {alpha : Type*} (value : alpha) : OptionTrace alpha :=
  (some value, 1)

def traceFailure {alpha : Type*} : OptionTrace alpha :=
  (none, 1)

def traceLiftOption {alpha : Type*}
    (value : Option alpha) (cost : Nat) : OptionTrace alpha :=
  (value, cost + 1)

def traceBind {alpha beta : Type*}
    (source : OptionTrace alpha)
    (next : alpha -> OptionTrace beta) : OptionTrace beta :=
  match source.1 with
  | none => (none, source.2 + 1)
  | some value =>
      let result := next value
      (result.1, source.2 + result.2 + 1)

@[simp] theorem tracePure_result {alpha : Type*} (value : alpha) :
    (tracePure value).1 = some value := rfl

@[simp] theorem traceFailure_result {alpha : Type*} :
    (traceFailure : OptionTrace alpha).1 = none := rfl

@[simp] theorem traceLiftOption_result
    {alpha : Type*} (value : Option alpha) (cost : Nat) :
    (traceLiftOption value cost).1 = value := rfl

theorem traceBind_result {alpha beta : Type*}
    (source : OptionTrace alpha)
    (next : alpha -> OptionTrace beta) :
    (traceBind source next).1 = source.1.bind (fun value => (next value).1) := by
  cases hsource : source.1 <;> simp [traceBind, hsource]

def decodeManyVectorTrace {alpha : Type*}
    (decode : List Bool -> OptionTrace (alpha × List Bool)) :
    (count : Nat) -> List Bool ->
      OptionTrace (List.Vector alpha count × List Bool)
  | 0, bits => tracePure (List.Vector.nil, bits)
  | count + 1, bits =>
      traceBind (decode bits) fun headResult =>
        traceBind (decodeManyVectorTrace decode count headResult.2)
          fun tailResult =>
            tracePure (headResult.1 ::ᵥ tailResult.1, tailResult.2)

theorem decodeManyVectorTrace_result
    {alpha : Type*}
    (decodeTrace : List Bool -> OptionTrace (alpha × List Bool))
    (decode : List Bool -> Option (alpha × List Bool))
    (hdecode : forall bits, (decodeTrace bits).1 = decode bits) :
    forall (count : Nat) (bits : List Bool),
      (decodeManyVectorTrace decodeTrace count bits).1 =
        decodeManyVector decode count bits
  | 0, bits => by simp [decodeManyVectorTrace, decodeManyVector, tracePure]
  | count + 1, bits => by
      simp only [decodeManyVectorTrace, decodeManyVector, traceBind_result,
        tracePure_result]
      rw [hdecode bits]
      cases hhead : decode bits with
      | none => simp
      | some headResult =>
          rcases headResult with ⟨head, afterHead⟩
          simp only [Option.bind_some]
          rw [decodeManyVectorTrace_result decodeTrace decode hdecode
            count afterHead]
          cases htail : decodeManyVector decode count afterHead with
          | none => simp [htail]
          | some tailResult =>
              rcases tailResult with ⟨tail, afterTail⟩
              simp [htail]

def decodeCompactTermTrace (arity : Nat) :
    Nat -> List Bool ->
      OptionTrace
        (LO.FirstOrder.ArithmeticSemiterm Nat arity × List Bool)
  | 0, _ => traceFailure
  | fuel + 1, bits =>
      traceBind (decodeBinaryNatTrace bits) fun tagResult =>
        match tagResult.1 with
        | 0 =>
            traceBind (decodeBinaryNatTrace tagResult.2) fun indexResult =>
              if hindex : indexResult.1 < arity then
                tracePure
                  (Semiterm.bvar ⟨indexResult.1, hindex⟩, indexResult.2)
              else traceFailure
        | 1 =>
            traceBind (decodeBinaryNatTrace tagResult.2) fun indexResult =>
              tracePure (Semiterm.fvar indexResult.1, indexResult.2)
        | 2 =>
            traceBind (decodeBinaryNatTrace tagResult.2) fun arityResult =>
              traceBind (decodeBinaryNatTrace arityResult.2)
                fun symbolResult =>
                  traceBind
                    (traceLiftOption
                      (Encodable.decode₂ _ symbolResult.1 :
                        Option (LO.FirstOrder.Language.Func
                          ℒₒᵣ arityResult.1))
                      (Nat.size arityResult.1 + Nat.size symbolResult.1 + 1))
                    fun functionSymbol =>
                      traceBind
                        (decodeManyVectorTrace
                          (decodeCompactTermTrace arity fuel)
                          arityResult.1 symbolResult.2)
                        fun argumentsResult =>
                          tracePure
                            (Semiterm.func functionSymbol
                              argumentsResult.1.get,
                              argumentsResult.2)
        | _ => traceFailure

theorem decodeCompactTermTrace_result
    (arity fuel : Nat) (bits : List Bool) :
    (decodeCompactTermTrace arity fuel bits).1 =
      decodeCompactTerm arity fuel bits := by
  induction fuel generalizing bits with
  | zero => simp [decodeCompactTermTrace, decodeCompactTerm, traceFailure]
  | succ fuel ih =>
      have hmany := decodeManyVectorTrace_result
        (decodeCompactTermTrace arity fuel)
        (decodeCompactTerm arity fuel) ih
      simp only [decodeCompactTermTrace, decodeCompactTerm,
        traceBind_result, tracePure_result, traceFailure_result,
        traceLiftOption_result, decodeBinaryNatTrace_result]
      cases htag : decodeBinaryNat bits with
      | none => simp
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          simp only [Option.bind_eq_bind, Option.bind_some]
          rcases tag with (_ | _ | _ | tag)
          · simp only [traceBind_result, decodeBinaryNatTrace_result]
            cases hindexResult : decodeBinaryNat afterTag with
            | none => simp
            | some indexResult =>
                rcases indexResult with ⟨index, afterIndex⟩
                simp only [Option.bind_some]
                split <;> rfl
          · simp [traceBind_result, tracePure_result,
              decodeBinaryNatTrace_result]
          · simp [traceBind_result, tracePure_result, traceFailure_result,
              traceLiftOption_result, decodeBinaryNatTrace_result, hmany]
          ·
            simp [traceBind_result, tracePure_result, traceFailure_result,
              traceLiftOption_result, Option.bind_some, Option.bind_none,
              decodeBinaryNatTrace_result]

def decodeCompactFormulaTrace (arity : Nat) :
    Nat -> List Bool ->
      OptionTrace
        (LO.FirstOrder.ArithmeticSemiformula Nat arity × List Bool)
  | 0, _ => traceFailure
  | fuel + 1, bits =>
      traceBind (decodeBinaryNatTrace bits) fun tagResult =>
        match tagResult.1 with
        | 0 =>
            traceBind (decodeBinaryNatTrace tagResult.2) fun arityResult =>
              traceBind (decodeBinaryNatTrace arityResult.2)
                fun symbolResult =>
                  traceBind
                    (traceLiftOption
                      (Encodable.decode₂ _ symbolResult.1 :
                        Option (LO.FirstOrder.Language.Rel
                          ℒₒᵣ arityResult.1))
                      (Nat.size arityResult.1 + Nat.size symbolResult.1 + 1))
                    fun relationSymbol =>
                      traceBind
                        (decodeManyVectorTrace
                          (decodeCompactTermTrace arity fuel)
                          arityResult.1 symbolResult.2)
                        fun argumentsResult =>
                          tracePure
                            (Semiformula.rel relationSymbol
                              argumentsResult.1.get,
                              argumentsResult.2)
        | 1 =>
            traceBind (decodeBinaryNatTrace tagResult.2) fun arityResult =>
              traceBind (decodeBinaryNatTrace arityResult.2)
                fun symbolResult =>
                  traceBind
                    (traceLiftOption
                      (Encodable.decode₂ _ symbolResult.1 :
                        Option (LO.FirstOrder.Language.Rel
                          ℒₒᵣ arityResult.1))
                      (Nat.size arityResult.1 + Nat.size symbolResult.1 + 1))
                    fun relationSymbol =>
                      traceBind
                        (decodeManyVectorTrace
                          (decodeCompactTermTrace arity fuel)
                          arityResult.1 symbolResult.2)
                        fun argumentsResult =>
                          tracePure
                            (Semiformula.nrel relationSymbol
                              argumentsResult.1.get,
                              argumentsResult.2)
        | 2 => tracePure (⊤, tagResult.2)
        | 3 => tracePure (⊥, tagResult.2)
        | 4 =>
            traceBind (decodeCompactFormulaTrace arity fuel tagResult.2)
              fun leftResult =>
                traceBind
                  (decodeCompactFormulaTrace arity fuel leftResult.2)
                  fun rightResult =>
                    tracePure
                      (leftResult.1 ⋏ rightResult.1, rightResult.2)
        | 5 =>
            traceBind (decodeCompactFormulaTrace arity fuel tagResult.2)
              fun leftResult =>
                traceBind
                  (decodeCompactFormulaTrace arity fuel leftResult.2)
                  fun rightResult =>
                    tracePure
                      (leftResult.1 ⋎ rightResult.1, rightResult.2)
        | 6 =>
            traceBind
              (decodeCompactFormulaTrace (arity + 1) fuel tagResult.2)
              fun bodyResult =>
                tracePure (∀⁰ bodyResult.1, bodyResult.2)
        | 7 =>
            traceBind
              (decodeCompactFormulaTrace (arity + 1) fuel tagResult.2)
              fun bodyResult =>
                tracePure (∃⁰ bodyResult.1, bodyResult.2)
        | _ => traceFailure

theorem decodeCompactFormulaTrace_result
    (arity fuel : Nat) (bits : List Bool) :
    (decodeCompactFormulaTrace arity fuel bits).1 =
      decodeCompactFormula arity fuel bits := by
  induction fuel generalizing arity bits with
  | zero => simp [decodeCompactFormulaTrace, decodeCompactFormula,
      traceFailure]
  | succ fuel ih =>
      have hterm (termArity : Nat) := decodeCompactTermTrace_result
        termArity fuel
      have hmany (termArity : Nat) := decodeManyVectorTrace_result
        (decodeCompactTermTrace termArity fuel)
        (decodeCompactTerm termArity fuel) (hterm termArity)
      simp only [decodeCompactFormulaTrace, decodeCompactFormula,
        traceBind_result, tracePure_result, traceFailure_result,
        traceLiftOption_result, decodeBinaryNatTrace_result]
      cases htag : decodeBinaryNat bits with
      | none => simp
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          simp only [Option.bind_eq_bind, Option.bind_some]
          rcases tag with (_ | _ | _ | _ | _ | _ | _ | _ | tag) <;>
            simp [traceBind_result, tracePure_result, traceFailure_result,
              traceLiftOption_result, Option.bind_some, Option.bind_none,
              decodeBinaryNatTrace_result, hmany, ih]

#print axioms decodeManyVectorTrace_result
#print axioms decodeCompactTermTrace_result
#print axioms decodeCompactFormulaTrace_result

end FoundationCompactSyntaxDecoderCost
