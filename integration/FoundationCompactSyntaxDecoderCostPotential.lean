import integration.FoundationCompactDecoderCostPotential

/-!
# Amortized cost bounds for compact term and formula decoding
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactSyntaxDecoderCostPotential

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactVerifierStructuralBound
open FoundationCompactCanonicalDecodeLength
open FoundationCompactNatDecoderCost
open FoundationCompactSyntaxDecoderCost
open FoundationCompactDecoderCostPotential

theorem decodedNatPair_charge_le
    {bits afterFirst afterSecond : List Bool}
    {first second : Nat}
    (hfirst : decodeBinaryNat bits = some (first, afterFirst))
    (hsecond : decodeBinaryNat afterFirst = some (second, afterSecond)) :
    Nat.size first + Nat.size second + 2 <= bits.length := by
  have hfirstLength := decodeBinaryNat_canonical_length_le hfirst
  have hsecondLength := decodeBinaryNat_canonical_length_le hsecond
  rw [binaryNatCode_length] at hfirstLength hsecondLength
  omega

theorem decodeCompactTermTrace_suffix_le
    {arity fuel : Nat} {bits suffix : List Bool}
    {term : LO.FirstOrder.ArithmeticSemiterm Nat arity}
    (htrace : (decodeCompactTermTrace arity fuel bits).1 =
      some (term, suffix)) :
    suffix.length <= bits.length := by
  have hdecode : decodeCompactTerm arity fuel bits = some (term, suffix) := by
    rw [← decodeCompactTermTrace_result arity fuel]
    exact htrace
  have hbound := decodeCompactTerm_symbolCount_le hdecode
  omega

theorem decodeCompactFormulaTrace_suffix_le
    {arity fuel : Nat} {bits suffix : List Bool}
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat arity}
    (htrace : (decodeCompactFormulaTrace arity fuel bits).1 =
      some (formula, suffix)) :
    suffix.length <= bits.length := by
  have hdecode :
      decodeCompactFormula arity fuel bits = some (formula, suffix) := by
    rw [← decodeCompactFormulaTrace_result arity fuel]
    exact htrace
  have hbound := decodeCompactFormula_symbolCount_le hdecode
  omega

theorem seventeen_le_decoderPotential (length : Nat) :
    17 <= decoderPotential length := by
  have hbound := quadratic_plus_sixteen_le_decoderPotential length
  have hone : 1 <= (length + 1) * (length + 1) := by nlinarith
  omega

theorem one_add_parserReserve_le_decoderPotential (length : Nat) :
    1 + parserReserve length <= decoderPotential length := by
  have hbound := linear_plus_quadratic_le_decoderPotential length
  have hone : 1 <= (length + 1) * (length + 1) := by nlinarith
  unfold parserReserve primitiveReserve at *
  omega

theorem decodeCompactTermTrace_parserCostBound :
    forall (arity fuel : Nat) (bits : List Bool),
      parserCostBound (decodeCompactTermTrace arity fuel bits) bits := by
  intro arity fuel
  induction fuel generalizing arity with
  | zero =>
      intro bits
      unfold parserCostBound parserCostBoundWith
      simp [decodeCompactTermTrace, traceFailure]
      exact one_add_parserReserve_le_decoderPotential bits.length
  | succ fuel ih =>
      intro bits
      have htagStrong := decodeBinaryNatTrace_primitiveCostBound bits
      cases htagTrace : (decodeBinaryNatTrace bits).1 with
      | none =>
          have htagBound :
              (decodeBinaryNatTrace bits).2 + primitiveReserve bits.length <=
                decoderPotential bits.length := by
            simpa [parserCostBoundWith, htagTrace] using htagStrong
          unfold parserCostBound parserCostBoundWith
          simp [decodeCompactTermTrace, traceBind, htagTrace]
          unfold parserReserve primitiveReserve at *
          omega
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          have htagBound :
              (decodeBinaryNatTrace bits).2 +
                  decoderPotential afterTag.length +
                  primitiveReserve bits.length <=
                decoderPotential bits.length := by
            simpa [parserCostBoundWith, htagTrace] using htagStrong
          have htagDecode :
              decodeBinaryNat bits = some (tag, afterTag) := by
            rw [← decodeBinaryNatTrace_result bits]
            exact htagTrace
          have htagConsume := decodeBinaryNat_consumes_two htagDecode
          unfold parserCostBound parserCostBoundWith
          simp only [decodeCompactTermTrace, traceBind, htagTrace]
          rcases tag with (_ | _ | _ | tag)
          · cases hindexTrace : (decodeBinaryNatTrace afterTag).1 with
            | none =>
                have hindex := decodeBinaryNatTrace_parserCostBound afterTag
                simp [parserCostBound, parserCostBoundWith, hindexTrace]
                  at hindex
                simp
                unfold parserReserve primitiveReserve at *
                omega
            | some indexResult =>
                rcases indexResult with ⟨index, suffix⟩
                have hindex := decodeBinaryNatTrace_parserCostBound afterTag
                simp [parserCostBound, parserCostBoundWith, hindexTrace]
                  at hindex
                by_cases hindexBound : index < arity <;>
                  simp [tracePure, traceFailure, hindexBound] <;>
                  unfold parserReserve primitiveReserve at * <;>
                  omega
          · cases hindexTrace : (decodeBinaryNatTrace afterTag).1 with
            | none =>
                have hindex := decodeBinaryNatTrace_parserCostBound afterTag
                simp [parserCostBound, parserCostBoundWith, hindexTrace]
                  at hindex
                simp
                unfold parserReserve primitiveReserve at *
                omega
            | some indexResult =>
                rcases indexResult with ⟨index, suffix⟩
                have hindex := decodeBinaryNatTrace_parserCostBound afterTag
                simp [parserCostBound, parserCostBoundWith, hindexTrace]
                  at hindex
                simp [tracePure]
                unfold parserReserve primitiveReserve at *
                omega
          · cases harityTrace : (decodeBinaryNatTrace afterTag).1 with
            | none =>
                have harity := decodeBinaryNatTrace_parserCostBound afterTag
                simp [parserCostBound, parserCostBoundWith, harityTrace]
                  at harity
                simp
                unfold parserReserve primitiveReserve at *
                omega
            | some arityResult =>
                rcases arityResult with ⟨symbolArity, afterArity⟩
                have harity := decodeBinaryNatTrace_parserCostBound afterTag
                simp [parserCostBound, parserCostBoundWith, harityTrace]
                  at harity
                cases hsymbolTrace : (decodeBinaryNatTrace afterArity).1 with
                | none =>
                    have hsymbol :=
                      decodeBinaryNatTrace_parserCostBound afterArity
                    simp [parserCostBound, parserCostBoundWith, hsymbolTrace]
                      at hsymbol
                    simp [hsymbolTrace]
                    unfold parserReserve primitiveReserve at *
                    omega
                | some symbolResult =>
                    rcases symbolResult with ⟨symbolCode, afterSymbol⟩
                    have hsymbol :=
                      decodeBinaryNatTrace_parserCostBound afterArity
                    simp [parserCostBound, parserCostBoundWith, hsymbolTrace]
                      at hsymbol
                    have harityDecode :
                        decodeBinaryNat afterTag =
                          some (symbolArity, afterArity) := by
                      rw [← decodeBinaryNatTrace_result afterTag]
                      exact harityTrace
                    have hsymbolDecode :
                        decodeBinaryNat afterArity =
                          some (symbolCode, afterSymbol) := by
                      rw [← decodeBinaryNatTrace_result afterArity]
                      exact hsymbolTrace
                    have hdecodeCharge :=
                      decodedNatPair_charge_le harityDecode hsymbolDecode
                    cases hfunction :
                        (Encodable.decode₂ _ symbolCode :
                          Option (LO.FirstOrder.Language.Func
                            ℒₒᵣ symbolArity)) with
                    | none =>
                        simp [hsymbolTrace, hfunction]
                        unfold parserReserve primitiveReserve at *
                        omega
                    | some functionSymbol =>
                        have hfunctionCharge :=
                          arithmeticFunc_decode_charge_le hfunction
                        have hargument := fun argumentBits =>
                          ih arity argumentBits
                        have hmany := decodeManyVectorTrace_potential
                          (decodeCompactTermTrace arity fuel) hargument
                          symbolArity afterSymbol
                        cases hmanyResult :
                            (decodeManyVectorTrace
                              (decodeCompactTermTrace arity fuel)
                              symbolArity afterSymbol).1 with
                        | none =>
                            simp [hmanyResult] at hmany
                            simp [hsymbolTrace, hfunction, hmanyResult]
                            unfold parserReserve primitiveReserve at *
                            omega
                        | some argumentsResult =>
                            rcases argumentsResult with ⟨arguments, suffix⟩
                            simp [hmanyResult] at hmany
                            simp [tracePure, hsymbolTrace, hfunction,
                              hmanyResult]
                            unfold parserReserve primitiveReserve at *
                            omega
          · simp [traceFailure]
            unfold parserReserve primitiveReserve at *
            omega

theorem decodeCompactFormulaTrace_parserCostBound :
    forall (arity fuel : Nat) (bits : List Bool),
      parserCostBound (decodeCompactFormulaTrace arity fuel bits) bits := by
  intro arity fuel
  induction fuel generalizing arity with
  | zero =>
      intro bits
      unfold parserCostBound parserCostBoundWith
      simp [decodeCompactFormulaTrace, traceFailure]
      exact one_add_parserReserve_le_decoderPotential bits.length
  | succ fuel ih =>
      intro bits
      have htagStrong := decodeBinaryNatTrace_primitiveCostBound bits
      cases htagTrace : (decodeBinaryNatTrace bits).1 with
      | none =>
          have htagBound :
              (decodeBinaryNatTrace bits).2 + primitiveReserve bits.length <=
                decoderPotential bits.length := by
            simpa [parserCostBoundWith, htagTrace] using htagStrong
          unfold parserCostBound parserCostBoundWith
          simp [decodeCompactFormulaTrace, traceBind, htagTrace]
          unfold parserReserve primitiveReserve at *
          omega
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          have htagBound :
              (decodeBinaryNatTrace bits).2 +
                  decoderPotential afterTag.length +
                  primitiveReserve bits.length <=
                decoderPotential bits.length := by
            simpa [parserCostBoundWith, htagTrace] using htagStrong
          have htagDecode :
              decodeBinaryNat bits = some (tag, afterTag) := by
            rw [← decodeBinaryNatTrace_result bits]
            exact htagTrace
          have htagConsume := decodeBinaryNat_consumes_two htagDecode
          unfold parserCostBound parserCostBoundWith
          simp only [decodeCompactFormulaTrace, traceBind, htagTrace]
          rcases tag with (_ | _ | _ | _ | _ | _ | _ | _ | tag)
          · cases harityTrace : (decodeBinaryNatTrace afterTag).1 with
            | none =>
                have harity := decodeBinaryNatTrace_parserCostBound afterTag
                simp [parserCostBound, parserCostBoundWith, harityTrace]
                  at harity
                simp
                unfold parserReserve primitiveReserve at *
                omega
            | some arityResult =>
                rcases arityResult with ⟨relationArity, afterArity⟩
                have harity := decodeBinaryNatTrace_parserCostBound afterTag
                simp [parserCostBound, parserCostBoundWith, harityTrace]
                  at harity
                cases hsymbolTrace : (decodeBinaryNatTrace afterArity).1 with
                | none =>
                    have hsymbol :=
                      decodeBinaryNatTrace_parserCostBound afterArity
                    simp [parserCostBound, parserCostBoundWith, hsymbolTrace]
                      at hsymbol
                    simp [hsymbolTrace]
                    unfold parserReserve primitiveReserve at *
                    omega
                | some symbolResult =>
                    rcases symbolResult with ⟨symbolCode, afterSymbol⟩
                    have hsymbol :=
                      decodeBinaryNatTrace_parserCostBound afterArity
                    simp [parserCostBound, parserCostBoundWith, hsymbolTrace]
                      at hsymbol
                    have harityDecode :
                        decodeBinaryNat afterTag =
                          some (relationArity, afterArity) := by
                      rw [← decodeBinaryNatTrace_result afterTag]
                      exact harityTrace
                    have hsymbolDecode :
                        decodeBinaryNat afterArity =
                          some (symbolCode, afterSymbol) := by
                      rw [← decodeBinaryNatTrace_result afterArity]
                      exact hsymbolTrace
                    have hdecodeCharge :=
                      decodedNatPair_charge_le harityDecode hsymbolDecode
                    cases hrelation :
                        (Encodable.decode₂ _ symbolCode :
                          Option (LO.FirstOrder.Language.Rel
                            ℒₒᵣ relationArity)) with
                    | none =>
                        simp [hsymbolTrace, hrelation]
                        unfold parserReserve primitiveReserve at *
                        omega
                    | some relationSymbol =>
                        have hrelationCharge :=
                          arithmeticRel_decode_charge_le hrelation
                        have hargument := fun argumentBits =>
                          decodeCompactTermTrace_parserCostBound
                            arity fuel argumentBits
                        have hmany := decodeManyVectorTrace_potential
                          (decodeCompactTermTrace arity fuel) hargument
                          relationArity afterSymbol
                        cases hmanyResult :
                            (decodeManyVectorTrace
                              (decodeCompactTermTrace arity fuel)
                              relationArity afterSymbol).1 with
                        | none =>
                            simp [hmanyResult] at hmany
                            simp [hsymbolTrace, hrelation, hmanyResult]
                            unfold parserReserve primitiveReserve at *
                            omega
                        | some argumentsResult =>
                            rcases argumentsResult with ⟨arguments, suffix⟩
                            simp [hmanyResult] at hmany
                            simp [tracePure, hsymbolTrace, hrelation,
                              hmanyResult]
                            unfold parserReserve primitiveReserve at *
                            omega
          · cases harityTrace : (decodeBinaryNatTrace afterTag).1 with
            | none =>
                have harity := decodeBinaryNatTrace_parserCostBound afterTag
                simp [parserCostBound, parserCostBoundWith, harityTrace]
                  at harity
                simp
                unfold parserReserve primitiveReserve at *
                omega
            | some arityResult =>
                rcases arityResult with ⟨relationArity, afterArity⟩
                have harity := decodeBinaryNatTrace_parserCostBound afterTag
                simp [parserCostBound, parserCostBoundWith, harityTrace]
                  at harity
                cases hsymbolTrace : (decodeBinaryNatTrace afterArity).1 with
                | none =>
                    have hsymbol :=
                      decodeBinaryNatTrace_parserCostBound afterArity
                    simp [parserCostBound, parserCostBoundWith, hsymbolTrace]
                      at hsymbol
                    simp [hsymbolTrace]
                    unfold parserReserve primitiveReserve at *
                    omega
                | some symbolResult =>
                    rcases symbolResult with ⟨symbolCode, afterSymbol⟩
                    have hsymbol :=
                      decodeBinaryNatTrace_parserCostBound afterArity
                    simp [parserCostBound, parserCostBoundWith, hsymbolTrace]
                      at hsymbol
                    have harityDecode :
                        decodeBinaryNat afterTag =
                          some (relationArity, afterArity) := by
                      rw [← decodeBinaryNatTrace_result afterTag]
                      exact harityTrace
                    have hsymbolDecode :
                        decodeBinaryNat afterArity =
                          some (symbolCode, afterSymbol) := by
                      rw [← decodeBinaryNatTrace_result afterArity]
                      exact hsymbolTrace
                    have hdecodeCharge :=
                      decodedNatPair_charge_le harityDecode hsymbolDecode
                    cases hrelation :
                        (Encodable.decode₂ _ symbolCode :
                          Option (LO.FirstOrder.Language.Rel
                            ℒₒᵣ relationArity)) with
                    | none =>
                        simp [hsymbolTrace, hrelation]
                        unfold parserReserve primitiveReserve at *
                        omega
                    | some relationSymbol =>
                        have hrelationCharge :=
                          arithmeticRel_decode_charge_le hrelation
                        have hargument := fun argumentBits =>
                          decodeCompactTermTrace_parserCostBound
                            arity fuel argumentBits
                        have hmany := decodeManyVectorTrace_potential
                          (decodeCompactTermTrace arity fuel) hargument
                          relationArity afterSymbol
                        cases hmanyResult :
                            (decodeManyVectorTrace
                              (decodeCompactTermTrace arity fuel)
                              relationArity afterSymbol).1 with
                        | none =>
                            simp [hmanyResult] at hmany
                            simp [hsymbolTrace, hrelation, hmanyResult]
                            unfold parserReserve primitiveReserve at *
                            omega
                        | some argumentsResult =>
                            rcases argumentsResult with ⟨arguments, suffix⟩
                            simp [hmanyResult] at hmany
                            simp [tracePure, hsymbolTrace, hrelation,
                              hmanyResult]
                            unfold parserReserve primitiveReserve at *
                            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · cases hleftTrace :
                (decodeCompactFormulaTrace arity fuel afterTag).1 with
            | none =>
                have hleft := ih arity afterTag
                simp [parserCostBound, parserCostBoundWith, hleftTrace]
                  at hleft
                simp
                unfold parserReserve primitiveReserve at *
                omega
            | some leftResult =>
                rcases leftResult with ⟨leftFormula, afterLeft⟩
                have hleft := ih arity afterTag
                simp [parserCostBound, parserCostBoundWith, hleftTrace]
                  at hleft
                cases hrightTrace :
                    (decodeCompactFormulaTrace arity fuel afterLeft).1 with
                | none =>
                    have hright := ih arity afterLeft
                    simp [parserCostBound, parserCostBoundWith, hrightTrace]
                      at hright
                    simp [hrightTrace]
                    unfold parserReserve primitiveReserve at *
                    omega
                | some rightResult =>
                    rcases rightResult with ⟨rightFormula, suffix⟩
                    have hright := ih arity afterLeft
                    simp [parserCostBound, parserCostBoundWith, hrightTrace]
                      at hright
                    simp [tracePure, hrightTrace]
                    unfold parserReserve primitiveReserve at *
                    omega
          · cases hleftTrace :
                (decodeCompactFormulaTrace arity fuel afterTag).1 with
            | none =>
                have hleft := ih arity afterTag
                simp [parserCostBound, parserCostBoundWith, hleftTrace]
                  at hleft
                simp
                unfold parserReserve primitiveReserve at *
                omega
            | some leftResult =>
                rcases leftResult with ⟨leftFormula, afterLeft⟩
                have hleft := ih arity afterTag
                simp [parserCostBound, parserCostBoundWith, hleftTrace]
                  at hleft
                cases hrightTrace :
                    (decodeCompactFormulaTrace arity fuel afterLeft).1 with
                | none =>
                    have hright := ih arity afterLeft
                    simp [parserCostBound, parserCostBoundWith, hrightTrace]
                      at hright
                    simp [hrightTrace]
                    unfold parserReserve primitiveReserve at *
                    omega
                | some rightResult =>
                    rcases rightResult with ⟨rightFormula, suffix⟩
                    have hright := ih arity afterLeft
                    simp [parserCostBound, parserCostBoundWith, hrightTrace]
                      at hright
                    simp [tracePure, hrightTrace]
                    unfold parserReserve primitiveReserve at *
                    omega
          · cases hbodyTrace :
                (decodeCompactFormulaTrace (arity + 1) fuel afterTag).1 with
            | none =>
                have hbody := ih (arity + 1) afterTag
                simp [parserCostBound, parserCostBoundWith, hbodyTrace]
                  at hbody
                simp
                unfold parserReserve primitiveReserve at *
                omega
            | some bodyResult =>
                rcases bodyResult with ⟨body, suffix⟩
                have hbody := ih (arity + 1) afterTag
                simp [parserCostBound, parserCostBoundWith, hbodyTrace]
                  at hbody
                simp [tracePure]
                unfold parserReserve primitiveReserve at *
                omega
          · cases hbodyTrace :
                (decodeCompactFormulaTrace (arity + 1) fuel afterTag).1 with
            | none =>
                have hbody := ih (arity + 1) afterTag
                simp [parserCostBound, parserCostBoundWith, hbodyTrace]
                  at hbody
                simp
                unfold parserReserve primitiveReserve at *
                omega
            | some bodyResult =>
                rcases bodyResult with ⟨body, suffix⟩
                have hbody := ih (arity + 1) afterTag
                simp [parserCostBound, parserCostBoundWith, hbodyTrace]
                  at hbody
                simp [tracePure]
                unfold parserReserve primitiveReserve at *
                omega
          · simp [traceFailure]
            unfold parserReserve primitiveReserve at *
            omega

#print axioms decodedNatPair_charge_le
#print axioms decodeCompactTermTrace_suffix_le
#print axioms decodeCompactFormulaTrace_suffix_le
#print axioms decodeCompactTermTrace_parserCostBound
#print axioms decodeCompactFormulaTrace_parserCostBound

end FoundationCompactSyntaxDecoderCostPotential
