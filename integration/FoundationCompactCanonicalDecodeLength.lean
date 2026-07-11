import integration.FoundationCompactSyntaxTransformationBounds

/-!
# Canonical re-encoding length of decoded compact syntax

Successful decoding cannot hide large numeric labels behind a shorter input:
the canonical re-encoding of every decoded object fits in the consumed prefix.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCanonicalDecodeLength

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactVerifierStructuralBound

theorem binaryNatCode_length (value : Nat) :
    (binaryNatCode value).length = 2 * Nat.size value + 2 := by
  simp [binaryNatCode, Nat.size_eq_bits_len, List.length_flatMap,
    Nat.mul_comm]

theorem binaryNatCode_bit_length_le
    (bit : Bool) (value : Nat) :
    (binaryNatCode (Nat.bit bit value)).length <=
      (binaryNatCode value).length + 2 := by
  rw [binaryNatCode_length, binaryNatCode_length]
  by_cases hzero : Nat.bit bit value = 0
  · rw [hzero]
    simp
  · rw [Nat.size_bit hzero]
    omega

theorem decodeBinaryNat_canonical_length_le
    {bits suffix : List Bool} {value : Nat}
    (hdecode : decodeBinaryNat bits = some (value, suffix)) :
    (binaryNatCode value).length + suffix.length <= bits.length := by
  induction bits using List.twoStepInduction generalizing value suffix with
  | nil => simp [decodeBinaryNat] at hdecode
  | singleton bit => cases bit <;> simp [decodeBinaryNat] at hdecode
  | cons_cons first second rest ihRest ihCons =>
      cases first with
      | false =>
          cases second with
          | false =>
              simp [decodeBinaryNat] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              simp [binaryNatCode]
              omega
          | true => simp [decodeBinaryNat] at hdecode
      | true =>
          cases hrest : decodeBinaryNat rest with
          | none => simp [decodeBinaryNat, hrest] at hdecode
          | some result =>
              rcases result with ⟨restValue, restSuffix⟩
              have htail := ihRest hrest
              have hbit := binaryNatCode_bit_length_le second restValue
              simp [decodeBinaryNat, hrest] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              simp only [List.length_cons]
              omega

theorem decodeCompactTerm_canonical_length_le :
    forall {arity fuel bits suffix term},
      decodeCompactTerm arity fuel bits = some (term, suffix) ->
      (binaryTermCode term).length + suffix.length <= bits.length := by
  intro arity fuel
  induction fuel generalizing arity with
  | zero =>
      intro bits suffix term hdecode
      simp [decodeCompactTerm] at hdecode
  | succ fuel ih =>
      intro bits suffix term hdecode
      cases htag : decodeBinaryNat bits with
      | none => simp [decodeCompactTerm, htag] at hdecode
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          have htagLength := decodeBinaryNat_canonical_length_le htag
          cases tag with
          | zero =>
              cases hindex : decodeBinaryNat afterTag with
              | none => simp [decodeCompactTerm, htag, hindex] at hdecode
              | some indexResult =>
                  rcases indexResult with ⟨index, afterIndex⟩
                  by_cases hindexBound : index < arity
                  · simp [decodeCompactTerm, htag, hindex,
                      hindexBound] at hdecode
                    rcases hdecode with ⟨rfl, rfl⟩
                    have hindexLength :=
                      decodeBinaryNat_canonical_length_le hindex
                    simp only [binaryTermCode, List.length_append]
                    omega
                  · simp [decodeCompactTerm, htag, hindex,
                      hindexBound] at hdecode
          | succ tag =>
              cases tag with
              | zero =>
                  cases hindex : decodeBinaryNat afterTag with
                  | none => simp [decodeCompactTerm, htag, hindex] at hdecode
                  | some indexResult =>
                      rcases indexResult with ⟨index, afterIndex⟩
                      simp [decodeCompactTerm, htag, hindex] at hdecode
                      rcases hdecode with ⟨rfl, rfl⟩
                      have hindexLength :=
                        decodeBinaryNat_canonical_length_le hindex
                      change (binaryNatCode 1).length +
                          afterTag.length <= bits.length at htagLength
                      simp only [binaryTermCode, List.length_append]
                      omega
              | succ tag =>
                  cases tag with
                  | zero =>
                      cases harity : decodeBinaryNat afterTag with
                      | none => simp [decodeCompactTerm, htag, harity] at hdecode
                      | some arityResult =>
                          rcases arityResult with ⟨functionArity, afterArity⟩
                          cases hfunction : decodeBinaryNat afterArity with
                          | none =>
                              simp [decodeCompactTerm, htag, harity,
                                hfunction] at hdecode
                          | some functionResult =>
                              rcases functionResult with
                                ⟨functionCode, afterFunction⟩
                              cases hsymbol :
                                  (Encodable.decode₂ _ functionCode :
                                    Option (LO.FirstOrder.Language.Func
                                      ℒₒᵣ functionArity)) with
                              | none =>
                                  simp [decodeCompactTerm, htag, harity,
                                    hfunction, hsymbol] at hdecode
                              | some functionSymbol =>
                                  cases harguments :
                                      decodeManyVector
                                        (decodeCompactTerm arity fuel)
                                        functionArity afterFunction with
                                  | none =>
                                      simp [decodeCompactTerm, htag, harity,
                                        hfunction, hsymbol, harguments]
                                        at hdecode
                                  | some argumentsResult =>
                                      rcases argumentsResult with
                                        ⟨arguments, afterArguments⟩
                                      simp [decodeCompactTerm, htag, harity,
                                        hfunction, hsymbol, harguments]
                                        at hdecode
                                      rcases hdecode with ⟨rfl, rfl⟩
                                      have hargumentsLength :=
                                        decodeManyVector_weight_le
                                          (decodeCompactTerm arity fuel)
                                          (fun term =>
                                            (binaryTermCode term).length)
                                          (fun h => ih h) harguments
                                      rw [vector_map_sum_eq_finset_sum]
                                        at hargumentsLength
                                      have harityLength :=
                                        decodeBinaryNat_canonical_length_le
                                          harity
                                      have hfunctionLength :=
                                        decodeBinaryNat_canonical_length_le
                                          hfunction
                                      have hencode :
                                          Encodable.encode functionSymbol =
                                            functionCode :=
                                        Encodable.decode₂_eq_some.mp hsymbol
                                      have hflatten :=
                                        length_flatten_ofFn
                                          (fun index => binaryTermCode
                                            (arguments.get index))
                                      have hargumentsLength' :
                                          (List.ofFn (fun index =>
                                              binaryTermCode
                                                (arguments.get index))).flatten.length +
                                              afterArguments.length <=
                                            afterFunction.length := by
                                        rw [hflatten]
                                        exact hargumentsLength
                                      change (binaryNatCode 2).length +
                                          afterTag.length <= bits.length
                                        at htagLength
                                      simp only [binaryTermCode,
                                        List.length_append]
                                      rw [hencode]
                                      omega
                  | succ tag =>
                      simp [decodeCompactTerm, htag] at hdecode

theorem decodeCompactFormula_canonical_length_le :
    forall {arity fuel bits suffix formula},
      decodeCompactFormula arity fuel bits = some (formula, suffix) ->
      (binaryFormulaCode formula).length + suffix.length <= bits.length := by
  intro arity fuel
  induction fuel generalizing arity with
  | zero =>
      intro bits suffix formula hdecode
      simp [decodeCompactFormula] at hdecode
  | succ fuel ih =>
      intro bits suffix formula hdecode
      cases htag : decodeBinaryNat bits with
      | none => simp [decodeCompactFormula, htag] at hdecode
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          have htagLength := decodeBinaryNat_canonical_length_le htag
          cases tag with
          | zero =>
              cases harity : decodeBinaryNat afterTag with
              | none => simp [decodeCompactFormula, htag, harity] at hdecode
              | some arityResult =>
                  rcases arityResult with ⟨relationArity, afterArity⟩
                  cases hrelation : decodeBinaryNat afterArity with
                  | none =>
                      simp [decodeCompactFormula, htag, harity,
                        hrelation] at hdecode
                  | some relationResult =>
                      rcases relationResult with
                        ⟨relationCode, afterRelation⟩
                      cases hsymbol :
                          (Encodable.decode₂ _ relationCode :
                            Option (LO.FirstOrder.Language.Rel
                              ℒₒᵣ relationArity)) with
                      | none =>
                          simp [decodeCompactFormula, htag, harity,
                            hrelation, hsymbol] at hdecode
                      | some relationSymbol =>
                          cases harguments :
                              decodeManyVector
                                (decodeCompactTerm arity fuel)
                                relationArity afterRelation with
                          | none =>
                              simp [decodeCompactFormula, htag, harity,
                                hrelation, hsymbol, harguments] at hdecode
                          | some argumentsResult =>
                              rcases argumentsResult with
                                ⟨arguments, afterArguments⟩
                              simp [decodeCompactFormula, htag, harity,
                                hrelation, hsymbol, harguments] at hdecode
                              rcases hdecode with ⟨rfl, rfl⟩
                              have hargumentsLength :=
                                decodeManyVector_weight_le
                                  (decodeCompactTerm arity fuel)
                                  (fun term =>
                                    (binaryTermCode term).length)
                                  (fun h =>
                                    decodeCompactTerm_canonical_length_le h)
                                  harguments
                              rw [vector_map_sum_eq_finset_sum]
                                at hargumentsLength
                              have harityLength :=
                                decodeBinaryNat_canonical_length_le harity
                              have hrelationLength :=
                                decodeBinaryNat_canonical_length_le hrelation
                              have hencode :
                                  Encodable.encode relationSymbol =
                                    relationCode :=
                                Encodable.decode₂_eq_some.mp hsymbol
                              have hflatten :=
                                length_flatten_ofFn
                                  (fun index => binaryTermCode
                                    (arguments.get index))
                              have hargumentsLength' :
                                  (List.ofFn (fun index => binaryTermCode
                                      (arguments.get index))).flatten.length +
                                      afterArguments.length <=
                                    afterRelation.length := by
                                rw [hflatten]
                                exact hargumentsLength
                              simp only [binaryFormulaCode,
                                List.length_append]
                              rw [hencode]
                              omega
          | succ tag =>
              cases tag with
              | zero =>
                  cases harity : decodeBinaryNat afterTag with
                  | none =>
                      simp [decodeCompactFormula, htag, harity] at hdecode
                  | some arityResult =>
                      rcases arityResult with ⟨relationArity, afterArity⟩
                      cases hrelation : decodeBinaryNat afterArity with
                      | none =>
                          simp [decodeCompactFormula, htag, harity,
                            hrelation] at hdecode
                      | some relationResult =>
                          rcases relationResult with
                            ⟨relationCode, afterRelation⟩
                          cases hsymbol :
                              (Encodable.decode₂ _ relationCode :
                                Option (LO.FirstOrder.Language.Rel
                                  ℒₒᵣ relationArity)) with
                          | none =>
                              simp [decodeCompactFormula, htag, harity,
                                hrelation, hsymbol] at hdecode
                          | some relationSymbol =>
                              cases harguments :
                                  decodeManyVector
                                    (decodeCompactTerm arity fuel)
                                    relationArity afterRelation with
                              | none =>
                                  simp [decodeCompactFormula, htag, harity,
                                    hrelation, hsymbol, harguments] at hdecode
                              | some argumentsResult =>
                                  rcases argumentsResult with
                                    ⟨arguments, afterArguments⟩
                                  simp [decodeCompactFormula, htag, harity,
                                    hrelation, hsymbol, harguments] at hdecode
                                  rcases hdecode with ⟨rfl, rfl⟩
                                  have hargumentsLength :=
                                    decodeManyVector_weight_le
                                      (decodeCompactTerm arity fuel)
                                      (fun term =>
                                        (binaryTermCode term).length)
                                      (fun h =>
                                        decodeCompactTerm_canonical_length_le h)
                                      harguments
                                  rw [vector_map_sum_eq_finset_sum]
                                    at hargumentsLength
                                  have harityLength :=
                                    decodeBinaryNat_canonical_length_le harity
                                  have hrelationLength :=
                                    decodeBinaryNat_canonical_length_le hrelation
                                  have hencode :
                                      Encodable.encode relationSymbol =
                                        relationCode :=
                                    Encodable.decode₂_eq_some.mp hsymbol
                                  have hflatten :=
                                    length_flatten_ofFn
                                      (fun index => binaryTermCode
                                        (arguments.get index))
                                  have hargumentsLength' :
                                      (List.ofFn (fun index => binaryTermCode
                                          (arguments.get index))).flatten.length +
                                          afterArguments.length <=
                                        afterRelation.length := by
                                    rw [hflatten]
                                    exact hargumentsLength
                                  change (binaryNatCode 1).length +
                                      afterTag.length <= bits.length
                                    at htagLength
                                  simp only [binaryFormulaCode,
                                    List.length_append]
                                  rw [hencode]
                                  omega
              | succ tag =>
                  cases tag with
                  | zero =>
                      simp [decodeCompactFormula, htag] at hdecode
                      rcases hdecode with ⟨rfl, rfl⟩
                      change (binaryNatCode 2).length +
                          afterTag.length <= bits.length at htagLength
                      simpa [binaryFormulaCode] using htagLength
                  | succ tag =>
                      cases tag with
                      | zero =>
                          simp [decodeCompactFormula, htag] at hdecode
                          rcases hdecode with ⟨rfl, rfl⟩
                          change (binaryNatCode 3).length +
                              afterTag.length <= bits.length at htagLength
                          simpa [binaryFormulaCode] using htagLength
                      | succ tag =>
                          cases tag with
                          | zero =>
                              cases hleft :
                                  decodeCompactFormula arity fuel afterTag with
                              | none =>
                                  simp [decodeCompactFormula, htag, hleft]
                                    at hdecode
                              | some leftResult =>
                                  rcases leftResult with ⟨left, afterLeft⟩
                                  cases hright :
                                      decodeCompactFormula arity fuel afterLeft with
                                  | none =>
                                      simp [decodeCompactFormula, htag, hleft,
                                        hright] at hdecode
                                  | some rightResult =>
                                      rcases rightResult with
                                        ⟨right, afterRight⟩
                                      simp [decodeCompactFormula, htag, hleft,
                                        hright] at hdecode
                                      rcases hdecode with ⟨rfl, rfl⟩
                                      have hleftLength := ih hleft
                                      have hrightLength := ih hright
                                      change (binaryNatCode 4).length +
                                          afterTag.length <= bits.length
                                        at htagLength
                                      simp only [binaryFormulaCode,
                                        List.length_append]
                                      omega
                          | succ tag =>
                              cases tag with
                              | zero =>
                                  cases hleft :
                                      decodeCompactFormula arity fuel afterTag with
                                  | none =>
                                      simp [decodeCompactFormula, htag, hleft]
                                        at hdecode
                                  | some leftResult =>
                                      rcases leftResult with ⟨left, afterLeft⟩
                                      cases hright :
                                          decodeCompactFormula arity fuel
                                            afterLeft with
                                      | none =>
                                          simp [decodeCompactFormula, htag,
                                            hleft, hright] at hdecode
                                      | some rightResult =>
                                          rcases rightResult with
                                            ⟨right, afterRight⟩
                                          simp [decodeCompactFormula, htag,
                                            hleft, hright] at hdecode
                                          rcases hdecode with ⟨rfl, rfl⟩
                                          have hleftLength := ih hleft
                                          have hrightLength := ih hright
                                          change (binaryNatCode 5).length +
                                              afterTag.length <= bits.length
                                            at htagLength
                                          simp only [binaryFormulaCode,
                                            List.length_append]
                                          omega
                              | succ tag =>
                                  cases tag with
                                  | zero =>
                                      cases hbody :
                                          decodeCompactFormula (arity + 1)
                                            fuel afterTag with
                                      | none =>
                                          simp [decodeCompactFormula, htag,
                                            hbody] at hdecode
                                      | some bodyResult =>
                                          rcases bodyResult with
                                            ⟨body, afterBody⟩
                                          simp [decodeCompactFormula, htag,
                                            hbody] at hdecode
                                          rcases hdecode with ⟨rfl, rfl⟩
                                          have hbodyLength := ih hbody
                                          change (binaryNatCode 6).length +
                                              afterTag.length <= bits.length
                                            at htagLength
                                          simp only [binaryFormulaCode,
                                            List.length_append]
                                          omega
                                  | succ tag =>
                                      cases tag with
                                      | zero =>
                                          cases hbody :
                                              decodeCompactFormula (arity + 1)
                                                fuel afterTag with
                                          | none =>
                                              simp [decodeCompactFormula,
                                                htag, hbody] at hdecode
                                          | some bodyResult =>
                                              rcases bodyResult with
                                                ⟨body, afterBody⟩
                                              simp [decodeCompactFormula,
                                                htag, hbody] at hdecode
                                              rcases hdecode with ⟨rfl, rfl⟩
                                              have hbodyLength := ih hbody
                                              change (binaryNatCode 7).length +
                                                  afterTag.length <= bits.length
                                                at htagLength
                                              simp only [binaryFormulaCode,
                                                List.length_append]
                                              omega
                                      | succ tag =>
                                          simp [decodeCompactFormula, htag]
                                            at hdecode

theorem binaryNatCode_length_mono
    {smaller larger : Nat} (hle : smaller <= larger) :
    (binaryNatCode smaller).length <= (binaryNatCode larger).length := by
  rw [binaryNatCode_length, binaryNatCode_length]
  have hsize := Nat.size_le_size hle
  omega

theorem decodeCompactSequent_canonical_length_le
    {fuel : Nat} {bits suffix : List Bool}
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (hdecode : decodeCompactSequent fuel bits = some (Gamma, suffix)) :
    (binarySequentCode Gamma).length + suffix.length <= bits.length := by
  cases hcardinality : decodeBinaryNat bits with
  | none => simp [decodeCompactSequent, hcardinality] at hdecode
  | some cardinalityResult =>
      rcases cardinalityResult with ⟨cardinality, afterCardinality⟩
      cases hformulas :
          decodeManyVector (decodeCompactFormula 0 fuel)
            cardinality afterCardinality with
      | none =>
          simp [decodeCompactSequent, hcardinality, hformulas] at hdecode
      | some formulasResult =>
          rcases formulasResult with ⟨formulas, afterFormulas⟩
          simp [decodeCompactSequent, hcardinality, hformulas] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          have hheaderLength :=
            decodeBinaryNat_canonical_length_le hcardinality
          have hformulasLength :=
            decodeManyVector_weight_le
              (decodeCompactFormula 0 fuel)
              (fun formula => (binaryFormulaCode formula).length)
              (fun h => decodeCompactFormula_canonical_length_le h)
              hformulas
          have hcard : formulas.toList.toFinset.card <= cardinality := by
            simpa using List.toFinset_card_le (l := formulas.toList)
          have hcanonicalHeader := binaryNatCode_length_mono hcard
          have hcanonicalPayload :
              (formulas.toList.toFinset.toList.flatMap
                  binaryFormulaCode).length <=
                (formulas.toList.map
                  (fun formula => (binaryFormulaCode formula).length)).sum := by
            have hset := list_toFinset_sum_le_map_sum formulas.toList
              (fun formula => (binaryFormulaCode formula).length)
            rw [List.length_flatMap]
            simpa using hset
          simp only [binarySequentCode, List.length_append]
          omega

#print axioms decodeBinaryNat_canonical_length_le
#print axioms decodeCompactTerm_canonical_length_le
#print axioms decodeCompactFormula_canonical_length_le
#print axioms decodeCompactSequent_canonical_length_le

end FoundationCompactCanonicalDecodeLength
