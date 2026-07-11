import integration.FoundationCompactBinaryNatStreamSynchronization
import integration.FoundationCompactSyntaxTokenMachine

/-!
# Exact bit/token synchronization for compact arithmetic syntax

The theorems in this file connect the existing typed bit decoders to the
natural-token syntax encodings on arbitrary successful inputs.  Redundant
zero bits in a natural token are allowed; the exact residual bit list is
carried by `BinaryNatTokensDecode`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactSyntaxBitTokenSynchronization

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactSyntaxTokenMachine
open FoundationCompactBinaryNatStreamSynchronization

theorem decodeManyVector_tokens_sound
    {alpha : Type*}
    (decode : List Bool -> Option (alpha × List Bool))
    (tokensOf : alpha -> List Nat)
    (hsingle : forall {bits suffix item},
      decode bits = some (item, suffix) ->
        BinaryNatTokensDecode (tokensOf item) bits suffix) :
    forall {count bits suffix} {items : List.Vector alpha count},
      decodeManyVector decode count bits = some (items, suffix) ->
        BinaryNatTokensDecode
          (items.toList.flatMap tokensOf) bits suffix := by
  intro count
  induction count with
  | zero =>
      intro bits suffix items hdecode
      simp [decodeManyVector] at hdecode
      rcases hdecode with ⟨rfl, rfl⟩
      exact .nil bits
  | succ count ih =>
      intro bits suffix items hdecode
      cases hhead : decode bits with
      | none => simp [decodeManyVector, hhead] at hdecode
      | some result =>
          rcases result with ⟨head, rest⟩
          cases htail : decodeManyVector decode count rest with
          | none => simp [decodeManyVector, hhead, htail] at hdecode
          | some result =>
              rcases result with ⟨tail, finalSuffix⟩
              simp [decodeManyVector, hhead, htail] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              simp only [List.Vector.toList_cons, List.flatMap_cons]
              exact binaryNatTokensDecode_append
                (hsingle hhead) (ih htail)

theorem decodeManyVector_tokens_complete
    {alpha : Type*}
    (decode : List Bool -> Option (alpha × List Bool))
    (tokensOf : alpha -> List Nat) :
    forall {count} (items : List.Vector alpha count) {bits suffix},
      (forall {itemBits itemSuffix} (item : alpha),
        item ∈ items.toList ->
          BinaryNatTokensDecode
              (tokensOf item) itemBits itemSuffix ->
            decode itemBits = some (item, itemSuffix)) ->
      BinaryNatTokensDecode
          (items.toList.flatMap tokensOf) bits suffix ->
        decodeManyVector decode count bits = some (items, suffix) := by
  intro count
  induction count with
  | zero =>
      intro items bits suffix hsingle htokens
      have hitems : items = List.Vector.nil := Subsingleton.elim _ _
      subst items
      simp only [List.Vector.toList_nil, List.flatMap_nil] at htokens
      cases htokens
      rfl
  | succ count ih =>
      intro items bits suffix hsingle htokens
      obtain ⟨head, tail, rfl⟩ := List.Vector.exists_eq_cons items
      simp only [List.Vector.toList_cons, List.flatMap_cons] at htokens
      obtain ⟨middle, hhead, htail⟩ :=
        binaryNatTokensDecode_split_append
          (tokensOf head) (tail.toList.flatMap tokensOf) htokens
      have hheadDecode := hsingle head (by simp) hhead
      have htailDecode := ih tail
        (fun item hitem hitemTokens =>
          hsingle item (by simp [hitem]) hitemTokens) htail
      simp [decodeManyVector, hheadDecode, htailDecode]

theorem decodeManyVector_tokens_complete_of_input_length
    {alpha : Type*}
    (decode : List Bool -> Option (alpha × List Bool))
    (tokensOf : alpha -> List Nat) (fuel : Nat) :
    forall {count} (items : List.Vector alpha count) {bits suffix},
      (forall {itemBits itemSuffix} (item : alpha),
        item ∈ items.toList -> itemBits.length < fuel ->
          BinaryNatTokensDecode
              (tokensOf item) itemBits itemSuffix ->
            decode itemBits = some (item, itemSuffix)) ->
      bits.length < fuel ->
      BinaryNatTokensDecode
          (items.toList.flatMap tokensOf) bits suffix ->
        decodeManyVector decode count bits = some (items, suffix) := by
  intro count
  induction count with
  | zero =>
      intro items bits suffix hsingle hbits htokens
      have hitems : items = List.Vector.nil := Subsingleton.elim _ _
      subst items
      simp only [List.Vector.toList_nil, List.flatMap_nil] at htokens
      cases htokens
      rfl
  | succ count ih =>
      intro items bits suffix hsingle hbits htokens
      obtain ⟨head, tail, rfl⟩ := List.Vector.exists_eq_cons items
      simp only [List.Vector.toList_cons, List.flatMap_cons] at htokens
      obtain ⟨middle, hhead, htail⟩ :=
        binaryNatTokensDecode_split_append
          (tokensOf head) (tail.toList.flatMap tokensOf) htokens
      have hmiddleLength := binaryNatTokensDecode_length hhead
      have hmiddle : middle.length < fuel := by omega
      have hheadDecode := hsingle head (by simp) hbits hhead
      have htailDecode := ih tail
        (fun item hitem hitemBits hitemTokens =>
          hsingle item (by simp [hitem]) hitemBits hitemTokens)
        hmiddle htail
      simp [decodeManyVector, hheadDecode, htailDecode]

theorem decodeCompactTerm_tokens_sound :
    forall {arity fuel bits suffix term},
      decodeCompactTerm arity fuel bits = some (term, suffix) ->
        BinaryNatTokensDecode
          (compactArithmeticTermTokens term) bits suffix := by
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
                    exact .cons htag (.cons hindex (.nil afterIndex))
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
                      exact .cons htag (.cons hindex (.nil afterIndex))
              | succ tag =>
                  cases tag with
                  | zero =>
                      cases harity : decodeBinaryNat afterTag with
                      | none => simp [decodeCompactTerm, htag, harity] at hdecode
                      | some arityResult =>
                          rcases arityResult with
                            ⟨functionArity, afterArity⟩
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
                                      have hargumentTokens :=
                                        decodeManyVector_tokens_sound
                                          (decodeCompactTerm arity fuel)
                                          compactArithmeticTermTokens
                                          (fun h => ih h) harguments
                                      have hfunctionCode :
                                          Encodable.encode functionSymbol =
                                            functionCode :=
                                        Encodable.decode₂_eq_some.mp hsymbol
                                      have hargumentTokenList :
                                          arguments.toList.flatMap
                                              compactArithmeticTermTokens =
                                            (List.ofFn fun index =>
                                              compactArithmeticTermTokens
                                                (arguments.get index)).flatten := by
                                        calc
                                          arguments.toList.flatMap
                                              compactArithmeticTermTokens =
                                              (List.Vector.ofFn
                                                arguments.get).toList.flatMap
                                                  compactArithmeticTermTokens := by
                                                    rw [List.Vector.ofFn_get]
                                          _ = (List.ofFn arguments.get).flatMap
                                                compactArithmeticTermTokens := by
                                                  rw [List.Vector.toList_ofFn]
                                          _ = (List.ofFn fun index =>
                                                compactArithmeticTermTokens
                                                  (arguments.get index)).flatten := by
                                                  simpa [compactTermListTokens]
                                                    using
                                                      compactTermListTokens_ofFn
                                                        arguments.get
                                      rw [hargumentTokenList] at hargumentTokens
                                      simp only [compactArithmeticTermTokens]
                                      rw [hfunctionCode]
                                      exact .cons htag <| .cons harity <|
                                        .cons hfunction hargumentTokens
                  | succ tag =>
                      simp [decodeCompactTerm, htag] at hdecode

theorem decodeCompactTerm_tokens_complete
    {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (fuel : Nat) (hfuel : termSymbolCount term < fuel)
    {bits suffix : List Bool}
    (htokens : BinaryNatTokensDecode
      (compactArithmeticTermTokens term) bits suffix) :
    decodeCompactTerm arity fuel bits = some (term, suffix) := by
  induction term generalizing fuel bits suffix with
  | bvar index =>
      cases fuel with
      | zero => simp [termSymbolCount] at hfuel
      | succ fuel =>
          simp only [compactArithmeticTermTokens] at htokens
          cases htokens with
          | cons htag hrest =>
              cases hrest with
              | cons hindex hdone =>
                  cases hdone
                  simp [decodeCompactTerm, htag, hindex, index.isLt]
  | fvar freeIndex =>
      cases fuel with
      | zero => simp [termSymbolCount] at hfuel
      | succ fuel =>
          simp only [compactArithmeticTermTokens] at htokens
          cases htokens with
          | cons htag hrest =>
              cases hrest with
              | cons hindex hdone =>
                  cases hdone
                  simp [decodeCompactTerm, htag, hindex]
  | func functionSymbol arguments ih =>
      cases fuel with
      | zero => simp [termSymbolCount] at hfuel
      | succ fuel =>
          have hchild (index) :
              termSymbolCount (arguments index) < fuel := by
            have hle :
                termSymbolCount (arguments index) <=
                  Finset.univ.sum
                    (fun j => termSymbolCount (arguments j)) :=
              Finset.single_le_sum
                (f := fun j => termSymbolCount (arguments j))
                (s := Finset.univ)
                (fun j _ => Nat.zero_le (termSymbolCount (arguments j)))
                (Finset.mem_univ index)
            simp [termSymbolCount] at hfuel
            omega
          simp only [compactArithmeticTermTokens] at htokens
          cases htokens with
          | cons htag hrest =>
              cases hrest with
              | cons harity hrest =>
                  cases hrest with
                  | cons hfunction harguments =>
                      let argumentVector : List.Vector _ _ :=
                        List.Vector.ofFn arguments
                      have hargumentTokenList :
                          argumentVector.toList.flatMap
                              compactArithmeticTermTokens =
                            (List.ofFn fun index =>
                              compactArithmeticTermTokens
                                (arguments index)).flatten := by
                        simp only [argumentVector,
                          List.Vector.toList_ofFn]
                        change compactTermListTokens
                          (List.ofFn arguments) = _
                        exact compactTermListTokens_ofFn arguments
                      rw [← hargumentTokenList] at harguments
                      have hmany :=
                        decodeManyVector_tokens_complete
                          (decodeCompactTerm _ fuel)
                          compactArithmeticTermTokens
                          argumentVector
                          (fun child hchildMem hchildTokens => by
                            rcases (List.mem_ofFn' arguments child).mp
                                (by simpa [argumentVector] using
                                  hchildMem) with
                              ⟨index, rfl⟩
                            exact ih index fuel (hchild index)
                              hchildTokens)
                          harguments
                      simp [decodeCompactTerm, htag, harity, hfunction,
                        Encodable.decode₂_encode, hmany, argumentVector]
                      funext index
                      simp

theorem decodeCompactTerm_success_iff_tokens
    {arity fuel : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (hfuel : termSymbolCount term < fuel)
    (bits suffix : List Bool) :
    decodeCompactTerm arity fuel bits = some (term, suffix) <->
      BinaryNatTokensDecode
        (compactArithmeticTermTokens term) bits suffix := by
  constructor
  · exact decodeCompactTerm_tokens_sound
  · exact decodeCompactTerm_tokens_complete term fuel hfuel

theorem decodeCompactTerm_tokens_complete_of_input_length
    {arity fuel : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    {bits suffix : List Bool}
    (hbits : bits.length < fuel)
    (htokens : BinaryNatTokensDecode
      (compactArithmeticTermTokens term) bits suffix) :
    decodeCompactTerm arity fuel bits = some (term, suffix) := by
  have hcanonical :=
    binaryNatTokensDecode_canonical_bit_length htokens
  rw [← binaryTermCode_eq_tokenStream] at hcanonical
  have hsymbols := termSymbolCount_le_binaryTermCode_length term
  exact decodeCompactTerm_tokens_complete term fuel (by omega) htokens

theorem decodeCompactFormula_tokens_sound :
    forall {arity fuel bits suffix formula},
      decodeCompactFormula arity fuel bits = some (formula, suffix) ->
        BinaryNatTokensDecode
          (compactArithmeticFormulaTokens formula) bits suffix := by
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
          rcases tag with (_ | _ | _ | _ | _ | _ | _ | _ | tag)
          · cases harity : decodeBinaryNat afterTag with
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
                            have hargumentTokens :=
                              decodeManyVector_tokens_sound
                                (decodeCompactTerm arity fuel)
                                compactArithmeticTermTokens
                                (fun h => decodeCompactTerm_tokens_sound h)
                                harguments
                            have hargumentTokenList :
                                arguments.toList.flatMap
                                    compactArithmeticTermTokens =
                                  (List.ofFn fun index =>
                                    compactArithmeticTermTokens
                                      (arguments.get index)).flatten := by
                              calc
                                arguments.toList.flatMap
                                    compactArithmeticTermTokens =
                                    (List.Vector.ofFn
                                      arguments.get).toList.flatMap
                                        compactArithmeticTermTokens := by
                                          rw [List.Vector.ofFn_get]
                                _ = (List.ofFn arguments.get).flatMap
                                      compactArithmeticTermTokens := by
                                        rw [List.Vector.toList_ofFn]
                                _ = (List.ofFn fun index =>
                                      compactArithmeticTermTokens
                                        (arguments.get index)).flatten := by
                                        simpa [compactTermListTokens]
                                          using compactTermListTokens_ofFn
                                            arguments.get
                            rw [hargumentTokenList] at hargumentTokens
                            have hrelationCode :
                                Encodable.encode relationSymbol =
                                  relationCode :=
                              Encodable.decode₂_eq_some.mp hsymbol
                            simp only [compactArithmeticFormulaTokens]
                            rw [hrelationCode]
                            exact .cons htag <| .cons harity <|
                              .cons hrelation hargumentTokens
          · cases harity : decodeBinaryNat afterTag with
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
                            have hargumentTokens :=
                              decodeManyVector_tokens_sound
                                (decodeCompactTerm arity fuel)
                                compactArithmeticTermTokens
                                (fun h => decodeCompactTerm_tokens_sound h)
                                harguments
                            have hargumentTokenList :
                                arguments.toList.flatMap
                                    compactArithmeticTermTokens =
                                  (List.ofFn fun index =>
                                    compactArithmeticTermTokens
                                      (arguments.get index)).flatten := by
                              calc
                                arguments.toList.flatMap
                                    compactArithmeticTermTokens =
                                    (List.Vector.ofFn
                                      arguments.get).toList.flatMap
                                        compactArithmeticTermTokens := by
                                          rw [List.Vector.ofFn_get]
                                _ = (List.ofFn arguments.get).flatMap
                                      compactArithmeticTermTokens := by
                                        rw [List.Vector.toList_ofFn]
                                _ = (List.ofFn fun index =>
                                      compactArithmeticTermTokens
                                        (arguments.get index)).flatten := by
                                        simpa [compactTermListTokens]
                                          using compactTermListTokens_ofFn
                                            arguments.get
                            rw [hargumentTokenList] at hargumentTokens
                            have hrelationCode :
                                Encodable.encode relationSymbol =
                                  relationCode :=
                              Encodable.decode₂_eq_some.mp hsymbol
                            simp only [compactArithmeticFormulaTokens]
                            rw [hrelationCode]
                            exact .cons htag <| .cons harity <|
                              .cons hrelation hargumentTokens
          · simp [decodeCompactFormula, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodeCompactFormula, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · cases hleft : decodeCompactFormula arity fuel afterTag with
            | none => simp [decodeCompactFormula, htag, hleft] at hdecode
            | some leftResult =>
                rcases leftResult with ⟨left, afterLeft⟩
                cases hright : decodeCompactFormula arity fuel afterLeft with
                | none =>
                    simp [decodeCompactFormula, htag, hleft, hright] at hdecode
                | some rightResult =>
                    rcases rightResult with ⟨right, afterRight⟩
                    simp [decodeCompactFormula, htag, hleft, hright] at hdecode
                    rcases hdecode with ⟨rfl, rfl⟩
                    simp only [compactArithmeticFormulaTokens]
                    exact .cons htag <|
                      binaryNatTokensDecode_append (ih hleft) (ih hright)
          · cases hleft : decodeCompactFormula arity fuel afterTag with
            | none => simp [decodeCompactFormula, htag, hleft] at hdecode
            | some leftResult =>
                rcases leftResult with ⟨left, afterLeft⟩
                cases hright : decodeCompactFormula arity fuel afterLeft with
                | none =>
                    simp [decodeCompactFormula, htag, hleft, hright] at hdecode
                | some rightResult =>
                    rcases rightResult with ⟨right, afterRight⟩
                    simp [decodeCompactFormula, htag, hleft, hright] at hdecode
                    rcases hdecode with ⟨rfl, rfl⟩
                    simp only [compactArithmeticFormulaTokens]
                    exact .cons htag <|
                      binaryNatTokensDecode_append (ih hleft) (ih hright)
          · cases hbody :
                decodeCompactFormula (arity + 1) fuel afterTag with
            | none => simp [decodeCompactFormula, htag, hbody] at hdecode
            | some bodyResult =>
                rcases bodyResult with ⟨body, afterBody⟩
                simp [decodeCompactFormula, htag, hbody] at hdecode
                rcases hdecode with ⟨rfl, rfl⟩
                exact .cons htag (ih hbody)
          · cases hbody :
                decodeCompactFormula (arity + 1) fuel afterTag with
            | none => simp [decodeCompactFormula, htag, hbody] at hdecode
            | some bodyResult =>
                rcases bodyResult with ⟨body, afterBody⟩
                simp [decodeCompactFormula, htag, hbody] at hdecode
                rcases hdecode with ⟨rfl, rfl⟩
                exact .cons htag (ih hbody)
          · simp [decodeCompactFormula, htag] at hdecode

theorem decodeCompactFormula_tokens_complete
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity)
    (fuel : Nat) (hfuel : formulaSymbolCount formula < fuel)
    {bits suffix : List Bool}
    (htokens : BinaryNatTokensDecode
      (compactArithmeticFormulaTokens formula) bits suffix) :
    decodeCompactFormula arity fuel bits = some (formula, suffix) := by
  induction formula generalizing fuel bits suffix with
  | rel relationSymbol arguments =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hchild (index) :
              termSymbolCount (arguments index) < fuel := by
            have hle :
                termSymbolCount (arguments index) <=
                  Finset.univ.sum
                    (fun j => termSymbolCount (arguments j)) :=
              Finset.single_le_sum
                (f := fun j => termSymbolCount (arguments j))
                (s := Finset.univ)
                (fun j _ => Nat.zero_le (termSymbolCount (arguments j)))
                (Finset.mem_univ index)
            simp [formulaSymbolCount] at hfuel
            omega
          simp only [compactArithmeticFormulaTokens] at htokens
          cases htokens with
          | cons htag hrest =>
              cases hrest with
              | cons harity hrest =>
                  cases hrest with
                  | cons hrelation harguments =>
                      let argumentVector : List.Vector _ _ :=
                        List.Vector.ofFn arguments
                      have hargumentTokenList :
                          argumentVector.toList.flatMap
                              compactArithmeticTermTokens =
                            (List.ofFn fun index =>
                              compactArithmeticTermTokens
                                (arguments index)).flatten := by
                        simp only [argumentVector,
                          List.Vector.toList_ofFn]
                        change compactTermListTokens
                          (List.ofFn arguments) = _
                        exact compactTermListTokens_ofFn arguments
                      rw [← hargumentTokenList] at harguments
                      have hmany :=
                        decodeManyVector_tokens_complete
                          (decodeCompactTerm _ fuel)
                          compactArithmeticTermTokens
                          argumentVector
                          (fun child hchildMem hchildTokens => by
                            rcases (List.mem_ofFn' arguments child).mp
                                (by simpa [argumentVector] using
                                  hchildMem) with
                              ⟨index, rfl⟩
                            exact decodeCompactTerm_tokens_complete
                              (arguments index) fuel (hchild index)
                              hchildTokens)
                          harguments
                      simp [decodeCompactFormula, htag, harity, hrelation,
                        Encodable.decode₂_encode, hmany, argumentVector]
                      funext index
                      simp
  | nrel relationSymbol arguments =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hchild (index) :
              termSymbolCount (arguments index) < fuel := by
            have hle :
                termSymbolCount (arguments index) <=
                  Finset.univ.sum
                    (fun j => termSymbolCount (arguments j)) :=
              Finset.single_le_sum
                (f := fun j => termSymbolCount (arguments j))
                (s := Finset.univ)
                (fun j _ => Nat.zero_le (termSymbolCount (arguments j)))
                (Finset.mem_univ index)
            simp [formulaSymbolCount] at hfuel
            omega
          simp only [compactArithmeticFormulaTokens] at htokens
          cases htokens with
          | cons htag hrest =>
              cases hrest with
              | cons harity hrest =>
                  cases hrest with
                  | cons hrelation harguments =>
                      let argumentVector : List.Vector _ _ :=
                        List.Vector.ofFn arguments
                      have hargumentTokenList :
                          argumentVector.toList.flatMap
                              compactArithmeticTermTokens =
                            (List.ofFn fun index =>
                              compactArithmeticTermTokens
                                (arguments index)).flatten := by
                        simp only [argumentVector,
                          List.Vector.toList_ofFn]
                        change compactTermListTokens
                          (List.ofFn arguments) = _
                        exact compactTermListTokens_ofFn arguments
                      rw [← hargumentTokenList] at harguments
                      have hmany :=
                        decodeManyVector_tokens_complete
                          (decodeCompactTerm _ fuel)
                          compactArithmeticTermTokens
                          argumentVector
                          (fun child hchildMem hchildTokens => by
                            rcases (List.mem_ofFn' arguments child).mp
                                (by simpa [argumentVector] using
                                  hchildMem) with
                              ⟨index, rfl⟩
                            exact decodeCompactTerm_tokens_complete
                              (arguments index) fuel (hchild index)
                              hchildTokens)
                          harguments
                      simp [decodeCompactFormula, htag, harity, hrelation,
                        Encodable.decode₂_encode, hmany, argumentVector]
                      funext index
                      simp
  | verum =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          simp only [compactArithmeticFormulaTokens] at htokens
          cases htokens with
          | cons htag hdone =>
              cases hdone
              simp [decodeCompactFormula, htag]
              rfl
  | falsum =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          simp only [compactArithmeticFormulaTokens] at htokens
          cases htokens with
          | cons htag hdone =>
              cases hdone
              simp [decodeCompactFormula, htag]
              rfl
  | and left right ihLeft ihRight =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hleftBound : formulaSymbolCount left < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          have hrightBound : formulaSymbolCount right < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          simp only [compactArithmeticFormulaTokens] at htokens
          cases htokens with
          | cons htag hchildren =>
              obtain ⟨middle, hleft, hright⟩ :=
                binaryNatTokensDecode_split_append
                  (compactArithmeticFormulaTokens left)
                  (compactArithmeticFormulaTokens right) hchildren
              have hleftDecode :=
                ihLeft fuel hleftBound hleft
              have hrightDecode :=
                ihRight fuel hrightBound hright
              simp [decodeCompactFormula, htag,
                hleftDecode, hrightDecode]
              rfl
  | or left right ihLeft ihRight =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hleftBound : formulaSymbolCount left < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          have hrightBound : formulaSymbolCount right < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          simp only [compactArithmeticFormulaTokens] at htokens
          cases htokens with
          | cons htag hchildren =>
              obtain ⟨middle, hleft, hright⟩ :=
                binaryNatTokensDecode_split_append
                  (compactArithmeticFormulaTokens left)
                  (compactArithmeticFormulaTokens right) hchildren
              have hleftDecode :=
                ihLeft fuel hleftBound hleft
              have hrightDecode :=
                ihRight fuel hrightBound hright
              simp [decodeCompactFormula, htag,
                hleftDecode, hrightDecode]
              rfl
  | all body ih =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hbodyBound : formulaSymbolCount body < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          simp only [compactArithmeticFormulaTokens] at htokens
          cases htokens with
          | cons htag hbody =>
              have hbodyDecode := ih fuel hbodyBound hbody
              simp [decodeCompactFormula, htag, hbodyDecode]
              rfl
  | exs body ih =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hbodyBound : formulaSymbolCount body < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          simp only [compactArithmeticFormulaTokens] at htokens
          cases htokens with
          | cons htag hbody =>
              have hbodyDecode := ih fuel hbodyBound hbody
              simp [decodeCompactFormula, htag, hbodyDecode]
              rfl

theorem decodeCompactFormula_success_iff_tokens
    {arity fuel : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity)
    (hfuel : formulaSymbolCount formula < fuel)
    (bits suffix : List Bool) :
    decodeCompactFormula arity fuel bits = some (formula, suffix) <->
      BinaryNatTokensDecode
        (compactArithmeticFormulaTokens formula) bits suffix := by
  constructor
  · exact decodeCompactFormula_tokens_sound
  · exact decodeCompactFormula_tokens_complete formula fuel hfuel

theorem decodeCompactFormula_tokens_complete_of_input_length
    {arity fuel : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity)
    {bits suffix : List Bool}
    (hbits : bits.length < fuel)
    (htokens : BinaryNatTokensDecode
      (compactArithmeticFormulaTokens formula) bits suffix) :
    decodeCompactFormula arity fuel bits = some (formula, suffix) := by
  have hcanonical :=
    binaryNatTokensDecode_canonical_bit_length htokens
  rw [← binaryFormulaCode_eq_tokenStream] at hcanonical
  have hsymbols := formulaSymbolCount_le_binaryFormulaCode_length formula
  exact decodeCompactFormula_tokens_complete formula fuel (by omega) htokens

#print axioms decodeCompactTerm_tokens_sound
#print axioms decodeCompactTerm_tokens_complete
#print axioms decodeCompactTerm_success_iff_tokens
#print axioms decodeCompactTerm_tokens_complete_of_input_length
#print axioms decodeCompactFormula_tokens_sound
#print axioms decodeCompactFormula_tokens_complete
#print axioms decodeCompactFormula_success_iff_tokens
#print axioms decodeCompactFormula_tokens_complete_of_input_length

end FoundationCompactSyntaxBitTokenSynchronization
