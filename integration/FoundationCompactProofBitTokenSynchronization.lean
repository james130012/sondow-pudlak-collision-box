import integration.FoundationCompactSyntaxBitTokenSynchronization
import integration.FoundationCompactProofTokenMachine

/-!
# Exact bit/token synchronization for listed compact proof trees

This file lifts the arbitrary-bit syntax equivalence to list-preserving
sequents and the ten-rule compact proof decoder.  The completeness direction
uses the actual remaining bit length as fuel; it never assumes that a
successful natural token was canonically encoded.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactProofBitTokenSynchronization

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactListedProofDecoder
open FoundationCompactProofTokenMachine
open FoundationCompactSyntaxTokenMachine
open FoundationCompactBinaryNatStreamSynchronization
open FoundationCompactSyntaxBitTokenSynchronization
open FoundationCompactVerifierStructuralBound

theorem decodeCompactSequentList_tokens_sound
    {fuel : Nat} {bits suffix : List Bool}
    {Gamma : List LO.FirstOrder.ArithmeticProposition}
    (hdecode : decodeCompactSequentList fuel bits = some (Gamma, suffix)) :
    BinaryNatTokensDecode (compactSequentListTokens Gamma) bits suffix := by
  cases hcardinality : decodeBinaryNat bits with
  | none => simp [decodeCompactSequentList, hcardinality] at hdecode
  | some cardinalityResult =>
      rcases cardinalityResult with ⟨cardinality, afterCardinality⟩
      cases hformulas :
          decodeManyVector (decodeCompactFormula 0 fuel) cardinality
            afterCardinality with
      | none =>
          simp [decodeCompactSequentList, hcardinality, hformulas] at hdecode
      | some formulasResult =>
          rcases formulasResult with ⟨formulas, afterFormulas⟩
          simp [decodeCompactSequentList, hcardinality, hformulas] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          have hformulaTokens :=
            decodeManyVector_tokens_sound
              (decodeCompactFormula 0 fuel)
              compactArithmeticFormulaTokens
              (fun h => decodeCompactFormula_tokens_sound h)
              hformulas
          simp only [compactSequentListTokens]
          have hcardinality' :
              decodeBinaryNat bits =
                some (formulas.toList.length, afterCardinality) := by
            simpa using hcardinality
          exact .cons hcardinality' hformulaTokens

theorem decodeCompactSequentList_tokens_complete_of_input_length
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (fuel : Nat) {bits suffix : List Bool}
    (hbits : bits.length < fuel)
    (htokens : BinaryNatTokensDecode
      (compactSequentListTokens Gamma) bits suffix) :
    decodeCompactSequentList fuel bits = some (Gamma, suffix) := by
  simp only [compactSequentListTokens] at htokens
  cases htokens with
  | @cons _ _ _ afterCardinality _ hcardinality hformulas =>
      have hafterLength := decodeBinaryNat_consumes_two hcardinality
      let formulaVector :
          List.Vector LO.FirstOrder.ArithmeticProposition Gamma.length :=
        ⟨Gamma, rfl⟩
      have hmany :=
        decodeManyVector_tokens_complete_of_input_length
          (decodeCompactFormula 0 fuel)
          compactArithmeticFormulaTokens fuel formulaVector
          (bits := afterCardinality) (suffix := suffix)
          (fun formula _ hformulaBits hformulaTokens =>
            decodeCompactFormula_tokens_complete_of_input_length
              formula hformulaBits hformulaTokens)
          (by omega) (by simpa [formulaVector] using hformulas)
      simp [decodeCompactSequentList, hcardinality,
        hmany, formulaVector]

set_option maxHeartbeats 1000000 in
theorem decodeCompactListedProof_tokens_sound :
    forall {fuel bits suffix tree},
      decodeCompactListedProof fuel bits = some (tree, suffix) ->
        BinaryNatTokensDecode
          (compactListedProofTokens tree) bits suffix := by
  intro fuel
  induction fuel with
  | zero =>
      intro bits suffix tree hdecode
      simp [decodeCompactListedProof] at hdecode
  | succ fuel ih =>
      intro bits suffix tree hdecode
      cases htag : decodeBinaryNat bits with
      | none => simp [decodeCompactListedProof, htag] at hdecode
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          simp only [decodeCompactListedProof] at hdecode
          simp only [htag] at hdecode
          cases hsequent : decodeCompactSequentList fuel afterTag with
          | none =>
              simp [hsequent] at hdecode
          | some sequentResult =>
              rcases sequentResult with ⟨Gamma, afterSequent⟩
              have hsequentTokens :=
                decodeCompactSequentList_tokens_sound hsequent
              rcases tag with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | tag)
              ·
                cases hformula : decodeCompactFormula 0 fuel afterSequent with
                | none =>
                    simp [hsequent, hformula] at hdecode
                | some formulaResult =>
                    rcases formulaResult with ⟨formula, afterFormula⟩
                    simp [hsequent, hformula] at hdecode
                    rcases hdecode with ⟨rfl, rfl⟩
                    have hformulaTokens :=
                      decodeCompactFormula_tokens_sound hformula
                    exact .cons htag <|
                      binaryNatTokensDecode_append
                        hsequentTokens hformulaTokens
              ·
                cases hformula : decodeCompactFormula 0 fuel afterSequent with
                | none =>
                    simp [hsequent, hformula] at hdecode
                | some formulaResult =>
                    rcases formulaResult with ⟨formula, afterFormula⟩
                    cases hsentence : propositionToSentence formula with
                    | none =>
                        simp [hsequent, hformula, hsentence] at hdecode
                    | some sentence =>
                        simp [hsequent, hformula, hsentence] at hdecode
                        rcases hdecode with ⟨rfl, rfl⟩
                        have hemb :
                            (Rewriting.emb sentence :
                              LO.FirstOrder.ArithmeticProposition) =
                              formula := by
                          unfold propositionToSentence at hsentence
                          split at hsentence
                          next hclosed =>
                            simp at hsentence
                            subst sentence
                            exact Semiformula.emb_toEmpty formula hclosed
                          next hnotClosed => simp at hsentence
                        have hformulaTokens :=
                          decodeCompactFormula_tokens_sound hformula
                        rw [← hemb] at hformulaTokens
                        exact .cons htag <|
                          binaryNatTokensDecode_append
                            hsequentTokens hformulaTokens
              ·
                simp [hsequent] at hdecode

                rcases hdecode with ⟨rfl, rfl⟩
                exact .cons htag hsequentTokens
              ·
                cases hleftFormula :
                    decodeCompactFormula 0 fuel afterSequent with
                | none =>
                    simp [hsequent, hleftFormula] at hdecode
                | some leftFormulaResult =>
                    rcases leftFormulaResult with
                      ⟨leftFormula, afterLeftFormula⟩
                    cases hrightFormula :
                        decodeCompactFormula 0 fuel afterLeftFormula with
                    | none =>
                        simp [hsequent, hleftFormula, hrightFormula] at hdecode
                    | some rightFormulaResult =>
                        rcases rightFormulaResult with
                          ⟨rightFormula, afterRightFormula⟩
                        cases hleftProof :
                            decodeCompactListedProof fuel afterRightFormula with
                        | none =>
                            simp [hsequent, hleftFormula, hrightFormula,
                              hleftProof] at hdecode
                        | some leftProofResult =>
                            rcases leftProofResult with
                              ⟨leftProof, afterLeftProof⟩
                            cases hrightProof :
                                decodeCompactListedProof fuel afterLeftProof with
                            | none =>
                                simp [hsequent, hleftFormula, hrightFormula,
                                  hleftProof, hrightProof] at hdecode
                            | some rightProofResult =>
                                rcases rightProofResult with
                                  ⟨rightProof, finalSuffix⟩
                                simp [hsequent, hleftFormula, hrightFormula,
                                  hleftProof, hrightProof] at hdecode
                                rcases hdecode with ⟨rfl, rfl⟩
                                have hall := BinaryNatTokensDecode.cons htag <|
                                  binaryNatTokensDecode_append hsequentTokens <|
                                  binaryNatTokensDecode_append
                                    (decodeCompactFormula_tokens_sound
                                      hleftFormula) <|
                                  binaryNatTokensDecode_append
                                    (decodeCompactFormula_tokens_sound
                                      hrightFormula) <|
                                  binaryNatTokensDecode_append
                                    (ih hleftProof) (ih hrightProof)
                                simpa only [compactListedProofTokens,
                                  List.append_assoc, List.cons_append, Nat.reduceAdd] using hall
              ·
                cases hleftFormula :
                    decodeCompactFormula 0 fuel afterSequent with
                | none =>
                    simp [hsequent, hleftFormula] at hdecode
                | some leftFormulaResult =>
                    rcases leftFormulaResult with
                      ⟨leftFormula, afterLeftFormula⟩
                    cases hrightFormula :
                        decodeCompactFormula 0 fuel afterLeftFormula with
                    | none =>
                        simp [hsequent, hleftFormula, hrightFormula] at hdecode
                    | some rightFormulaResult =>
                        rcases rightFormulaResult with
                          ⟨rightFormula, afterRightFormula⟩
                        cases hpremise :
                            decodeCompactListedProof fuel afterRightFormula with
                        | none =>
                            simp [hsequent, hleftFormula, hrightFormula, hpremise] at hdecode
                        | some premiseResult =>
                            rcases premiseResult with ⟨premise, finalSuffix⟩
                            simp [hsequent, hleftFormula, hrightFormula, hpremise] at hdecode
                            rcases hdecode with ⟨rfl, rfl⟩
                            have hall := BinaryNatTokensDecode.cons htag <|
                              binaryNatTokensDecode_append hsequentTokens <|
                              binaryNatTokensDecode_append
                                (decodeCompactFormula_tokens_sound
                                  hleftFormula) <|
                              binaryNatTokensDecode_append
                                (decodeCompactFormula_tokens_sound
                                  hrightFormula) (ih hpremise)
                            simpa only [compactListedProofTokens,
                              List.append_assoc, List.cons_append, Nat.reduceAdd] using hall
              ·
                cases hformula : decodeCompactFormula 1 fuel afterSequent with
                | none =>
                    simp [hsequent, hformula] at hdecode
                | some formulaResult =>
                    rcases formulaResult with ⟨formula, afterFormula⟩
                    cases hpremise :
                        decodeCompactListedProof fuel afterFormula with
                    | none =>
                        simp [hsequent, hformula, hpremise] at hdecode
                    | some premiseResult =>
                        rcases premiseResult with ⟨premise, finalSuffix⟩
                        simp [hsequent, hformula, hpremise] at hdecode
                        rcases hdecode with ⟨rfl, rfl⟩
                        have hall := BinaryNatTokensDecode.cons htag <|
                          binaryNatTokensDecode_append hsequentTokens <|
                          binaryNatTokensDecode_append
                            (decodeCompactFormula_tokens_sound hformula)
                            (ih hpremise)
                        simpa only [compactListedProofTokens,
                          List.append_assoc, List.cons_append, Nat.reduceAdd] using hall
              ·
                cases hformula : decodeCompactFormula 1 fuel afterSequent with
                | none =>
                    simp [hsequent, hformula] at hdecode
                | some formulaResult =>
                    rcases formulaResult with ⟨formula, afterFormula⟩
                    cases hwitness : decodeCompactTerm 0 fuel afterFormula with
                    | none =>
                        simp [hsequent, hformula, hwitness] at hdecode
                    | some witnessResult =>
                        rcases witnessResult with ⟨witness, afterWitness⟩
                        cases hpremise :
                            decodeCompactListedProof fuel afterWitness with
                        | none =>
                            simp [hsequent, hformula, hwitness, hpremise] at hdecode
                        | some premiseResult =>
                            rcases premiseResult with ⟨premise, finalSuffix⟩
                            simp [hsequent, hformula, hwitness, hpremise] at hdecode
                            rcases hdecode with ⟨rfl, rfl⟩
                            have hall := BinaryNatTokensDecode.cons htag <|
                              binaryNatTokensDecode_append hsequentTokens <|
                              binaryNatTokensDecode_append
                                (decodeCompactFormula_tokens_sound hformula) <|
                              binaryNatTokensDecode_append
                                (decodeCompactTerm_tokens_sound hwitness)
                                (ih hpremise)
                            simpa only [compactListedProofTokens,
                              List.append_assoc, List.cons_append, Nat.reduceAdd] using hall
              ·
                cases hpremise : decodeCompactListedProof fuel afterSequent with
                | none =>
                    simp [hsequent, hpremise] at hdecode
                | some premiseResult =>
                    rcases premiseResult with ⟨premise, finalSuffix⟩
                    simp [hsequent, hpremise] at hdecode
                    rcases hdecode with ⟨rfl, rfl⟩
                    have hall := BinaryNatTokensDecode.cons htag <|
                      binaryNatTokensDecode_append
                        hsequentTokens (ih hpremise)
                    simpa only [compactListedProofTokens,
                      List.append_assoc, List.cons_append, Nat.reduceAdd] using hall
              ·
                cases hpremise : decodeCompactListedProof fuel afterSequent with
                | none =>
                    simp [hsequent, hpremise] at hdecode
                | some premiseResult =>
                    rcases premiseResult with ⟨premise, finalSuffix⟩
                    simp [hsequent, hpremise] at hdecode
                    rcases hdecode with ⟨rfl, rfl⟩
                    have hall := BinaryNatTokensDecode.cons htag <|
                      binaryNatTokensDecode_append
                        hsequentTokens (ih hpremise)
                    simpa only [compactListedProofTokens,
                      List.append_assoc, List.cons_append, Nat.reduceAdd] using hall
              ·
                cases hformula : decodeCompactFormula 0 fuel afterSequent with
                | none =>
                    simp [hsequent, hformula] at hdecode
                | some formulaResult =>
                    rcases formulaResult with ⟨formula, afterFormula⟩
                    cases hleftProof :
                        decodeCompactListedProof fuel afterFormula with
                    | none =>
                        simp [hsequent, hformula, hleftProof] at hdecode
                    | some leftProofResult =>
                        rcases leftProofResult with
                          ⟨leftProof, afterLeftProof⟩
                        cases hrightProof :
                            decodeCompactListedProof fuel afterLeftProof with
                        | none =>
                            simp [hsequent, hformula, hleftProof, hrightProof] at hdecode
                        | some rightProofResult =>
                            rcases rightProofResult with
                              ⟨rightProof, finalSuffix⟩
                            simp [hsequent, hformula, hleftProof, hrightProof] at hdecode
                            rcases hdecode with ⟨rfl, rfl⟩
                            have hall := BinaryNatTokensDecode.cons htag <|
                              binaryNatTokensDecode_append hsequentTokens <|
                              binaryNatTokensDecode_append
                                (decodeCompactFormula_tokens_sound hformula) <|
                              binaryNatTokensDecode_append
                                (ih hleftProof) (ih hrightProof)
                            simpa only [compactListedProofTokens,
                              List.append_assoc, List.cons_append, Nat.reduceAdd] using hall
              ·
                simp [hsequent] at hdecode

theorem binaryNatTokensDecode_suffix_length_lt
    {tokens : List Nat} {bits suffix : List Bool} {bound : Nat}
    (hdecode : BinaryNatTokensDecode tokens bits suffix)
    (hbits : bits.length < bound) :
    suffix.length < bound := by
  have hlength := binaryNatTokensDecode_length hdecode
  omega

set_option maxHeartbeats 1000000 in
theorem decodeCompactListedProof_tokens_complete_of_input_length
    (tree : ListedCheckedPAProofTree)
    (fuel : Nat) {bits suffix : List Bool}
    (hbits : bits.length < fuel)
    (htokens : BinaryNatTokensDecode
      (compactListedProofTokens tree) bits suffix) :
    decodeCompactListedProof fuel bits = some (tree, suffix) := by
  induction tree generalizing fuel bits suffix with
  | closed Gamma formula =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactListedProofTokens] at htokens
          cases htokens with
          | cons htag htail =>
              obtain ⟨afterSequent, hsequent, hformula⟩ :=
                binaryNatTokensDecode_split_append
                  (compactSequentListTokens Gamma)
                  (compactArithmeticFormulaTokens formula) htail
              have hafterTag := decodeBinaryNat_consumes_two htag
              have hsequentDecode :=
                decodeCompactSequentList_tokens_complete_of_input_length
                  Gamma fuel (by omega) hsequent
              have hafterSequent :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel) hsequent (by omega)
              have hformulaDecode :=
                decodeCompactFormula_tokens_complete_of_input_length
                  formula hafterSequent hformula
              simp [decodeCompactListedProof, htag,
                hsequentDecode, hformulaDecode]
  | axm Gamma sentence =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactListedProofTokens] at htokens
          cases htokens with
          | cons htag htail =>
              obtain ⟨afterSequent, hsequent, hformula⟩ :=
                binaryNatTokensDecode_split_append
                  (compactSequentListTokens Gamma)
                  (compactArithmeticFormulaTokens
                    (Rewriting.emb sentence :
                      LO.FirstOrder.ArithmeticProposition)) htail
              have hafterTag := decodeBinaryNat_consumes_two htag
              have hsequentDecode :=
                decodeCompactSequentList_tokens_complete_of_input_length
                  Gamma fuel (by omega) hsequent
              have hafterSequent :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel) hsequent (by omega)
              have hformulaDecode :=
                decodeCompactFormula_tokens_complete_of_input_length
                  (Rewriting.emb sentence :
                    LO.FirstOrder.ArithmeticProposition)
                  hafterSequent hformula
              simp [decodeCompactListedProof, htag,
                hsequentDecode, hformulaDecode, propositionToSentence]
  | verum Gamma =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactListedProofTokens] at htokens
          cases htokens with
          | cons htag hsequent =>
              have hafterTag := decodeBinaryNat_consumes_two htag
              have hsequentDecode :=
                decodeCompactSequentList_tokens_complete_of_input_length
                  Gamma fuel (by omega) hsequent
              simp [decodeCompactListedProof, htag, hsequentDecode]
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactListedProofTokens] at htokens
          cases htokens with
          | @cons _ _ _ afterTag _ htag htail =>
              obtain ⟨afterLeftProof, hbeforeRightProof, hrightProof⟩ :=
                binaryNatTokensDecode_split_append
                  (((compactSequentListTokens Gamma ++
                    compactArithmeticFormulaTokens leftFormula) ++
                    compactArithmeticFormulaTokens rightFormula) ++
                    compactListedProofTokens left)
                  (compactListedProofTokens right) htail
              obtain ⟨afterRightFormula, hbeforeLeftProof, hleftProof⟩ :=
                binaryNatTokensDecode_split_append
                  ((compactSequentListTokens Gamma ++
                    compactArithmeticFormulaTokens leftFormula) ++
                    compactArithmeticFormulaTokens rightFormula)
                  (compactListedProofTokens left) hbeforeRightProof
              obtain ⟨afterLeftFormula, hbeforeRightFormula,
                  hrightFormula⟩ :=
                binaryNatTokensDecode_split_append
                  (compactSequentListTokens Gamma ++
                    compactArithmeticFormulaTokens leftFormula)
                  (compactArithmeticFormulaTokens rightFormula)
                  hbeforeLeftProof
              obtain ⟨afterSequent, hsequent, hleftFormula⟩ :=
                binaryNatTokensDecode_split_append
                  (compactSequentListTokens Gamma)
                  (compactArithmeticFormulaTokens leftFormula)
                  hbeforeRightFormula
              have hafterTag := decodeBinaryNat_consumes_two htag
              have hsequentDecode :=
                decodeCompactSequentList_tokens_complete_of_input_length
                  Gamma fuel (by omega) hsequent
              have hafterSequent :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel) hsequent (by omega)
              have hleftFormulaDecode :=
                decodeCompactFormula_tokens_complete_of_input_length
                  leftFormula hafterSequent hleftFormula
              have hafterLeftFormula :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel)
                  hleftFormula hafterSequent
              have hrightFormulaDecode :=
                decodeCompactFormula_tokens_complete_of_input_length
                  rightFormula hafterLeftFormula hrightFormula
              have hafterRightFormula :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel)
                  hrightFormula hafterLeftFormula
              have hleftProofDecode :=
                ihLeft fuel hafterRightFormula hleftProof
              have hafterLeftProof :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel)
                  hleftProof hafterRightFormula
              have hrightProofDecode :=
                ihRight fuel hafterLeftProof hrightProof
              simp [decodeCompactListedProof, htag, hsequentDecode,
                hleftFormulaDecode, hrightFormulaDecode,
                hleftProofDecode, hrightProofDecode]
  | or Gamma leftFormula rightFormula premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactListedProofTokens] at htokens
          cases htokens with
          | @cons _ _ _ afterTag _ htag htail =>
              obtain ⟨afterRightFormula, hbeforePremise, hpremise⟩ :=
                binaryNatTokensDecode_split_append
                  ((compactSequentListTokens Gamma ++
                    compactArithmeticFormulaTokens leftFormula) ++
                    compactArithmeticFormulaTokens rightFormula)
                  (compactListedProofTokens premise) htail
              obtain ⟨afterLeftFormula, hbeforeRightFormula,
                  hrightFormula⟩ :=
                binaryNatTokensDecode_split_append
                  (compactSequentListTokens Gamma ++
                    compactArithmeticFormulaTokens leftFormula)
                  (compactArithmeticFormulaTokens rightFormula)
                  hbeforePremise
              obtain ⟨afterSequent, hsequent, hleftFormula⟩ :=
                binaryNatTokensDecode_split_append
                  (compactSequentListTokens Gamma)
                  (compactArithmeticFormulaTokens leftFormula)
                  hbeforeRightFormula
              have hafterTag := decodeBinaryNat_consumes_two htag
              have hsequentDecode :=
                decodeCompactSequentList_tokens_complete_of_input_length
                  Gamma fuel (by omega) hsequent
              have hafterSequent :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel) hsequent (by omega)
              have hleftFormulaDecode :=
                decodeCompactFormula_tokens_complete_of_input_length
                  leftFormula hafterSequent hleftFormula
              have hafterLeftFormula :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel)
                  hleftFormula hafterSequent
              have hrightFormulaDecode :=
                decodeCompactFormula_tokens_complete_of_input_length
                  rightFormula hafterLeftFormula hrightFormula
              have hafterRightFormula :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel)
                  hrightFormula hafterLeftFormula
              have hpremiseDecode :=
                ih fuel hafterRightFormula hpremise
              simp [decodeCompactListedProof, htag, hsequentDecode,
                hleftFormulaDecode, hrightFormulaDecode, hpremiseDecode]
  | all Gamma formula premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactListedProofTokens] at htokens
          cases htokens with
          | @cons _ _ _ afterTag _ htag htail =>
              obtain ⟨afterFormula, hbeforePremise, hpremise⟩ :=
                binaryNatTokensDecode_split_append
                  (compactSequentListTokens Gamma ++
                    compactArithmeticFormulaTokens formula)
                  (compactListedProofTokens premise) htail
              obtain ⟨afterSequent, hsequent, hformula⟩ :=
                binaryNatTokensDecode_split_append
                  (compactSequentListTokens Gamma)
                  (compactArithmeticFormulaTokens formula) hbeforePremise
              have hafterTag := decodeBinaryNat_consumes_two htag
              have hsequentDecode :=
                decodeCompactSequentList_tokens_complete_of_input_length
                  Gamma fuel (by omega) hsequent
              have hafterSequent :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel) hsequent (by omega)
              have hformulaDecode :=
                decodeCompactFormula_tokens_complete_of_input_length
                  formula hafterSequent hformula
              have hafterFormula :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel)
                  hformula hafterSequent
              have hpremiseDecode := ih fuel hafterFormula hpremise
              simp [decodeCompactListedProof, htag, hsequentDecode,
                hformulaDecode, hpremiseDecode]
  | exs Gamma formula witness premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactListedProofTokens] at htokens
          cases htokens with
          | @cons _ _ _ afterTag _ htag htail =>
              obtain ⟨afterWitness, hbeforePremise, hpremise⟩ :=
                binaryNatTokensDecode_split_append
                  ((compactSequentListTokens Gamma ++
                    compactArithmeticFormulaTokens formula) ++
                    compactArithmeticTermTokens witness)
                  (compactListedProofTokens premise) htail
              obtain ⟨afterFormula, hbeforeWitness, hwitness⟩ :=
                binaryNatTokensDecode_split_append
                  (compactSequentListTokens Gamma ++
                    compactArithmeticFormulaTokens formula)
                  (compactArithmeticTermTokens witness) hbeforePremise
              obtain ⟨afterSequent, hsequent, hformula⟩ :=
                binaryNatTokensDecode_split_append
                  (compactSequentListTokens Gamma)
                  (compactArithmeticFormulaTokens formula) hbeforeWitness
              have hafterTag := decodeBinaryNat_consumes_two htag
              have hsequentDecode :=
                decodeCompactSequentList_tokens_complete_of_input_length
                  Gamma fuel (by omega) hsequent
              have hafterSequent :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel) hsequent (by omega)
              have hformulaDecode :=
                decodeCompactFormula_tokens_complete_of_input_length
                  formula hafterSequent hformula
              have hafterFormula :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel)
                  hformula hafterSequent
              have hwitnessDecode :=
                decodeCompactTerm_tokens_complete_of_input_length
                  witness hafterFormula hwitness
              have hafterWitness :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel)
                  hwitness hafterFormula
              have hpremiseDecode := ih fuel hafterWitness hpremise
              simp [decodeCompactListedProof, htag, hsequentDecode,
                hformulaDecode, hwitnessDecode, hpremiseDecode]
  | wk Gamma premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactListedProofTokens] at htokens
          cases htokens with
          | cons htag htail =>
              obtain ⟨afterSequent, hsequent, hpremise⟩ :=
                binaryNatTokensDecode_split_append
                  (compactSequentListTokens Gamma)
                  (compactListedProofTokens premise) htail
              have hafterTag := decodeBinaryNat_consumes_two htag
              have hsequentDecode :=
                decodeCompactSequentList_tokens_complete_of_input_length
                  Gamma fuel (by omega) hsequent
              have hafterSequent :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel) hsequent (by omega)
              have hpremiseDecode := ih fuel hafterSequent hpremise
              simp [decodeCompactListedProof, htag,
                hsequentDecode, hpremiseDecode]
  | shift Gamma premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactListedProofTokens] at htokens
          cases htokens with
          | cons htag htail =>
              obtain ⟨afterSequent, hsequent, hpremise⟩ :=
                binaryNatTokensDecode_split_append
                  (compactSequentListTokens Gamma)
                  (compactListedProofTokens premise) htail
              have hafterTag := decodeBinaryNat_consumes_two htag
              have hsequentDecode :=
                decodeCompactSequentList_tokens_complete_of_input_length
                  Gamma fuel (by omega) hsequent
              have hafterSequent :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel) hsequent (by omega)
              have hpremiseDecode := ih fuel hafterSequent hpremise
              simp [decodeCompactListedProof, htag,
                hsequentDecode, hpremiseDecode]
  | cut Gamma formula left right ihLeft ihRight =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactListedProofTokens] at htokens
          cases htokens with
          | @cons _ _ _ afterTag _ htag htail =>
              obtain ⟨afterLeftProof, hbeforeRightProof, hrightProof⟩ :=
                binaryNatTokensDecode_split_append
                  ((compactSequentListTokens Gamma ++
                    compactArithmeticFormulaTokens formula) ++
                    compactListedProofTokens left)
                  (compactListedProofTokens right) htail
              obtain ⟨afterFormula, hbeforeLeftProof, hleftProof⟩ :=
                binaryNatTokensDecode_split_append
                  (compactSequentListTokens Gamma ++
                    compactArithmeticFormulaTokens formula)
                  (compactListedProofTokens left) hbeforeRightProof
              obtain ⟨afterSequent, hsequent, hformula⟩ :=
                binaryNatTokensDecode_split_append
                  (compactSequentListTokens Gamma)
                  (compactArithmeticFormulaTokens formula) hbeforeLeftProof
              have hafterTag := decodeBinaryNat_consumes_two htag
              have hsequentDecode :=
                decodeCompactSequentList_tokens_complete_of_input_length
                  Gamma fuel (by omega) hsequent
              have hafterSequent :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel) hsequent (by omega)
              have hformulaDecode :=
                decodeCompactFormula_tokens_complete_of_input_length
                  formula hafterSequent hformula
              have hafterFormula :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel)
                  hformula hafterSequent
              have hleftProofDecode :=
                ihLeft fuel hafterFormula hleftProof
              have hafterLeftProof :=
                binaryNatTokensDecode_suffix_length_lt (bound := fuel)
                  hleftProof hafterFormula
              have hrightProofDecode :=
                ihRight fuel hafterLeftProof hrightProof
              simp [decodeCompactListedProof, htag, hsequentDecode,
                hformulaDecode, hleftProofDecode, hrightProofDecode]

theorem decodeCompactListedProof_success_iff_tokens
    (tree : ListedCheckedPAProofTree)
    (fuel : Nat) (bits suffix : List Bool)
    (hbits : bits.length < fuel) :
    decodeCompactListedProof fuel bits = some (tree, suffix) <->
      BinaryNatTokensDecode
        (compactListedProofTokens tree) bits suffix := by
  constructor
  · exact decodeCompactListedProof_tokens_sound
  · exact decodeCompactListedProof_tokens_complete_of_input_length
      tree fuel hbits


#print axioms decodeCompactSequentList_tokens_sound
#print axioms decodeCompactSequentList_tokens_complete_of_input_length
#print axioms decodeCompactListedProof_tokens_sound
#print axioms decodeCompactListedProof_tokens_complete_of_input_length
#print axioms decodeCompactListedProof_success_iff_tokens

end FoundationCompactProofBitTokenSynchronization
