import integration.FoundationCompactSyntaxBitTokenSynchronization
import integration.FoundationCompactCertificateTokenMachine

/-!
# Exact bit/token synchronization for compact PA certificates

The typed PA-axiom and structural-certificate decoders use the same natural
tokens as the primitive-recursive certificate machines.  These proofs retain
the exact residual bit list and allow noncanonical encodings of every natural.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertificateBitTokenSynchronization

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertificateTokenMachine
open FoundationCompactSyntaxTokenMachine
open FoundationCompactBinaryNatStreamSynchronization
open FoundationCompactSyntaxBitTokenSynchronization
open FoundationCompactVerifierStructuralBound

theorem binaryNatTokensDecode_suffix_length_lt
    {tokens : List Nat} {bits suffix : List Bool} {bound : Nat}
    (hdecode : BinaryNatTokensDecode tokens bits suffix)
    (hbits : bits.length < bound) :
    suffix.length < bound := by
  have hlength := binaryNatTokensDecode_length hdecode
  omega

theorem decodePAAxiomCertificate_tokens_complete_of_input_length
    (certificate : PAAxiomCertificate)
    (fuel : Nat) {bits suffix : List Bool}
    (hbits : bits.length < fuel)
    (htokens : BinaryNatTokensDecode
      (compactPAAxiomCertificateTokens certificate) bits suffix) :
    decodePAAxiomCertificate fuel bits = some (certificate, suffix) := by
  cases certificate with
  | eqRefl =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | eqSymm =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | eqTrans =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | eqFuncExt functionSymbol =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hrest =>
              cases hrest with
              | cons harity hrest =>
                  cases hrest with
                  | cons hfunction hdone =>
                      cases hdone
                      simp [decodePAAxiomCertificate, htag, harity,
                        hfunction, Encodable.decode₂_encode]
  | eqRelExt relationSymbol =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hrest =>
              cases hrest with
              | cons harity hrest =>
                  cases hrest with
                  | cons hrelation hdone =>
                      cases hdone
                      simp [decodePAAxiomCertificate, htag, harity,
                        hrelation, Encodable.decode₂_encode]
  | addZero =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | addAssoc =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | addComm =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | addEqOfLt =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | zeroLe =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | zeroLtOne =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | oneLeOfZeroLt =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | addLtAdd =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | mulZero =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | mulOne =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | mulAssoc =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | mulComm =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | mulLtMul =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | distr =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | ltIrrefl =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | ltTrans =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | ltTri =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone => cases hdone; simp [decodePAAxiomCertificate, htag]
  | induction body =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactPAAxiomCertificateTokens] at htokens
          cases htokens with
          | cons htag hbody =>
              have hafterTag := decodeBinaryNat_consumes_two htag
              have hbodyDecode :=
                decodeCompactFormula_tokens_complete_of_input_length
                  (fuel := fuel) body (by omega) hbody
              simp [decodePAAxiomCertificate, htag, hbodyDecode]

set_option maxHeartbeats 600000 in
theorem decodePAAxiomCertificate_tokens_sound :
    forall {fuel bits suffix certificate},
      decodePAAxiomCertificate fuel bits = some (certificate, suffix) ->
        BinaryNatTokensDecode
          (compactPAAxiomCertificateTokens certificate) bits suffix := by
  intro fuel
  induction fuel with
  | zero =>
      intro bits suffix certificate hdecode
      simp [decodePAAxiomCertificate] at hdecode
  | succ fuel ih =>
      intro bits suffix certificate hdecode
      cases htag : decodeBinaryNat bits with
      | none => simp [decodePAAxiomCertificate, htag] at hdecode
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          rcases tag with
            (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
             _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | tag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · cases harity : decodeBinaryNat afterTag with
            | none => simp [decodePAAxiomCertificate, htag, harity] at hdecode
            | some arityResult =>
                rcases arityResult with ⟨arity, afterArity⟩
                cases hfunction : decodeBinaryNat afterArity with
                | none =>
                    simp [decodePAAxiomCertificate, htag, harity,
                      hfunction] at hdecode
                | some functionResult =>
                    rcases functionResult with ⟨functionCode, afterFunction⟩
                    cases hsymbol :
                        (Encodable.decode₂ _ functionCode :
                          Option (LO.FirstOrder.Language.Func ℒₒᵣ arity)) with
                    | none =>
                        simp [decodePAAxiomCertificate, htag, harity,
                          hfunction, hsymbol] at hdecode
                    | some functionSymbol =>
                        simp [decodePAAxiomCertificate, htag, harity,
                          hfunction, hsymbol] at hdecode
                        rcases hdecode with ⟨rfl, rfl⟩
                        have hcode : Encodable.encode functionSymbol =
                            functionCode :=
                          Encodable.decode₂_eq_some.mp hsymbol
                        simp only [compactPAAxiomCertificateTokens]
                        rw [hcode]
                        exact .cons htag <| .cons harity <|
                          .cons hfunction (.nil afterFunction)
          · cases harity : decodeBinaryNat afterTag with
            | none => simp [decodePAAxiomCertificate, htag, harity] at hdecode
            | some arityResult =>
                rcases arityResult with ⟨arity, afterArity⟩
                cases hrelation : decodeBinaryNat afterArity with
                | none =>
                    simp [decodePAAxiomCertificate, htag, harity,
                      hrelation] at hdecode
                | some relationResult =>
                    rcases relationResult with ⟨relationCode, afterRelation⟩
                    cases hsymbol :
                        (Encodable.decode₂ _ relationCode :
                          Option (LO.FirstOrder.Language.Rel ℒₒᵣ arity)) with
                    | none =>
                        simp [decodePAAxiomCertificate, htag, harity,
                          hrelation, hsymbol] at hdecode
                    | some relationSymbol =>
                        simp [decodePAAxiomCertificate, htag, harity,
                          hrelation, hsymbol] at hdecode
                        rcases hdecode with ⟨rfl, rfl⟩
                        have hcode : Encodable.encode relationSymbol =
                            relationCode :=
                          Encodable.decode₂_eq_some.mp hsymbol
                        simp only [compactPAAxiomCertificateTokens]
                        rw [hcode]
                        exact .cons htag <| .cons harity <|
                          .cons hrelation (.nil afterRelation)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · simp [decodePAAxiomCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · cases hbody : decodeCompactFormula 1 fuel afterTag with
            | none => simp [decodePAAxiomCertificate, htag, hbody] at hdecode
            | some bodyResult =>
                rcases bodyResult with ⟨body, afterBody⟩
                simp [decodePAAxiomCertificate, htag, hbody] at hdecode
                rcases hdecode with ⟨rfl, rfl⟩
                exact .cons htag (decodeCompactFormula_tokens_sound hbody)
          · simp [decodePAAxiomCertificate, htag] at hdecode

theorem decodePAAxiomCertificate_success_iff_tokens
    (certificate : PAAxiomCertificate)
    (fuel : Nat) (bits suffix : List Bool)
    (hbits : bits.length < fuel) :
    decodePAAxiomCertificate fuel bits = some (certificate, suffix) <->
      BinaryNatTokensDecode
        (compactPAAxiomCertificateTokens certificate) bits suffix := by
  constructor
  · exact decodePAAxiomCertificate_tokens_sound
  · exact decodePAAxiomCertificate_tokens_complete_of_input_length
      certificate fuel hbits

set_option maxHeartbeats 600000 in
theorem decodeStructuralValidityCertificate_tokens_complete_of_input_length
    (certificate : StructuralValidityCertificate)
    (fuel : Nat) {bits suffix : List Bool}
    (hbits : bits.length < fuel)
    (htokens : BinaryNatTokensDecode
      (compactStructuralCertificateTokens certificate) bits suffix) :
    decodeStructuralValidityCertificate fuel bits =
      some (certificate, suffix) := by
  induction certificate generalizing fuel bits suffix with
  | leaf =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactStructuralCertificateTokens] at htokens
          cases htokens with
          | cons htag hdone =>
              cases hdone
              simp [decodeStructuralValidityCertificate, htag]
  | axiomCert certificate =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactStructuralCertificateTokens] at htokens
          cases htokens with
          | cons htag haxiom =>
              have hafterTag := decodeBinaryNat_consumes_two htag
              have haxiomDecode :=
                decodePAAxiomCertificate_tokens_complete_of_input_length
                  certificate fuel (by omega) haxiom
              simp [decodeStructuralValidityCertificate, htag, haxiomDecode]
  | unary premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactStructuralCertificateTokens] at htokens
          cases htokens with
          | cons htag hpremise =>
              have hafterTag := decodeBinaryNat_consumes_two htag
              have hpremiseDecode := ih fuel (by omega) hpremise
              simp [decodeStructuralValidityCertificate, htag, hpremiseDecode]
  | binary left right ihLeft ihRight =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [compactStructuralCertificateTokens] at htokens
          cases htokens with
          | cons htag htail =>
              obtain ⟨afterLeft, hleft, hright⟩ :=
                binaryNatTokensDecode_split_append
                  (compactStructuralCertificateTokens left)
                  (compactStructuralCertificateTokens right) htail
              have hafterTag := decodeBinaryNat_consumes_two htag
              have hleftDecode := ihLeft fuel (by omega) hleft
              have hafterLeft :=
                binaryNatTokensDecode_suffix_length_lt
                  (bound := fuel) hleft (by omega)
              have hrightDecode := ihRight fuel hafterLeft hright
              simp [decodeStructuralValidityCertificate, htag,
                hleftDecode, hrightDecode]

set_option maxHeartbeats 600000 in
theorem decodeStructuralValidityCertificate_tokens_sound :
    forall {fuel bits suffix certificate},
      decodeStructuralValidityCertificate fuel bits =
        some (certificate, suffix) ->
      BinaryNatTokensDecode
        (compactStructuralCertificateTokens certificate) bits suffix := by
  intro fuel
  induction fuel with
  | zero =>
      intro bits suffix certificate hdecode
      simp [decodeStructuralValidityCertificate] at hdecode
  | succ fuel ih =>
      intro bits suffix certificate hdecode
      cases htag : decodeBinaryNat bits with
      | none =>
          simp [decodeStructuralValidityCertificate, htag] at hdecode
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          rcases tag with (_ | _ | _ | _ | tag)
          · simp [decodeStructuralValidityCertificate, htag] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            exact .cons htag (.nil afterTag)
          · cases haxiom : decodePAAxiomCertificate fuel afterTag with
            | none =>
                simp [decodeStructuralValidityCertificate, htag,
                  haxiom] at hdecode
            | some axiomResult =>
                rcases axiomResult with ⟨axiomCertificate, afterAxiom⟩
                simp [decodeStructuralValidityCertificate, htag,
                  haxiom] at hdecode
                rcases hdecode with ⟨rfl, rfl⟩
                exact .cons htag
                  (decodePAAxiomCertificate_tokens_sound haxiom)
          · cases hpremise :
                decodeStructuralValidityCertificate fuel afterTag with
            | none =>
                simp [decodeStructuralValidityCertificate, htag,
                  hpremise] at hdecode
            | some premiseResult =>
                rcases premiseResult with ⟨premise, afterPremise⟩
                simp [decodeStructuralValidityCertificate, htag,
                  hpremise] at hdecode
                rcases hdecode with ⟨rfl, rfl⟩
                exact .cons htag (ih hpremise)
          · cases hleft :
                decodeStructuralValidityCertificate fuel afterTag with
            | none =>
                simp [decodeStructuralValidityCertificate, htag,
                  hleft] at hdecode
            | some leftResult =>
                rcases leftResult with ⟨left, afterLeft⟩
                cases hright :
                    decodeStructuralValidityCertificate fuel afterLeft with
                | none =>
                    simp [decodeStructuralValidityCertificate, htag,
                      hleft, hright] at hdecode
                | some rightResult =>
                    rcases rightResult with ⟨right, afterRight⟩
                    simp [decodeStructuralValidityCertificate, htag,
                      hleft, hright] at hdecode
                    rcases hdecode with ⟨rfl, rfl⟩
                    exact .cons htag <|
                      binaryNatTokensDecode_append
                        (ih hleft) (ih hright)
          · simp [decodeStructuralValidityCertificate, htag] at hdecode

theorem decodeStructuralValidityCertificate_success_iff_tokens
    (certificate : StructuralValidityCertificate)
    (fuel : Nat) (bits suffix : List Bool)
    (hbits : bits.length < fuel) :
    decodeStructuralValidityCertificate fuel bits =
        some (certificate, suffix) <->
      BinaryNatTokensDecode
        (compactStructuralCertificateTokens certificate) bits suffix := by
  constructor
  · exact decodeStructuralValidityCertificate_tokens_sound
  · exact
      decodeStructuralValidityCertificate_tokens_complete_of_input_length
        certificate fuel hbits

#print axioms decodePAAxiomCertificate_tokens_complete_of_input_length
#print axioms decodePAAxiomCertificate_tokens_sound
#print axioms decodePAAxiomCertificate_success_iff_tokens
#print axioms decodeStructuralValidityCertificate_tokens_complete_of_input_length
#print axioms decodeStructuralValidityCertificate_tokens_sound
#print axioms decodeStructuralValidityCertificate_success_iff_tokens

end FoundationCompactCertificateBitTokenSynchronization
