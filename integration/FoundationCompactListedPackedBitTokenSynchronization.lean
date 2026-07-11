import integration.FoundationCompactProofBitTokenSynchronization
import integration.FoundationCompactCertificateBitTokenSynchronization
import integration.FoundationCompactListedCertifiedVerifier

/-!
# Exact packed-input synchronization for the listed certified verifier

The public verifier receives two sentinel-terminated natural-number inputs.
This file connects those exact packed inputs to the primitive-recursive stream
of natural tokens.  The relation preserves the actual bit suffix and therefore
covers noncanonical `binaryNat` encodings rather than silently replacing them
with canonical bit strings.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedPackedBitTokenSynchronization

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertifiedVerifier
open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedVerifierArithmeticInput
open FoundationCompactBinaryNatStreamMachine
open FoundationCompactBinaryNatStreamSynchronization
open FoundationCompactProofBitTokenSynchronization
open FoundationCompactCertificateBitTokenSynchronization
open FoundationCompactSyntaxBitTokenSynchronization

def compactListedCertifiedTokens
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) : List Nat :=
  compactListedProofTokens tree ++
    compactStructuralCertificateTokens certificate

theorem decodeCompactListedCertifiedPAProof_tokens_sound
    {fuel : Nat} {bits suffix : List Bool}
    {tree : ListedCheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    (hdecode : decodeCompactListedCertifiedPAProof fuel bits =
      some ((tree, certificate), suffix)) :
    BinaryNatTokensDecode
      (compactListedCertifiedTokens tree certificate) bits suffix := by
  cases htree : decodeCompactListedProof fuel bits with
  | none =>
      simp [decodeCompactListedCertifiedPAProof, htree] at hdecode
  | some treeResult =>
      rcases treeResult with ⟨decodedTree, afterTree⟩
      cases hcertificate :
          decodeStructuralValidityCertificate fuel afterTree with
      | none =>
          simp [decodeCompactListedCertifiedPAProof, htree,
            hcertificate] at hdecode
      | some certificateResult =>
          rcases certificateResult with
            ⟨decodedCertificate, afterCertificate⟩
          simp [decodeCompactListedCertifiedPAProof, htree,
            hcertificate] at hdecode
          rcases hdecode with ⟨⟨rfl, rfl⟩, rfl⟩
          exact binaryNatTokensDecode_append
            (decodeCompactListedProof_tokens_sound htree)
            (decodeStructuralValidityCertificate_tokens_sound hcertificate)

theorem decodeCompactListedCertifiedPAProof_tokens_complete_of_input_length
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (fuel : Nat) {bits suffix : List Bool}
    (hbits : bits.length < fuel)
    (htokens : BinaryNatTokensDecode
      (compactListedCertifiedTokens tree certificate) bits suffix) :
    decodeCompactListedCertifiedPAProof fuel bits =
      some ((tree, certificate), suffix) := by
  obtain ⟨afterTree, htree, hcertificate⟩ :=
    binaryNatTokensDecode_split_append
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate) htokens
  have htreeDecode :=
    decodeCompactListedProof_tokens_complete_of_input_length
      tree fuel hbits htree
  have hafterTree :=
    FoundationCompactProofBitTokenSynchronization.binaryNatTokensDecode_suffix_length_lt
      (bound := fuel) htree hbits
  have hcertificateDecode :=
    decodeStructuralValidityCertificate_tokens_complete_of_input_length
      certificate fuel hafterTree hcertificate
  simp [decodeCompactListedCertifiedPAProof,
    htreeDecode, hcertificateDecode]

theorem decodeCompactListedCertifiedPAProof_success_iff_tokens
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (fuel : Nat) (bits suffix : List Bool)
    (hbits : bits.length < fuel) :
    decodeCompactListedCertifiedPAProof fuel bits =
        some ((tree, certificate), suffix) <->
      BinaryNatTokensDecode
        (compactListedCertifiedTokens tree certificate) bits suffix := by
  constructor
  · exact decodeCompactListedCertifiedPAProof_tokens_sound
  · exact
      decodeCompactListedCertifiedPAProof_tokens_complete_of_input_length
        tree certificate fuel hbits

/-- Pure numeric tokenization of the exact sentinel-packed public input. -/
def compactPackedTokenStream (code : Nat) : Option (List Nat) :=
  (packedPayloadBits code).bind binaryNatStreamTokens

theorem compactPackedTokenStream_primrec :
    Primrec compactPackedTokenStream := by
  exact
    (Primrec.option_bind packedPayloadBits_primrec
      ((binaryNatStreamTokens_primrec.comp Primrec.snd).to₂)).of_eq
        fun code => by rfl

theorem compactPackedTokenStream_success_iff
    (code : Nat) (tokens : List Nat) :
    compactPackedTokenStream code = some tokens <->
      exists payload,
        packedPayloadBits code = some payload /\
          BinaryNatTokensDecode tokens payload [] := by
  cases hpayload : packedPayloadBits code with
  | none =>
      simp [compactPackedTokenStream, hpayload]
  | some payload =>
      simp only [compactPackedTokenStream, hpayload, Option.bind_some]
      rw [binaryNatStreamTokens_eq_decodeBinaryNatStream,
        decodeBinaryNatStream_success_iff]
      constructor
      · intro htokens
        exact ⟨payload, rfl, htokens⟩
      · rintro ⟨decodedPayload, hdecodedPayload, htokens⟩
        cases hdecodedPayload
        exact htokens

theorem decodeCompactPackedListedCertifiedPAProof_success_iff_tokens
    (code : Nat) (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    decodeCompactPackedListedCertifiedPAProof code =
        some (tree, certificate) <->
      exists payload,
        packedPayloadBits code = some payload /\
          BinaryNatTokensDecode
            (compactListedCertifiedTokens tree certificate) payload [] := by
  constructor
  · intro hdecode
    simp only [decodeCompactPackedListedCertifiedPAProof] at hdecode
    cases hlast : code.bits.getLast? with
    | none => simp [hlast] at hdecode
    | some lastBit =>
        cases lastBit with
        | false => simp [hlast] at hdecode
        | true =>
            cases hproof :
                decodeCompactListedCertifiedPAProof
                  (code.bits.length - 1 + 1) code.bits.dropLast with
            | none => simp [hlast, hproof] at hdecode
            | some proofResult =>
                rcases proofResult with ⟨decodedProof, suffix⟩
                cases suffix with
                | cons head tail => simp [hlast, hproof] at hdecode
                | nil =>
                    rcases decodedProof with
                      ⟨decodedTree, decodedCertificate⟩
                    simp [hlast, hproof] at hdecode
                    rcases hdecode with ⟨rfl, rfl⟩
                    refine ⟨code.bits.dropLast, ?_, ?_⟩
                    · simp [packedPayloadBits, hlast]
                    · exact
                        decodeCompactListedCertifiedPAProof_tokens_sound hproof
  · rintro ⟨payload, hpayload, htokens⟩
    have hpack :=
      (packedPayloadBits_eq_some_iff code payload).mp hpayload
    rw [<- hpack]
    have hdecode :=
      decodeCompactListedCertifiedPAProof_tokens_complete_of_input_length
        tree certificate (payload.length + 1) (by omega) htokens
    simp [decodeCompactPackedListedCertifiedPAProof, hdecode]

theorem compactPackedTokenStream_eq_proofTokens_iff
    (code : Nat) (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    compactPackedTokenStream code =
        some (compactListedCertifiedTokens tree certificate) <->
      decodeCompactPackedListedCertifiedPAProof code =
        some (tree, certificate) := by
  rw [compactPackedTokenStream_success_iff]
  exact
    (decodeCompactPackedListedCertifiedPAProof_success_iff_tokens
      code tree certificate).symm

theorem decodeCompactPackedFormula_success_iff_tokens
    (code : Nat) (formula : LO.FirstOrder.ArithmeticProposition) :
    decodeCompactPackedFormula code = some formula <->
      exists payload,
        packedPayloadBits code = some payload /\
          BinaryNatTokensDecode
            (compactArithmeticFormulaTokens formula) payload [] := by
  constructor
  · intro hdecode
    simp only [decodeCompactPackedFormula] at hdecode
    cases hlast : code.bits.getLast? with
    | none => simp [hlast] at hdecode
    | some lastBit =>
        cases lastBit with
        | false => simp [hlast] at hdecode
        | true =>
            cases hformula :
                decodeCompactFormula 0
                  (code.bits.length - 1 + 1) code.bits.dropLast with
            | none => simp [hlast, hformula] at hdecode
            | some formulaResult =>
                rcases formulaResult with ⟨decodedFormula, suffix⟩
                cases suffix with
                | cons head tail => simp [hlast, hformula] at hdecode
                | nil =>
                    simp [hlast, hformula] at hdecode
                    subst decodedFormula
                    refine ⟨code.bits.dropLast, ?_, ?_⟩
                    · simp [packedPayloadBits, hlast]
                    · exact decodeCompactFormula_tokens_sound hformula
  · rintro ⟨payload, hpayload, htokens⟩
    have hpack :=
      (packedPayloadBits_eq_some_iff code payload).mp hpayload
    rw [<- hpack]
    have hdecode :=
      decodeCompactFormula_tokens_complete_of_input_length
        formula (fuel := payload.length + 1) (by omega) htokens
    simp [decodeCompactPackedFormula, hdecode]

theorem compactPackedTokenStream_eq_formulaTokens_iff
    (code : Nat) (formula : LO.FirstOrder.ArithmeticProposition) :
    compactPackedTokenStream code =
        some (compactArithmeticFormulaTokens formula) <->
      decodeCompactPackedFormula code = some formula := by
  rw [compactPackedTokenStream_success_iff]
  exact (decodeCompactPackedFormula_success_iff_tokens code formula).symm

#print axioms decodeCompactListedCertifiedPAProof_success_iff_tokens
#print axioms compactPackedTokenStream_primrec
#print axioms compactPackedTokenStream_eq_proofTokens_iff
#print axioms compactPackedTokenStream_eq_formulaTokens_iff

end FoundationCompactListedPackedBitTokenSynchronization
