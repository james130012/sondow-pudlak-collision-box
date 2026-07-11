import integration.FoundationCompactCertificateDecoderCost
import integration.FoundationCompactListedCertifiedVerifier

/-!
# Cost trace for the public list-preserving certified verifier decoder

This file connects the proof-tree and certificate decoder traces, charges the
packed-natural envelope, and proves exact result agreement with both public
packed decoders and the public Boolean verifier.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedCertifiedDecoderCost

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertifiedVerifier
open FoundationCompactListedCertificateVerifier
open FoundationCompactNatDecoderCost
open FoundationCompactSyntaxDecoderCost
open FoundationCompactListedProofDecoderCost
open FoundationCompactCertificateDecoderCost

def decodeCompactListedCertifiedPAProofTrace
    (fuel : Nat) (bits : List Bool) :
    OptionTrace
      ((ListedCheckedPAProofTree × StructuralValidityCertificate) ×
        List Bool) :=
  traceBind (decodeCompactListedProofTrace fuel bits) fun treeResult =>
    traceBind
      (decodeStructuralValidityCertificateTrace fuel treeResult.2)
      fun certificateResult =>
        tracePure ((treeResult.1, certificateResult.1), certificateResult.2)

theorem decodeCompactListedCertifiedPAProofTrace_result
    (fuel : Nat) (bits : List Bool) :
    (decodeCompactListedCertifiedPAProofTrace fuel bits).1 =
      decodeCompactListedCertifiedPAProof fuel bits := by
  simp [decodeCompactListedCertifiedPAProofTrace,
    decodeCompactListedCertifiedPAProof, traceBind_result,
    tracePure_result, decodeCompactListedProofTrace_result,
    decodeStructuralValidityCertificateTrace_result]

/-- Read the canonical sentinel-terminated payload of a packed natural.  The
cost charges reading the natural bits, locating the sentinel, and dropping it.
-/
def packedPayloadTrace (code : Nat) : OptionTrace (List Bool) :=
  let bits := code.bits
  if bits.getLast? = some true then
    (some bits.dropLast, Nat.size code + bits.length + 3)
  else
    (none, Nat.size code + bits.length + 2)

theorem packedPayloadTrace_result (code : Nat) :
    (packedPayloadTrace code).1 =
      if code.bits.getLast? = some true then
        some code.bits.dropLast
      else none := by
  by_cases hlast : code.bits.getLast? = some true <;>
    simp [packedPayloadTrace, hlast]

theorem packedPayloadTrace_result_guard (code : Nat) :
    (packedPayloadTrace code).1 =
      ((guard (code.bits.getLast? = some true) : Option PUnit).bind
        fun _ => some code.bits.dropLast) := by
  by_cases hlast : code.bits.getLast? = some true <;>
    simp [packedPayloadTrace, hlast]

def requireEmptySuffixTrace {alpha : Type*}
    (value : alpha) (suffix : List Bool) : OptionTrace alpha :=
  if suffix.isEmpty then
    (some value, suffix.length + 2)
  else
    (none, suffix.length + 2)

theorem requireEmptySuffixTrace_result {alpha : Type*}
    (value : alpha) (suffix : List Bool) :
    (requireEmptySuffixTrace value suffix).1 =
      if suffix.isEmpty then some value else none := by
  cases suffix <;> simp [requireEmptySuffixTrace]

theorem requireEmptySuffixTrace_result_guard {alpha : Type*}
    (value : alpha) (suffix : List Bool) :
    (requireEmptySuffixTrace value suffix).1 =
      ((guard (suffix = []) : Option PUnit).bind fun _ => some value) := by
  cases suffix <;> simp [requireEmptySuffixTrace]

def decodeCompactPackedListedCertifiedPAProofTrace
    (code : Nat) :
    OptionTrace (ListedCheckedPAProofTree × StructuralValidityCertificate) :=
  traceBind (packedPayloadTrace code) fun payload =>
    traceBind
      (decodeCompactListedCertifiedPAProofTrace
        (payload.length + 1) payload)
      fun proofResult =>
        requireEmptySuffixTrace proofResult.1 proofResult.2

theorem decodeCompactPackedListedCertifiedPAProofTrace_result
    (code : Nat) :
    (decodeCompactPackedListedCertifiedPAProofTrace code).1 =
      decodeCompactPackedListedCertifiedPAProof code := by
  by_cases hlast : code.bits.getLast? = some true
  · simp [decodeCompactPackedListedCertifiedPAProofTrace,
      decodeCompactPackedListedCertifiedPAProof, traceBind_result,
      packedPayloadTrace_result_guard, hlast,
      decodeCompactListedCertifiedPAProofTrace_result,
      requireEmptySuffixTrace_result_guard, List.length_dropLast]
  · simp [decodeCompactPackedListedCertifiedPAProofTrace,
      decodeCompactPackedListedCertifiedPAProof, traceBind_result,
      packedPayloadTrace_result_guard, hlast]

def decodeCompactPackedFormulaTrace
    (code : Nat) : OptionTrace LO.FirstOrder.ArithmeticProposition :=
  traceBind (packedPayloadTrace code) fun payload =>
    traceBind
      (decodeCompactFormulaTrace 0 (payload.length + 1) payload)
      fun formulaResult =>
        requireEmptySuffixTrace formulaResult.1 formulaResult.2

theorem decodeCompactPackedFormulaTrace_result (code : Nat) :
    (decodeCompactPackedFormulaTrace code).1 =
      decodeCompactPackedFormula code := by
  by_cases hlast : code.bits.getLast? = some true
  · simp [decodeCompactPackedFormulaTrace, decodeCompactPackedFormula,
      traceBind_result, packedPayloadTrace_result_guard, hlast,
      decodeCompactFormulaTrace_result,
      requireEmptySuffixTrace_result_guard,
      List.length_dropLast]
  · simp [decodeCompactPackedFormulaTrace, decodeCompactPackedFormula,
      traceBind_result, packedPayloadTrace_result_guard, hlast]

def listedCompactCertifiedPAProofVerifierTrace
    (code formulaCode : Nat) : Bool × Nat :=
  let proofTrace := decodeCompactPackedListedCertifiedPAProofTrace code
  let formulaTrace := decodeCompactPackedFormulaTrace formulaCode
  match proofTrace.1, formulaTrace.1 with
  | some (tree, certificate), some formula =>
      let localTrace :=
        listedCertifiedPAProofLocalTrace
          tree certificate formula formulaCode
      (localTrace.1, proofTrace.2 + formulaTrace.2 + localTrace.2 + 1)
  | _, _ => (false, proofTrace.2 + formulaTrace.2 + 1)

theorem listedCompactCertifiedPAProofVerifierTrace_result
    (code formulaCode : Nat) :
    (listedCompactCertifiedPAProofVerifierTrace code formulaCode).1 =
      listedCompactCertifiedPAProofVerifier code formulaCode := by
  simp only [listedCompactCertifiedPAProofVerifierTrace,
    listedCompactCertifiedPAProofVerifier]
  rw [decodeCompactPackedListedCertifiedPAProofTrace_result,
    decodeCompactPackedFormulaTrace_result]
  cases decodeCompactPackedListedCertifiedPAProof code <;>
    cases decodeCompactPackedFormula formulaCode <;> rfl

#print axioms decodeCompactListedCertifiedPAProofTrace_result
#print axioms decodeCompactPackedListedCertifiedPAProofTrace_result
#print axioms decodeCompactPackedFormulaTrace_result
#print axioms listedCompactCertifiedPAProofVerifierTrace_result

end FoundationCompactListedCertifiedDecoderCost
