import integration.FoundationCompactNumericListedDirectTokenStreamInverse
import integration.FoundationCompactNumericListedPublicVerifier

/-!
# Direct arithmetic tableaux for both public verifier inputs

The proof input may use redundant high zero bits in a `binaryNat` token.  This
module normalizes that input without increasing the honest payload cutoff.  An
accepted formula input is already canonical because the public verifier checks
its payload against the canonical formula token stream.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectInputTableau

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactAdditiveTokenCodec
open FoundationCompactListedPackedBitTokenSynchronization
open FoundationCompactNumericListedPublicVerifier
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTokenStreamInverse

/-- The two public inputs, represented by the same direct canonical token
tableau relation. -/
def CompactCanonicalVerifierInputTableaux
    (proofCode formulaCode
      proofTokenCount proofTokenTable proofOffsetTable
      formulaTokenCount formulaTokenTable formulaOffsetTable : Nat) : Prop :=
  CompactCanonicalPackedTokenStreamTableau
      proofCode proofTokenCount proofTokenTable proofOffsetTable ∧
    CompactCanonicalPackedTokenStreamTableau
      formulaCode formulaTokenCount formulaTokenTable formulaOffsetTable

/-- Handwritten bounded arithmetic graph for both verifier input streams. -/
def compactCanonicalVerifierInputTableauxDef : 𝚺₀.Semisentence 8 := .mkSigma
  “proofCode formulaCode
      proofTokenCount proofTokenTable proofOffsetTable
      formulaTokenCount formulaTokenTable formulaOffsetTable.
    !(compactCanonicalPackedTokenStreamTableauDef)
      proofCode proofTokenCount proofTokenTable proofOffsetTable ∧
    !(compactCanonicalPackedTokenStreamTableauDef)
      formulaCode formulaTokenCount formulaTokenTable formulaOffsetTable”

@[simp] theorem compactCanonicalVerifierInputTableauxDef_spec
    (proofCode formulaCode
      proofTokenCount proofTokenTable proofOffsetTable
      formulaTokenCount formulaTokenTable formulaOffsetTable : Nat) :
    compactCanonicalVerifierInputTableauxDef.val.Evalb
        ![proofCode, formulaCode,
          proofTokenCount, proofTokenTable, proofOffsetTable,
          formulaTokenCount, formulaTokenTable, formulaOffsetTable] ↔
      CompactCanonicalVerifierInputTableaux
        proofCode formulaCode
        proofTokenCount proofTokenTable proofOffsetTable
        formulaTokenCount formulaTokenTable formulaOffsetTable := by
  simp [compactCanonicalVerifierInputTableauxDef,
    CompactCanonicalVerifierInputTableaux]

theorem compactCanonicalVerifierInputTableauxDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCanonicalVerifierInputTableauxDef.val := by
  simp [compactCanonicalVerifierInputTableauxDef]

theorem compactCanonicalVerifierInputTableaux_canonical
    (proofTokens formulaTokens : List Nat) :
    let proofWidth := (compactBinaryNatPayloadBits proofTokens).length
    let formulaWidth := (compactBinaryNatPayloadBits formulaTokens).length
    CompactCanonicalVerifierInputTableaux
      (compactAdditivePackedCode proofTokens)
      (compactAdditivePackedCode formulaTokens)
      proofTokens.length
      (FoundationCompactNumericListedDirectArithmeticPrimitives.compactFixedWidthTableCode
        proofWidth proofTokens)
      (FoundationCompactNumericListedDirectArithmeticPrimitives.compactFixedWidthTableCode
        proofWidth (compactBinaryNatTokenOffsets proofTokens))
      formulaTokens.length
      (FoundationCompactNumericListedDirectArithmeticPrimitives.compactFixedWidthTableCode
        formulaWidth formulaTokens)
      (FoundationCompactNumericListedDirectArithmeticPrimitives.compactFixedWidthTableCode
        formulaWidth (compactBinaryNatTokenOffsets formulaTokens)) := by
  simp only [CompactCanonicalVerifierInputTableaux]
  exact ⟨
    compactCanonicalPackedTokenStreamTableau_canonical proofTokens,
    compactCanonicalPackedTokenStreamTableau_canonical formulaTokens⟩

theorem CompactCanonicalVerifierInputTableaux.decode
    {proofCode formulaCode
      proofTokenCount proofTokenTable proofOffsetTable
      formulaTokenCount formulaTokenTable formulaOffsetTable : Nat}
    (hvalid : CompactCanonicalVerifierInputTableaux
      proofCode formulaCode
      proofTokenCount proofTokenTable proofOffsetTable
      formulaTokenCount formulaTokenTable formulaOffsetTable) :
    ∃ proofTokens formulaTokens : List Nat,
      proofTokens.length = proofTokenCount ∧
      formulaTokens.length = formulaTokenCount ∧
      compactPackedTokenStream proofCode = some proofTokens ∧
      compactPackedTokenStream formulaCode = some formulaTokens := by
  rcases hvalid with ⟨hproof, hformula⟩
  rcases hproof.decode with ⟨proofTokens, hproofLength, hproofDecode⟩
  rcases hformula.decode with
    ⟨formulaTokens, hformulaLength, hformulaDecode⟩
  exact ⟨proofTokens, formulaTokens, hproofLength, hformulaLength,
    hproofDecode, hformulaDecode⟩

/-- Replacing one decoded proof stream by its canonical packing leaves the
numeric public verifier pointwise unchanged. -/
theorem compactNumericListedPublicVerifier_normalize_proofCode
    {proofCode formulaCode : Nat} {proofTokens : List Nat}
    (hdecode : compactPackedTokenStream proofCode = some proofTokens) :
    compactNumericListedPublicVerifier
        (compactAdditivePackedCode proofTokens) formulaCode =
      compactNumericListedPublicVerifier proofCode formulaCode := by
  simp [compactNumericListedPublicVerifier,
    compactPackedTokenStream_additivePackedCode, hdecode]

theorem compactFormulaCode_eq_additivePackedCode
    (formula : LO.FirstOrder.ArithmeticProposition) :
    compactFormulaCode formula =
      compactAdditivePackedCode
        (FoundationCompactSyntaxTokenMachine.compactArithmeticFormulaTokens
          formula) := by
  unfold compactFormulaCode compactAdditivePackedCode
    compactAdditivePackedBits
  rw [← FoundationCompactNumericTokenBitLength.compactArithmeticFormulaTokens_flatMap_binaryNatCode
    formula]
  rfl

/-- Every accepted input pair has a canonical two-tableau representative at
the same formula code and no larger proof-code length. -/
theorem accepted_has_canonical_input_tableaux
    {proofCode formulaCode : Nat}
    (haccept :
      compactNumericListedPublicVerifier proofCode formulaCode = true) :
    ∃ normalizedProofCode
        proofTokenCount proofTokenTable proofOffsetTable
        formulaTokenCount formulaTokenTable formulaOffsetTable,
      Nat.size normalizedProofCode ≤ Nat.size proofCode ∧
      compactNumericListedPublicVerifier
        normalizedProofCode formulaCode = true ∧
      CompactCanonicalVerifierInputTableaux
        normalizedProofCode formulaCode
        proofTokenCount proofTokenTable proofOffsetTable
        formulaTokenCount formulaTokenTable formulaOffsetTable := by
  rcases (compactNumericListedPublicVerifier_eq_true_iff
      proofCode formulaCode).mp haccept with
    ⟨tree, certificate, formula, hproofDecode,
      _hcertificate, _hconclusion, hformulaCode⟩
  let proofTokens := compactListedCertifiedTokens tree certificate
  let formulaTokens :=
    FoundationCompactSyntaxTokenMachine.compactArithmeticFormulaTokens formula
  have hproofStream :
      compactPackedTokenStream proofCode = some proofTokens := by
    exact (compactPackedTokenStream_eq_proofTokens_iff
      proofCode tree certificate).mpr hproofDecode
  rcases compactPackedTokenStream_to_canonical_tableau hproofStream with
    ⟨normalizedProofCode, proofTokenTable, proofOffsetTable,
      hnormalizedCode, hsize, hproofTableau⟩
  have hformulaCodeCanonical :
      formulaCode = compactAdditivePackedCode formulaTokens := by
    rw [← hformulaCode]
    exact compactFormulaCode_eq_additivePackedCode formula
  let formulaWidth := (compactBinaryNatPayloadBits formulaTokens).length
  let formulaTokenTable :=
    FoundationCompactNumericListedDirectArithmeticPrimitives.compactFixedWidthTableCode
      formulaWidth formulaTokens
  let formulaOffsetTable :=
    FoundationCompactNumericListedDirectArithmeticPrimitives.compactFixedWidthTableCode
      formulaWidth (compactBinaryNatTokenOffsets formulaTokens)
  have hformulaTableau :
      CompactCanonicalPackedTokenStreamTableau
        formulaCode formulaTokens.length
        formulaTokenTable formulaOffsetTable := by
    rw [hformulaCodeCanonical]
    exact compactCanonicalPackedTokenStreamTableau_canonical formulaTokens
  refine ⟨normalizedProofCode, proofTokens.length,
    proofTokenTable, proofOffsetTable, formulaTokens.length,
    formulaTokenTable, formulaOffsetTable, hsize, ?_, ?_⟩
  · rw [hnormalizedCode]
    exact (compactNumericListedPublicVerifier_normalize_proofCode
      hproofStream).trans haccept
  · exact ⟨hproofTableau, hformulaTableau⟩

theorem accepted_has_canonical_input_tableaux_payload_le
    {proofCode formulaCode : Nat}
    (haccept :
      compactNumericListedPublicVerifier proofCode formulaCode = true) :
    ∃ normalizedProofCode
        proofTokenCount proofTokenTable proofOffsetTable
        formulaTokenCount formulaTokenTable formulaOffsetTable,
      packedPayloadLength normalizedProofCode ≤
        packedPayloadLength proofCode ∧
      compactNumericListedPublicVerifier
        normalizedProofCode formulaCode = true ∧
      CompactCanonicalVerifierInputTableaux
        normalizedProofCode formulaCode
        proofTokenCount proofTokenTable proofOffsetTable
        formulaTokenCount formulaTokenTable formulaOffsetTable := by
  rcases accepted_has_canonical_input_tableaux haccept with
    ⟨normalizedProofCode, proofTokenCount, proofTokenTable, proofOffsetTable,
      formulaTokenCount, formulaTokenTable, formulaOffsetTable,
      hsize, hnormalizedAccept, htableaux⟩
  refine ⟨normalizedProofCode, proofTokenCount, proofTokenTable,
    proofOffsetTable, formulaTokenCount, formulaTokenTable,
    formulaOffsetTable, ?_, hnormalizedAccept, htableaux⟩
  unfold packedPayloadLength
  omega

/-- Exact cutoff-preserving replacement of the public bounded proof
predicate by its canonical two-input tableau form. -/
theorem exists_accepted_code_iff_exists_canonical_input_tableaux
    (bound formulaCode : Nat) :
    (∃ proofCode,
      packedPayloadLength proofCode ≤ bound ∧
      compactNumericListedPublicVerifier proofCode formulaCode = true) ↔
    ∃ proofCode
        proofTokenCount proofTokenTable proofOffsetTable
        formulaTokenCount formulaTokenTable formulaOffsetTable,
      packedPayloadLength proofCode ≤ bound ∧
      compactNumericListedPublicVerifier proofCode formulaCode = true ∧
      CompactCanonicalVerifierInputTableaux
        proofCode formulaCode
        proofTokenCount proofTokenTable proofOffsetTable
        formulaTokenCount formulaTokenTable formulaOffsetTable := by
  constructor
  · rintro ⟨proofCode, hbound, haccept⟩
    rcases accepted_has_canonical_input_tableaux_payload_le haccept with
      ⟨normalizedProofCode,
        proofTokenCount, proofTokenTable, proofOffsetTable,
        formulaTokenCount, formulaTokenTable, formulaOffsetTable,
        hnormalizedLe, hnormalizedAccept, htableaux⟩
    exact ⟨normalizedProofCode,
      proofTokenCount, proofTokenTable, proofOffsetTable,
      formulaTokenCount, formulaTokenTable, formulaOffsetTable,
      hnormalizedLe.trans hbound, hnormalizedAccept, htableaux⟩
  · rintro ⟨proofCode, _proofTokenCount, _proofTokenTable,
      _proofOffsetTable, _formulaTokenCount, _formulaTokenTable,
      _formulaOffsetTable, hbound, haccept, _htableaux⟩
    exact ⟨proofCode, hbound, haccept⟩

#print axioms compactCanonicalVerifierInputTableauxDef_spec
#print axioms compactCanonicalVerifierInputTableauxDef_sigmaZero
#print axioms compactCanonicalVerifierInputTableaux_canonical
#print axioms CompactCanonicalVerifierInputTableaux.decode
#print axioms compactNumericListedPublicVerifier_normalize_proofCode
#print axioms compactFormulaCode_eq_additivePackedCode
#print axioms accepted_has_canonical_input_tableaux
#print axioms accepted_has_canonical_input_tableaux_payload_le
#print axioms exists_accepted_code_iff_exists_canonical_input_tableaux

end FoundationCompactNumericListedDirectInputTableau
