import integration.FoundationCompactNumericListedTaskMachine
import integration.FoundationCompactProofTokenMachineInversion
import integration.FoundationCompactCertificateTokenMachineInversion
import integration.FoundationCompactListedPackedBitTokenSynchronization
import integration.FoundationCompactNumericTokenBitLength

/-!
# Pure numeric public verifier for compact listed PA proofs

This module connects the synchronized local-check task machine to the two
sentinel-packed natural inputs of the public verifier. Runtime values contain
only naturals, Boolean values, and finite lists.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedPublicVerifier

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedProofDecoder
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationCompactListedCertificateVerifier
open FoundationCompactVerifierFormulaListChecks
open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactProofTokenMachineInversion
open FoundationCompactCertificateTokenMachineInversion
open FoundationCompactListedPackedBitTokenSynchronization
open FoundationCompactListedCertifiedVerifier
open FoundationCompactListedVerifierArithmeticInput
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericTokenBitLength

abbrev CompactNumericCertifiedParts :=
  List Nat × (List Nat × CompactNumericSequentValue)

def compactNumericCertifiedPartsAfter
    (tokens certificateTokens : List Nat) :
    Option CompactNumericCertifiedParts :=
  if compactStructuralCertificateTokenParser certificateTokens = some [] then
    let proofTokens := consumedTokenPrefix tokens certificateTokens
    (compactListedProofNodeFieldsParser proofTokens).map fun node =>
      (proofTokens, (certificateTokens, node.2.1))
  else
    none

def compactNumericCertifiedPartsParser
    (tokens : List Nat) : Option CompactNumericCertifiedParts := do
  let certificateTokens <- compactProofTokenParser tokens
  compactNumericCertifiedPartsAfter tokens certificateTokens

def compactNumericWholeFormulaValue
    (tokens : List Nat) : Option (List Nat) :=
  match compactFormulaTokenValueParser 0 tokens with
  | some (value, []) => some value
  | _ => none

def compactCanonicalTokenBits (tokens : List Nat) : List Bool :=
  tokens.flatMap compactBinaryNatCode

def compactNumericFormulaPayloadMatches
    (formulaCode : Nat) (formulaTokens : List Nat) : Bool :=
  match packedPayloadBits formulaCode with
  | some payload =>
      decide (payload = compactCanonicalTokenBits formulaTokens)
  | none => false

def compactNumericCertifiedPartsLocalCheck
    (parts : CompactNumericCertifiedParts)
    (formulaTokens : List Nat) (formulaCode : Nat) : Bool :=
  compactNumericVerifierResult parts.1 parts.2.1 &&
    (tokenFormulaSetEq parts.2.2 [formulaTokens] &&
      compactNumericFormulaPayloadMatches formulaCode formulaTokens)

def compactNumericParsedStreamsCheck
    (input : List Nat × (List Nat × Nat)) : Bool :=
  match compactNumericCertifiedPartsParser input.1,
      compactNumericWholeFormulaValue input.2.1 with
  | some parts, some formulaValue =>
      compactNumericCertifiedPartsLocalCheck
        parts formulaValue input.2.2
  | _, _ => false

def compactNumericFormulaCodeStreamCheck
    (certifiedTokens : List Nat) (formulaCode : Nat) : Bool :=
  match compactPackedTokenStream formulaCode with
  | some formulaTokens =>
      compactNumericParsedStreamsCheck
        (certifiedTokens, (formulaTokens, formulaCode))
  | none => false

def compactNumericListedPublicVerifier
    (code formulaCode : Nat) : Bool :=
  match compactPackedTokenStream code with
  | some certifiedTokens =>
      compactNumericFormulaCodeStreamCheck certifiedTokens formulaCode
  | none => false

theorem compactNumericCertifiedPartsAfter_primrec :
    Primrec₂ compactNumericCertifiedPartsAfter := by
  apply Primrec₂.mk
  let Input := List Nat × List Nat
  have hcertificateParser : Primrec (fun input : Input =>
      compactStructuralCertificateTokenParser input.2) :=
    compactStructuralCertificateTokenParser_primrec.comp Primrec.snd
  have hcertificateComplete : PrimrecPred (fun input : Input =>
      compactStructuralCertificateTokenParser input.2 = some []) :=
    Primrec.eq.comp hcertificateParser (Primrec.const (some []))
  have hproofTokens : Primrec (fun input : Input =>
      consumedTokenPrefix input.1 input.2) :=
    consumedTokenPrefix_primrec.comp Primrec.fst Primrec.snd
  have hnodeParser : Primrec (fun input : Input =>
      compactListedProofNodeFieldsParser
        (consumedTokenPrefix input.1 input.2)) :=
    compactListedProofNodeFieldsParser_primrec.comp hproofTokens
  have hsuccess : Primrec₂
      (fun (input : Input) (node : Nat × CompactNumericNodeFields) =>
        (consumedTokenPrefix input.1 input.2,
          (input.2, node.2.1))) := by
    apply Primrec₂.mk
    let PairInput := Input × (Nat × CompactNumericNodeFields)
    have hproof : Primrec (fun pair : PairInput =>
        consumedTokenPrefix pair.1.1 pair.1.2) :=
      hproofTokens.comp Primrec.fst
    have hcertificate : Primrec (fun pair : PairInput => pair.1.2) :=
      Primrec.snd.comp Primrec.fst
    have hGamma : Primrec (fun pair : PairInput => pair.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    exact Primrec.pair hproof (Primrec.pair hcertificate hGamma)
  have hparsed : Primrec (fun input : Input =>
      (compactListedProofNodeFieldsParser
          (consumedTokenPrefix input.1 input.2)).map fun node =>
        (consumedTokenPrefix input.1 input.2,
          (input.2, node.2.1))) :=
    Primrec.option_map hnodeParser hsuccess
  exact
    (Primrec.ite hcertificateComplete hparsed (Primrec.const none)).of_eq
      fun input => by simp [compactNumericCertifiedPartsAfter]

theorem compactNumericCertifiedPartsParser_primrec :
    Primrec compactNumericCertifiedPartsParser := by
  exact
    (Primrec.option_bind compactProofTokenParser_primrec
      compactNumericCertifiedPartsAfter_primrec).of_eq fun _tokens => by
        rfl

theorem compactNumericWholeFormulaValue_primrec :
    Primrec compactNumericWholeFormulaValue := by
  have hparser : Primrec (fun tokens : List Nat =>
      compactFormulaTokenValueParser 0 tokens) :=
    compactFormulaTokenValueParser_primrec.comp
      (Primrec.const 0) Primrec.id
  have hsuccess : Primrec₂
      (fun (_tokens : List Nat) (result : List Nat × List Nat) =>
        if result.2 = [] then some result.1 else none) := by
    apply Primrec₂.mk
    let Input := List Nat × (List Nat × List Nat)
    have hempty : PrimrecPred (fun input : Input => input.2.2 = []) :=
      Primrec.eq.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.const [])
    have hsome : Primrec (fun input : Input => some input.2.1) :=
      Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)
    exact Primrec.ite hempty hsome (Primrec.const none)
  exact
    (Primrec.option_bind hparser hsuccess).of_eq fun tokens => by
      cases hresult : compactFormulaTokenValueParser 0 tokens with
      | none => simp [compactNumericWholeFormulaValue, hresult]
      | some result =>
          rcases result with ⟨value, suffix⟩
          cases suffix <;>
            simp [compactNumericWholeFormulaValue, hresult]

theorem compactCanonicalTokenBits_primrec :
    Primrec compactCanonicalTokenBits := by
  exact
    (Primrec.list_flatMap Primrec.id
      (compactBinaryNatCode_primrec.comp₂ Primrec₂.right)).of_eq
      fun tokens => by rfl

theorem compactNumericFormulaPayloadMatches_primrec :
    Primrec₂ compactNumericFormulaPayloadMatches := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  have hpayload : Primrec (fun input : Input =>
      packedPayloadBits input.1) :=
    packedPayloadBits_primrec.comp Primrec.fst
  have hcanonical : Primrec (fun input : Input =>
      compactCanonicalTokenBits input.2) :=
    compactCanonicalTokenBits_primrec.comp Primrec.snd
  have hsuccess : Primrec₂
      (fun (input : Input) (payload : List Bool) =>
        decide (payload = compactCanonicalTokenBits input.2)) :=
    by
      apply Primrec₂.mk
      let PairInput := Input × List Bool
      have hpayloadValue : Primrec (fun pair : PairInput => pair.2) :=
        Primrec.snd
      have hcanonicalValue : Primrec (fun pair : PairInput =>
          compactCanonicalTokenBits pair.1.2) :=
        hcanonical.comp Primrec.fst
      exact Primrec.eq.decide.comp hpayloadValue hcanonicalValue
  exact
    (Primrec.option_casesOn hpayload (Primrec.const false) hsuccess).of_eq
      fun input => by
        cases hresult : packedPayloadBits input.1 <;>
          simp [compactNumericFormulaPayloadMatches, hresult]

theorem compactNumericCertifiedPartsLocalCheck_primrec :
    Primrec₂ (fun (parts : CompactNumericCertifiedParts)
        (input : List Nat × Nat) =>
      compactNumericCertifiedPartsLocalCheck parts input.1 input.2) := by
  apply Primrec₂.mk
  let Input := CompactNumericCertifiedParts × (List Nat × Nat)
  have hvalid : Primrec (fun input : Input =>
      compactNumericVerifierResult input.1.1 input.1.2.1) :=
    compactNumericVerifierResult_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hsingleton : Primrec (fun input : Input => [input.2.1]) :=
    Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.const [])
  have hconclusion : Primrec (fun input : Input =>
      tokenFormulaSetEq input.1.2.2 [input.2.1]) :=
    tokenFormulaSetEq_primrec.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) hsingleton
  have hpayload : Primrec (fun input : Input =>
      compactNumericFormulaPayloadMatches input.2.2 input.2.1) :=
    compactNumericFormulaPayloadMatches_primrec.comp
      (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd)
  exact
    (Primrec.and.comp hvalid (Primrec.and.comp hconclusion hpayload)).of_eq
      fun input => by rfl

theorem compactNumericParsedStreamsCheck_primrec :
    Primrec compactNumericParsedStreamsCheck := by
  let Input := List Nat × (List Nat × Nat)
  have hparts : Primrec (fun input : Input =>
      compactNumericCertifiedPartsParser input.1) :=
    compactNumericCertifiedPartsParser_primrec.comp Primrec.fst
  have hpartsSuccess : Primrec₂
      (fun (input : Input) (parts : CompactNumericCertifiedParts) =>
        match compactNumericWholeFormulaValue input.2.1 with
        | none => false
        | some formulaValue =>
            compactNumericCertifiedPartsLocalCheck
              parts formulaValue input.2.2) := by
    apply Primrec₂.mk
    let State := Input × CompactNumericCertifiedParts
    have hformula : Primrec (fun state : State =>
        compactNumericWholeFormulaValue state.1.2.1) :=
      compactNumericWholeFormulaValue_primrec.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    have hcheck : Primrec₂
        (fun (state : State) (formulaValue : List Nat) =>
          compactNumericCertifiedPartsLocalCheck
            state.2 formulaValue state.1.2.2) := by
      apply Primrec₂.mk
      let PairState := State × List Nat
      have hpartsValue : Primrec (fun state : PairState => state.1.2) :=
        Primrec.snd.comp Primrec.fst
      have hformulaAndCode : Primrec (fun state : PairState =>
          (state.2, state.1.1.2.2)) :=
        Primrec.pair Primrec.snd
          (Primrec.snd.comp
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      exact compactNumericCertifiedPartsLocalCheck_primrec.comp
        hpartsValue hformulaAndCode
    exact
      (Primrec.option_casesOn hformula (Primrec.const false) hcheck).of_eq
        fun state => by
          cases hresult : compactNumericWholeFormulaValue state.1.2.1 <;>
            simp
  exact
    (Primrec.option_casesOn hparts (Primrec.const false)
      hpartsSuccess).of_eq fun input => by
        cases hpartsResult : compactNumericCertifiedPartsParser input.1 <;>
          cases hformulaResult :
            compactNumericWholeFormulaValue input.2.1 <;>
          simp [compactNumericParsedStreamsCheck,
            hpartsResult, hformulaResult]

theorem compactNumericFormulaCodeStreamCheck_primrec :
    Primrec₂ compactNumericFormulaCodeStreamCheck := by
  apply Primrec₂.mk
  let Input := List Nat × Nat
  have hformulaStream : Primrec (fun input : Input =>
      compactPackedTokenStream input.2) :=
    compactPackedTokenStream_primrec.comp Primrec.snd
  have hsuccess : Primrec₂
      (fun (input : Input) (formulaTokens : List Nat) =>
        compactNumericParsedStreamsCheck
          (input.1, (formulaTokens, input.2))) := by
    apply Primrec₂.mk
    let State := Input × List Nat
    have hinput : Primrec (fun state : State =>
        (state.1.1, (state.2, state.1.2))) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))
    exact compactNumericParsedStreamsCheck_primrec.comp hinput
  exact
    (Primrec.option_casesOn hformulaStream (Primrec.const false)
      hsuccess).of_eq fun input => by
        cases hresult : compactPackedTokenStream input.2 <;>
          simp [compactNumericFormulaCodeStreamCheck, hresult]

theorem compactNumericListedPublicVerifier_primrec :
    Primrec₂ compactNumericListedPublicVerifier := by
  apply Primrec₂.mk
  let Input := Nat × Nat
  have hproofStream : Primrec (fun input : Input =>
      compactPackedTokenStream input.1) :=
    compactPackedTokenStream_primrec.comp Primrec.fst
  have hsuccess : Primrec₂
      (fun (input : Input) (certifiedTokens : List Nat) =>
        compactNumericFormulaCodeStreamCheck certifiedTokens input.2) := by
    apply Primrec₂.mk
    let State := Input × List Nat
    exact compactNumericFormulaCodeStreamCheck_primrec.comp
      Primrec.snd (Primrec.snd.comp Primrec.fst)
  exact
    (Primrec.option_casesOn hproofStream (Primrec.const false)
      hsuccess).of_eq fun input => by
        cases hresult : compactPackedTokenStream input.1 <;>
          simp [compactNumericListedPublicVerifier, hresult]

/-! ## Exact arbitrary-input semantics -/

@[simp] theorem compactNumericCertifiedPartsParser_canonical
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    compactNumericCertifiedPartsParser
        (compactListedCertifiedTokens tree certificate) =
      some (compactListedProofTokens tree,
        (compactStructuralCertificateTokens certificate,
          arithmeticPropositionTokenValues tree.conclusionList)) := by
  rw [compactListedCertifiedTokens]
  unfold compactNumericCertifiedPartsParser
  rw [compactProofTokenParser_canonical_append]
  change compactNumericCertifiedPartsAfter
      (compactListedProofTokens tree ++
        compactStructuralCertificateTokens certificate)
      (compactStructuralCertificateTokens certificate) = _
  unfold compactNumericCertifiedPartsAfter
  have hcertificate :
      compactStructuralCertificateTokenParser
          (compactStructuralCertificateTokens certificate) = some [] := by
    simpa using
      compactStructuralCertificateTokenParser_canonical_append certificate []
  rw [hcertificate]
  simp only [if_pos, consumedTokenPrefix_append]
  have hnode :
      compactListedProofNodeFieldsParser
          (compactListedProofTokens tree) =
        some (compactListedProofNodeExpectedFields tree []) := by
    simpa using compactListedProofNodeFieldsParser_canonical_append tree []
  rw [hnode]
  cases tree <;> rfl

theorem compactNumericCertifiedPartsParser_success_iff
    (tokens : List Nat) (parts : CompactNumericCertifiedParts) :
    compactNumericCertifiedPartsParser tokens = some parts ↔
      ∃ (tree : ListedCheckedPAProofTree)
          (certificate : StructuralValidityCertificate),
        tokens = compactListedCertifiedTokens tree certificate ∧
          parts = (compactListedProofTokens tree,
            (compactStructuralCertificateTokens certificate,
              arithmeticPropositionTokenValues tree.conclusionList)) := by
  constructor
  · intro hparser
    cases hproof : compactProofTokenParser tokens with
    | none =>
        simp [compactNumericCertifiedPartsParser, hproof] at hparser
    | some certificateTokens =>
        obtain ⟨tree, htokens⟩ :=
          (compactProofTokenParser_success_iff
            tokens certificateTokens).mp hproof
        by_cases hcertificate :
            compactStructuralCertificateTokenParser certificateTokens =
              some []
        · obtain ⟨certificate, hcertificateTokens⟩ :=
            (compactStructuralCertificateTokenParser_success_iff
              certificateTokens []).mp hcertificate
          have hcertificateTokens' :
              certificateTokens =
                compactStructuralCertificateTokens certificate := by
            simpa using hcertificateTokens
          have htogether :
              tokens = compactListedCertifiedTokens tree certificate := by
            rw [compactListedCertifiedTokens, htokens,
              hcertificateTokens']
          rw [htogether] at hparser
          have hcanonical :=
            compactNumericCertifiedPartsParser_canonical tree certificate
          have hparts :
              parts = (compactListedProofTokens tree,
                (compactStructuralCertificateTokens certificate,
                  arithmeticPropositionTokenValues
                    tree.conclusionList)) :=
            Option.some.inj (hparser.symm.trans hcanonical)
          exact ⟨tree, certificate, htogether, hparts⟩
        · simp [compactNumericCertifiedPartsParser,
            compactNumericCertifiedPartsAfter, hproof, hcertificate]
            at hparser
  · rintro ⟨tree, certificate, rfl, rfl⟩
    exact compactNumericCertifiedPartsParser_canonical tree certificate

@[simp] theorem compactNumericWholeFormulaValue_canonical
    (formula : LO.FirstOrder.ArithmeticProposition) :
    compactNumericWholeFormulaValue
        (compactArithmeticFormulaTokens formula) =
      some (compactArithmeticFormulaTokens formula) := by
  unfold compactNumericWholeFormulaValue
  rw [← List.append_nil (compactArithmeticFormulaTokens formula),
    compactFormulaTokenValueParser_canonical_append]
  simp

theorem compactNumericWholeFormulaValue_success_iff
    (tokens value : List Nat) :
    compactNumericWholeFormulaValue tokens = some value ↔
      ∃ formula : LO.FirstOrder.ArithmeticProposition,
        tokens = compactArithmeticFormulaTokens formula ∧
          value = compactArithmeticFormulaTokens formula := by
  constructor
  · intro hparser
    cases hraw : compactFormulaTokenValueParser 0 tokens with
    | none =>
        simp [compactNumericWholeFormulaValue, hraw] at hparser
    | some result =>
        rcases result with ⟨parsedValue, suffix⟩
        cases suffix with
        | cons head tail =>
            simp [compactNumericWholeFormulaValue, hraw] at hparser
        | nil =>
            have hvalue : value = parsedValue := by
              simpa [compactNumericWholeFormulaValue, hraw] using hparser.symm
            obtain ⟨formula, htokens, hparsedValue⟩ :=
              compactFormulaTokenValueParser_sound hraw
            exact ⟨formula, by simpa using htokens,
              hvalue.trans hparsedValue⟩
  · rintro ⟨formula, rfl, rfl⟩
    exact compactNumericWholeFormulaValue_canonical formula

theorem compactNumericFormulaPayloadMatches_canonical_eq_true_iff
    (formula : LO.FirstOrder.ArithmeticProposition) (formulaCode : Nat) :
    compactNumericFormulaPayloadMatches formulaCode
        (compactArithmeticFormulaTokens formula) = true ↔
      compactFormulaCode formula = formulaCode := by
  constructor
  · intro hmatch
    cases hpayload : packedPayloadBits formulaCode with
    | none =>
        simp [compactNumericFormulaPayloadMatches, hpayload] at hmatch
    | some payload =>
        have hpayloadCanonical :
            payload = binaryFormulaCode formula := by
          simpa [compactNumericFormulaPayloadMatches, hpayload,
            compactCanonicalTokenBits,
            compactArithmeticFormulaTokens_flatMap_binaryNatCode]
            using hmatch
        have hpack :=
          (packedPayloadBits_eq_some_iff formulaCode payload).mp hpayload
        calc
          compactFormulaCode formula = packBinaryString payload := by
            simp [compactFormulaCode, hpayloadCanonical]
          _ = formulaCode := hpack
  · intro hcode
    rw [← hcode]
    simp [compactNumericFormulaPayloadMatches, compactFormulaCode,
      packedPayloadBits_packBinaryString, compactCanonicalTokenBits,
      compactArithmeticFormulaTokens_flatMap_binaryNatCode]

theorem compactNumericCertifiedPartsLocalCheck_canonical_eq_true_iff
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (formulaCode : Nat) :
    compactNumericCertifiedPartsLocalCheck
        (compactListedProofTokens tree,
          (compactStructuralCertificateTokens certificate,
            arithmeticPropositionTokenValues tree.conclusionList))
        (compactArithmeticFormulaTokens formula) formulaCode = true ↔
      listedCertificateValid tree certificate ∧
        tree.conclusionList.toFinset = {formula} ∧
          compactFormulaCode formula = formulaCode := by
  rw [compactNumericCertifiedPartsLocalCheck,
    compactNumericVerifierResult_canonical,
    show [compactArithmeticFormulaTokens formula] =
        arithmeticPropositionTokenValues [formula] by
      rfl,
    tokenFormulaSetEq_canonical_eq_formulaSetEqTrace_result,
    Bool.and_eq_true, Bool.and_eq_true,
    listedCertificateValidTrace_result_eq_true_iff,
    formulaSetEqTrace_result_eq_true_iff,
    compactNumericFormulaPayloadMatches_canonical_eq_true_iff]
  simp

theorem compactNumericParsedStreamsCheck_eq_true_iff
    (certifiedTokens formulaTokens : List Nat) (formulaCode : Nat) :
    compactNumericParsedStreamsCheck
        (certifiedTokens, (formulaTokens, formulaCode)) = true ↔
      ∃ (tree : ListedCheckedPAProofTree)
          (certificate : StructuralValidityCertificate)
          (formula : LO.FirstOrder.ArithmeticProposition),
        certifiedTokens = compactListedCertifiedTokens tree certificate ∧
          formulaTokens = compactArithmeticFormulaTokens formula ∧
          listedCertificateValid tree certificate ∧
          tree.conclusionList.toFinset = {formula} ∧
          compactFormulaCode formula = formulaCode := by
  constructor
  · intro haccept
    cases hparts :
        compactNumericCertifiedPartsParser certifiedTokens with
    | none =>
        simp [compactNumericParsedStreamsCheck, hparts] at haccept
    | some parts =>
        cases hformula :
            compactNumericWholeFormulaValue formulaTokens with
        | none =>
            simp [compactNumericParsedStreamsCheck, hparts, hformula]
              at haccept
        | some formulaValue =>
            obtain ⟨tree, certificate, hcertifiedTokens, hpartsValue⟩ :=
              (compactNumericCertifiedPartsParser_success_iff
                certifiedTokens parts).mp hparts
            obtain ⟨formula, hformulaTokens, hformulaValue⟩ :=
              (compactNumericWholeFormulaValue_success_iff
                formulaTokens formulaValue).mp hformula
            subst parts
            subst formulaValue
            have hlocal :=
              (compactNumericCertifiedPartsLocalCheck_canonical_eq_true_iff
                tree certificate formula formulaCode).mp <| by
                  simpa [compactNumericParsedStreamsCheck,
                    hparts, hformula] using haccept
            exact ⟨tree, certificate, formula, hcertifiedTokens,
              hformulaTokens, hlocal.1, hlocal.2.1, hlocal.2.2⟩
  · rintro ⟨tree, certificate, formula, rfl, rfl,
      hcertificate, hconclusion, hformulaCode⟩
    simp [compactNumericParsedStreamsCheck,
      compactNumericCertifiedPartsLocalCheck_canonical_eq_true_iff,
      hcertificate, hconclusion, hformulaCode]

theorem compactNumericListedPublicVerifier_eq_true_iff
    (code formulaCode : Nat) :
    compactNumericListedPublicVerifier code formulaCode = true ↔
      ListedCompactCertifiedPAProofChecks code formulaCode := by
  constructor
  · intro haccept
    cases hproofStream : compactPackedTokenStream code with
    | none =>
        simp [compactNumericListedPublicVerifier, hproofStream] at haccept
    | some certifiedTokens =>
        cases hformulaStream : compactPackedTokenStream formulaCode with
        | none =>
            simp [compactNumericListedPublicVerifier,
              compactNumericFormulaCodeStreamCheck,
              hproofStream, hformulaStream] at haccept
        | some formulaTokens =>
            have hparsed :
                compactNumericParsedStreamsCheck
                    (certifiedTokens, (formulaTokens, formulaCode)) = true := by
              simpa [compactNumericListedPublicVerifier,
                compactNumericFormulaCodeStreamCheck,
                hproofStream, hformulaStream] using haccept
            obtain ⟨tree, certificate, formula, hcertifiedTokens,
                hformulaTokens, hcertificate, hconclusion, hformulaCode⟩ :=
              (compactNumericParsedStreamsCheck_eq_true_iff
                certifiedTokens formulaTokens formulaCode).mp hparsed
            have hproofStream' :
                compactPackedTokenStream code =
                  some (compactListedCertifiedTokens tree certificate) := by
              simpa [hcertifiedTokens] using hproofStream
            have hformulaStream' :
                compactPackedTokenStream formulaCode =
                  some (compactArithmeticFormulaTokens formula) := by
              simpa [hformulaTokens] using hformulaStream
            exact ⟨tree, certificate, formula,
              (compactPackedTokenStream_eq_proofTokens_iff
                code tree certificate).mp hproofStream',
              hcertificate, hconclusion, hformulaCode⟩
  · rintro ⟨tree, certificate, formula, hdecode,
      hcertificate, hconclusion, hformulaCode⟩
    have hproofStream :
        compactPackedTokenStream code =
          some (compactListedCertifiedTokens tree certificate) :=
      (compactPackedTokenStream_eq_proofTokens_iff
        code tree certificate).mpr hdecode
    have hformulaDecode :
        decodeCompactPackedFormula formulaCode = some formula := by
      rw [← hformulaCode]
      exact decodeCompactPackedFormula_compactFormulaCode formula
    have hformulaStream :
        compactPackedTokenStream formulaCode =
          some (compactArithmeticFormulaTokens formula) :=
      (compactPackedTokenStream_eq_formulaTokens_iff
        formulaCode formula).mpr hformulaDecode
    have hparsed :
        compactNumericParsedStreamsCheck
            (compactListedCertifiedTokens tree certificate,
              (compactArithmeticFormulaTokens formula, formulaCode)) = true :=
      (compactNumericParsedStreamsCheck_eq_true_iff
        (compactListedCertifiedTokens tree certificate)
        (compactArithmeticFormulaTokens formula) formulaCode).mpr
          ⟨tree, certificate, formula, rfl, rfl,
            hcertificate, hconclusion, hformulaCode⟩
    simp [compactNumericListedPublicVerifier,
      compactNumericFormulaCodeStreamCheck,
      hproofStream, hformulaStream, hparsed]

theorem compactNumericListedPublicVerifier_pointwise
    (code formulaCode : Nat) :
    compactNumericListedPublicVerifier code formulaCode =
      listedCompactCertifiedPAProofVerifier code formulaCode := by
  apply Bool.eq_iff_iff.mpr
  rw [compactNumericListedPublicVerifier_eq_true_iff,
    listedCompactCertifiedPAProofVerifier_eq_true_iff]

#print axioms compactNumericCertifiedPartsParser_primrec
#print axioms compactNumericWholeFormulaValue_primrec
#print axioms compactNumericFormulaPayloadMatches_primrec
#print axioms compactNumericParsedStreamsCheck_primrec
#print axioms compactNumericFormulaCodeStreamCheck_primrec
#print axioms compactNumericListedPublicVerifier_primrec
#print axioms compactNumericCertifiedPartsParser_success_iff
#print axioms compactNumericWholeFormulaValue_success_iff
#print axioms compactNumericParsedStreamsCheck_eq_true_iff
#print axioms compactNumericListedPublicVerifier_eq_true_iff
#print axioms compactNumericListedPublicVerifier_pointwise

end FoundationCompactNumericListedPublicVerifier
