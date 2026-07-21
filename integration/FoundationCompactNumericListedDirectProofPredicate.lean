import integration.FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrix
import integration.FoundationCompactNumericListedDirectVerifierAcceptedConclusionRow
import integration.FoundationCompactNumericListedDirectInputTableau
import integration.FoundationCompactNumericListedVerifierRunExactness

/-!
# Direct two-variable proof predicate

This file combines the canonical proof-code tableau, the complete accepted
verifier trace, the canonical formula-code tableau, and the unique checked
conclusion into one direct bounded-arithmetic matrix.  The outer formula has
only the public payload cutoff and formula code as free variables.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofPredicate

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactAdditiveTokenCodec
open FoundationCompactListedPackedBitTokenSynchronization
open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedPublicVerifier
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectInputTableau
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierCheckedStepRows
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierAcceptedTraceFormula
open FoundationCompactNumericListedDirectVerifierAcceptedTraceExactness
open FoundationCompactNumericListedDirectVerifierAcceptedTraceInputTableau
open FoundationCompactNumericListedDirectVerifierAcceptedTraceInputSplit
open FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrix
open FoundationCompactNumericListedDirectVerifierAcceptedConclusionRow

def compactNumericVerifierDirectLastRow (inputTokenCount : Nat) : Nat :=
  4 * (inputTokenCount + 1) + 7

def CompactNumericListedDirectPredicateMatrix
    (bound formulaCode proofCode
      inputTokenCount inputTable inputOffsetTable inputWidth
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split
      traceWidth traceTable traceValueBound
      formulaTokenCount formulaTable formulaOffsetTable formulaWidth : Nat) :
    Prop :=
  inputWidth <= bound /\
    CompactNumericVerifierAcceptedPayloadMatrix
      proofCode inputTokenCount inputTable inputOffsetTable inputWidth
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split
      traceWidth traceTable traceValueBound /\
    CompactCanonicalPackedTokenStreamTableauAtWidth
      formulaCode formulaTokenCount formulaTable formulaOffsetTable
      formulaWidth /\
    CompactNumericVerifierAcceptedConclusionRow
      traceWidth traceTable traceValueBound
      (compactNumericVerifierDirectLastRow inputTokenCount)
      formulaTable formulaWidth formulaTokenCount

def compactNumericListedDirectPredicateMatrixDef :
    HierarchySymbol.sigmaZero.Semisentence 22 := .mkSigma
  “bound formulaCode proofCode
      inputTokenCount inputTable inputOffsetTable inputWidth
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split
      traceWidth traceTable traceValueBound
      formulaTokenCount formulaTable formulaOffsetTable formulaWidth.
    inputWidth ≤ bound ∧
    !(compactNumericVerifierAcceptedPayloadMatrixDef)
      proofCode inputTokenCount inputTable inputOffsetTable inputWidth
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split
      traceWidth traceTable traceValueBound ∧
    !(compactCanonicalPackedTokenStreamTableauAtWidthDef)
      formulaCode formulaTokenCount formulaTable formulaOffsetTable
      formulaWidth ∧
    !(compactNumericVerifierAcceptedConclusionRowDef)
      traceWidth traceTable traceValueBound
      (4 * (inputTokenCount + 1) + 7)
      formulaTable formulaWidth formulaTokenCount”

@[simp] theorem compactNumericListedDirectPredicateMatrixDef_spec
    (bound formulaCode proofCode
      inputTokenCount inputTable inputOffsetTable inputWidth
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split
      traceWidth traceTable traceValueBound
      formulaTokenCount formulaTable formulaOffsetTable formulaWidth : Nat) :
    compactNumericListedDirectPredicateMatrixDef.val.Evalb
        ![bound, formulaCode, proofCode,
          inputTokenCount, inputTable, inputOffsetTable, inputWidth,
          sourceTable, sourceWidth, sourceTokenCount,
          proofStart, proofFinish, certificateStart, certificateFinish, split,
          traceWidth, traceTable, traceValueBound,
          formulaTokenCount, formulaTable, formulaOffsetTable, formulaWidth] ↔
      CompactNumericListedDirectPredicateMatrix
        bound formulaCode proofCode
        inputTokenCount inputTable inputOffsetTable inputWidth
        sourceTable sourceWidth sourceTokenCount
        proofStart proofFinish certificateStart certificateFinish split
        traceWidth traceTable traceValueBound
        formulaTokenCount formulaTable formulaOffsetTable formulaWidth := by
  let env : Fin 22 -> Nat :=
    ![bound, formulaCode, proofCode,
      inputTokenCount, inputTable, inputOffsetTable, inputWidth,
      sourceTable, sourceWidth, sourceTokenCount,
      proofStart, proofFinish, certificateStart, certificateFinish, split,
      traceWidth, traceTable, traceValueBound,
      formulaTokenCount, formulaTable, formulaOffsetTable, formulaWidth]
  change compactNumericListedDirectPredicateMatrixDef.val.Evalb env ↔ _
  have hpayloadEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#2 : Semiterm ℒₒᵣ Empty 22), #3, #4, #5, #6, #7, #8, #9,
          #10, #11, #12, #13, #14, #15, #16, #17]) =
        ![proofCode, inputTokenCount, inputTable, inputOffsetTable, inputWidth,
          sourceTable, sourceWidth, sourceTokenCount,
          proofStart, proofFinish, certificateStart, certificateFinish, split,
          traceWidth, traceTable, traceValueBound] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have hformulaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#1 : Semiterm ℒₒᵣ Empty 22), #18, #19, #20, #21]) =
        ![formulaCode, formulaTokenCount, formulaTable, formulaOffsetTable,
          formulaWidth] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have hconclusionEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#15 : Semiterm ℒₒᵣ Empty 22), #16, #17,
          ‘(4 * (#3 + 1) + 7)’, #19, #21, #18]) =
        ![traceWidth, traceTable, traceValueBound,
          compactNumericVerifierDirectLastRow inputTokenCount,
          formulaTable, formulaWidth, formulaTokenCount] := by
    funext coordinate
    fin_cases coordinate <;>
      simp [env, compactNumericVerifierDirectLastRow]
  simp [compactNumericListedDirectPredicateMatrixDef,
    CompactNumericListedDirectPredicateMatrix,
    Semiformula.eval_substs, hpayloadEnv, hformulaEnv, hconclusionEnv, env]

theorem compactNumericListedDirectPredicateMatrixDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericListedDirectPredicateMatrixDef.val :=
  compactNumericListedDirectPredicateMatrixDef.sigma_prop

def CompactListedPADirectProofPredicate
    (bound formulaCode : Nat) : Prop :=
  exists proofCode
      inputTokenCount inputTable inputOffsetTable inputWidth
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split
      traceWidth traceTable traceValueBound
      formulaTokenCount formulaTable formulaOffsetTable formulaWidth,
    CompactNumericListedDirectPredicateMatrix
      bound formulaCode proofCode
      inputTokenCount inputTable inputOffsetTable inputWidth
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split
      traceWidth traceTable traceValueBound
      formulaTokenCount formulaTable formulaOffsetTable formulaWidth

structure CompactListedPADirectWitness
    (bound formulaCode : Nat) where
  proofCode : Nat
  inputTokenCount : Nat
  inputTable : Nat
  inputOffsetTable : Nat
  inputWidth : Nat
  sourceTable : Nat
  sourceWidth : Nat
  sourceTokenCount : Nat
  proofStart : Nat
  proofFinish : Nat
  certificateStart : Nat
  certificateFinish : Nat
  split : Nat
  traceWidth : Nat
  traceTable : Nat
  traceValueBound : Nat
  formulaTokenCount : Nat
  formulaTable : Nat
  formulaOffsetTable : Nat
  formulaWidth : Nat
  matrix : CompactNumericListedDirectPredicateMatrix
    bound formulaCode proofCode
    inputTokenCount inputTable inputOffsetTable inputWidth
    sourceTable sourceWidth sourceTokenCount
    proofStart proofFinish certificateStart certificateFinish split
    traceWidth traceTable traceValueBound
    formulaTokenCount formulaTable formulaOffsetTable formulaWidth

/-- The exact canonical coordinates produced from one accepted public code.
This is derived output, not an additional assumption of the direct
predicate.  Retaining the equations prevents later quantitative arguments
from replacing the small canonical tables by arbitrary extensionally valid
tables with unused high bits. -/
structure CompactListedPADirectCanonicalWitness
    (bound formulaCode : Nat) where
  witness : CompactListedPADirectWitness bound formulaCode
  proofTokens : List Nat
  certificateTokens : List Nat
  formulaTokens : List Nat
  proofCode_eq : witness.proofCode =
    compactAdditivePackedCode (proofTokens ++ certificateTokens)
  formulaCode_eq : formulaCode = compactAdditivePackedCode formulaTokens
  inputTokenCount_eq : witness.inputTokenCount =
    (proofTokens ++ certificateTokens).length
  inputWidth_eq : witness.inputWidth =
    (compactBinaryNatPayloadBits
      (proofTokens ++ certificateTokens)).length
  inputTable_eq : witness.inputTable =
    compactFixedWidthTableCode witness.inputWidth
      (proofTokens ++ certificateTokens)
  inputOffsetTable_eq : witness.inputOffsetTable =
    compactFixedWidthTableCode witness.inputWidth
      (compactBinaryNatTokenOffsets (proofTokens ++ certificateTokens))
  sourceTokenCount_eq : witness.sourceTokenCount =
    (compactAdditiveEncode proofTokens ++
      compactAdditiveEncode certificateTokens).length
  sourceWidth_eq : witness.sourceWidth =
    (compactBinaryNatPayloadBits
      (compactAdditiveEncode proofTokens ++
        compactAdditiveEncode certificateTokens)).length
  sourceTable_eq : witness.sourceTable =
    compactFixedWidthTableCode witness.sourceWidth
      (compactAdditiveEncode proofTokens ++
        compactAdditiveEncode certificateTokens)
  proofStart_eq : witness.proofStart = 0
  proofFinish_eq : witness.proofFinish =
    (compactAdditiveEncode proofTokens).length
  certificateStart_eq : witness.certificateStart =
    (compactAdditiveEncode proofTokens).length
  certificateFinish_eq : witness.certificateFinish =
    (compactAdditiveEncode proofTokens ++
      compactAdditiveEncode certificateTokens).length
  split_eq : witness.split = proofTokens.length
  traceWidth_eq : witness.traceWidth =
    compactNumericVerifierStepFormulaDynamicWidth
      (compactNumericVerifierCanonicalStepFormulaRows
        (4 * ((proofTokens ++ certificateTokens).length + 1) + 8)
        (compactNumericVerifierInitialState proofTokens certificateTokens))
  traceTable_eq : witness.traceTable =
    compactNumericVerifierStepWitnessTableCode witness.traceWidth
      (compactNumericVerifierCanonicalStepFormulaRows
        (4 * ((proofTokens ++ certificateTokens).length + 1) + 8)
        (compactNumericVerifierInitialState proofTokens certificateTokens))
  traceValueBound_eq : witness.traceValueBound = 2 ^ witness.traceWidth
  formulaTokenCount_eq : witness.formulaTokenCount = formulaTokens.length
  formulaWidth_eq : witness.formulaWidth =
    (compactBinaryNatPayloadBits formulaTokens).length
  formulaTable_eq : witness.formulaTable =
    compactFixedWidthTableCode witness.formulaWidth formulaTokens
  formulaOffsetTable_eq : witness.formulaOffsetTable =
    compactFixedWidthTableCode witness.formulaWidth
      (compactBinaryNatTokenOffsets formulaTokens)

def CompactListedPADirectWitness.toPredicate
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    CompactListedPADirectProofPredicate bound formulaCode :=
  ⟨witness.proofCode,
    witness.inputTokenCount, witness.inputTable,
    witness.inputOffsetTable, witness.inputWidth,
    witness.sourceTable, witness.sourceWidth, witness.sourceTokenCount,
    witness.proofStart, witness.proofFinish,
    witness.certificateStart, witness.certificateFinish, witness.split,
    witness.traceWidth, witness.traceTable, witness.traceValueBound,
    witness.formulaTokenCount, witness.formulaTable,
    witness.formulaOffsetTable, witness.formulaWidth,
    witness.matrix⟩

def compactListedPADirectProofFormula : 𝚺₁.Semisentence 2 := .mkSigma
  “bound formulaCode.
    ∃ proofCode,
    ∃ inputTokenCount,
    ∃ inputTable,
    ∃ inputOffsetTable,
    ∃ inputWidth,
    ∃ sourceTable,
    ∃ sourceWidth,
    ∃ sourceTokenCount,
    ∃ proofStart,
    ∃ proofFinish,
    ∃ certificateStart,
    ∃ certificateFinish,
    ∃ split,
    ∃ traceWidth,
    ∃ traceTable,
    ∃ traceValueBound,
    ∃ formulaTokenCount,
    ∃ formulaTable,
    ∃ formulaOffsetTable,
    ∃ formulaWidth,
      !(compactNumericListedDirectPredicateMatrixDef)
        bound formulaCode proofCode
        inputTokenCount inputTable inputOffsetTable inputWidth
        sourceTable sourceWidth sourceTokenCount
        proofStart proofFinish certificateStart certificateFinish split
        traceWidth traceTable traceValueBound
        formulaTokenCount formulaTable formulaOffsetTable formulaWidth”

@[simp] theorem compactListedPADirectProofFormula_spec
    (bound formulaCode : Nat) :
    compactListedPADirectProofFormula.val.Evalb ![bound, formulaCode] ↔
      CompactListedPADirectProofPredicate bound formulaCode := by
  have hmatrix
      (proofCode
        inputTokenCount inputTable inputOffsetTable inputWidth
        sourceTable sourceWidth sourceTokenCount
        proofStart proofFinish certificateStart certificateFinish split
        traceWidth traceTable traceValueBound
        formulaTokenCount formulaTable formulaOffsetTable formulaWidth : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![formulaWidth, formulaOffsetTable, formulaTable,
                formulaTokenCount, traceValueBound, traceTable, traceWidth,
                split, certificateFinish, certificateStart,
                proofFinish, proofStart,
                sourceTokenCount, sourceWidth, sourceTable,
                inputWidth, inputOffsetTable, inputTable, inputTokenCount,
                proofCode, bound, formulaCode]
              Empty.elim ∘
            ![(#20 : Semiterm ℒₒᵣ Empty 22), #21, #19, #18, #17, #16,
              #15, #14, #13, #12, #11, #10, #9, #8, #7, #6, #5, #4,
              #3, #2, #1, #0])
          Empty.elim) compactNumericListedDirectPredicateMatrixDef.val ↔
        CompactNumericListedDirectPredicateMatrix
          bound formulaCode proofCode
          inputTokenCount inputTable inputOffsetTable inputWidth
          sourceTable sourceWidth sourceTokenCount
          proofStart proofFinish certificateStart certificateFinish split
          traceWidth traceTable traceValueBound
          formulaTokenCount formulaTable formulaOffsetTable formulaWidth := by
    have henv :
        (Semiterm.val
            ![formulaWidth, formulaOffsetTable, formulaTable,
              formulaTokenCount, traceValueBound, traceTable, traceWidth,
              split, certificateFinish, certificateStart,
              proofFinish, proofStart,
              sourceTokenCount, sourceWidth, sourceTable,
              inputWidth, inputOffsetTable, inputTable, inputTokenCount,
              proofCode, bound, formulaCode]
            Empty.elim ∘
          ![(#20 : Semiterm ℒₒᵣ Empty 22), #21, #19, #18, #17, #16,
            #15, #14, #13, #12, #11, #10, #9, #8, #7, #6, #5, #4,
            #3, #2, #1, #0]) =
          ![bound, formulaCode, proofCode,
            inputTokenCount, inputTable, inputOffsetTable, inputWidth,
            sourceTable, sourceWidth, sourceTokenCount,
            proofStart, proofFinish, certificateStart, certificateFinish,
            split, traceWidth, traceTable, traceValueBound,
            formulaTokenCount, formulaTable, formulaOffsetTable,
            formulaWidth] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactNumericListedDirectPredicateMatrixDef_spec
      bound formulaCode proofCode
      inputTokenCount inputTable inputOffsetTable inputWidth
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split
      traceWidth traceTable traceValueBound
      formulaTokenCount formulaTable formulaOffsetTable formulaWidth
  simp [compactListedPADirectProofFormula,
    CompactListedPADirectProofPredicate, hmatrix]

theorem compactListedPADirectProofFormula_sigmaOne :
    Hierarchy Polarity.sigma 1 compactListedPADirectProofFormula.val :=
  compactListedPADirectProofFormula.sigma_prop

/-- Public acceptance produces every witness in the direct two-variable
predicate.  In particular, the accepted final row is tied to the same formula
code; no separate conclusion or trace certificate is assumed. -/
theorem directCanonicalWitness_nonempty_of_public
    {bound proofCode formulaCode : Nat}
    (hbound : packedPayloadLength proofCode <= bound)
    (haccept :
      compactNumericListedPublicVerifier proofCode formulaCode = true) :
    Nonempty (CompactListedPADirectCanonicalWitness bound formulaCode) := by
  rcases (compactNumericListedPublicVerifier_eq_true_iff
      proofCode formulaCode).mp haccept with
    ⟨tree, certificate, formula, hproofDecode,
      hcertificate, hconclusion, hformulaCode⟩
  let proofTokens := compactListedProofTokens tree
  let certificateTokens := compactStructuralCertificateTokens certificate
  let inputTokens := proofTokens ++ certificateTokens
  let inputWidth := (compactBinaryNatPayloadBits inputTokens).length
  let inputTable := compactFixedWidthTableCode inputWidth inputTokens
  let inputOffsetTable := compactFixedWidthTableCode inputWidth
    (compactBinaryNatTokenOffsets inputTokens)
  have hproofStream :
      compactPackedTokenStream proofCode = some inputTokens := by
    have hraw := (compactPackedTokenStream_eq_proofTokens_iff
      proofCode tree certificate).mpr hproofDecode
    simpa [inputTokens, proofTokens, certificateTokens,
      compactListedCertifiedTokens] using hraw
  rcases compactPackedTokenStream_to_canonical_tableau hproofStream with
    ⟨normalizedProofCode, _normalizedTable, _normalizedOffsetTable,
      hnormalizedCode, hnormalizedSize, _hnormalizedTableau⟩
  have hnormalizedBound :
      packedPayloadLength normalizedProofCode <= bound := by
    unfold packedPayloadLength at hbound ⊢
    omega
  have hinput : CompactCanonicalPackedTokenStreamTableauAtWidth
      normalizedProofCode inputTokens.length inputTable inputOffsetTable
        inputWidth := by
    rw [hnormalizedCode]
    exact compactCanonicalPackedTokenStreamTableauAtWidth_canonical inputTokens

  let proofEncoded := compactAdditiveEncode proofTokens
  let certificateEncoded := compactAdditiveEncode certificateTokens
  let sourceTokens := proofEncoded ++ certificateEncoded
  let sourceWidth := (compactBinaryNatPayloadBits sourceTokens).length
  let sourceTable := compactFixedWidthTableCode sourceWidth sourceTokens
  have hsplit : CompactNumericVerifierAcceptedTraceInputSplit
      inputTable inputWidth inputTokens.length
      sourceTable sourceWidth sourceTokens.length
      0 proofEncoded.length proofEncoded.length sourceTokens.length
      proofTokens.length := by
    exact compactNumericVerifierAcceptedTraceInputSplit_canonical
      proofTokens certificateTokens
  have hproofLayout : CompactAdditiveNatListDirectLayout
      sourceTable sourceWidth sourceTokens.length
      0 proofEncoded.length proofTokens := by
    have hsourceTokens :
        [] ++ compactAdditiveEncode proofTokens ++ certificateEncoded =
          sourceTokens := by
      simp [sourceTokens, proofEncoded]
    have hraw := compactAdditiveNatListDirectLayout_canonical
      [] proofTokens certificateEncoded
    dsimp only at hraw
    rw [hsourceTokens] at hraw
    have hfinish : ([] : List Nat).length +
        (compactAdditiveEncode proofTokens).length = proofEncoded.length := by
      simp [proofEncoded]
    rw [hfinish] at hraw
    exact hraw
  have hcertificateLayout : CompactAdditiveNatListDirectLayout
      sourceTable sourceWidth sourceTokens.length
      proofEncoded.length sourceTokens.length certificateTokens := by
    have hsourceTokens :
        proofEncoded ++ compactAdditiveEncode certificateTokens ++ [] =
          sourceTokens := by
      simp [sourceTokens, certificateEncoded]
    have hraw := compactAdditiveNatListDirectLayout_canonical
      proofEncoded certificateTokens []
    dsimp only at hraw
    rw [hsourceTokens] at hraw
    have hfinish : proofEncoded.length +
        (compactAdditiveEncode certificateTokens).length =
          sourceTokens.length := by
      simp [sourceTokens, certificateEncoded]
    rw [hfinish] at hraw
    exact hraw

  have hvalidTrace :
      (listedCertificateValidTrace tree certificate).1 = true :=
    (listedCertificateValidTrace_result_eq_true_iff tree certificate).2
      hcertificate
  have hmachine :
      compactNumericVerifierResult proofTokens certificateTokens = true := by
    rw [show proofTokens = compactListedProofTokens tree by rfl,
      show certificateTokens =
        compactStructuralCertificateTokens certificate by rfl,
      compactNumericVerifierResult_canonical]
    exact hvalidTrace
  have hstateAccepted :
      (compactNumericVerifierStateAt
        (compactNumericVerifierInitialState proofTokens certificateTokens)
        (4 * (inputTokens.length + 1) + 8)).2 = some true := by
    have hpublic := (stateAccepted_iff_verifierResult_true
      proofTokens certificateTokens).mpr hmachine
    simpa [compactNumericVerifierFuelBound, inputTokens] using hpublic
  let traceFuel := 4 * (inputTokens.length + 1) + 8
  let traceStart := compactNumericVerifierInitialState
    proofTokens certificateTokens
  let traceRows := compactNumericVerifierCanonicalStepFormulaRows
    traceFuel traceStart
  let traceWidth := compactNumericVerifierStepFormulaDynamicWidth traceRows
  let traceTable := compactNumericVerifierStepWitnessTableCode
    traceWidth traceRows
  have htrace : CompactNumericVerifierAcceptedTraceTable
      traceWidth traceTable (2 ^ traceWidth) traceFuel
      sourceTable sourceWidth sourceTokens.length
      0 proofEncoded.length
      sourceTable sourceWidth sourceTokens.length
      proofEncoded.length sourceTokens.length := by
    simpa only [traceFuel, traceStart, traceRows, traceWidth, traceTable] using
      acceptedTraceTable_complete_canonical
        (fuel := traceFuel) (by simp [traceFuel])
        hproofLayout hcertificateLayout
        (by simpa only [traceFuel] using hstateAccepted)
  have hpayloadMatrix : CompactNumericVerifierAcceptedPayloadMatrix
      normalizedProofCode inputTokens.length inputTable inputOffsetTable
        inputWidth sourceTable sourceWidth sourceTokens.length
        0 proofEncoded.length proofEncoded.length sourceTokens.length
        proofTokens.length traceWidth traceTable (2 ^ traceWidth) := by
    refine ⟨hinput, hsplit, ?_⟩
    simpa only [traceFuel] using htrace

  let formulaTokens := compactArithmeticFormulaTokens formula
  let formulaWidth := (compactBinaryNatPayloadBits formulaTokens).length
  let formulaTable := compactFixedWidthTableCode formulaWidth formulaTokens
  let formulaOffsetTable := compactFixedWidthTableCode formulaWidth
    (compactBinaryNatTokenOffsets formulaTokens)
  have hformulaCodeCanonical :
      formulaCode = compactAdditivePackedCode formulaTokens := by
    rw [← hformulaCode]
    exact compactFormulaCode_eq_additivePackedCode formula
  have hformulaTableau : CompactCanonicalPackedTokenStreamTableauAtWidth
      formulaCode formulaTokens.length formulaTable formulaOffsetTable
        formulaWidth := by
    rw [hformulaCodeCanonical]
    exact compactCanonicalPackedTokenStreamTableauAtWidth_canonical
      formulaTokens

  rcases acceptedTraceTable_exact_finalLayout
      htrace hproofLayout hcertificateLayout with
    ⟨hstep, hstateLayout⟩
  have hlastRow :
      (4 * (inputTokens.length + 1) + 8) - 1 =
        compactNumericVerifierDirectLastRow inputTokens.length := by
    unfold compactNumericVerifierDirectLastRow
    omega
  rw [hlastRow] at hstep hstateLayout
  have hstateAt :
      compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          (4 * (inputTokens.length + 1) + 8) =
        (compactNumericTreeFinalPayload tree certificate, some true) := by
    have hrun := compactNumericVerifierRun_canonical_of_valid
      tree certificate hcertificate
    simpa [compactNumericVerifierStateAt, compactNumericVerifierRun,
      compactNumericVerifierFuelBound, inputTokens, proofTokens,
      certificateTokens] using hrun
  rw [hstateAt] at hstateLayout
  have hvaluesLength :
      ((compactNumericTreeFinalPayload tree certificate, some true) :
        CompactNumericVerifierState).1.2.2.length = 1 := by
    simp [compactNumericTreeFinalPayload]
  have hchildTrue :
      (((compactNumericTreeFinalPayload tree certificate, some true) :
        CompactNumericVerifierState).1.2.2.getI 0).2 = true := by
    simp [compactNumericTreeFinalPayload, hvalidTrace]
  have htokenSet :
      (arithmeticPropositionTokenValues tree.conclusionList).toFinset =
        (arithmeticPropositionTokenValues [formula]).toFinset :=
    (arithmeticPropositionTokenValues_toFinset_eq_iff
      tree.conclusionList [formula]).2 hconclusion
  have hformulaSet :
      (((compactNumericTreeFinalPayload tree certificate, some true) :
        CompactNumericVerifierState).1.2.2.getI 0).1.toFinset =
          {formulaTokens} := by
    simpa [compactNumericTreeFinalPayload, formulaTokens,
      arithmeticPropositionTokenValues, arithmeticPropositionTokenValue]
      using htokenSet
  have hformulaEntries : forall index, index < formulaTokens.length ->
      CompactFixedWidthEntry formulaTable formulaWidth
        index (formulaTokens.getI index) := by
    intro index hindex
    apply compactFixedWidthTableCode_entry formulaWidth formulaTokens
      index hindex
    intro value hvalue
    exact compactBinaryNatToken_size_le_payloadLength
      formulaTokens value hvalue
  have hconclusionRow : CompactNumericVerifierAcceptedConclusionRow
      traceWidth traceTable (2 ^ traceWidth)
      (compactNumericVerifierDirectLastRow inputTokens.length)
      formulaTable formulaWidth formulaTokens.length := by
    exact CompactNumericVerifierAcceptedConclusionRow.of_formulaSet
      rfl hstep hstateLayout hvaluesLength hchildTrue hformulaSet
      rfl hformulaEntries
  have hinputWidthBound : inputWidth <= bound := by
    rw [← hinput.packedPayloadLength_eq]
    exact hnormalizedBound
  let witness : CompactListedPADirectWitness bound formulaCode :=
    ⟨normalizedProofCode,
      inputTokens.length, inputTable, inputOffsetTable, inputWidth,
      sourceTable, sourceWidth, sourceTokens.length,
      0, proofEncoded.length, proofEncoded.length, sourceTokens.length,
      proofTokens.length, traceWidth, traceTable, 2 ^ traceWidth,
      formulaTokens.length, formulaTable, formulaOffsetTable, formulaWidth,
      ⟨hinputWidthBound, hpayloadMatrix, hformulaTableau,
        hconclusionRow⟩⟩
  refine ⟨
    { witness := witness
      proofTokens := proofTokens
      certificateTokens := certificateTokens
      formulaTokens := formulaTokens
      proofCode_eq := ?_
      formulaCode_eq := ?_
      inputTokenCount_eq := ?_
      inputWidth_eq := ?_
      inputTable_eq := ?_
      inputOffsetTable_eq := ?_
      sourceTokenCount_eq := ?_
      sourceWidth_eq := ?_
      sourceTable_eq := ?_
      proofStart_eq := ?_
      proofFinish_eq := ?_
      certificateStart_eq := ?_
      certificateFinish_eq := ?_
      split_eq := ?_
      traceWidth_eq := ?_
      traceTable_eq := ?_
      traceValueBound_eq := ?_
      formulaTokenCount_eq := ?_
      formulaWidth_eq := ?_
      formulaTable_eq := ?_
      formulaOffsetTable_eq := ?_ }⟩
  · simpa only [witness, inputTokens] using hnormalizedCode
  · simpa only [formulaTokens] using hformulaCodeCanonical
  all_goals rfl

theorem directWitness_nonempty_of_public
    {bound proofCode formulaCode : Nat}
    (hbound : packedPayloadLength proofCode <= bound)
    (haccept :
      compactNumericListedPublicVerifier proofCode formulaCode = true) :
    Nonempty (CompactListedPADirectWitness bound formulaCode) := by
  rcases directCanonicalWitness_nonempty_of_public hbound haccept with
    ⟨canonical⟩
  exact ⟨canonical.witness⟩

theorem directProofPredicate_of_public
    {bound proofCode formulaCode : Nat}
    (hbound : packedPayloadLength proofCode <= bound)
    (haccept :
      compactNumericListedPublicVerifier proofCode formulaCode = true) :
    CompactListedPADirectProofPredicate bound formulaCode := by
  rcases directWitness_nonempty_of_public hbound haccept with ⟨witness⟩
  exact witness.toPredicate

#print axioms compactNumericListedDirectPredicateMatrixDef_spec
#print axioms compactNumericListedDirectPredicateMatrixDef_sigmaZero
#print axioms compactListedPADirectProofFormula_spec
#print axioms compactListedPADirectProofFormula_sigmaOne
#print axioms directCanonicalWitness_nonempty_of_public
#print axioms directWitness_nonempty_of_public
#print axioms directProofPredicate_of_public

end FoundationCompactNumericListedDirectProofPredicate
