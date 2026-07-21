import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceInputSplit
import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceExactness

/-!
# Direct bounded matrix for one accepted canonical proof payload

This matrix joins the canonical public proof-code tableau, the exact split into
proof and certificate list bodies, and the complete accepted verifier trace.
The public fuel is fixed by the decoded input-token count; it is not a witness
or an externally supplied bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrix

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierInitialEnvironmentFormula
open FoundationCompactNumericListedDirectVerifierAcceptedTraceFormula
open FoundationCompactNumericListedDirectVerifierAcceptedTraceExactness
open FoundationCompactNumericListedDirectVerifierAcceptedTraceInputTableau
open FoundationCompactNumericListedDirectVerifierAcceptedTraceInputSplit

def CompactNumericVerifierAcceptedPayloadMatrix
    (code inputTokenCount inputTable inputOffsetTable inputWidth
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split
      traceWidth traceTable traceValueBound : Nat) : Prop :=
  CompactCanonicalPackedTokenStreamTableauAtWidth
      code inputTokenCount inputTable inputOffsetTable inputWidth /\
    CompactNumericVerifierAcceptedTraceInputSplit
      inputTable inputWidth inputTokenCount
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split /\
    CompactNumericVerifierAcceptedTraceTable
      traceWidth traceTable traceValueBound
      (4 * (inputTokenCount + 1) + 8)
      sourceTable sourceWidth sourceTokenCount proofStart proofFinish
      sourceTable sourceWidth sourceTokenCount
        certificateStart certificateFinish

def compactNumericVerifierAcceptedPayloadMatrixDef :
    HierarchySymbol.sigmaZero.Semisentence 16 := .mkSigma
  “code inputTokenCount inputTable inputOffsetTable inputWidth
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split
      traceWidth traceTable traceValueBound.
    !(compactCanonicalPackedTokenStreamTableauAtWidthDef)
      code inputTokenCount inputTable inputOffsetTable inputWidth ∧
    !(compactNumericVerifierAcceptedTraceInputSplitDef)
      inputTable inputWidth inputTokenCount
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split ∧
    !(compactNumericVerifierAcceptedTraceTableDef)
      traceWidth traceTable traceValueBound
      (4 * (inputTokenCount + 1) + 8)
      sourceTable sourceWidth sourceTokenCount proofStart proofFinish
      sourceTable sourceWidth sourceTokenCount
        certificateStart certificateFinish”

@[simp] theorem compactNumericVerifierAcceptedPayloadMatrixDef_spec
    (code inputTokenCount inputTable inputOffsetTable inputWidth
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split
      traceWidth traceTable traceValueBound : Nat) :
    compactNumericVerifierAcceptedPayloadMatrixDef.val.Evalb
        ![code, inputTokenCount, inputTable, inputOffsetTable, inputWidth,
          sourceTable, sourceWidth, sourceTokenCount,
          proofStart, proofFinish, certificateStart, certificateFinish, split,
          traceWidth, traceTable, traceValueBound] ↔
      CompactNumericVerifierAcceptedPayloadMatrix
        code inputTokenCount inputTable inputOffsetTable inputWidth
        sourceTable sourceWidth sourceTokenCount
        proofStart proofFinish certificateStart certificateFinish split
        traceWidth traceTable traceValueBound := by
  let env : Fin 16 -> Nat :=
    ![code, inputTokenCount, inputTable, inputOffsetTable, inputWidth,
      sourceTable, sourceWidth, sourceTokenCount,
      proofStart, proofFinish, certificateStart, certificateFinish, split,
      traceWidth, traceTable, traceValueBound]
  change compactNumericVerifierAcceptedPayloadMatrixDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 16), #1, #2, #3, #4]) =
        ![code, inputTokenCount, inputTable, inputOffsetTable, inputWidth] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have hsplitEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#2 : Semiterm ℒₒᵣ Empty 16), #4, #1,
          #5, #6, #7, #8, #9, #10, #11, #12]) =
        ![inputTable, inputWidth, inputTokenCount,
          sourceTable, sourceWidth, sourceTokenCount,
          proofStart, proofFinish, certificateStart, certificateFinish,
          split] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have htraceEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#13 : Semiterm ℒₒᵣ Empty 16), #14, #15,
          ‘(4 * (#1 + 1) + 8)’, #5, #6, #7, #8, #9,
          #5, #6, #7, #10, #11]) =
        ![traceWidth, traceTable, traceValueBound,
          4 * (inputTokenCount + 1) + 8,
          sourceTable, sourceWidth, sourceTokenCount,
          proofStart, proofFinish,
          sourceTable, sourceWidth, sourceTokenCount,
          certificateStart, certificateFinish] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  simp [compactNumericVerifierAcceptedPayloadMatrixDef,
    CompactNumericVerifierAcceptedPayloadMatrix,
    Semiformula.eval_substs, hinputEnv, hsplitEnv, htraceEnv, env]

theorem compactNumericVerifierAcceptedPayloadMatrixDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierAcceptedPayloadMatrixDef.val :=
  compactNumericVerifierAcceptedPayloadMatrixDef.sigma_prop

theorem exists_acceptedPayloadMatrix_iff
    (code : Nat) :
    (exists inputTokenCount inputTable inputOffsetTable inputWidth
        sourceTable sourceWidth sourceTokenCount
        proofStart proofFinish certificateStart certificateFinish split
        traceWidth traceTable traceValueBound,
      CompactNumericVerifierAcceptedPayloadMatrix
        code inputTokenCount inputTable inputOffsetTable inputWidth
        sourceTable sourceWidth sourceTokenCount
        proofStart proofFinish certificateStart certificateFinish split
        traceWidth traceTable traceValueBound) ↔
      exists proofTokens certificateTokens : List Nat,
        code = compactAdditivePackedCode (proofTokens ++ certificateTokens) /\
          compactNumericVerifierResult proofTokens certificateTokens = true := by
  constructor
  · rintro ⟨inputTokenCount, inputTable, inputOffsetTable, inputWidth,
      sourceTable, sourceWidth, sourceTokenCount,
      proofStart, proofFinish, certificateStart, certificateFinish, split,
      traceWidth, traceTable, traceValueBound,
      hinput, hsplit, htrace⟩
    let environment :=
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        traceWidth traceTable 0
    have htraceCopy := htrace
    rcases htrace with
      ⟨_hvalueBound, _hfuel, _hbounded, _hadjacent, hinitial,
        _lastRow, _hlastRow, _hlastNext, _hfinal⟩
    have hinitialEnvironment : CompactNumericVerifierInitialEnvironment
        environment
        sourceTable sourceWidth sourceTokenCount proofStart proofFinish
        sourceTable sourceWidth sourceTokenCount
          certificateStart certificateFinish := by
      simpa only [environment] using hinitial.canonical_environment
    rcases acceptedTraceTable_sound_exists_initialLists htraceCopy with
      ⟨proofTokens, certificateTokens,
        hproofLayout, hcertificateLayout, hstateAccepted⟩
    have hdecoded := hsplit.decodedTokens_eq hinput
      hinitialEnvironment.1 hinitialEnvironment.2.1
      hproofLayout hcertificateLayout
    have hcode : code =
        compactAdditivePackedCode (proofTokens ++ certificateTokens) := by
      calc
        code = compactAdditivePackedCode
            (compactCanonicalPackedTokenStreamTableauAtWidthTokens
              inputTokenCount inputTable inputWidth) :=
          hinput.code_eq_canonical
        _ = compactAdditivePackedCode
            (proofTokens ++ certificateTokens) := by rw [hdecoded]
    have hlength : inputTokenCount =
        proofTokens.length + certificateTokens.length := by
      have hlengths := congrArg List.length hdecoded
      simpa using hlengths
    have hfuel : 4 * (inputTokenCount + 1) + 8 =
        compactNumericVerifierFuelBound proofTokens certificateTokens := by
      simp only [compactNumericVerifierFuelBound]
      omega
    rw [hfuel] at hstateAccepted
    exact ⟨proofTokens, certificateTokens, hcode,
      (stateAccepted_iff_verifierResult_true
        proofTokens certificateTokens).mp hstateAccepted⟩
  · rintro ⟨proofTokens, certificateTokens, hcode, haccepted⟩
    let inputTokens := proofTokens ++ certificateTokens
    let inputWidth := (compactBinaryNatPayloadBits inputTokens).length
    let inputTable := compactFixedWidthTableCode inputWidth inputTokens
    let inputOffsetTable := compactFixedWidthTableCode inputWidth
      (compactBinaryNatTokenOffsets inputTokens)
    let proofEncoded := compactAdditiveEncode proofTokens
    let certificateEncoded := compactAdditiveEncode certificateTokens
    let sourceTokens := proofEncoded ++ certificateEncoded
    let sourceWidth := (compactBinaryNatPayloadBits sourceTokens).length
    let sourceTable := compactFixedWidthTableCode sourceWidth sourceTokens
    have hinput : CompactCanonicalPackedTokenStreamTableauAtWidth
        code inputTokens.length inputTable inputOffsetTable inputWidth := by
      rw [hcode]
      exact compactCanonicalPackedTokenStreamTableauAtWidth_canonical
        inputTokens
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
    have hstateAccepted :
        (compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          (4 * (inputTokens.length + 1) + 8)).2 = some true := by
      have hpublic := (stateAccepted_iff_verifierResult_true
        proofTokens certificateTokens).mpr haccepted
      simpa [compactNumericVerifierFuelBound, inputTokens] using hpublic
    rcases acceptedTraceTable_complete
        (fuel := 4 * (inputTokens.length + 1) + 8)
        (by omega) hproofLayout hcertificateLayout hstateAccepted with
      ⟨traceWidth, traceTable, htrace⟩
    exact ⟨inputTokens.length, inputTable, inputOffsetTable, inputWidth,
      sourceTable, sourceWidth, sourceTokens.length,
      0, proofEncoded.length, proofEncoded.length, sourceTokens.length,
      proofTokens.length, traceWidth, traceTable, 2 ^ traceWidth,
      hinput, hsplit, htrace⟩

#print axioms compactNumericVerifierAcceptedPayloadMatrixDef_spec
#print axioms compactNumericVerifierAcceptedPayloadMatrixDef_sigmaZero
#print axioms exists_acceptedPayloadMatrix_iff

end FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrix
