import integration.FoundationCompactNumericListedDirectVerifierTypedLeafStateTableControlBounds
import integration.FoundationCompactNumericListedDirectVerifierTypedNonLeafStateTableControlBounds
import integration.FoundationCompactNumericListedDirectVerifierCombineStateTableControlBounds
import integration.FoundationCompactNumericListedDirectVerifierCombineActiveCountPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierTypedClosedGlobalBound
import integration.FoundationCompactNumericListedDirectVerifierCheckedRowExecutionSplicing

/-!
# Unified accepted-tree row bounds with numeric state-table controls

This strengthens the existing all-coordinate binary-size property by retaining
numeric bounds for the two state-table loop controls on the very same row.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTreeRowStateTableControlBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierCheckedRowExecutionSplicing
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
open FoundationCompactNumericListedDirectVerifierAcceptedTreeGlobalCoordinateBound
open FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierTypedLeafStateTableControlBounds
open FoundationCompactNumericListedDirectVerifierTypedClosedStepPublicBounds
open FoundationCompactNumericListedDirectVerifierTypedClosedGlobalBound
open FoundationCompactNumericListedDirectVerifierTypedVerumStepPublicBounds
open FoundationCompactNumericListedDirectVerifierTypedVerumGlobalBound
open FoundationCompactNumericListedDirectVerifierTypedAcceptedPAAxiomStepPublicBounds
open FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomGlobalBound
open FoundationCompactNumericListedDirectVerifierTypedNonLeafStateTableControlBounds
open FoundationCompactNumericListedDirectVerifierTypedNonLeafStepPublicBounds
open FoundationCompactNumericListedDirectVerifierTypedNonLeafGlobalBound
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectVerifierCombineStateTableControlBounds
open FoundationCompactNumericListedDirectVerifierCombineActiveCountBounds
open FoundationCompactNumericListedDirectVerifierCombineActiveCountPublicBounds
open FoundationCompactNumericListedDirectVerifierCombinePublicBounds
open FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsGlobalBound
open FoundationCompactNumericListedPAAxiomLeafOccurrence

structure CompactNumericVerifierAcceptedTreeControlledRowBound
    (rowWeight : Nat) (row : CompactNumericVerifierCheckedStepRow) : Prop where
  coordinates : forall coordinate : Fin 429,
    Nat.size (row.environment coordinate) <=
      compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound rowWeight
  stateTable :
    CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight
  parserControls : row.currentState.2 = none ->
    forall restTasks,
      row.currentState.1.2.1 = compactNumericParseTask :: restTasks ->
        CompactNumericVerifierParseSuccessParserControlBounds
          row.environment
            (compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
              rowWeight)
  combineControls : row.currentState.2 = none ->
    forall task restTasks,
      row.currentState.1.2.1 = task :: restTasks ->
      task.1 ≠ 10 ->
        CompactNumericVerifierCombineEnvironmentCountControls
          row.environment

theorem combineEnvironmentCountControls_vacuous_of_parseTask
    (row : CompactNumericVerifierCheckedStepRow)
    (restTasks : List CompactNumericVerifierTask)
    (htasks : row.currentState.1.2.1 =
      compactNumericParseTask :: restTasks) :
    row.currentState.2 = none ->
      forall task taskRest,
        row.currentState.1.2.1 = task :: taskRest ->
        task.1 ≠ 10 ->
          CompactNumericVerifierCombineEnvironmentCountControls
            row.environment := by
  intro _hstatus task taskRest htask htaskNe
  have hcons : compactNumericParseTask :: restTasks = task :: taskRest :=
    htasks.symm.trans htask
  have htaskEq : task = compactNumericParseTask :=
    (List.cons.inj hcons).1.symm
  exact (htaskNe (by simpa [htaskEq, compactNumericParseTask])).elim

/-- A successful parse row with all numeric parser loops bounded by the same
global polynomial envelope used for its 429 coordinate bit-size bounds. -/
structure CompactNumericVerifierAcceptedParseControlledRowBound
    (rowWeight : Nat) (row : CompactNumericVerifierCheckedStepRow) : Prop where
  rowBound : CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row
  parserControls : CompactNumericVerifierParseSuccessParserControlBounds
    row.environment
      (compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound rowWeight)

theorem CompactNumericVerifierAcceptedParseControlledRowBound.of_local
    {rowWeight localBound : Nat}
    {row : CompactNumericVerifierCheckedStepRow}
    (hrow : CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row)
    (hparser : CompactNumericVerifierParseSuccessParserControlBounds
      row.environment localBound)
    (hle : localBound <=
      compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound rowWeight) :
    CompactNumericVerifierAcceptedParseControlledRowBound rowWeight row :=
  { rowBound := hrow
    parserControls := hparser.mono hle }

theorem exists_acceptedParseControlledRow_of_localBounds
    {currentState nextState : CompactNumericVerifierState}
    {rowWeight coordinateBound parserBound : Nat}
    (hrow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState /\
        row.nextState = nextState /\
        CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight /\
        (forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <= coordinateBound) /\
        CompactNumericVerifierParseSuccessParserControlBounds
          row.environment parserBound)
    (hparseTask : exists restTasks,
      currentState.1.2.1 = compactNumericParseTask :: restTasks)
    (hcoordinate : coordinateBound <=
      compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound rowWeight)
    (hparser : parserBound <=
      compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound rowWeight) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState /\
        row.nextState = nextState /\
        CompactNumericVerifierAcceptedParseControlledRowBound rowWeight row := by
  rcases hrow with
    ⟨row, hrowCurrent, hrowNext, hstate, hcoordinates, hparserControls⟩
  rcases hparseTask with ⟨restTasks, hcurrentTasks⟩
  have hrowBound :
      CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row :=
    { coordinates := fun coordinate =>
        (hcoordinates coordinate).trans hcoordinate
      stateTable := hstate
      parserControls := by
        intro _hstatus _restTasks _htasks
        exact hparserControls.mono hparser
      combineControls :=
        combineEnvironmentCountControls_vacuous_of_parseTask row restTasks
          (by simpa only [hrowCurrent] using hcurrentTasks) }
  exact ⟨row, hrowCurrent, hrowNext,
    CompactNumericVerifierAcceptedParseControlledRowBound.of_local
      hrowBound hparserControls hparser⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierTypedClosedCheckedStepRow_with_globalControlBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.closed Gamma formula) .leaf)
    {rowWeight : Nat} :
    let tree : ListedCheckedPAProofTree := .closed Gamma formula
    let structuralCertificate : StructuralValidityCertificate := .leaf
    let proofTokens := compactListedProofTokens tree ++ proofSuffix
    let certificateTokens :=
      compactStructuralCertificateTokens structuralCertificate ++
        certificateSuffix
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofSuffix, certificateSuffix),
        (restTasks, (proofNode.2.1, true) :: values)), none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          CompactNumericVerifierAcceptedTreeControlledRowBound
            rowWeight row := by
  dsimp only
  intro hcurrent hnext
  rcases
      exists_compactNumericVerifierTypedClosedCheckedStepRow_with_controlBounds
        Gamma formula proofSuffix certificateSuffix restTasks values hvalid
          hcurrent hnext with
    ⟨row, hrowCurrent, hrowNext, hcontrol, hcoordinates,
      hparserControls⟩
  have hsourceToGlobal :=
    (compactNumericVerifierTypedClosedStepSourceCoordinateSizeBound_le_global
      (by simpa only [hrowCurrent] using hcurrent)
      (by simpa only [hrowNext] using hnext)).trans
        (compactNumericVerifierTypedClosedGlobal_le_acceptedTreeGlobal
          rowWeight)
  refine ⟨row, hrowCurrent, hrowNext, ?_⟩
  refine
    { coordinates := fun coordinate =>
        (hcoordinates coordinate).trans hsourceToGlobal
      stateTable := hcontrol
      parserControls := ?_
      combineControls :=
        combineEnvironmentCountControls_vacuous_of_parseTask row restTasks
          (by simpa only [hrowCurrent]) }
  intro _hstatus _restTasks _htasks
  exact hparserControls.mono
    ((blockBound_le_compactNumericVerifierParseSuccessStepCoordinateSizeBound
      _ _ _).trans hsourceToGlobal)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierTypedClosedCheckedStepRow_with_globalParseControlBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.closed Gamma formula) .leaf)
    {rowWeight : Nat} :
    let tree : ListedCheckedPAProofTree := .closed Gamma formula
    let structuralCertificate : StructuralValidityCertificate := .leaf
    let proofTokens := compactListedProofTokens tree ++ proofSuffix
    let certificateTokens :=
      compactStructuralCertificateTokens structuralCertificate ++
        certificateSuffix
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofSuffix, certificateSuffix),
        (restTasks, (proofNode.2.1, true) :: values)), none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          CompactNumericVerifierAcceptedParseControlledRowBound
            rowWeight row := by
  dsimp only
  intro hcurrent hnext
  let tree : ListedCheckedPAProofTree := .closed Gamma formula
  let structuralCertificate : StructuralValidityCertificate := .leaf
  let proofTokens := compactListedProofTokens tree ++ proofSuffix
  let certificateTokens :=
    compactStructuralCertificateTokens structuralCertificate ++
      certificateSuffix
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens),
      (compactNumericParseTask :: restTasks, values)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofSuffix, certificateSuffix),
      (restTasks, (proofNode.2.1, true) :: values)), none)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
    width tokens.length
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  let blockBound :=
    compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  change compactNumericVerifierStateWeight currentState <= rowWeight at hcurrent
  change compactNumericVerifierStateWeight nextState <= rowWeight at hnext
  rcases
      exists_compactNumericVerifierTypedClosedCheckedStepRow_with_controlBounds
        Gamma formula proofSuffix certificateSuffix restTasks values hvalid
          hcurrent hnext with
    ⟨row, hrowCurrent, hrowNext, hcontrol, hcoordinates,
      hparserControls⟩
  change CompactNumericVerifierParseSuccessParserControlBounds
    row.environment blockBound at hparserControls
  have hsourceToGlobal :
      compactNumericVerifierTypedClosedStepSourceCoordinateSizeBound
          currentState nextState <=
        compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
          rowWeight :=
    (compactNumericVerifierTypedClosedStepSourceCoordinateSizeBound_le_global
      hcurrent hnext).trans
        (compactNumericVerifierTypedClosedGlobal_le_acceptedTreeGlobal
          rowWeight)
  have hblockToSource : blockBound <=
      compactNumericVerifierTypedClosedStepSourceCoordinateSizeBound
        currentState nextState := by
    simpa only [blockBound, stateBound, proofWeight, certificateWeight,
      compactNumericVerifierTypedClosedStepSourceCoordinateSizeBound,
      currentState, nextState, currentTokens, nextTokens, tokens, width,
      tree, structuralCertificate, proofTokens, certificateTokens,
      proofNode] using
        blockBound_le_compactNumericVerifierParseSuccessStepCoordinateSizeBound
          width tokens.length blockBound
  have hrowBound :
      CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row :=
    { coordinates := fun coordinate =>
        (hcoordinates coordinate).trans hsourceToGlobal
      stateTable := hcontrol
      parserControls := by
        intro _hstatus _restTasks _htasks
        exact hparserControls.mono
          (hblockToSource.trans hsourceToGlobal)
      combineControls :=
        combineEnvironmentCountControls_vacuous_of_parseTask row restTasks
          (by simpa only [hrowCurrent]) }
  exact ⟨row, hrowCurrent, hrowNext,
    CompactNumericVerifierAcceptedParseControlledRowBound.of_local
      hrowBound hparserControls (hblockToSource.trans hsourceToGlobal)⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierTypedVerumCheckedStepRow_with_globalControlBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.verum Gamma) .leaf)
    {rowWeight : Nat} :
    let tree : ListedCheckedPAProofTree := .verum Gamma
    let structuralCertificate : StructuralValidityCertificate := .leaf
    let proofTokens := compactListedProofTokens tree ++ proofSuffix
    let certificateTokens :=
      compactStructuralCertificateTokens structuralCertificate ++
        certificateSuffix
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofSuffix, certificateSuffix),
        (restTasks, (proofNode.2.1, true) :: values)), none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          CompactNumericVerifierAcceptedTreeControlledRowBound
            rowWeight row := by
  dsimp only
  intro hcurrent hnext
  rcases
      exists_compactNumericVerifierTypedVerumCheckedStepRow_with_controlBounds
        Gamma proofSuffix certificateSuffix restTasks values hvalid
          hcurrent hnext with
    ⟨row, hrowCurrent, hrowNext, hcontrol, hcoordinates,
      hparserControls⟩
  have hsourceToGlobal :=
    (compactNumericVerifierTypedVerumStepSourceCoordinateSizeBound_le_global
      (by simpa only [hrowCurrent] using hcurrent)
      (by simpa only [hrowNext] using hnext)).trans
        (compactNumericVerifierTypedVerumGlobal_le_acceptedTreeGlobal
          rowWeight)
  refine ⟨row, hrowCurrent, hrowNext, ?_⟩
  refine
    { coordinates := fun coordinate =>
        (hcoordinates coordinate).trans hsourceToGlobal
      stateTable := hcontrol
      parserControls := ?_
      combineControls :=
        combineEnvironmentCountControls_vacuous_of_parseTask row restTasks
          (by simpa only [hrowCurrent]) }
  intro _hstatus _restTasks _htasks
  exact hparserControls.mono
    ((blockBound_le_compactNumericVerifierParseSuccessStepCoordinateSizeBound
      _ _ _).trans hsourceToGlobal)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierTypedVerumCheckedStepRow_with_globalParseControlBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.verum Gamma) .leaf)
    {rowWeight : Nat} :
    let tree : ListedCheckedPAProofTree := .verum Gamma
    let structuralCertificate : StructuralValidityCertificate := .leaf
    let proofTokens := compactListedProofTokens tree ++ proofSuffix
    let certificateTokens :=
      compactStructuralCertificateTokens structuralCertificate ++
        certificateSuffix
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofSuffix, certificateSuffix),
        (restTasks, (proofNode.2.1, true) :: values)), none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          CompactNumericVerifierAcceptedParseControlledRowBound
            rowWeight row := by
  dsimp only
  intro hcurrent hnext
  have hlocal :=
    exists_compactNumericVerifierTypedVerumCheckedStepRow_with_controlBounds
      Gamma proofSuffix certificateSuffix restTasks values hvalid
        hcurrent hnext
  have hcoordinate :=
    (compactNumericVerifierTypedVerumStepSourceCoordinateSizeBound_le_global
      hcurrent hnext).trans
        (compactNumericVerifierTypedVerumGlobal_le_acceptedTreeGlobal
          rowWeight)
  refine exists_acceptedParseControlledRow_of_localBounds
    hlocal ⟨restTasks, rfl⟩ hcoordinate ?_
  exact
    (blockBound_le_compactNumericVerifierParseSuccessStepCoordinateSizeBound
      _ _ _).trans hcoordinate

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierTypedAcceptedPAAxiomCheckedStepRow_with_globalControlBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (paCertificate : PAAxiomCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid
      (.axm Gamma sentence) (.axiomCert paCertificate))
    {rowWeight : Nat} :
    let tree : ListedCheckedPAProofTree := .axm Gamma sentence
    let structuralCertificate : StructuralValidityCertificate :=
      .axiomCert paCertificate
    let proofTokens := compactListedProofTokens tree ++ proofSuffix
    let certificateTokens :=
      compactStructuralCertificateTokens structuralCertificate ++
        certificateSuffix
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let certificateNode :=
      compactStructuralCertificateNodeExpected structuralCertificate
        certificateSuffix
    let result := compactAxmRuleCheck
      (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1))
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofSuffix, certificateSuffix),
        (restTasks, (proofNode.2.1, result) :: values)), none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          CompactNumericVerifierAcceptedTreeControlledRowBound
            rowWeight row := by
  dsimp only
  intro hcurrent hnext
  rcases
      exists_compactNumericVerifierTypedAcceptedPAAxiomCheckedStepRow_with_controlBounds
        Gamma sentence paCertificate proofSuffix certificateSuffix restTasks
          values hvalid hcurrent hnext with
    ⟨row, hrowCurrent, hrowNext, hcontrol, hcoordinates,
      hparserControls⟩
  have hsourceToGlobal :=
    (compactNumericVerifierAcceptedPAAxiomStepSourceCoordinateSizeBound_le_global
      (by simpa only [hrowCurrent] using hcurrent)
      (by simpa only [hrowNext] using hnext)).trans
        (compactNumericVerifierAcceptedPAAxiomGlobal_le_acceptedTreeGlobal
          rowWeight)
  refine ⟨row, hrowCurrent, hrowNext, ?_⟩
  refine
    { coordinates := fun coordinate =>
        (hcoordinates coordinate).trans hsourceToGlobal
      stateTable := hcontrol
      parserControls := ?_
      combineControls :=
        combineEnvironmentCountControls_vacuous_of_parseTask row restTasks
          (by simpa only [hrowCurrent]) }
  intro _hstatus _restTasks _htasks
  exact hparserControls.mono
    ((blockBound_le_compactNumericVerifierParseSuccessStepCoordinateSizeBound
      _ _ _).trans hsourceToGlobal)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierTypedAcceptedPAAxiomCheckedStepRow_with_globalParseControlBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (paCertificate : PAAxiomCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid
      (.axm Gamma sentence) (.axiomCert paCertificate))
    {rowWeight : Nat} :
    let tree : ListedCheckedPAProofTree := .axm Gamma sentence
    let structuralCertificate : StructuralValidityCertificate :=
      .axiomCert paCertificate
    let proofTokens := compactListedProofTokens tree ++ proofSuffix
    let certificateTokens :=
      compactStructuralCertificateTokens structuralCertificate ++
        certificateSuffix
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let certificateNode :=
      compactStructuralCertificateNodeExpected structuralCertificate
        certificateSuffix
    let result := compactAxmRuleCheck
      (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1))
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofSuffix, certificateSuffix),
        (restTasks, (proofNode.2.1, result) :: values)), none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          CompactNumericVerifierAcceptedParseControlledRowBound
            rowWeight row := by
  dsimp only
  intro hcurrent hnext
  have hlocal :=
    exists_compactNumericVerifierTypedAcceptedPAAxiomCheckedStepRow_with_controlBounds
      Gamma sentence paCertificate proofSuffix certificateSuffix restTasks
        values hvalid hcurrent hnext
  have hcoordinate :=
    (compactNumericVerifierAcceptedPAAxiomStepSourceCoordinateSizeBound_le_global
      hcurrent hnext).trans
        (compactNumericVerifierAcceptedPAAxiomGlobal_le_acceptedTreeGlobal
          rowWeight)
  refine exists_acceptedParseControlledRow_of_localBounds
    hlocal ⟨restTasks, rfl⟩ hcoordinate ?_
  exact
    (blockBound_le_compactNumericVerifierParseSuccessStepCoordinateSizeBound
      _ _ _).trans hcoordinate

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000000 in
theorem
    exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_globalControlBound
    (proofTokens certificateTokens nextProofTokens nextCertificateTokens :
      List Nat)
    (restTasks nextTasks : List CompactNumericVerifierTask)
    (values nextValues : List CompactNumericChildResult)
    (proofNode : CompactNumericVerifierTask)
    (certificateNode : CompactNumericCertificateNode)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser
      certificateTokens = some certificateNode)
    (hproofTag : proofNode.1 = 3 \/ proofNode.1 = 4 \/ proofNode.1 = 5 \/
      proofNode.1 = 6 \/ proofNode.1 = 7 \/ proofNode.1 = 8 \/
      proofNode.1 = 9)
    (houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens), (nextTasks, nextValues)))
    {rowWeight : Nat} :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((nextProofTokens, nextCertificateTokens),
        (nextTasks, nextValues)), none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          CompactNumericVerifierAcceptedTreeControlledRowBound
            rowWeight row := by
  dsimp only
  intro hcurrent hnext
  rcases
      exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_controlBounds
        proofTokens certificateTokens nextProofTokens nextCertificateTokens
          restTasks nextTasks values nextValues proofNode certificateNode
          hproofParser hcertificateParser hproofTag houtputCase
          hcurrent hnext with
    ⟨row, hrowCurrent, hrowNext, hcontrol, hcoordinates,
      hparserControls⟩
  have hsourceToGlobal :=
    (compactNumericVerifierTypedNonLeafStepSourceCoordinateSizeBound_le_global
      (by simpa only [hrowCurrent] using hcurrent)
      (by simpa only [hrowNext] using hnext)).trans
        (compactNumericVerifierTypedNonLeafGlobal_le_acceptedTreeGlobal
          rowWeight)
  refine ⟨row, hrowCurrent, hrowNext, ?_⟩
  refine
    { coordinates := fun coordinate =>
        (hcoordinates coordinate).trans hsourceToGlobal
      stateTable := hcontrol
      parserControls := ?_
      combineControls :=
        combineEnvironmentCountControls_vacuous_of_parseTask row restTasks
          (by simpa only [hrowCurrent]) }
  intro _hstatus _restTasks _htasks
  exact hparserControls.mono
    ((blockBound_le_compactNumericVerifierParseSuccessStepCoordinateSizeBound
      _ _ _).trans hsourceToGlobal)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000000 in
theorem
    exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_globalParseControlBound
    (proofTokens certificateTokens nextProofTokens nextCertificateTokens :
      List Nat)
    (restTasks nextTasks : List CompactNumericVerifierTask)
    (values nextValues : List CompactNumericChildResult)
    (proofNode : CompactNumericVerifierTask)
    (certificateNode : CompactNumericCertificateNode)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser
      certificateTokens = some certificateNode)
    (hproofTag : proofNode.1 = 3 \/ proofNode.1 = 4 \/ proofNode.1 = 5 \/
      proofNode.1 = 6 \/ proofNode.1 = 7 \/ proofNode.1 = 8 \/
      proofNode.1 = 9)
    (houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens), (nextTasks, nextValues)))
    {rowWeight : Nat} :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((nextProofTokens, nextCertificateTokens),
        (nextTasks, nextValues)), none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          CompactNumericVerifierAcceptedParseControlledRowBound
            rowWeight row := by
  dsimp only
  intro hcurrent hnext
  have hlocal :=
    exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_controlBounds
      proofTokens certificateTokens nextProofTokens nextCertificateTokens
        restTasks nextTasks values nextValues proofNode certificateNode
        hproofParser hcertificateParser hproofTag houtputCase hcurrent hnext
  have hcoordinate :=
    (compactNumericVerifierTypedNonLeafStepSourceCoordinateSizeBound_le_global
      hcurrent hnext).trans
        (compactNumericVerifierTypedNonLeafGlobal_le_acceptedTreeGlobal
          rowWeight)
  refine exists_acceptedParseControlledRow_of_localBounds
    hlocal ⟨restTasks, rfl⟩ hcoordinate ?_
  exact
    (blockBound_le_compactNumericVerifierParseSuccessStepCoordinateSizeBound
      _ _ _).trans hcoordinate

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000000 in
theorem
    exists_compactNumericVerifierPublicCombineCheckedStepRow_with_globalControlBound_of_transition
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (htaskNe : task.1 ≠ 10)
    (htransition : compactNumericCombineState task
      ((proofTokens, certificateTokens), (tasks, source)) =
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus))
    {rowWeight : Nat}
    (hcurrent : compactNumericVerifierStateWeight
      ((((proofTokens, certificateTokens), (task :: tasks, source)), none)) <=
        rowWeight)
    (hnext : compactNumericVerifierStateWeight
      ((((proofTokens, certificateTokens), (tasks, target)), nextStatus)) <=
        rowWeight) :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (task :: tasks, source)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState /\
        row.nextState = nextState /\
        CompactNumericVerifierAcceptedTreeControlledRowBound
          rowWeight row := by
  dsimp only
  rcases
      exists_compactNumericVerifierPublicCombineCheckedStepRow_with_controlBounds_and_countControls_of_transition
        proofTokens certificateTokens task tasks source target nextStatus
          htaskNe htransition hcurrent hnext with
    ⟨row, hrowCurrent, hrowNext, hcontrol, hcoordinates, hcombineControls⟩
  refine ⟨row, hrowCurrent, hrowNext, ?_⟩
  refine
    { coordinates := ?_
      stateTable := hcontrol
      parserControls := ?_
      combineControls := ?_ }
  · intro coordinate
    exact (hcoordinates coordinate).trans
      (((compactNumericVerifierCombineLocalCoordinateSizeBound_le_global
          hcurrent hnext).trans
        (compactNumericVerifierCombineGlobal_le_nonParseGlobal rowWeight)).trans
        (compactNumericVerifierNonParseGlobal_le_acceptedTreeGlobal rowWeight))
  · intro _hstatus rest htasks
    have htasks' : task :: tasks = compactNumericParseTask :: rest := by
      simpa only [hrowCurrent] using htasks
    have htaskEq : task = compactNumericParseTask := (List.cons.inj htasks').1
    have htagEq : task.1 = 10 := by
      simpa [compactNumericParseTask] using congrArg Prod.fst htaskEq
    exact (htaskNe htagEq).elim
  · intro _hstatus actualTask rest htasks hactualTaskNe
    have htasks' : task :: tasks = actualTask :: rest := by
      simpa only [hrowCurrent] using htasks
    have htaskEq : actualTask = task := (List.cons.inj htasks').1.symm
    simpa only [htaskEq] using hcombineControls

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000000 in
theorem
    exists_compactNumericVerifierCanonicalNonLeafCheckedStepRow_with_globalControlBound
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix nextProofTokens nextCertificateTokens :
      List Nat)
    (restTasks nextTasks : List CompactNumericVerifierTask)
    (values nextValues : List CompactNumericChildResult)
    {rowWeight : Nat} :
    let proofTokens := compactListedProofTokens tree ++ proofSuffix
    let certificateTokens :=
      compactStructuralCertificateTokens certificate ++ certificateSuffix
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let certificateNode :=
      compactStructuralCertificateNodeExpected certificate certificateSuffix
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((nextProofTokens, nextCertificateTokens),
        (nextTasks, nextValues)), none)
    (proofNode.1 = 3 \/ proofNode.1 = 4 \/ proofNode.1 = 5 \/
      proofNode.1 = 6 \/ proofNode.1 = 7 \/ proofNode.1 = 8 \/
      proofNode.1 = 9) ->
    compactNumericNodeTransition proofNode certificateNode restTasks values =
      some ((nextProofTokens, nextCertificateTokens),
        (nextTasks, nextValues)) ->
    compactNumericVerifierStateWeight currentState <= rowWeight ->
    compactNumericVerifierStateWeight nextState <= rowWeight ->
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState /\
        row.nextState = nextState /\
        CompactNumericVerifierAcceptedTreeControlledRowBound
          rowWeight row := by
  dsimp only
  intro hproofTag htransition hcurrent hnext
  let proofTokens := compactListedProofTokens tree ++ proofSuffix
  let certificateTokens :=
    compactStructuralCertificateTokens certificate ++ certificateSuffix
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected certificate certificateSuffix
  have hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode := by
    simp only [proofTokens, proofNode,
      compactListedProofNodeFieldsParser_canonical_append]
  have hcertificateParser :
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode := by
    simp only [certificateTokens, certificateNode,
      compactStructuralCertificateNodeParser_canonical_append]
  have houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens), (nextTasks, nextValues)) :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens),
          (nextTasks, nextValues))).mp htransition
  exact
    exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_globalControlBound
      proofTokens certificateTokens nextProofTokens nextCertificateTokens
        restTasks nextTasks values nextValues proofNode certificateNode
        hproofParser hcertificateParser hproofTag houtputCase hcurrent hnext

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem exists_compactNumericVerifierAcceptedClosedLeafRow_at_zero_with_control
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.closed Gamma formula) .leaf)
    {rowWeight : Nat}
    (hweights : forall offset,
      offset <= compactNumericTreeTaskSteps (.closed Gamma formula) .leaf ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState (.closed Gamma formula) .leaf
              proofSuffix certificateSuffix restTasks values) offset) <=
          rowWeight) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.closed Gamma formula) .leaf
          proofSuffix certificateSuffix restTasks values) 0 /\
      row.nextState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.closed Gamma formula) .leaf
          proofSuffix certificateSuffix restTasks values) 1 /\
      CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree := .closed Gamma formula
  let certificate : StructuralValidityCertificate := .leaf
  let start := compactNumericTreeTaskStartState tree certificate
    proofSuffix certificateSuffix restTasks values
  let nextState : CompactNumericVerifierState :=
    (((proofSuffix, certificateSuffix),
      (restTasks,
        ((compactListedProofNodeExpectedFields tree proofSuffix).2.1,
          true) :: values)), none)
  have htrace : (listedCertificateValidTrace tree certificate).1 = true :=
    (listedCertificateValidTrace_result_eq_true_iff tree certificate).2 hvalid
  have hrunRaw := compactNumericClosedLeafTask_execute Gamma formula
    proofSuffix certificateSuffix restTasks values
  have hstep : compactNumericVerifierStep start = nextState := by
    simpa [tree, certificate, start, nextState,
      compactNumericTreeTaskStartState, compactNumericTreeTaskSteps,
      compactNumericTreeTaskSuccessState, compactListedProofNodeExpectedFields,
      ListedCheckedPAProofTree.conclusionList, Function.iterate_one,
      htrace] using hrunRaw
  have hcurrent : compactNumericVerifierStateWeight start <= rowWeight := by
    simpa [start, tree, certificate, compactNumericVerifierStateAt] using
      hweights 0 (by simp [compactNumericTreeTaskSteps])
  have hnext : compactNumericVerifierStateWeight nextState <= rowWeight := by
    rw [← hstep]
    simpa [start, tree, certificate, compactNumericVerifierStateAt,
      Function.iterate_one] using
      hweights 1 (by simp [compactNumericTreeTaskSteps])
  rcases
      exists_compactNumericVerifierTypedClosedCheckedStepRow_with_globalControlBound
        Gamma formula proofSuffix certificateSuffix restTasks values hvalid
          hcurrent hnext with
    ⟨row, hrowCurrent, hrowNext, hrowBound⟩
  refine ⟨row, ?_, ?_, hrowBound⟩
  · simpa [start, tree, certificate, compactNumericVerifierStateAt,
      compactNumericTreeTaskStartState] using hrowCurrent
  · have hstateAtOne :
        compactNumericVerifierStateAt start 1 = nextState := by
      simpa only [compactNumericVerifierStateAt, Function.iterate_one] using
        hstep
    exact hrowNext.trans (by
      simpa only [start, tree, certificate] using hstateAtOne.symm)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 9000000 in
theorem exists_compactNumericVerifierAcceptedPAAxiomLeafRow_at_zero_with_control
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (paCertificate : PAAxiomCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.axm Gamma sentence)
      (.axiomCert paCertificate))
    {rowWeight : Nat}
    (hweights : forall offset,
      offset <= compactNumericTreeTaskSteps (.axm Gamma sentence)
          (.axiomCert paCertificate) ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState (.axm Gamma sentence)
              (.axiomCert paCertificate) proofSuffix certificateSuffix
              restTasks values) offset) <= rowWeight) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.axm Gamma sentence)
          (.axiomCert paCertificate) proofSuffix certificateSuffix restTasks
          values) 0 /\
      row.nextState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.axm Gamma sentence)
          (.axiomCert paCertificate) proofSuffix certificateSuffix restTasks
          values) 1 /\
      CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree := .axm Gamma sentence
  let certificate : StructuralValidityCertificate :=
    .axiomCert paCertificate
  let start := compactNumericTreeTaskStartState tree certificate
    proofSuffix certificateSuffix restTasks values
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected certificate certificateSuffix
  let result := compactAxmRuleCheck
    (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1))
  let nextState : CompactNumericVerifierState :=
    (((proofSuffix, certificateSuffix),
      (restTasks, (proofNode.2.1, result) :: values)), none)
  have htrace : (listedCertificateValidTrace tree certificate).1 = true :=
    (listedCertificateValidTrace_result_eq_true_iff tree certificate).2 hvalid
  have hresult : result = true := by
    simpa [result, proofNode, certificateNode, tree, certificate,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactSentenceTokens, arithmeticPropositionTokenValue] using
      (compactAxmRuleCheck_canonical Gamma sentence paCertificate).trans
        htrace
  have hrunRaw := compactNumericAxmLeafTask_execute Gamma sentence
    paCertificate proofSuffix certificateSuffix restTasks values
  have hstep : compactNumericVerifierStep start = nextState := by
    simpa [tree, certificate, start, proofNode, result, nextState,
      compactNumericTreeTaskStartState, compactNumericTreeTaskSteps,
      compactNumericTreeTaskSuccessState, compactListedProofNodeExpectedFields,
      ListedCheckedPAProofTree.conclusionList, Function.iterate_one, htrace,
      hresult] using hrunRaw
  have hcurrent : compactNumericVerifierStateWeight start <= rowWeight := by
    simpa [start, tree, certificate, compactNumericVerifierStateAt] using
      hweights 0 (by simp [compactNumericTreeTaskSteps])
  have hnext : compactNumericVerifierStateWeight nextState <= rowWeight := by
    rw [← hstep]
    simpa [start, tree, certificate, compactNumericVerifierStateAt,
      Function.iterate_one] using
      hweights 1 (by simp [compactNumericTreeTaskSteps])
  rcases
      exists_compactNumericVerifierTypedAcceptedPAAxiomCheckedStepRow_with_globalControlBound
        Gamma sentence paCertificate proofSuffix certificateSuffix restTasks
          values hvalid hcurrent hnext with
    ⟨row, hrowCurrent, hrowNext, hrowBound⟩
  refine ⟨row, ?_, ?_, hrowBound⟩
  · simpa [start, tree, certificate, compactNumericVerifierStateAt,
      compactNumericTreeTaskStartState] using hrowCurrent
  · have hstateAtOne :
        compactNumericVerifierStateAt start 1 = nextState := by
      simpa only [compactNumericVerifierStateAt, Function.iterate_one] using
        hstep
    exact hrowNext.trans (by
      simpa only [start, tree, certificate] using hstateAtOne.symm)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem exists_compactNumericVerifierAcceptedVerumLeafRow_at_zero_with_control
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.verum Gamma) .leaf)
    {rowWeight : Nat}
    (hweights : forall offset,
      offset <= compactNumericTreeTaskSteps (.verum Gamma) .leaf ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState (.verum Gamma) .leaf
              proofSuffix certificateSuffix restTasks values) offset) <=
          rowWeight) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.verum Gamma) .leaf proofSuffix
          certificateSuffix restTasks values) 0 /\
      row.nextState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.verum Gamma) .leaf proofSuffix
          certificateSuffix restTasks values) 1 /\
      CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree := .verum Gamma
  let certificate : StructuralValidityCertificate := .leaf
  let start := compactNumericTreeTaskStartState tree certificate
    proofSuffix certificateSuffix restTasks values
  let nextState : CompactNumericVerifierState :=
    (((proofSuffix, certificateSuffix),
      (restTasks,
        ((compactListedProofNodeExpectedFields tree proofSuffix).2.1,
          true) :: values)), none)
  have htrace : (listedCertificateValidTrace tree certificate).1 = true :=
    (listedCertificateValidTrace_result_eq_true_iff tree certificate).2 hvalid
  have hrunRaw := compactNumericVerumLeafTask_execute Gamma proofSuffix
    certificateSuffix restTasks values
  have hstep : compactNumericVerifierStep start = nextState := by
    simpa [tree, certificate, start, nextState,
      compactNumericTreeTaskStartState, compactNumericTreeTaskSteps,
      compactNumericTreeTaskSuccessState, compactListedProofNodeExpectedFields,
      ListedCheckedPAProofTree.conclusionList, Function.iterate_one,
      htrace] using hrunRaw
  have hcurrent : compactNumericVerifierStateWeight start <= rowWeight := by
    simpa [start, tree, certificate, compactNumericVerifierStateAt] using
      hweights 0 (by simp [compactNumericTreeTaskSteps])
  have hnext : compactNumericVerifierStateWeight nextState <= rowWeight := by
    rw [← hstep]
    simpa [start, tree, certificate, compactNumericVerifierStateAt,
      Function.iterate_one] using
      hweights 1 (by simp [compactNumericTreeTaskSteps])
  rcases
      exists_compactNumericVerifierTypedVerumCheckedStepRow_with_globalControlBound
        Gamma proofSuffix certificateSuffix restTasks values hvalid hcurrent
          hnext with
    ⟨row, hrowCurrent, hrowNext, hrowBound⟩
  refine ⟨row, ?_, ?_, hrowBound⟩
  · simpa [start, tree, certificate, compactNumericVerifierStateAt,
      compactNumericTreeTaskStartState] using hrowCurrent
  · have hstateAtOne :
        compactNumericVerifierStateAt start 1 = nextState := by
      simpa only [compactNumericVerifierStateAt, Function.iterate_one] using
        hstep
    exact hrowNext.trans (by
      simpa only [start, tree, certificate] using hstateAtOne.symm)

theorem exists_compactNumericVerifierAcceptedTreeControlledRow_at_unary_offset
    {start childStart beforeCombine finish : CompactNumericVerifierState}
    {childSteps offset rowWeight : Nat}
    (hrootStep : compactNumericVerifierStep start = childStart)
    (hchildExecute :
      (compactNumericVerifierStep^[childSteps]) childStart = beforeCombine)
    (hcombineStep : compactNumericVerifierStep beforeCombine = finish)
    (hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = childStart /\
        CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row)
    (hchildRows : forall childOffset, childOffset < childSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt childStart childOffset /\
          row.nextState =
            compactNumericVerifierStateAt childStart (childOffset + 1) /\
          CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row)
    (hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row)
    (hoffset : offset < 1 + childSteps + 1) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt start offset /\
        row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
        CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
  exact exists_checkedStepRow_at_unary_execution_offset
    (CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight)
      hrootStep hchildExecute hcombineStep hrootRow hchildRows hcombineRow
        hoffset

theorem exists_compactNumericVerifierAcceptedTreeControlledRow_at_binary_offset
    {start leftStart rightStart beforeCombine finish :
      CompactNumericVerifierState}
    {leftSteps rightSteps offset rowWeight : Nat}
    (hrootStep : compactNumericVerifierStep start = leftStart)
    (hleftExecute :
      (compactNumericVerifierStep^[leftSteps]) leftStart = rightStart)
    (hrightExecute :
      (compactNumericVerifierStep^[rightSteps]) rightStart = beforeCombine)
    (hcombineStep : compactNumericVerifierStep beforeCombine = finish)
    (hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = leftStart /\
        CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row)
    (hleftRows : forall leftOffset, leftOffset < leftSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt leftStart leftOffset /\
          row.nextState =
            compactNumericVerifierStateAt leftStart (leftOffset + 1) /\
          CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row)
    (hrightRows : forall rightOffset, rightOffset < rightSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt rightStart rightOffset /\
          row.nextState =
            compactNumericVerifierStateAt rightStart (rightOffset + 1) /\
          CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row)
    (hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row)
    (hoffset : offset < 1 + leftSteps + rightSteps + 1) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt start offset /\
        row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
        CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
  exact exists_checkedStepRow_at_binary_execution_offset
    (CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight)
      hrootStep hleftExecute hrightExecute hcombineStep hrootRow hleftRows
        hrightRows hcombineRow hoffset

#print axioms
  exists_compactNumericVerifierTypedClosedCheckedStepRow_with_globalControlBound
#print axioms
  exists_compactNumericVerifierTypedVerumCheckedStepRow_with_globalControlBound
#print axioms
  exists_compactNumericVerifierTypedAcceptedPAAxiomCheckedStepRow_with_globalControlBound
#print axioms
  exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_globalControlBound
#print axioms
  exists_compactNumericVerifierPublicCombineCheckedStepRow_with_globalControlBound_of_transition
#print axioms
  exists_compactNumericVerifierCanonicalNonLeafCheckedStepRow_with_globalControlBound
#print axioms
  exists_compactNumericVerifierAcceptedClosedLeafRow_at_zero_with_control
#print axioms
  exists_compactNumericVerifierAcceptedPAAxiomLeafRow_at_zero_with_control
#print axioms
  exists_compactNumericVerifierAcceptedVerumLeafRow_at_zero_with_control
#print axioms
  exists_compactNumericVerifierAcceptedTreeControlledRow_at_unary_offset
#print axioms
  exists_compactNumericVerifierAcceptedTreeControlledRow_at_binary_offset

end FoundationCompactNumericListedDirectVerifierAcceptedTreeRowStateTableControlBounds
