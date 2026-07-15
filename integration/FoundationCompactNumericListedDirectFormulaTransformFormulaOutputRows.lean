import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRows

/-!
# Exact direct output rows for syntax-formula transformation steps

Formula tasks copy their consumed header in the free, shift, and substitution
modes.  Negation replaces exactly the first formula tag and preserves the
remaining consumed tokens.  Both alternatives are exposed by bounded direct
row graphs below.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactParserDirectTrace
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListAppendSourcePrefix
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefix
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows

def compactFormulaTransformFormulaEmission
    (mode tag consumedCount : Nat) (source : List Nat) : List Nat :=
  if consumedCount = 0 then
    []
  else if mode = 0 then
    source.take consumedCount
  else if mode = 1 then
    source.take consumedCount
  else if mode = 2 then
    source.take consumedCount
  else if mode = 4 then
    []
  else if mode = 5 then
    source.take consumedCount
  else
    FoundationCompactNumericFormulaNegation.compactNegationFormulaTag tag ::
      (source.take consumedCount).drop 1

def CompactFormulaTransformFormulaOutputRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat) : Prop :=
  current.parserTokensCount =
      consumedCount + next.parserTokensCount ∧
    ((consumedCount = 0 ∧
        CompactFormulaTransformOutputSameRows
          tokenTable width tokenCount current next) ∨
     (1 ≤ consumedCount ∧
       (((mode = 0 ∨ mode = 1 ∨ mode = 2 ∨ mode = 5) ∧
          CompactFormulaTransformOutputRawPrefixRows
            tokenTable width tokenCount current next consumedCount) ∨
        (mode = 4 ∧
          CompactFormulaTransformOutputSameRows
            tokenTable width tokenCount current next) ∨
        (mode ≠ 0 ∧ mode ≠ 1 ∧ mode ≠ 2 ∧ mode ≠ 4 ∧ mode ≠ 5 ∧
          CompactNegationFormulaTagGraph tag mappedHead ∧
          CompactFormulaTransformOutputMappedPrefixRows
            tokenTable width tokenCount current next
              consumedCount mappedHead))))

def compactFormulaTransformFormulaOutputRowsDef :
    𝚺₀.Semisentence 29 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentParserFinish
      currentParserTokensFinish currentParserTasksFinish
      currentParserTokensBoundary currentParserTokensCount
      currentParserTasksBoundary currentParserTasksCount
      currentOutputBoundary currentOutputCount
      nextStart nextFinish nextParserFinish
      nextParserTokensFinish nextParserTasksFinish
      nextParserTokensBoundary nextParserTokensCount
      nextParserTasksBoundary nextParserTasksCount
      nextOutputBoundary nextOutputCount
      mode tag consumedCount mappedHead.
    currentParserTokensCount = consumedCount + nextParserTokensCount ∧
    ((consumedCount = 0 ∧
      !(compactAdditiveNatListSameRowsDef)
        tokenTable width tokenCount
        currentOutputBoundary currentOutputCount
        nextOutputBoundary nextOutputCount) ∨
     (1 ≤ consumedCount ∧
      (((mode = 0 ∨ mode = 1 ∨ mode = 2 ∨ mode = 5) ∧
        !(compactAdditiveNatListAppendSourcePrefixDef)
          tokenTable width tokenCount
          currentParserFinish currentFinish currentOutputCount
          currentStart currentParserTokensFinish
            currentParserTokensCount consumedCount
          nextParserFinish nextFinish nextOutputCount) ∨
       (mode = 4 ∧
        !(compactAdditiveNatListSameRowsDef)
          tokenTable width tokenCount
          currentOutputBoundary currentOutputCount
          nextOutputBoundary nextOutputCount) ∨
       (mode ≠ 0 ∧ mode ≠ 1 ∧ mode ≠ 2 ∧ mode ≠ 4 ∧ mode ≠ 5 ∧
        !(compactNegationFormulaTagGraphDef) tag mappedHead ∧
        !(compactAdditiveNatListAppendMappedSourcePrefixDef)
          tokenTable width tokenCount
          currentParserFinish currentFinish currentOutputCount
          currentStart currentParserTokensFinish
            currentParserTokensCount consumedCount
          nextParserFinish nextFinish nextOutputBoundary nextOutputCount
          mappedHead))))”

def compactFormulaTransformFormulaOutputRowsEnvironment
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat) : Fin 29 → Nat :=
  ![tokenTable, width, tokenCount,
    current.start, current.finish, current.parserFinish,
    current.parserTokensFinish, current.parserTasksFinish,
    current.parserTokensBoundary, current.parserTokensCount,
    current.parserTasksBoundary, current.parserTasksCount,
    current.outputBoundary, current.outputCount,
    next.start, next.finish, next.parserFinish,
    next.parserTokensFinish, next.parserTasksFinish,
    next.parserTokensBoundary, next.parserTokensCount,
    next.parserTasksBoundary, next.parserTasksCount,
    next.outputBoundary, next.outputCount,
    mode, tag, consumedCount, mappedHead]

@[simp] theorem compactFormulaTransformFormulaOutputRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat) :
    compactFormulaTransformFormulaOutputRowsDef.val.Evalb
        (compactFormulaTransformFormulaOutputRowsEnvironment
          tokenTable width tokenCount current next
            mode tag consumedCount mappedHead) ↔
      CompactFormulaTransformFormulaOutputRows
        tokenTable width tokenCount current next
          mode tag consumedCount mappedHead := by
  let env := compactFormulaTransformFormulaOutputRowsEnvironment
    tokenTable width tokenCount current next mode tag consumedCount mappedHead
  change compactFormulaTransformFormulaOutputRowsDef.val.Evalb env ↔ _
  have hsameEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 29), #1, #2,
          #12, #13, #23, #24]) =
        ![tokenTable, width, tokenCount,
          current.outputBoundary, current.outputCount,
          next.outputBoundary, next.outputCount] := by
    funext index
    fin_cases index <;> simp [env,
      compactFormulaTransformFormulaOutputRowsEnvironment]
  have hrawEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 29), #1, #2,
          #5, #4, #13, #3, #6, #9, #27, #16, #15, #24]) =
        ![tokenTable, width, tokenCount,
          current.parserFinish, current.finish, current.outputCount,
          current.start, current.parserTokensFinish,
          current.parserTokensCount, consumedCount,
          next.parserFinish, next.finish, next.outputCount] := by
    funext index
    fin_cases index <;> simp [env,
      compactFormulaTransformFormulaOutputRowsEnvironment]
  have htagEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#26 : Semiterm ℒₒᵣ Empty 29), #28]) =
        ![tag, mappedHead] := by
    funext index
    fin_cases index <;> simp [env,
      compactFormulaTransformFormulaOutputRowsEnvironment]
  have hmappedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 29), #1, #2,
          #5, #4, #13, #3, #6, #9, #27,
          #16, #15, #23, #24, #28]) =
        ![tokenTable, width, tokenCount,
          current.parserFinish, current.finish, current.outputCount,
          current.start, current.parserTokensFinish,
          current.parserTokensCount, consumedCount,
          next.parserFinish, next.finish, next.outputBoundary,
          next.outputCount, mappedHead] := by
    funext index
    fin_cases index <;> simp [env,
      compactFormulaTransformFormulaOutputRowsEnvironment]
  have hsameSpec : compactAdditiveNatListSameRowsDef.val.Evalb
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 29), #1, #2,
            #12, #13, #23, #24]) ↔
      CompactAdditiveNatListSameRows tokenTable width tokenCount
        current.outputBoundary current.outputCount
        next.outputBoundary next.outputCount := by
    rw [hsameEnv]
    exact compactAdditiveNatListSameRowsDef_spec
      tokenTable width tokenCount current.outputBoundary current.outputCount
        next.outputBoundary next.outputCount
  have hrawSpec : compactAdditiveNatListAppendSourcePrefixDef.val.Evalb
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 29), #1, #2,
            #5, #4, #13, #3, #6, #9, #27, #16, #15, #24]) ↔
      CompactAdditiveNatListAppendSourcePrefix tokenTable width tokenCount
        current.parserFinish current.finish current.outputCount
        current.start current.parserTokensFinish current.parserTokensCount
        consumedCount next.parserFinish next.finish next.outputCount := by
    rw [hrawEnv]
    exact compactAdditiveNatListAppendSourcePrefixDef_spec
      tokenTable width tokenCount
      current.parserFinish current.finish current.outputCount
      current.start current.parserTokensFinish current.parserTokensCount
      consumedCount next.parserFinish next.finish next.outputCount
  have htagSpec : compactNegationFormulaTagGraphDef.val.Evalb
        (Semiterm.val env Empty.elim ∘
          ![(#26 : Semiterm ℒₒᵣ Empty 29), #28]) ↔
      CompactNegationFormulaTagGraph tag mappedHead := by
    rw [htagEnv]
    exact compactNegationFormulaTagGraphDef_spec tag mappedHead
  have hmappedSpec : compactAdditiveNatListAppendMappedSourcePrefixDef.val.Evalb
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 29), #1, #2,
            #5, #4, #13, #3, #6, #9, #27,
            #16, #15, #23, #24, #28]) ↔
      CompactAdditiveNatListAppendMappedSourcePrefix
        tokenTable width tokenCount
        current.parserFinish current.finish current.outputCount
        current.start current.parserTokensFinish current.parserTokensCount
        consumedCount next.parserFinish next.finish next.outputBoundary
        next.outputCount mappedHead := by
    rw [hmappedEnv]
    exact compactAdditiveNatListAppendMappedSourcePrefixDef_spec
      tokenTable width tokenCount
      current.parserFinish current.finish current.outputCount
      current.start current.parserTokensFinish current.parserTokensCount
      consumedCount next.parserFinish next.finish next.outputBoundary
      next.outputCount mappedHead
  have hcurrentCountValue : env 9 = current.parserTokensCount := rfl
  have hnextCountValue : env 20 = next.parserTokensCount := rfl
  have hmodeValue : env 25 = mode := rfl
  have htagValue : env 26 = tag := rfl
  have hconsumedValue : env 27 = consumedCount := rfl
  simp [compactFormulaTransformFormulaOutputRowsDef,
    CompactFormulaTransformFormulaOutputRows,
    CompactFormulaTransformStateRowCoordinates.parser,
    CompactFormulaTransformOutputSameRows,
    CompactFormulaTransformOutputRawPrefixRows,
    CompactFormulaTransformOutputMappedPrefixRows,
    hsameSpec, hrawSpec, hmappedSpec,
    hcurrentCountValue, hnextCountValue, hmodeValue,
    htagValue, hconsumedValue]
  intro _hcount
  rfl

theorem compactFormulaTransformFormulaOutputRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformFormulaOutputRowsDef.val := by
  simp [compactFormulaTransformFormulaOutputRowsDef]

theorem exists_mapped_compactFormulaTransformFormulaOutputRows_iff
    {tokenTable width tokenCount mode tag consumedCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    (∃ mappedHead,
        CompactFormulaTransformFormulaOutputRows
          tokenTable width tokenCount currentCoordinates nextCoordinates
            mode tag consumedCount mappedHead) ↔
      currentCoordinates.parserTokensCount =
          consumedCount + nextCoordinates.parserTokensCount ∧
        next.2 = current.2 ++
          compactFormulaTransformFormulaEmission
            mode tag consumedCount current.1.1 := by
  have hsame := compactFormulaTransformOutputSameRows_iff hcurrent hnext
  have hraw := compactFormulaTransformOutputRawPrefixRows_iff
    (consumedCount := consumedCount) hcurrent hnext
  constructor
  · rintro ⟨mappedHead, hcount, hzero | hpositive⟩
    · rcases hzero with ⟨hconsumed, hsameRows⟩
      have hout : next.2 = current.2 := hsame.mp hsameRows
      exact ⟨hcount, by
        simpa [compactFormulaTransformFormulaEmission, hconsumed] using hout⟩
    · rcases hpositive with ⟨hconsumed, hrawMode | hfvListMode | hmappedMode⟩
      · rcases hrawMode with ⟨hmode, hrows⟩
        have hout := (hraw.mp hrows).2
        rcases hmode with hmodeZero | hmodeOne | hmodeTwo | hmodeFive
        · exact ⟨hcount, by
            simpa [compactFormulaTransformFormulaEmission,
              show consumedCount ≠ 0 by omega, hmodeZero] using hout⟩
        · exact ⟨hcount, by
            simpa [compactFormulaTransformFormulaEmission,
              show consumedCount ≠ 0 by omega,
              show mode ≠ 0 by omega, hmodeOne] using hout⟩
        · exact ⟨hcount, by
            simpa [compactFormulaTransformFormulaEmission,
              show consumedCount ≠ 0 by omega,
              show mode ≠ 0 by omega, show mode ≠ 1 by omega,
              hmodeTwo] using hout⟩
        · exact ⟨hcount, by
            simpa [compactFormulaTransformFormulaEmission,
              show consumedCount ≠ 0 by omega,
              show mode ≠ 0 by omega, show mode ≠ 1 by omega,
              show mode ≠ 2 by omega, show mode ≠ 4 by omega,
              hmodeFive] using hout⟩
      · rcases hfvListMode with ⟨rfl, hrows⟩
        exact ⟨hcount, by
          simpa [compactFormulaTransformFormulaEmission,
            show consumedCount ≠ 0 by omega] using hsame.mp hrows⟩
      · rcases hmappedMode with
          ⟨hmodeZero, hmodeOne, hmodeTwo, hmodeFour, hmodeFive,
            htagGraph, hrows⟩
        have hmapped : mappedHead =
            FoundationCompactNumericFormulaNegation.compactNegationFormulaTag
              tag :=
          (compactNegationFormulaTagGraph_iff tag mappedHead).mp htagGraph
        have hout :=
          (compactFormulaTransformOutputMappedPrefixRows_iff
            hcurrent hnext).mp hrows
        exact ⟨hcount, by
          simpa [compactFormulaTransformFormulaEmission,
            show consumedCount ≠ 0 by omega,
            hmodeZero, hmodeOne, hmodeTwo, hmodeFour, hmodeFive,
            hmapped] using hout.2.2⟩
  · rintro ⟨hcount, hout⟩
    have hcurrentTokenCount :
        currentCoordinates.parserTokensCount = current.1.1.length := by
      simpa [CompactFormulaTransformStateRowCoordinates.parser] using
        hcurrent.parserLayout.tokensCount_eq
    have hconsumedLe : consumedCount ≤ current.1.1.length := by
      rw [← hcurrentTokenCount]
      omega
    by_cases hconsumed : consumedCount = 0
    · refine ⟨0, hcount, Or.inl ⟨hconsumed, hsame.mpr ?_⟩⟩
      simpa [compactFormulaTransformFormulaEmission, hconsumed] using hout
    · by_cases hmodeZero : mode = 0
      · refine ⟨0, hcount, Or.inr ⟨by omega,
          Or.inl ⟨Or.inl hmodeZero,
            hraw.mpr ⟨hconsumedLe, ?_⟩⟩⟩⟩
        simpa [compactFormulaTransformFormulaEmission,
          hconsumed, hmodeZero] using hout
      · by_cases hmodeOne : mode = 1
        · refine ⟨0, hcount, Or.inr ⟨by omega,
            Or.inl ⟨Or.inr (Or.inl hmodeOne),
              hraw.mpr ⟨hconsumedLe, ?_⟩⟩⟩⟩
          simpa [compactFormulaTransformFormulaEmission,
            hconsumed, hmodeZero, hmodeOne] using hout
        · by_cases hmodeTwo : mode = 2
          · refine ⟨0, hcount, Or.inr ⟨by omega,
              Or.inl ⟨Or.inr (Or.inr (Or.inl hmodeTwo)),
                hraw.mpr ⟨hconsumedLe, ?_⟩⟩⟩⟩
            simpa [compactFormulaTransformFormulaEmission,
              hconsumed, hmodeZero, hmodeOne, hmodeTwo] using hout
          · by_cases hmodeFour : mode = 4
            · refine ⟨0, hcount, Or.inr ⟨by omega,
                Or.inr (Or.inl ⟨hmodeFour, hsame.mpr ?_⟩)⟩⟩
              simpa [compactFormulaTransformFormulaEmission, hconsumed,
                hmodeZero, hmodeOne, hmodeTwo, hmodeFour] using hout
            · by_cases hmodeFive : mode = 5
              · refine ⟨0, hcount, Or.inr ⟨by omega,
                  Or.inl ⟨Or.inr (Or.inr (Or.inr hmodeFive)),
                    hraw.mpr ⟨hconsumedLe, ?_⟩⟩⟩⟩
                simpa [compactFormulaTransformFormulaEmission, hconsumed,
                  hmodeZero, hmodeOne, hmodeTwo, hmodeFour,
                  hmodeFive] using hout
              · let mappedHead :=
                  FoundationCompactNumericFormulaNegation.compactNegationFormulaTag
                    tag
                have htagGraph : CompactNegationFormulaTagGraph tag mappedHead :=
                  (compactNegationFormulaTagGraph_iff tag mappedHead).mpr rfl
                have hmappedOutput : next.2 = current.2 ++
                    (mappedHead ::
                      (current.1.1.take consumedCount).drop 1) := by
                  simpa [compactFormulaTransformFormulaEmission,
                    hconsumed, hmodeZero, hmodeOne, hmodeTwo,
                    hmodeFour, hmodeFive, mappedHead] using hout
                refine ⟨mappedHead, hcount, Or.inr ⟨by omega,
                  Or.inr (Or.inr ⟨hmodeZero, hmodeOne, hmodeTwo,
                    hmodeFour, hmodeFive, htagGraph, ?_⟩)⟩⟩
                exact (compactFormulaTransformOutputMappedPrefixRows_iff
                  hcurrent hnext).mpr
                    ⟨by omega, hconsumedLe, hmappedOutput⟩

theorem compactUnifiedParserSyntaxFormulaRows_consumption_cases
    {tokenTable width tokenCount binderArity : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current : CompactUnifiedParserState}
    {witness : CompactSyntaxFormulaTaskWitnessCoordinates}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hrows : CompactUnifiedParserSyntaxFormulaRows
      tokenTable width tokenCount currentCoordinates nextCoordinates
        binderArity witness) :
    nextCoordinates.tokensCount = currentCoordinates.tokensCount ∨
      (currentCoordinates.tokensCount = 1 + nextCoordinates.tokensCount ∧
        compactTokenAt 0 current.1 = witness.tag) ∨
      (currentCoordinates.tokensCount = 3 + nextCoordinates.tokensCount ∧
        compactTokenAt 0 current.1 = witness.tag) := by
  rcases hrows with ⟨_hcurrentRunning, _huncons, hshort | henough⟩
  · exact Or.inl hshort.2.2.1.1
  · rcases henough with ⟨_hlength, htagRows, hcontrol⟩
    have htag :=
      (compactAdditiveNatListAtRows_iff_getI
        hcurrent.tokensRows 0 witness.tag).mp (by
          simpa only [hcurrent.tokensCount_eq] using htagRows)
    have htagToken : compactTokenAt 0 current.1 = witness.tag :=
      (FoundationCompactNumericListedDirectParserSyntaxTermRows.compactTokenAt_eq_getI
        0 current.1).trans htag.2
    rcases hcontrol with
      hrelation | hatomic | hbinary | hquantifier | hinvalid
    · rcases hrelation with ⟨_htagClass, hshortRelation | henoughRelation⟩
      · exact Or.inl hshortRelation.2.2.1.1
      · rcases henoughRelation with
          ⟨_hlength, _harity, _hcode, hvalid | hinvalidCode⟩
        · exact Or.inr (Or.inr ⟨hvalid.2.2.1.2.1, htagToken⟩)
        · exact Or.inl hinvalidCode.2.2.1.1
    · exact Or.inr (Or.inl ⟨hatomic.2.2.1.2.1, htagToken⟩)
    · exact Or.inr (Or.inl ⟨hbinary.2.2.1.2.1, htagToken⟩)
    · exact Or.inr (Or.inl ⟨hquantifier.2.2.1.2.1, htagToken⟩)
    · rcases hinvalid with
        ⟨_hzero, _hone, _htwo, _hthree, _hfour, _hfive,
          _hsix, _hseven, hfailure⟩
      exact Or.inl hfailure.2.1.1

theorem compactNegateConsumedFormulaHeader_take_eq
    (count tag : Nat) (tokens : List Nat)
    (hpositive : 1 ≤ count) (hcount : count ≤ tokens.length)
    (htag : compactTokenAt 0 tokens = tag) :
    FoundationCompactNumericFormulaNegation.compactNegateConsumedFormulaHeader
        (tokens.take count) =
      FoundationCompactNumericFormulaNegation.compactNegationFormulaTag tag ::
        (tokens.take count).drop 1 := by
  cases tokens with
  | nil =>
      simp at hcount
      omega
  | cons head tail =>
      have hhead : head = tag := by
        simpa [compactTokenAt] using htag
      subst head
      cases count with
      | zero => omega
      | succ count =>
          simp [FoundationCompactNumericFormulaNegation.compactNegateConsumedFormulaHeader]

theorem compactFormulaTransformFormulaEmission_eq_transition
    {tokenTable width tokenCount mode binderArity consumedCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    {formulaWitness : CompactSyntaxFormulaTaskWitnessCoordinates}
    {witness : List Nat}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hformula : CompactUnifiedParserSyntaxFormulaRows
      tokenTable width tokenCount currentCoordinates.parser
        nextCoordinates.parser binderArity formulaWitness)
    (hcount : currentCoordinates.parserTokensCount =
      consumedCount + nextCoordinates.parserTokensCount) :
    compactFormulaTransformFormulaEmission
        mode formulaWitness.tag consumedCount current.1.1 =
      compactFormulaTransformTransitionEmission
        mode witness current.1 next.1 := by
  have hcase : CompactSyntaxParserFormulaTaskCase
      binderArity current.1 next.1 :=
    (compactUnifiedParserSyntaxFormulaRows_iff
      hcurrent.parserLayout hnext.parserLayout).mp
        ⟨formulaWitness, hformula⟩
  rcases hcase with ⟨_hstatus, tail, htasks, _hstep⟩
  have hfreeTask :
      FoundationCompactNumericFormulaFree.compactSyntaxCurrentTask current.1 =
        (1, binderArity, 0) := by
    simp [FoundationCompactNumericFormulaFree.compactSyntaxCurrentTask,
      htasks]
  have hshiftKind :
      FoundationCompactNumericFormulaShift.compactSyntaxCurrentTaskKind
          current.1 = 1 := by
    simp [FoundationCompactNumericFormulaShift.compactSyntaxCurrentTaskKind,
      htasks]
  have hsubstitutionTask :
      FoundationCompactNumericFormulaSubstitution.compactSyntaxCurrentTask
          current.1 = (1, binderArity, 0) := by
    simp [FoundationCompactNumericFormulaSubstitution.compactSyntaxCurrentTask,
      htasks]
  have hnegationKind :
      FoundationCompactNumericFormulaNegation.compactSyntaxCurrentTaskKind
          current.1 = 1 := by
    simp [FoundationCompactNumericFormulaNegation.compactSyntaxCurrentTaskKind,
      htasks]
  have hfvListKind :
      FoundationCompactNumericFormulaFvSup.compactSyntaxCurrentTaskKind
          current.1 = 1 := by
    simp [FoundationCompactNumericFormulaFvSup.compactSyntaxCurrentTaskKind,
      htasks]
  have hfixitrTask :
      FoundationCompactNumericFormulaFixitr.compactSyntaxCurrentTask current.1 =
        (1, binderArity, 0) := by
    simp [FoundationCompactNumericFormulaFixitr.compactSyntaxCurrentTask,
      htasks]
  have hcurrentTokenCount :
      currentCoordinates.parserTokensCount = current.1.1.length := by
    simpa [CompactFormulaTransformStateRowCoordinates.parser] using
      hcurrent.parserLayout.tokensCount_eq
  have hnextTokenCount :
      nextCoordinates.parserTokensCount = next.1.1.length := by
    simpa [CompactFormulaTransformStateRowCoordinates.parser] using
      hnext.parserLayout.tokensCount_eq
  have hprefix : consumedTokenPrefix current.1.1 next.1.1 =
      current.1.1.take consumedCount := by
    unfold consumedTokenPrefix
    congr 1
    rw [← hcurrentTokenCount, ← hnextTokenCount]
    omega
  have hconsumptionRaw :=
    compactUnifiedParserSyntaxFormulaRows_consumption_cases
      hcurrent.parserLayout hformula
  have hconsumption :
      nextCoordinates.parserTokensCount =
          currentCoordinates.parserTokensCount ∨
        (currentCoordinates.parserTokensCount =
            1 + nextCoordinates.parserTokensCount ∧
          compactTokenAt 0 current.1.1 = formulaWitness.tag) ∨
        (currentCoordinates.parserTokensCount =
            3 + nextCoordinates.parserTokensCount ∧
          compactTokenAt 0 current.1.1 = formulaWitness.tag) := by
    simpa [CompactFormulaTransformStateRowCoordinates.parser] using
      hconsumptionRaw
  rcases hconsumption with hsame | hone | hthree
  · have hconsumed : consumedCount = 0 := by omega
    subst consumedCount
    simp [compactFormulaTransformFormulaEmission,
      compactFormulaTransformTransitionEmission, hprefix,
      hfreeTask, hshiftKind, hsubstitutionTask, hnegationKind,
      hfvListKind, hfixitrTask,
      FoundationCompactNumericFormulaFree.compactFormulaFreeEmission,
      FoundationCompactNumericFormulaShift.compactFormulaShiftEmission,
      FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionEmission,
      FoundationCompactNumericFormulaNegation.compactFormulaNegationEmission,
      FoundationCompactNumericFormulaFvSup.compactFormulaFvListEmission,
      FoundationCompactNumericFormulaFixitr.compactFormulaFixitrEmission,
      FoundationCompactNumericFormulaNegation.compactNegateConsumedFormulaHeader]
  · rcases hone with ⟨honeCount, htag⟩
    have hconsumed : consumedCount = 1 := by omega
    subst consumedCount
    have hsourceLength : 1 ≤ current.1.1.length := by
      rw [← hcurrentTokenCount]
      omega
    have hnegate := compactNegateConsumedFormulaHeader_take_eq
      1 formulaWitness.tag current.1.1 (by omega) hsourceLength htag
    by_cases hmodeZero : mode = 0
    · simp [compactFormulaTransformFormulaEmission,
        compactFormulaTransformTransitionEmission, hmodeZero, hprefix,
        hfreeTask,
        FoundationCompactNumericFormulaFree.compactFormulaFreeEmission]
    · by_cases hmodeOne : mode = 1
      · simp [compactFormulaTransformFormulaEmission,
          compactFormulaTransformTransitionEmission, hmodeOne, hprefix,
          hshiftKind,
          FoundationCompactNumericFormulaShift.compactFormulaShiftEmission]
      · by_cases hmodeTwo : mode = 2
        · simp [compactFormulaTransformFormulaEmission,
            compactFormulaTransformTransitionEmission, hmodeTwo, hprefix,
            hsubstitutionTask,
            FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionEmission]
        · by_cases hmodeFour : mode = 4
          · simp [compactFormulaTransformFormulaEmission,
              compactFormulaTransformTransitionEmission,
              hmodeFour, hprefix, hfvListKind,
              FoundationCompactNumericFormulaFvSup.compactFormulaFvListEmission]
          · by_cases hmodeFive : mode = 5
            · simp [compactFormulaTransformFormulaEmission,
                compactFormulaTransformTransitionEmission,
                hmodeFive, hprefix, hfixitrTask,
                FoundationCompactNumericFormulaFixitr.compactFormulaFixitrEmission]
            · simp [compactFormulaTransformFormulaEmission,
                compactFormulaTransformTransitionEmission,
                hmodeZero, hmodeOne, hmodeTwo, hmodeFour, hmodeFive,
                hprefix, hnegationKind,
                FoundationCompactNumericFormulaNegation.compactFormulaNegationEmission,
                hnegate]
  · rcases hthree with ⟨hthreeCount, htag⟩
    have hconsumed : consumedCount = 3 := by omega
    subst consumedCount
    have hsourceLength : 3 ≤ current.1.1.length := by
      rw [← hcurrentTokenCount]
      omega
    have hnegate := compactNegateConsumedFormulaHeader_take_eq
      3 formulaWitness.tag current.1.1 (by omega) (by omega) htag
    by_cases hmodeZero : mode = 0
    · simp [compactFormulaTransformFormulaEmission,
        compactFormulaTransformTransitionEmission, hmodeZero, hprefix,
        hfreeTask,
        FoundationCompactNumericFormulaFree.compactFormulaFreeEmission]
    · by_cases hmodeOne : mode = 1
      · simp [compactFormulaTransformFormulaEmission,
          compactFormulaTransformTransitionEmission, hmodeOne, hprefix,
          hshiftKind,
          FoundationCompactNumericFormulaShift.compactFormulaShiftEmission]
      · by_cases hmodeTwo : mode = 2
        · simp [compactFormulaTransformFormulaEmission,
            compactFormulaTransformTransitionEmission, hmodeTwo, hprefix,
            hsubstitutionTask,
            FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionEmission]
        · by_cases hmodeFour : mode = 4
          · simp [compactFormulaTransformFormulaEmission,
              compactFormulaTransformTransitionEmission,
              hmodeFour, hprefix, hfvListKind,
              FoundationCompactNumericFormulaFvSup.compactFormulaFvListEmission]
          · by_cases hmodeFive : mode = 5
            · simp [compactFormulaTransformFormulaEmission,
                compactFormulaTransformTransitionEmission,
                hmodeFive, hprefix, hfixitrTask,
                FoundationCompactNumericFormulaFixitr.compactFormulaFixitrEmission]
            · simp [compactFormulaTransformFormulaEmission,
                compactFormulaTransformTransitionEmission,
                hmodeZero, hmodeOne, hmodeTwo, hmodeFour, hmodeFive,
                hprefix, hnegationKind,
                FoundationCompactNumericFormulaNegation.compactFormulaNegationEmission,
                hnegate]

theorem compactUnifiedParserSyntaxFormulaRows_parserStep
    {tokenTable width tokenCount binderArity : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    {formulaWitness : CompactSyntaxFormulaTaskWitnessCoordinates}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hformula : CompactUnifiedParserSyntaxFormulaRows
      tokenTable width tokenCount currentCoordinates nextCoordinates
        binderArity formulaWitness) :
    next = compactSyntaxParserStep current := by
  have hcase : CompactSyntaxParserFormulaTaskCase binderArity current next :=
    (compactUnifiedParserSyntaxFormulaRows_iff hcurrent hnext).mp
      ⟨formulaWitness, hformula⟩
  rcases hcase with ⟨hstatus, tail, htasks, hformulaStep⟩
  rcases current with ⟨tokens, tasks, status⟩
  simp only at hstatus htasks hformulaStep ⊢
  subst status
  subst tasks
  simpa [compactSyntaxParserStep, compactSyntaxRunningStep,
    compactSyntaxTaskTokenStep] using hformulaStep

theorem exists_compactFormulaTransformFormulaOutputRows_iff_step
    {tokenTable width tokenCount mode binderArity : Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    {formulaWitness : CompactSyntaxFormulaTaskWitnessCoordinates}
    {witness : List Nat}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hformula : CompactUnifiedParserSyntaxFormulaRows
      tokenTable width tokenCount currentCoordinates.parser
        nextCoordinates.parser binderArity formulaWitness) :
    (∃ consumedCount mappedHead,
        CompactFormulaTransformFormulaOutputRows
          tokenTable width tokenCount currentCoordinates nextCoordinates
            mode formulaWitness.tag consumedCount mappedHead) ↔
      next = compactFormulaTransformStep (mode, witness) current := by
  have hparser : next.1 = compactSyntaxParserStep current.1 :=
    compactUnifiedParserSyntaxFormulaRows_parserStep
      hcurrent.parserLayout hnext.parserLayout hformula
  have hstepTransition := compactFormulaTransformStep_eq_transition
    mode witness current next.1 hparser.symm
  constructor
  · rintro ⟨consumedCount, mappedHead, hrows⟩
    have hsemantic :=
      (exists_mapped_compactFormulaTransformFormulaOutputRows_iff
        hcurrent hnext).mp ⟨mappedHead, hrows⟩
    have hemitted := compactFormulaTransformFormulaEmission_eq_transition
      (mode := mode) (witness := witness)
      hcurrent hnext hformula hsemantic.1
    have houtput : next.2 = current.2 ++
        compactFormulaTransformTransitionEmission
          mode witness current.1 next.1 := by
      rw [← hemitted]
      exact hsemantic.2
    calc
      next = (next.1, next.2) := rfl
      _ = (next.1, current.2 ++
          compactFormulaTransformTransitionEmission
            mode witness current.1 next.1) := by rw [houtput]
      _ = compactFormulaTransformStep (mode, witness) current :=
        hstepTransition.symm
  · intro hstep
    have hconsumptionRaw :=
      compactUnifiedParserSyntaxFormulaRows_consumption_cases
        hcurrent.parserLayout hformula
    have hconsumption :
        nextCoordinates.parserTokensCount ≤
          currentCoordinates.parserTokensCount := by
      rcases hconsumptionRaw with hsame | hone | hthree
      · simpa [CompactFormulaTransformStateRowCoordinates.parser] using
          Nat.le_of_eq hsame
      · simp [CompactFormulaTransformStateRowCoordinates.parser] at hone
        omega
      · simp [CompactFormulaTransformStateRowCoordinates.parser] at hthree
        omega
    let consumedCount := currentCoordinates.parserTokensCount -
      nextCoordinates.parserTokensCount
    have hcount : currentCoordinates.parserTokensCount =
        consumedCount + nextCoordinates.parserTokensCount := by
      dsimp only [consumedCount]
      omega
    have hnextPair : next =
        (next.1, current.2 ++
          compactFormulaTransformTransitionEmission
            mode witness current.1 next.1) :=
      hstep.trans hstepTransition
    have houtput : next.2 = current.2 ++
        compactFormulaTransformTransitionEmission
          mode witness current.1 next.1 :=
      congrArg Prod.snd hnextPair
    have hemitted := compactFormulaTransformFormulaEmission_eq_transition
      (mode := mode) (witness := witness)
      hcurrent hnext hformula hcount
    have hsemantic : currentCoordinates.parserTokensCount =
          consumedCount + nextCoordinates.parserTokensCount ∧
        next.2 = current.2 ++
          compactFormulaTransformFormulaEmission
            mode formulaWitness.tag consumedCount current.1.1 := by
      refine ⟨hcount, ?_⟩
      rw [hemitted]
      exact houtput
    rcases (exists_mapped_compactFormulaTransformFormulaOutputRows_iff
      hcurrent hnext).mpr hsemantic with ⟨mappedHead, hrows⟩
    exact ⟨consumedCount, mappedHead, hrows⟩

theorem exists_compactFormulaTransformFormulaOutputFormula_iff_step
    {tokenTable width tokenCount mode binderArity : Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    {formulaWitness : CompactSyntaxFormulaTaskWitnessCoordinates}
    {witness : List Nat}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hformula : CompactUnifiedParserSyntaxFormulaRows
      tokenTable width tokenCount currentCoordinates.parser
        nextCoordinates.parser binderArity formulaWitness) :
    (∃ consumedCount mappedHead,
        compactFormulaTransformFormulaOutputRowsDef.val.Evalb
          (compactFormulaTransformFormulaOutputRowsEnvironment
            tokenTable width tokenCount currentCoordinates nextCoordinates
              mode formulaWitness.tag consumedCount mappedHead)) ↔
      next = compactFormulaTransformStep (mode, witness) current := by
  simpa only [compactFormulaTransformFormulaOutputRowsDef_spec] using
    exists_compactFormulaTransformFormulaOutputRows_iff_step
      (witness := witness) hcurrent hnext hformula

#print axioms compactFormulaTransformFormulaOutputRowsDef_spec
#print axioms compactFormulaTransformFormulaOutputRowsDef_sigmaZero
#print axioms exists_mapped_compactFormulaTransformFormulaOutputRows_iff
#print axioms compactUnifiedParserSyntaxFormulaRows_consumption_cases
#print axioms compactNegateConsumedFormulaHeader_take_eq
#print axioms compactFormulaTransformFormulaEmission_eq_transition
#print axioms compactUnifiedParserSyntaxFormulaRows_parserStep
#print axioms exists_compactFormulaTransformFormulaOutputRows_iff_step
#print axioms exists_compactFormulaTransformFormulaOutputFormula_iff_step

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows
