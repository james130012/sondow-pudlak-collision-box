import integration.FoundationCompactNumericListedDirectAllShiftCombineRuleRows
import integration.FoundationCompactNumericListedDirectFormulaShiftExactListRowsCompleteness
import integration.FoundationCompactNumericListedDirectAllShiftRuleCheckCompleteness
import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactCompleteness

/-!
# Converse constructors for universal and shift combine rows

The constructors use canonical single-formula and list-level traces, real
child-result heads, and the semantic target stack.  The success-bit table and
all finite witness bounds are constructed internally.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAllShiftCombineRuleRowsCompleteness

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectChildResultBoundedHeadEquality
open FoundationCompactNumericListedDirectChildResultListPushDropRows
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
open FoundationCompactNumericListedDirectFormulaTransformTotalExactCompleteness
open FoundationCompactNumericListedDirectFormulaShiftExactListRows
open FoundationCompactNumericListedDirectFormulaShiftExactListRowsCompleteness
open FoundationCompactNumericListedDirectAllShiftRuleCheck
open FoundationCompactNumericListedDirectAllShiftRuleCheckCompleteness
open FoundationCompactNumericListedDirectAllShiftCombineRuleRows

def compactFormulaShiftSuccessValues
    (formulas : List (List Nat)) : List Nat :=
  formulas.map fun formula =>
    compactAdditiveBoolTag (compactFormulaShiftExact 0 formula).isSome

def compactFormulaShiftSuccessTable
    (tokenCount : Nat) (formulas : List (List Nat)) : Nat :=
  compactFixedWidthTableCode tokenCount
    (compactFormulaShiftSuccessValues formulas)

theorem compactFormulaShiftSuccessTable_entry
    {tokenCount : Nat} (formulas : List (List Nat))
    (htokenCount : 1 ≤ tokenCount)
    (index : Nat) (hindex : index < formulas.length) :
    CompactFixedWidthEntry
      (compactFormulaShiftSuccessTable tokenCount formulas)
      tokenCount index
      (compactAdditiveBoolTag
        (compactFormulaShiftExact 0 (formulas.getI index)).isSome) := by
  have hvalues : ∀ value ∈ compactFormulaShiftSuccessValues formulas,
      Nat.size value ≤ tokenCount := by
    intro value hvalue
    rcases List.mem_map.mp hvalue with ⟨formula, _hformula, rfl⟩
    cases (compactFormulaShiftExact 0 formula).isSome
    · simp [compactAdditiveBoolTag]
    · simpa [compactAdditiveBoolTag] using htokenCount
  have hentry := compactFixedWidthTableCode_entry tokenCount
    (compactFormulaShiftSuccessValues formulas) index
    (by simpa [compactFormulaShiftSuccessValues] using hindex) hvalues
  have hget :
      (compactFormulaShiftSuccessValues formulas).getI index =
        compactAdditiveBoolTag
          (compactFormulaShiftExact 0 (formulas.getI index)).isSome := by
    rw [List.getI_eq_getElem _
      (by simpa [compactFormulaShiftSuccessValues] using hindex)]
    rw [List.getI_eq_getElem formulas hindex]
    simp [compactFormulaShiftSuccessValues]
  simpa only [compactFormulaShiftSuccessTable, hget] using hentry

theorem CompactNumericAllShiftCombineRuleRows.exists_of_all
    {tokenTable width tokenCount taskTag gammaFinish gammaBoundary firstFinish
      premiseGammaBoundary premiseBoolValue sourceBoundary targetBoundary
      freedStart freedFinish freeStateBoundary
      shiftCandidateBoundary shiftedBoundary emptyStart emptyFinish
      tableWidth valueBound : Nat}
    {Gamma premise : List (List Nat)} {formula : List Nat}
    {premiseValid : Bool} {source target : List CompactNumericChildResult}
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hformula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount gammaFinish firstFinish formula)
    (hfreed : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount freedStart freedFinish
        ((compactFormulaFreeExact formula).getD []))
    (hempty : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount emptyStart emptyFinish [])
    (hfreeTrace : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount freeStateBoundary
        (compactFormulaTransformStateTrace (0, [])
          (compactSyntaxRunFuelBound formula)
          (compactFormulaTransformInitialState 1 formula)))
    (hcandidate : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        shiftCandidateBoundary
        (Gamma.map fun candidateFormula =>
          (compactFormulaShiftExact 0 candidateFormula).getD []))
    (hshifted : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        shiftedBoundary ((compactFormulaShiftExactList Gamma).getD []))
    (hshiftTraces : ∀ index (_hindex : index < Gamma.length),
      ∃ stateBoundary,
        CompactFormulaTransformStateListRowLayouts
          tokenTable width tokenCount stateBoundary
          (compactFormulaTransformStateTrace (1, [])
            (compactSyntaxRunFuelBound (Gamma.getI index))
            (compactFormulaTransformInitialState 0 (Gamma.getI index))))
    (hpremise : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        premiseGammaBoundary premise)
    (hpremiseBool : premiseBoolValue =
      compactAdditiveBoolTag premiseValid)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound)
    (htokenCount : 1 ≤ tokenCount)
    (htag : taskTag = 5)
    (hsourceCount : 1 ≤ source.length)
    (hpremiseValue : source.getI 0 = (premise, premiseValid))
    (htarget : target =
      (Gamma, compactAllRuleCheck
        (Gamma, (formula, (premise, premiseValid)))) :: source.drop 1) :
    ∃ formulaBoundary formulaBoundarySize
        freedBoundary freedBoundarySize emptyBoundary emptyBoundarySize
        shiftWitnessBound freeTableWidth,
      CompactNumericAllShiftCombineRuleRows
        tokenTable width tokenCount
        taskTag gammaFinish Gamma.length gammaBoundary
        firstFinish formula.length
        premise.length premiseGammaBoundary premiseBoolValue
        sourceBoundary source.length targetBoundary target.length
        formulaBoundary formulaBoundarySize
        freedStart freedFinish freedBoundary
          ((compactFormulaFreeExact formula).getD []).length
          freedBoundarySize
        freeStateBoundary (compactSyntaxRunFuelBound formula + 1)
        shiftCandidateBoundary
          (compactFormulaShiftSuccessTable tokenCount Gamma)
        shiftedBoundary ((compactFormulaShiftExactList Gamma).getD []).length
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        shiftWitnessBound freeTableWidth (2 ^ freeTableWidth)
        tableWidth valueBound
        (compactAdditiveBoolTag
          (compactAllRuleCheck
            (Gamma, (formula, (premise, premiseValid))))) := by
  rcases hformula with
    ⟨formulaBoundary, hformulaStructure, hformulaRows, hformulaSize⟩
  rcases hfreed with
    ⟨freedBoundary, hfreedStructure, hfreedRows, hfreedSize⟩
  rcases hempty with
    ⟨emptyBoundary, hemptyStructure, hemptyRows, hemptySize⟩
  have hformulaLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount gammaFinish firstFinish formula :=
    ⟨formulaBoundary, hformulaStructure, hformulaRows, hformulaSize⟩
  have hfreedLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount freedStart freedFinish
        ((compactFormulaFreeExact formula).getD []) :=
    ⟨freedBoundary, hfreedStructure, hfreedRows, hfreedSize⟩
  have hemptyLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount emptyStart emptyFinish [] :=
    ⟨emptyBoundary, hemptyStructure, hemptyRows, hemptySize⟩
  have hformulaWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount gammaFinish formula.length firstFinish
        formulaBoundary (Nat.size formulaBoundary) :=
    ⟨hformulaStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hformulaRows,
      rfl, hformulaSize⟩
  have hfreedWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount freedStart
        ((compactFormulaFreeExact formula).getD []).length freedFinish
        freedBoundary (Nat.size freedBoundary) :=
    ⟨hfreedStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hfreedRows,
      rfl, hfreedSize⟩
  have hemptyWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount emptyStart 0 emptyFinish
        emptyBoundary (Nat.size emptyBoundary) :=
    ⟨hemptyStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hemptyRows,
      rfl, hemptySize⟩
  rcases CompactFormulaTransformTotalExactBoundedGraph.of_canonical_trace
      hfreeTrace hemptyLayout rfl hformulaRows hfreedRows hemptyRows
      (by simp [compactFormulaFreeExact]) with
    ⟨freeTableWidth, hfreeTransform⟩
  have hsuccess : ∀ index (hindex : index < Gamma.length),
      CompactFixedWidthEntry
        (compactFormulaShiftSuccessTable tokenCount Gamma)
        tokenCount index
        (compactAdditiveBoolTag
          (compactFormulaShiftExact 0 (Gamma.getI index)).isSome) :=
    fun index hindex =>
      compactFormulaShiftSuccessTable_entry Gamma htokenCount index hindex
  rcases CompactFormulaShiftExactListRows.of_canonical_rows
      hGamma hcandidate hshifted hemptyWitness hsuccess hshiftTraces with
    ⟨shiftWitnessBound, hshiftTransform⟩
  let result := compactAllRuleCheck
    (Gamma, (formula, (premise, premiseValid)))
  have hcheck : CompactAdditiveAllRuleCheck
      tokenTable width tokenCount
      gammaBoundary Gamma.length
      gammaFinish firstFinish formulaBoundary formula.length
      premiseGammaBoundary premise.length premiseBoolValue
      freedStart freedFinish freedBoundary
        ((compactFormulaFreeExact formula).getD []).length
      freeStateBoundary (compactSyntaxRunFuelBound formula + 1)
      shiftCandidateBoundary
        (compactFormulaShiftSuccessTable tokenCount Gamma)
      shiftedBoundary ((compactFormulaShiftExactList Gamma).getD []).length
      emptyStart emptyFinish emptyBoundary (Nat.size emptyBoundary)
      shiftWitnessBound freeTableWidth (2 ^ freeTableWidth)
      (compactAdditiveBoolTag result) :=
    CompactAdditiveAllRuleCheck.of_semantics
      hfreeTransform hshiftTransform hGamma hformulaLayout hpremise
      hfreedLayout hshifted hpremiseBool
  have hpush : CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount
      sourceBoundary source.length targetBoundary target.length
      gammaBoundary Gamma.length tableWidth valueBound 1
      (compactAdditiveBoolTag result) :=
    CompactAdditiveStructuredListElementRowLayouts.childResultPushDropRows
      hsourceRows htargetRows hGamma hsourceGraph htargetGraph
      hsourceCount (by simpa [result] using htarget)
  have hpremiseHeadCanonical :=
    CompactNumericChildResultBoundedHeadEq.of_value_eq
      hsourceGraph (by omega) hpremise hsourceRows hpremiseValue
  have hpremiseHead : CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount sourceBoundary
      premiseGammaBoundary premise.length valueBound 0 premiseBoolValue := by
    simpa only [hpremiseBool] using hpremiseHeadCanonical
  refine ⟨formulaBoundary, Nat.size formulaBoundary,
    freedBoundary, Nat.size freedBoundary,
    emptyBoundary, Nat.size emptyBoundary,
    shiftWitnessBound, freeTableWidth, ?_⟩
  left
  exact ⟨htag, hsourceCount, hformulaWitness, hfreedWitness,
    CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
      hpremise,
    hpremiseHead, hcheck, hpush⟩

theorem CompactNumericAllShiftCombineRuleRows.exists_of_shift
    {tokenTable width tokenCount taskTag gammaFinish firstFinish
      gammaBoundary premiseGammaBoundary premiseBoolValue
      sourceBoundary targetBoundary shiftCandidateBoundary shiftedBoundary
      emptyStart emptyFinish tableWidth valueBound : Nat}
    {Gamma premise : List (List Nat)} {premiseValid : Bool}
    {source target : List CompactNumericChildResult}
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hempty : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount emptyStart emptyFinish [])
    (hcandidate : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        shiftCandidateBoundary
        (premise.map fun candidateFormula =>
          (compactFormulaShiftExact 0 candidateFormula).getD []))
    (hshifted : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        shiftedBoundary ((compactFormulaShiftExactList premise).getD []))
    (hshiftTraces : ∀ index (_hindex : index < premise.length),
      ∃ stateBoundary,
        CompactFormulaTransformStateListRowLayouts
          tokenTable width tokenCount stateBoundary
          (compactFormulaTransformStateTrace (1, [])
            (compactSyntaxRunFuelBound (premise.getI index))
            (compactFormulaTransformInitialState 0 (premise.getI index))))
    (hpremise : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        premiseGammaBoundary premise)
    (hpremiseBool : premiseBoolValue =
      compactAdditiveBoolTag premiseValid)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound)
    (htokenCount : 1 ≤ tokenCount)
    (htag : taskTag = 8)
    (hsourceCount : 1 ≤ source.length)
    (hpremiseValue : source.getI 0 = (premise, premiseValid))
    (htarget : target =
      (Gamma, compactShiftRuleCheck
        (Gamma, (premise, premiseValid))) :: source.drop 1) :
    ∃ emptyBoundary emptyBoundarySize shiftWitnessBound,
      CompactNumericAllShiftCombineRuleRows
        tokenTable width tokenCount
        taskTag gammaFinish Gamma.length gammaBoundary
        firstFinish 0
        premise.length premiseGammaBoundary premiseBoolValue
        sourceBoundary source.length targetBoundary target.length
        0 0 0 0 0 0 0 0 0
        shiftCandidateBoundary
          (compactFormulaShiftSuccessTable tokenCount premise)
        shiftedBoundary
          ((compactFormulaShiftExactList premise).getD []).length
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        shiftWitnessBound 0 0 tableWidth valueBound
        (compactAdditiveBoolTag
          (compactShiftRuleCheck (Gamma, (premise, premiseValid)))) := by
  rcases hempty with
    ⟨emptyBoundary, hemptyStructure, hemptyRows, hemptySize⟩
  have hemptyWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount emptyStart 0 emptyFinish
        emptyBoundary (Nat.size emptyBoundary) :=
    ⟨hemptyStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hemptyRows,
      rfl, hemptySize⟩
  have hsuccess : ∀ index (hindex : index < premise.length),
      CompactFixedWidthEntry
        (compactFormulaShiftSuccessTable tokenCount premise)
        tokenCount index
        (compactAdditiveBoolTag
          (compactFormulaShiftExact 0 (premise.getI index)).isSome) :=
    fun index hindex =>
      compactFormulaShiftSuccessTable_entry premise htokenCount index hindex
  rcases CompactFormulaShiftExactListRows.of_canonical_rows
      hpremise hcandidate hshifted hemptyWitness hsuccess hshiftTraces with
    ⟨shiftWitnessBound, hshiftTransform⟩
  let result := compactShiftRuleCheck (Gamma, (premise, premiseValid))
  have hcheck : CompactAdditiveShiftRuleCheck
      tokenTable width tokenCount
      gammaBoundary Gamma.length
      premiseGammaBoundary premise.length premiseBoolValue
      shiftCandidateBoundary
        (compactFormulaShiftSuccessTable tokenCount premise)
      shiftedBoundary ((compactFormulaShiftExactList premise).getD []).length
      emptyStart emptyFinish emptyBoundary (Nat.size emptyBoundary)
      shiftWitnessBound (compactAdditiveBoolTag result) :=
    CompactAdditiveShiftRuleCheck.of_semantics
      hshiftTransform hGamma hshifted hpremiseBool
  have hpush : CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount
      sourceBoundary source.length targetBoundary target.length
      gammaBoundary Gamma.length tableWidth valueBound 1
      (compactAdditiveBoolTag result) :=
    CompactAdditiveStructuredListElementRowLayouts.childResultPushDropRows
      hsourceRows htargetRows hGamma hsourceGraph htargetGraph
      hsourceCount (by simpa [result] using htarget)
  have hpremiseHeadCanonical :=
    CompactNumericChildResultBoundedHeadEq.of_value_eq
      hsourceGraph (by omega) hpremise hsourceRows hpremiseValue
  have hpremiseHead : CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount sourceBoundary
      premiseGammaBoundary premise.length valueBound 0 premiseBoolValue := by
    simpa only [hpremiseBool] using hpremiseHeadCanonical
  refine ⟨emptyBoundary, Nat.size emptyBoundary, shiftWitnessBound, ?_⟩
  right
  exact ⟨htag, hsourceCount,
    CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
      hpremise,
    hpremiseHead, hcheck, hpush⟩

#print axioms compactFormulaShiftSuccessTable_entry
#print axioms CompactNumericAllShiftCombineRuleRows.exists_of_all
#print axioms CompactNumericAllShiftCombineRuleRows.exists_of_shift

end FoundationCompactNumericListedDirectAllShiftCombineRuleRowsCompleteness
