import integration.FoundationCompactNumericListedDirectExsCutCombineRuleRows
import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactCompleteness

/-!
# Converse constructors for existential and cut combine rows

The constructors start from typed direct layouts and the canonical executable
formula-transform trace.  They construct the bounded transform graph and all
flat-list witnesses; no transform-graph existence premise is accepted.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectExsCutCombineRuleRowsCompleteness

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectNatListListRowsRealization
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectChildResultBoundedHeadEquality
open FoundationCompactNumericListedDirectChildResultListPushDropRows
open FoundationCompactNumericListedDirectExsRuleCheck
open FoundationCompactNumericListedDirectCutRuleCheck
open FoundationCompactNumericListedDirectExsCutCombineRuleRows
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
open FoundationCompactNumericListedDirectFormulaTransformTotalExactCompleteness

theorem CompactNumericExsCutCombineRuleRows.exists_of_exs
    {tokenTable width tokenCount taskTag gammaFinish gammaBoundary firstFinish
      secondFinish witnessFinish rightGammaBoundary rightBoolValue
      sourceBoundary targetBoundary transformedStart transformedFinish
      transformStateBoundary emptyStart emptyFinish tableWidth valueBound : Nat}
    {Gamma : List (List Nat)} {formula witness : List Nat}
    {rightConclusion : List (List Nat)} {rightValid : Bool}
    {source target : List CompactNumericChildResult}
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hformula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount gammaFinish firstFinish formula)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount secondFinish witnessFinish witness)
    (htransformed : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount transformedStart transformedFinish
        ((compactFormulaSubstitutionExact 1 (witness, formula)).getD []))
    (hempty : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount emptyStart emptyFinish [])
    (htraceRows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount transformStateBoundary
        (compactFormulaTransformStateTrace (2, witness)
          (compactSyntaxRunFuelBound formula)
          (compactFormulaTransformInitialState 1 formula)))
    (hright : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        rightGammaBoundary rightConclusion)
    (hrightBool : rightBoolValue = compactAdditiveBoolTag rightValid)
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
    (htag : taskTag = 6)
    (hsourceCount : 1 ≤ source.length)
    (hrightValue : source.getI 0 = (rightConclusion, rightValid))
    (htarget : target =
      (Gamma, compactExsRuleCheck
        (Gamma, (formula, (witness, (rightConclusion, rightValid))))) ::
        source.drop 1) :
    ∃ formulaBoundary formulaBoundarySize
        transformedBoundary transformedBoundarySize
        emptyBoundary emptyBoundarySize transformTableWidth,
      CompactNumericExsCutCombineRuleRows
        tokenTable width tokenCount
        taskTag gammaFinish Gamma.length gammaBoundary
        firstFinish formula.length secondFinish witnessFinish witness.length
        rightConclusion.length rightGammaBoundary rightBoolValue
        0 0 0
        sourceBoundary source.length targetBoundary target.length
        formulaBoundary formulaBoundarySize
        transformedStart transformedFinish transformedBoundary
          ((compactFormulaSubstitutionExact 1
            (witness, formula)).getD []).length transformedBoundarySize
        transformStateBoundary (compactSyntaxRunFuelBound formula + 1)
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        transformTableWidth (2 ^ transformTableWidth)
        tableWidth valueBound
        (compactAdditiveBoolTag
          (compactExsRuleCheck
            (Gamma, (formula,
              (witness, (rightConclusion, rightValid)))))) := by
  rcases hformula with
    ⟨formulaBoundary, hformulaStructure, hformulaRows, hformulaSize⟩
  rcases htransformed with
    ⟨transformedBoundary, htransformedStructure,
      htransformedRows, htransformedSize⟩
  rcases hempty with
    ⟨emptyBoundary, hemptyStructure, hemptyRows, hemptySize⟩
  have hformulaLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount gammaFinish firstFinish formula :=
    ⟨formulaBoundary, hformulaStructure, hformulaRows, hformulaSize⟩
  have htransformedLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount transformedStart transformedFinish
        ((compactFormulaSubstitutionExact 1
          (witness, formula)).getD []) :=
    ⟨transformedBoundary, htransformedStructure,
      htransformedRows, htransformedSize⟩
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
  have htransformedWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount transformedStart
        ((compactFormulaSubstitutionExact 1
          (witness, formula)).getD []).length transformedFinish
        transformedBoundary (Nat.size transformedBoundary) :=
    ⟨htransformedStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        htransformedRows,
      rfl, htransformedSize⟩
  have hemptyWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount emptyStart 0 emptyFinish
        emptyBoundary (Nat.size emptyBoundary) :=
    ⟨hemptyStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hemptyRows,
      rfl, hemptySize⟩
  rcases CompactFormulaTransformTotalExactBoundedGraph.of_canonical_trace
      htraceRows hwitness rfl hformulaRows htransformedRows hemptyRows
      (by simp [compactFormulaSubstitutionExact]) with
    ⟨transformTableWidth, htransform⟩
  let result := compactExsRuleCheck
    (Gamma, (formula, (witness, (rightConclusion, rightValid))))
  have hcheck : CompactAdditiveExsRuleCheck
      tokenTable width tokenCount
      gammaBoundary Gamma.length
      gammaFinish firstFinish formulaBoundary formula.length
      secondFinish witnessFinish witness.length
      rightGammaBoundary rightConclusion.length rightBoolValue
      transformedStart transformedFinish transformedBoundary
        ((compactFormulaSubstitutionExact 1
          (witness, formula)).getD []).length
      transformStateBoundary (compactSyntaxRunFuelBound formula + 1)
      emptyBoundary transformTableWidth (2 ^ transformTableWidth)
      (compactAdditiveBoolTag result) :=
    (compactAdditiveExsRuleCheck_iff
      htransform hGamma hformulaLayout hformulaRows hwitness
      hright htransformedLayout htransformedRows hemptyRows
      hrightBool).mpr rfl
  have hpush : CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount
      sourceBoundary source.length targetBoundary target.length
      gammaBoundary Gamma.length tableWidth valueBound 1
      (compactAdditiveBoolTag result) :=
    CompactAdditiveStructuredListElementRowLayouts.childResultPushDropRows
      hsourceRows htargetRows hGamma hsourceGraph htargetGraph
      hsourceCount (by simpa [result] using htarget)
  have hrightHeadCanonical :=
    CompactNumericChildResultBoundedHeadEq.of_value_eq
      hsourceGraph (by omega) hright hsourceRows hrightValue
  have hrightHead : CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount sourceBoundary
      rightGammaBoundary rightConclusion.length valueBound 0
      rightBoolValue := by
    simpa only [hrightBool] using hrightHeadCanonical
  refine ⟨formulaBoundary, Nat.size formulaBoundary,
    transformedBoundary, Nat.size transformedBoundary,
    emptyBoundary, Nat.size emptyBoundary, transformTableWidth,
    hformulaWitness, htransformedWitness, hemptyWitness, ?_⟩
  left
  exact ⟨htag, hsourceCount,
    CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
      hright,
    hrightHead, hcheck, hpush⟩

#print axioms CompactNumericExsCutCombineRuleRows.exists_of_exs

theorem CompactNumericExsCutCombineRuleRows.exists_of_cut
    {tokenTable width tokenCount taskTag gammaFinish gammaBoundary firstFinish
      secondFinish witnessFinish rightGammaBoundary rightBoolValue
      leftGammaBoundary leftBoolValue sourceBoundary targetBoundary
      transformedStart transformedFinish transformStateBoundary
      emptyStart emptyFinish tableWidth valueBound : Nat}
    {Gamma : List (List Nat)} {formula witness : List Nat}
    {rightConclusion leftConclusion : List (List Nat)}
    {rightValid leftValid : Bool}
    {source target : List CompactNumericChildResult}
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hformula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount gammaFinish firstFinish formula)
    (hnegated : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount transformedStart transformedFinish
        ((compactFormulaNegationExact 0 formula).getD []))
    (hempty : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount emptyStart emptyFinish [])
    (htraceRows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount transformStateBoundary
        (compactFormulaTransformStateTrace (3, [])
          (compactSyntaxRunFuelBound formula)
          (compactFormulaTransformInitialState 0 formula)))
    (hright : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        rightGammaBoundary rightConclusion)
    (hleft : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        leftGammaBoundary leftConclusion)
    (hrightBool : rightBoolValue = compactAdditiveBoolTag rightValid)
    (hleftBool : leftBoolValue = compactAdditiveBoolTag leftValid)
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
    (htag : taskTag = 9)
    (hsourceCount : 2 ≤ source.length)
    (hrightValue : source.getI 0 = (rightConclusion, rightValid))
    (hleftValue : source.getI 1 = (leftConclusion, leftValid))
    (htarget : target =
      (Gamma, compactCutRuleCheck
        (Gamma, (formula,
          ((leftConclusion, leftValid),
            (rightConclusion, rightValid))))) :: source.drop 2) :
    ∃ formulaBoundary formulaBoundarySize
        transformedBoundary transformedBoundarySize
        emptyBoundary emptyBoundarySize transformTableWidth,
      CompactNumericExsCutCombineRuleRows
        tokenTable width tokenCount
        taskTag gammaFinish Gamma.length gammaBoundary
        firstFinish formula.length secondFinish witnessFinish witness.length
        rightConclusion.length rightGammaBoundary rightBoolValue
        leftConclusion.length leftGammaBoundary leftBoolValue
        sourceBoundary source.length targetBoundary target.length
        formulaBoundary formulaBoundarySize
        transformedStart transformedFinish transformedBoundary
          ((compactFormulaNegationExact 0 formula).getD []).length
          transformedBoundarySize
        transformStateBoundary (compactSyntaxRunFuelBound formula + 1)
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        transformTableWidth (2 ^ transformTableWidth)
        tableWidth valueBound
        (compactAdditiveBoolTag
          (compactCutRuleCheck
            (Gamma, (formula,
              ((leftConclusion, leftValid),
                (rightConclusion, rightValid)))))) := by
  rcases hformula with
    ⟨formulaBoundary, hformulaStructure, hformulaRows, hformulaSize⟩
  rcases hnegated with
    ⟨transformedBoundary, htransformedStructure,
      htransformedRows, htransformedSize⟩
  rcases hempty with
    ⟨emptyBoundary, hemptyStructure, hemptyRows, hemptySize⟩
  have hformulaLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount gammaFinish firstFinish formula :=
    ⟨formulaBoundary, hformulaStructure, hformulaRows, hformulaSize⟩
  have htransformedLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount transformedStart transformedFinish
        ((compactFormulaNegationExact 0 formula).getD []) :=
    ⟨transformedBoundary, htransformedStructure,
      htransformedRows, htransformedSize⟩
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
  have htransformedWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount transformedStart
        ((compactFormulaNegationExact 0 formula).getD []).length
        transformedFinish transformedBoundary
        (Nat.size transformedBoundary) :=
    ⟨htransformedStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        htransformedRows,
      rfl, htransformedSize⟩
  have hemptyWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount emptyStart 0 emptyFinish
        emptyBoundary (Nat.size emptyBoundary) :=
    ⟨hemptyStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hemptyRows,
      rfl, hemptySize⟩
  rcases CompactFormulaTransformTotalExactBoundedGraph.of_canonical_trace
      htraceRows hemptyLayout rfl hformulaRows htransformedRows hemptyRows
      (by simp [compactFormulaNegationExact]) with
    ⟨transformTableWidth, htransform⟩
  let result := compactCutRuleCheck
    (Gamma, (formula,
      ((leftConclusion, leftValid), (rightConclusion, rightValid))))
  have hcheck : CompactAdditiveCutRuleCheck
      tokenTable width tokenCount
      gammaBoundary Gamma.length
      gammaFinish firstFinish formulaBoundary formula.length
      leftGammaBoundary leftConclusion.length leftBoolValue
      rightGammaBoundary rightConclusion.length rightBoolValue
      transformedStart transformedFinish transformedBoundary
        ((compactFormulaNegationExact 0 formula).getD []).length
      transformStateBoundary (compactSyntaxRunFuelBound formula + 1)
      emptyStart emptyFinish emptyBoundary
      transformTableWidth (2 ^ transformTableWidth)
      (compactAdditiveBoolTag result) :=
    (compactAdditiveCutRuleCheck_iff
      htransform hGamma hformulaLayout hformulaRows hleft hright
      htransformedLayout htransformedRows hemptyLayout hemptyRows
      hleftBool hrightBool).mpr rfl
  have hpush : CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount
      sourceBoundary source.length targetBoundary target.length
      gammaBoundary Gamma.length tableWidth valueBound 2
      (compactAdditiveBoolTag result) :=
    CompactAdditiveStructuredListElementRowLayouts.childResultPushDropRows
      hsourceRows htargetRows hGamma hsourceGraph htargetGraph
      hsourceCount (by simpa [result] using htarget)
  have hrightHeadCanonical :=
    CompactNumericChildResultBoundedHeadEq.of_value_eq
      hsourceGraph (by omega) hright hsourceRows hrightValue
  have hrightHead : CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount sourceBoundary
      rightGammaBoundary rightConclusion.length valueBound 0
      rightBoolValue := by
    simpa only [hrightBool] using hrightHeadCanonical
  have hleftHeadCanonical :=
    CompactNumericChildResultBoundedHeadEq.of_value_eq
      hsourceGraph (by omega) hleft hsourceRows hleftValue
  have hleftHead : CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount sourceBoundary
      leftGammaBoundary leftConclusion.length valueBound 1
      leftBoolValue := by
    simpa only [hleftBool] using hleftHeadCanonical
  refine ⟨formulaBoundary, Nat.size formulaBoundary,
    transformedBoundary, Nat.size transformedBoundary,
    emptyBoundary, Nat.size emptyBoundary, transformTableWidth,
    hformulaWitness, htransformedWitness, hemptyWitness, ?_⟩
  right
  exact ⟨htag, hsourceCount,
    CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
      hright,
    CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
      hleft,
    hrightHead, hleftHead, hcheck, hpush⟩

#print axioms CompactNumericExsCutCombineRuleRows.exists_of_cut

end FoundationCompactNumericListedDirectExsCutCombineRuleRowsCompleteness
