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
open FoundationCompactNumericListedDirectAdditiveCodecGraph
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
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
open FoundationCompactNumericListedDirectFormulaTransformTotalExactCompleteness

def compactNumericExsCutFormulaTransformPublicFuelBound
    (tokenCount : Nat) : Nat :=
  16 * (tokenCount + 1) * (tokenCount + 1) + 8

def compactNumericExsCutCriticalCoordinateSizeBound
    (width tokenCount : Nat) : Nat :=
  let fuel := compactNumericExsCutFormulaTransformPublicFuelBound tokenCount
  compactFormulaTransformAdjacentStepPublicWidth width tokenCount +
    (tokenCount + 1) * tokenCount +
    (fuel + 2) * tokenCount +
    (fuel + 1) +
    compactFormulaTransformCanonicalTableWidthBound
      width tokenCount fuel + 8

structure CompactNumericExsCutCriticalCoordinateBounds
    (width tokenCount transformStateBoundary
      transformTableWidth transformValueBound : Nat) : Prop where
  transformStateBoundary_size : Nat.size transformStateBoundary ≤
    compactNumericExsCutCriticalCoordinateSizeBound width tokenCount
  transformTableWidth_size : Nat.size transformTableWidth ≤
    compactNumericExsCutCriticalCoordinateSizeBound width tokenCount
  transformValueBound_size : Nat.size transformValueBound ≤
    compactNumericExsCutCriticalCoordinateSizeBound width tokenCount

theorem compactSyntaxRunFuelBound_le_exsCutPublicFuelBound
    {formula : List Nat} {tokenCount : Nat}
    (hformulaCount : formula.length ≤ tokenCount) :
    compactSyntaxRunFuelBound formula ≤
      compactNumericExsCutFormulaTransformPublicFuelBound tokenCount := by
  have hlength := Nat.add_le_add_right hformulaCount 1
  have hsquare := Nat.mul_le_mul hlength hlength
  have hscaled := Nat.mul_le_mul_left 16 hsquare
  have htotal := Nat.add_le_add_right hscaled 8
  simpa [compactSyntaxRunFuelBound,
    compactNumericExsCutFormulaTransformPublicFuelBound, Nat.mul_assoc] using
      htotal

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
    (htraceRows :
      CompactFormulaTransformStateListRowLayouts
          tokenTable width tokenCount transformStateBoundary
          (compactFormulaTransformStateTrace (2, witness)
            (compactSyntaxRunFuelBound formula)
            (compactFormulaTransformInitialState 1 formula)) ∧
        Nat.size transformStateBoundary ≤
          ((compactFormulaTransformStateTrace (2, witness)
              (compactSyntaxRunFuelBound formula)
              (compactFormulaTransformInitialState 1 formula)).length + 1) *
            tokenCount)
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
              (witness, (rightConclusion, rightValid)))))) ∧
      CompactNumericExsCutCriticalCoordinateBounds
        width tokenCount transformStateBoundary
          transformTableWidth (2 ^ transformTableWidth) := by
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
  rcases
      CompactFormulaTransformTotalExactBoundedGraph.of_canonical_trace_with_width_bound
      htraceRows.1 hwitness rfl hformulaRows htransformedRows hemptyRows
      (by simp [compactFormulaSubstitutionExact]) with
    ⟨transformTableWidth, htransform, htransformTableWidthRaw⟩
  have hformulaCount :
      formula.length ≤ tokenCount :=
    structuredListLayout_count_le_tokenCount hformulaStructure
  have hfuel : compactSyntaxRunFuelBound formula ≤
      compactNumericExsCutFormulaTransformPublicFuelBound tokenCount :=
    compactSyntaxRunFuelBound_le_exsCutPublicFuelBound hformulaCount
  have htransformStateBoundaryRaw :
      Nat.size transformStateBoundary ≤
        (compactSyntaxRunFuelBound formula + 2) * tokenCount := by
    simpa using htraceRows.2
  have htransformStateBoundaryPublic :
      Nat.size transformStateBoundary ≤
        (compactNumericExsCutFormulaTransformPublicFuelBound tokenCount + 2) *
          tokenCount :=
    htransformStateBoundaryRaw.trans
      (Nat.mul_le_mul_right tokenCount (Nat.add_le_add_right hfuel 2))
  have htransformTableWidth :
      transformTableWidth ≤
        compactFormulaTransformCanonicalTableWidthBound width tokenCount
          (compactNumericExsCutFormulaTransformPublicFuelBound tokenCount) :=
    htransformTableWidthRaw.trans
      (compactFormulaTransformCanonicalTableWidthBound_mono_fuel
        width tokenCount hfuel)
  have htransformStateBoundarySize :
      Nat.size transformStateBoundary ≤
        compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    htransformStateBoundaryPublic.trans (by
      simp [compactNumericExsCutCriticalCoordinateSizeBound]
      omega)
  have htransformTableWidthSize :
      Nat.size transformTableWidth ≤
        compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    ((natSize_le_of_le (Nat.le_refl transformTableWidth)).trans
      htransformTableWidth).trans (by
        simp [compactNumericExsCutCriticalCoordinateSizeBound]
        omega)
  have htransformValueBoundSize :
      Nat.size (2 ^ transformTableWidth) ≤
        compactNumericExsCutCriticalCoordinateSizeBound width tokenCount := by
    rw [Nat.size_pow]
    exact (Nat.add_le_add_right htransformTableWidth 1).trans (by
      simp [compactNumericExsCutCriticalCoordinateSizeBound]
      omega)
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
    emptyBoundary, Nat.size emptyBoundary, transformTableWidth, ?_, ?_⟩
  · refine ⟨hformulaWitness, htransformedWitness, hemptyWitness, ?_⟩
    left
    exact ⟨htag, hsourceCount,
      CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hright,
      hrightHead, hcheck, hpush⟩
  · exact
      { transformStateBoundary_size := htransformStateBoundarySize
        transformTableWidth_size := htransformTableWidthSize
        transformValueBound_size := htransformValueBoundSize }

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
    (htraceRows :
      CompactFormulaTransformStateListRowLayouts
          tokenTable width tokenCount transformStateBoundary
          (compactFormulaTransformStateTrace (3, [])
            (compactSyntaxRunFuelBound formula)
            (compactFormulaTransformInitialState 0 formula)) ∧
        Nat.size transformStateBoundary ≤
          ((compactFormulaTransformStateTrace (3, [])
              (compactSyntaxRunFuelBound formula)
              (compactFormulaTransformInitialState 0 formula)).length + 1) *
            tokenCount)
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
                (rightConclusion, rightValid)))))) ∧
      CompactNumericExsCutCriticalCoordinateBounds
        width tokenCount transformStateBoundary
          transformTableWidth (2 ^ transformTableWidth) := by
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
  rcases
      CompactFormulaTransformTotalExactBoundedGraph.of_canonical_trace_with_width_bound
      htraceRows.1 hemptyLayout rfl hformulaRows htransformedRows hemptyRows
      (by simp [compactFormulaNegationExact]) with
    ⟨transformTableWidth, htransform, htransformTableWidthRaw⟩
  have hformulaCount :
      formula.length ≤ tokenCount :=
    structuredListLayout_count_le_tokenCount hformulaStructure
  have hfuel : compactSyntaxRunFuelBound formula ≤
      compactNumericExsCutFormulaTransformPublicFuelBound tokenCount :=
    compactSyntaxRunFuelBound_le_exsCutPublicFuelBound hformulaCount
  have htransformStateBoundaryRaw :
      Nat.size transformStateBoundary ≤
        (compactSyntaxRunFuelBound formula + 2) * tokenCount := by
    simpa using htraceRows.2
  have htransformStateBoundaryPublic :
      Nat.size transformStateBoundary ≤
        (compactNumericExsCutFormulaTransformPublicFuelBound tokenCount + 2) *
          tokenCount :=
    htransformStateBoundaryRaw.trans
      (Nat.mul_le_mul_right tokenCount (Nat.add_le_add_right hfuel 2))
  have htransformTableWidth :
      transformTableWidth ≤
        compactFormulaTransformCanonicalTableWidthBound width tokenCount
          (compactNumericExsCutFormulaTransformPublicFuelBound tokenCount) :=
    htransformTableWidthRaw.trans
      (compactFormulaTransformCanonicalTableWidthBound_mono_fuel
        width tokenCount hfuel)
  have htransformStateBoundarySize :
      Nat.size transformStateBoundary ≤
        compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    htransformStateBoundaryPublic.trans (by
      simp [compactNumericExsCutCriticalCoordinateSizeBound]
      omega)
  have htransformTableWidthSize :
      Nat.size transformTableWidth ≤
        compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    ((natSize_le_of_le (Nat.le_refl transformTableWidth)).trans
      htransformTableWidth).trans (by
        simp [compactNumericExsCutCriticalCoordinateSizeBound]
        omega)
  have htransformValueBoundSize :
      Nat.size (2 ^ transformTableWidth) ≤
        compactNumericExsCutCriticalCoordinateSizeBound width tokenCount := by
    rw [Nat.size_pow]
    exact (Nat.add_le_add_right htransformTableWidth 1).trans (by
      simp [compactNumericExsCutCriticalCoordinateSizeBound]
      omega)
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
    emptyBoundary, Nat.size emptyBoundary, transformTableWidth, ?_, ?_⟩
  · refine ⟨hformulaWitness, htransformedWitness, hemptyWitness, ?_⟩
    right
    exact ⟨htag, hsourceCount,
      CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hright,
      CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hleft,
      hrightHead, hleftHead, hcheck, hpush⟩
  · exact
      { transformStateBoundary_size := htransformStateBoundarySize
        transformTableWidth_size := htransformTableWidthSize
        transformValueBound_size := htransformValueBoundSize }

#print axioms CompactNumericExsCutCombineRuleRows.exists_of_cut

end FoundationCompactNumericListedDirectExsCutCombineRuleRowsCompleteness
