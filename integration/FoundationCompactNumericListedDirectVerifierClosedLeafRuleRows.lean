import integration.FoundationCompactNumericListedDirectVerifierLeafParseStackRows
import integration.FoundationCompactNumericListedDirectClosedRuleCheck

/-!
# Exact verifier leaf row for the closed rule

The proof/certificate tags are fixed to `0/0`.  The result bit is obtained by
the complete direct negation trace and the two checked membership queries on
the same decoded context and first formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierClosedLeafRuleRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectClosedRuleCheck

def CompactNumericVerifierClosedLeafRuleRows
    (tokenTable width tokenCount proofTag certificateTag
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      negatedStart negatedFinish negatedBoundary negatedCount
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBool : Nat) : Prop :=
  proofTag = 0 ∧
    certificateTag = 0 ∧
    CompactAdditiveClosedRuleCheck
      tokenTable width tokenCount
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      negatedStart negatedFinish negatedBoundary negatedCount
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBool

def compactNumericVerifierClosedLeafRuleRowsDef :
    𝚺₀.Semisentence 23 := .mkSigma
  “tokenTable width tokenCount proofTag certificateTag
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      negatedStart negatedFinish negatedBoundary negatedCount
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBool.
    proofTag = 0 ∧
    certificateTag = 0 ∧
    !(compactAdditiveClosedRuleCheckDef)
      tokenTable width tokenCount
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      negatedStart negatedFinish negatedBoundary negatedCount
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBool”

@[simp] theorem compactNumericVerifierClosedLeafRuleRowsDef_spec
    (tokenTable width tokenCount proofTag certificateTag
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      negatedStart negatedFinish negatedBoundary negatedCount
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBool : Nat) :
    compactNumericVerifierClosedLeafRuleRowsDef.val.Evalb
        ![tokenTable, width, tokenCount, proofTag, certificateTag,
          gammaBoundary, gammaCount,
          formulaStart, formulaFinish, formulaBoundary, formulaCount,
          negatedStart, negatedFinish, negatedBoundary, negatedCount,
          stateBoundary, stateCount,
          emptyStart, emptyFinish, emptyBoundary,
          tableWidth, valueBound, resultBool] ↔
      CompactNumericVerifierClosedLeafRuleRows
        tokenTable width tokenCount proofTag certificateTag
        gammaBoundary gammaCount
        formulaStart formulaFinish formulaBoundary formulaCount
        negatedStart negatedFinish negatedBoundary negatedCount
        stateBoundary stateCount
        emptyStart emptyFinish emptyBoundary
        tableWidth valueBound resultBool := by
  have hcheckEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount, proofTag, certificateTag,
            gammaBoundary, gammaCount,
            formulaStart, formulaFinish, formulaBoundary, formulaCount,
            negatedStart, negatedFinish, negatedBoundary, negatedCount,
            stateBoundary, stateCount,
            emptyStart, emptyFinish, emptyBoundary,
            tableWidth, valueBound, resultBool]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 23), #1, #2,
          #5, #6, #7, #8, #9, #10, #11, #12, #13, #14,
          #15, #16, #17, #18, #19, #20, #21, #22]) =
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount,
          formulaStart, formulaFinish, formulaBoundary, formulaCount,
          negatedStart, negatedFinish, negatedBoundary, negatedCount,
          stateBoundary, stateCount,
          emptyStart, emptyFinish, emptyBoundary,
          tableWidth, valueBound, resultBool] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierClosedLeafRuleRowsDef,
    CompactNumericVerifierClosedLeafRuleRows, hcheckEnv]

theorem compactNumericVerifierClosedLeafRuleRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierClosedLeafRuleRowsDef.val := by
  simp [compactNumericVerifierClosedLeafRuleRowsDef]

theorem CompactNumericVerifierClosedLeafRuleRows.sound
    {tokenTable width tokenCount certificateTag
      formulaBoundary
      negatedStart negatedFinish negatedBoundary
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBool : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    {root : CompactNumericVerifierTask}
    {negated : List Nat}
    (hcore : CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (hrootLayout : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount coordinates.start coordinates.finish root)
    (hparsed : ∃ parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0,
      root.2.2.1 =
        FoundationCompactSyntaxTokenMachine.compactArithmeticFormulaTokens
          parsed)
    (hformulaRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        formulaBoundary root.2.2.1)
    (hnegatedLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount negatedStart negatedFinish negated)
    (hnegatedRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        negatedBoundary negated)
    (hemptyLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount emptyStart emptyFinish [])
    (hemptyRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (hrows : CompactNumericVerifierClosedLeafRuleRows
      tokenTable width tokenCount coordinates.tag certificateTag
      coordinates.gammaBoundary coordinates.gammaCount
      coordinates.gammaFinish coordinates.firstFinish
        formulaBoundary coordinates.firstCount
      negatedStart negatedFinish negatedBoundary negated.length
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBool) :
    root.1 = 0 ∧
      certificateTag = 0 ∧
      resultBool = compactAdditiveBoolTag
        (compactClosedRuleCheck (root.2.1, root.2.2.1)) := by
  rcases hrows with ⟨hproofTag, hcertificateTag, hcheck⟩
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hcore with
    ⟨realizedRoot, hrealizedLayout, hrealizedTag,
      hgammaRows, hgammaLength,
      hformulaLayout, hformulaLength,
      _hsecondLayout, _hsecondLength,
      _hwitnessLayout, _hwitnessLength,
      _hsuffixLayout, _hsuffixLength⟩
  have hrootEq : realizedRoot = root :=
    FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hcore hrootLayout hrealizedLayout
  subst realizedRoot
  have hcheck' : CompactAdditiveClosedRuleCheck
      tokenTable width tokenCount
      coordinates.gammaBoundary root.2.1.length
      coordinates.gammaFinish coordinates.firstFinish
        formulaBoundary root.2.2.1.length
      negatedStart negatedFinish negatedBoundary negated.length
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBool := by
    simpa [hgammaLength, hformulaLength] using hcheck
  have hresult :=
    (compactAdditiveClosedRuleCheck_iff
      hcheck'.1 hgammaRows hformulaLayout hformulaRows
      hnegatedLayout hnegatedRows hemptyLayout hemptyRows hparsed).mp hcheck'
  exact ⟨hrealizedTag.trans hproofTag, hcertificateTag, hresult⟩

#print axioms compactNumericVerifierClosedLeafRuleRowsDef_spec
#print axioms compactNumericVerifierClosedLeafRuleRowsDef_sigmaZero
#print axioms CompactNumericVerifierClosedLeafRuleRows.sound

end FoundationCompactNumericListedDirectVerifierClosedLeafRuleRows
