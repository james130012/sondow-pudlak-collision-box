import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniversalFullyFixedBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds

/-!
# Fully fixed resource for the complete syntax-task equal-row certificate

This endpoint adds the count equality to the fixed row universal and removes
the remaining formula-dependent conjunction assembly cost.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListSameRowsFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniversalFullyFixedBounds
open FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds

private abbrev taskSameRowsZeroValuationFullyFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate.zeroValuation

def taskSameRowsCountEqualityFullyFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (binaryNumeralTermCodeEnvelope bitBound)

def taskSameRowsCompleteSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let countCode :=
    orderAtomicFormulaCodeEnvelope
      (binaryNumeralTermCodeEnvelope bitBound)
  let universalCode :=
    closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      (taskSameRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (taskSameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
  countCode + universalCode + 9

def taskSameRowsCompleteFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (taskSameRowsCompleteSyntaxFixedPolynomial numericBound bitBound)
    (taskSameRowsCountEqualityFullyFixedPayloadPolynomial bitBound)
    (taskSameRowsUniversalFullyFixedPayloadPolynomial numericBound bitBound)

theorem
    compactAdditiveSyntaxTaskListSameRowsClosedFormula_code_length_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hcount : targetCount = sourceCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary
        targetCount)).length <=
      taskSameRowsCompleteSyntaxFixedPolynomial numericBound bitBound := by
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount)”
  let universalFormula : ValuationFormula :=
    (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
      sourceBoundary targetBoundary).ballLT
        (shortBinaryNumeralTerm sourceCount)
  let countTermCode := binaryNumeralTermCodeEnvelope bitBound
  let countCode := orderAtomicFormulaCodeEnvelope countTermCode
  let universalCode :=
    closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      (taskSameRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (taskSameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCount).trans hnumericSize
  have htargetCountSize : Nat.size targetCount <= bitBound := by
    rw [hcount]
    exact hsourceCountSize
  have hsourceTerm :
      (binaryTermCode (shortBinaryNumeralTerm sourceCount)).length <=
        countTermCode := by
    dsimp only [countTermCode]
    exact binaryNumeralTerm_code_length_le_envelope sourceCount bitBound
      hsourceCountSize
  have htargetTerm :
      (binaryTermCode (shortBinaryNumeralTerm targetCount)).length <=
        countTermCode := by
    dsimp only [countTermCode]
    exact binaryNumeralTerm_code_length_le_envelope targetCount bitBound
      htargetCountSize
  have hcountCode :
      (binaryFormulaCode countFormula).length <= countCode := by
    dsimp only [countFormula, countCode]
    exact binaryRelationFormula_code_le_orderAtomic Language.Eq.eq
      (shortBinaryNumeralTerm targetCount)
      (shortBinaryNumeralTerm sourceCount) countTermCode htargetTerm
      hsourceTerm
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody :
      (binaryFormulaCode
        (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
          sourceBoundary targetBoundary)).length <=
        taskSameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound :=
    compactAdditiveSyntaxTaskListSameRowsBody_code_length_le_fixed tokenTable
      width tokenCount sourceBoundary targetBoundary numericBound bitBound
      htokenCount htokenTableSize hwidthSize htokenCountSize
      hsourceBoundarySize htargetBoundarySize
  have huniversalAlignment :
      universalFormula =
        ∀⁰ termBoundedUniversalBody
          (Rew.bShift (shortBinaryNumeralTerm sourceCount))
          (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width
            tokenCount sourceBoundary targetBoundary) := by
    dsimp only [universalFormula]
    rw [LO.FirstOrder.Semiformula.ballLT,
      LO.FirstOrder.Semiformula.ball_eq]
    unfold termBoundedUniversalBody termBoundFormula
    rw [finiteCaseLessThanFormula_eq_operator]
  have huniversalCode :
      (binaryFormulaCode universalFormula).length <= universalCode := by
    have hraw :=
      closedShortTermBoundedUniversalFormula_code_length_le_source
        (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width
          tokenCount sourceBoundary targetBoundary)
        sourceCount numericBound bitBound
        (taskSameRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
        (taskSameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
        hsourceCountSize hbody
    rw [huniversalAlignment]
    exact hraw
  rw [compactAdditiveSyntaxTaskListSameRowsClosedFormula_alignment]
  unfold compactAdditiveSyntaxTaskListSameRowsExplicitFormula
  rw [show taskSameRowsCompleteSyntaxFixedPolynomial numericBound bitBound =
      countCode + universalCode + 9 by rfl]
  exact (binaryFormulaCode_and_length_le countFormula universalFormula).trans
    (by
      omega)

theorem
    compactAdditiveSyntaxTaskListSameRowsClosedFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount : Nat) :
    (compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary
      targetCount).freeVariables = ∅ := by
  rw [compactAdditiveSyntaxTaskListSameRowsClosedFormula_alignment]
  unfold compactAdditiveSyntaxTaskListSameRowsExplicitFormula
  have huniversalAlignment :
      (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary).ballLT
          (shortBinaryNumeralTerm sourceCount) =
        ∀⁰ termBoundedUniversalBody
          (Rew.bShift (shortBinaryNumeralTerm sourceCount))
          (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width
            tokenCount sourceBoundary targetBoundary) := by
    rw [LO.FirstOrder.Semiformula.ballLT,
      LO.FirstOrder.Semiformula.ball_eq]
    unfold termBoundedUniversalBody termBoundFormula
    rw [finiteCaseLessThanFormula_eq_operator]
  rw [huniversalAlignment, LO.FirstOrder.Semiformula.freeVariables_and,
    compactAdditiveSyntaxTaskListSameRowsOuterFormula_freeVariables_eq_empty_fixed]
  simp [shortBinaryNumeralTerm_freeVariables_eq_empty]

theorem
    compactAdditiveSyntaxTaskListSameRowsFromRowDataPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hcount : targetCount = sourceCount)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskListSameRowsFromRowDataPayloadEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary targetCount
        rows <=
      taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount)”
  let universalFormula : ValuationFormula :=
    (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
      sourceBoundary targetBoundary).ballLT
        (shortBinaryNumeralTerm sourceCount)
  let countTermCode := binaryNumeralTermCodeEnvelope bitBound
  let countCode := orderAtomicFormulaCodeEnvelope countTermCode
  let universalCode :=
    closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      (taskSameRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
      (taskSameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
  let syntaxResource :=
    taskSameRowsCompleteSyntaxFixedPolynomial numericBound bitBound
  let countResource :=
    compactAdditiveSyntaxTaskListSameRowsCountEqualityPayloadPolynomial
      sourceCount targetCount
  let universalResource :=
    compactAdditiveSyntaxTaskListSameRowsUniversalPayloadEnvelope tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary rows
  let countBound :=
    taskSameRowsCountEqualityFullyFixedPayloadPolynomial bitBound
  let universalBound :=
    taskSameRowsUniversalFullyFixedPayloadPolynomial numericBound bitBound
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCount).trans hnumericSize
  have htargetCountSize : Nat.size targetCount <= bitBound := by
    rw [hcount]
    exact hsourceCountSize
  have hsourceTerm :
      (binaryTermCode (shortBinaryNumeralTerm sourceCount)).length <=
        countTermCode := by
    dsimp only [countTermCode]
    exact binaryNumeralTerm_code_length_le_envelope sourceCount bitBound
      hsourceCountSize
  have htargetTerm :
      (binaryTermCode (shortBinaryNumeralTerm targetCount)).length <=
        countTermCode := by
    dsimp only [countTermCode]
    exact binaryNumeralTerm_code_length_le_envelope targetCount bitBound
      htargetCountSize
  have hcountClosed : countFormula.freeVariables = ∅ := by
    dsimp only [countFormula]
    simp [shortBinaryNumeralTerm_freeVariables_eq_empty]
  have hcountCode :
      (binaryFormulaCode countFormula).length <= countCode := by
    dsimp only [countFormula, countCode]
    exact binaryRelationFormula_code_le_orderAtomic Language.Eq.eq
      (shortBinaryNumeralTerm targetCount)
      (shortBinaryNumeralTerm sourceCount) countTermCode htargetTerm
      hsourceTerm
  have hcountBound : countResource <= countBound := by
    unfold countResource
      compactAdditiveSyntaxTaskListSameRowsCountEqualityPayloadPolynomial
    unfold countBound taskSameRowsCountEqualityFullyFixedPayloadPolynomial
    exact compilePositiveRelationPayloadPolynomial_le_fixed
      taskSameRowsZeroValuationFullyFixed Language.Eq.eq
      ![shortBinaryNumeralTerm targetCount,
        shortBinaryNumeralTerm sourceCount]
      0 countTermCode
      (by
        change
          (shortBinaryNumeralTerm targetCount : ValuationTerm).freeVariables
            ⊆ {0}
        rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
        simp)
      (by
        change
          (shortBinaryNumeralTerm sourceCount : ValuationTerm).freeVariables
            ⊆ {0}
        rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
        simp)
      (by
        dsimp only [taskSameRowsZeroValuationFullyFixed]
        simp [
          FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate.zeroValuation])
      htargetTerm hsourceTerm
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody :
      (binaryFormulaCode
        (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
          sourceBoundary targetBoundary)).length <=
        taskSameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound :=
    compactAdditiveSyntaxTaskListSameRowsBody_code_length_le_fixed tokenTable
      width tokenCount sourceBoundary targetBoundary numericBound bitBound
      htokenCount htokenTableSize hwidthSize htokenCountSize
      hsourceBoundarySize htargetBoundarySize
  have huniversalAlignment :
      universalFormula =
        ∀⁰ termBoundedUniversalBody
          (Rew.bShift (shortBinaryNumeralTerm sourceCount))
          (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width
            tokenCount sourceBoundary targetBoundary) := by
    dsimp only [universalFormula]
    rw [LO.FirstOrder.Semiformula.ballLT,
      LO.FirstOrder.Semiformula.ball_eq]
    unfold termBoundedUniversalBody termBoundFormula
    rw [finiteCaseLessThanFormula_eq_operator]
  have huniversalCode :
      (binaryFormulaCode universalFormula).length <= universalCode := by
    have hraw :=
      closedShortTermBoundedUniversalFormula_code_length_le_source
        (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width
          tokenCount sourceBoundary targetBoundary)
        sourceCount numericBound bitBound
        (taskSameRowsUniversalSyntaxFixedPolynomial numericBound bitBound)
        (taskSameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound)
        hsourceCountSize hbody
    rw [huniversalAlignment]
    exact hraw
  have huniversalClosed : universalFormula.freeVariables = ∅ := by
    rw [huniversalAlignment]
    exact
      compactAdditiveSyntaxTaskListSameRowsOuterFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
  have hsyntaxResource :
      syntaxResource = countCode + universalCode + 9 := by
    rfl
  have hsyntaxPositive : 1 <= syntaxResource := by
    rw [hsyntaxResource]
    omega
  have hcountSyntax :
      (binaryFormulaCode countFormula).length <= syntaxResource := by
    exact hcountCode.trans (by
      rw [hsyntaxResource]
      omega)
  have huniversalSyntax :
      (binaryFormulaCode universalFormula).length <= syntaxResource := by
    exact huniversalCode.trans (by
      rw [hsyntaxResource]
      omega)
  have hconjunctionRaw :=
    binaryFormulaCode_and_length_le countFormula universalFormula
  have hconjunction :
      (binaryFormulaCode (countFormula ⋏ universalFormula)).length <=
        syntaxResource := by
    exact hconjunctionRaw.trans (by
      rw [hsyntaxResource]
      omega)
  have huniversalBound : universalResource <= universalBound := by
    unfold universalResource universalBound
    exact
      compactAdditiveSyntaxTaskListSameRowsUniversalPayloadEnvelope_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        numericBound bitBound rows hwidth htokenCount hsourceCount
        htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hmono :=
    transparentHybridConjunctionPayloadEnvelope_mono
      taskSameRowsZeroValuationFullyFixed countFormula universalFormula
      hcountBound huniversalBound
  have hclosed :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      taskSameRowsZeroValuationFullyFixed countFormula universalFormula
      countBound universalBound syntaxResource hsyntaxPositive hcountClosed
      huniversalClosed hcountSyntax huniversalSyntax hconjunction
  unfold compactAdditiveSyntaxTaskListSameRowsFromRowDataPayloadEnvelope
  unfold taskSameRowsCompleteFullyFixedPayloadPolynomial
  simpa only [countFormula, universalFormula, countResource,
    universalResource, countBound, universalBound, syntaxResource,
    taskSameRowsZeroValuationFullyFixed] using hmono.trans hclosed

theorem
    compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        hgraph <=
      taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound
        bitBound := by
  unfold compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope
  exact
    compactAdditiveSyntaxTaskListSameRowsFromRowDataPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound hgraph.1
      (compactAdditiveSyntaxTaskListSameRowDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        hgraph)
      hwidth htokenCount hsourceCount htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize

#print axioms
  compactAdditiveSyntaxTaskListSameRowsClosedFormula_code_length_le_fullyFixed
#print axioms
  compactAdditiveSyntaxTaskListSameRowsClosedFormula_freeVariables_eq_empty_fullyFixed
#print axioms
  compactAdditiveSyntaxTaskListSameRowsFromRowDataPayloadEnvelope_le_fullyFixed
#print axioms
  compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListSameRowsFullyFixedBounds
