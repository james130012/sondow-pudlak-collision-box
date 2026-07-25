import integration.FoundationCompactNumericListedDirectTokenSliceBitAtomClosedTermFixedBounds

/-!
# Fixed bit branches over arbitrary closed token-slice terms

The two truth branches, both implications, their conjunction, and the finite
bit-index sum preserve the caller's original closed arithmetic terms.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceBitClosedTermBranchesFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitAtomClosedTermFixedBounds

def tokenSliceClosedTermBitBranchSyntaxPolynomial
    (numericBound termCode : Nat) : Nat :=
  tokenSliceBitBranchContextCodePolynomial numericBound +
    8 * tokenSliceClosedTermBitAtomCodePolynomial termCode + 65

def tokenSliceClosedTermBitSingleBranchFixedPayloadPolynomial
    (numericBound termCode bitBound : Nat) : Nat :=
  let atomResource :=
    tokenSliceClosedTermBitAtomFixedPayloadPolynomial numericBound termCode
      bitBound
  let disjunctionResource :=
    hybridDisjunctionGeneralPayloadEnvelope
      (tokenSliceClosedTermBitBranchSyntaxPolynomial numericBound termCode)
      atomResource
  hybridConjunctionGeneralPayloadEnvelope
    (tokenSliceClosedTermBitBranchSyntaxPolynomial numericBound termCode)
    disjunctionResource disjunctionResource

def tokenSliceClosedTermBitBranchesFixedPayloadPolynomial
    (numericBound termCode bitBound : Nat) : Nat :=
  2 * tokenSliceClosedTermBitSingleBranchFixedPayloadPolynomial numericBound
    termCode bitBound

def tokenSliceClosedTermBitBranchPayloadSumFixedPolynomial
    (numericBound termCode bitBound : Nat) : Nat :=
  numericBound *
    tokenSliceClosedTermBitBranchesFixedPayloadPolynomial numericBound
      termCode bitBound

theorem tokenSliceAtValuationBitBranchStructuralEnvelope_le_closedFixed_aux
    (expected : Bool) (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset bitIndex numericBound termCode bitBound : Nat)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hsourceClosed : sourceStartTerm.freeVariables = ∅)
    (htargetClosed : targetStartTerm.freeVariables = ∅)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidthCode : (binaryTermCode widthTerm).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode)
    (hwidth : termValue valuation widthTerm <= numericBound)
    (hsource : termValue valuation sourceStartTerm <= numericBound)
    (htarget : termValue valuation targetStartTerm <= numericBound)
    (hoffset : offset <= numericBound)
    (hbitIndex : bitIndex < termValue valuation widthTerm)
    (htableSize : Nat.size (termValue valuation tokenTableTerm) <= bitBound) :
    (if expected then
      tokenSliceAtValuationBitTrueBranchStructuralEnvelope valuation
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset bitIndex
    else
      tokenSliceAtValuationBitFalseBranchStructuralEnvelope valuation
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
        bitIndex) <=
      tokenSliceClosedTermBitSingleBranchFixedPayloadPolynomial numericBound
        termCode bitBound := by
  let branchValuation :=
    extendValuation bitIndex (extendValuation offset valuation)
  let sourceAtom :=
    tokenSliceAtValuationBitAtom tokenTableTerm sourceStartTerm widthTerm
  let targetAtom :=
    tokenSliceAtValuationBitAtom tokenTableTerm targetStartTerm widthTerm
  let forwardFormula := (∼sourceAtom) ⋎ targetAtom
  let backwardFormula := (∼targetAtom) ⋎ sourceAtom
  let branchFormula := forwardFormula ⋏ backwardFormula
  let atomResource :=
    tokenSliceClosedTermBitAtomFixedPayloadPolynomial numericBound termCode
      bitBound
  let syntaxResource :=
    tokenSliceClosedTermBitBranchSyntaxPolynomial numericBound termCode
  let disjunctionResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource atomResource
  have hbitIndexBound : bitIndex <= numericBound :=
    (Nat.le_of_lt hbitIndex).trans hwidth
  have hsourceVars : sourceAtom.freeVariables ⊆ {0, 1} := by
    dsimp only [sourceAtom]
    exact tokenSliceClosedTermBitAtom_freeVariables_subset tokenTableTerm
      widthTerm sourceStartTerm htableClosed hwidthClosed hsourceClosed
  have htargetVars : targetAtom.freeVariables ⊆ {0, 1} := by
    dsimp only [targetAtom]
    exact tokenSliceClosedTermBitAtom_freeVariables_subset tokenTableTerm
      widthTerm targetStartTerm htableClosed hwidthClosed htargetClosed
  have hnegSourceVars : (∼sourceAtom).freeVariables ⊆ {0, 1} := by
    simpa using hsourceVars
  have hnegTargetVars : (∼targetAtom).freeVariables ⊆ {0, 1} := by
    simpa using htargetVars
  have hforwardVars : forwardFormula.freeVariables ⊆ {0, 1} := by
    dsimp only [forwardFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_or]
    exact Finset.union_subset hnegSourceVars htargetVars
  have hbackwardVars : backwardFormula.freeVariables ⊆ {0, 1} := by
    dsimp only [backwardFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_or]
    exact Finset.union_subset hnegTargetVars hsourceVars
  have hbranchVars : branchFormula.freeVariables ⊆ {0, 1} := by
    dsimp only [branchFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hforwardVars hbackwardVars
  have hsourceAtomCode :
      (binaryFormulaCode sourceAtom).length <=
        tokenSliceClosedTermBitAtomCodePolynomial termCode := by
    dsimp only [sourceAtom]
    exact tokenSliceClosedTermBitAtom_code_le tokenTableTerm widthTerm
      sourceStartTerm termCode htableCode hwidthCode hsourceCode
  have htargetAtomCode :
      (binaryFormulaCode targetAtom).length <=
        tokenSliceClosedTermBitAtomCodePolynomial termCode := by
    dsimp only [targetAtom]
    exact tokenSliceClosedTermBitAtom_code_le tokenTableTerm widthTerm
      targetStartTerm termCode htableCode hwidthCode htargetCode
  have hnegSourceRaw := binaryFormulaCode_neg_length_le sourceAtom
  have hnegTargetRaw := binaryFormulaCode_neg_length_le targetAtom
  have hforwardRaw := binaryFormulaCode_or_length_le (∼sourceAtom) targetAtom
  have hbackwardRaw := binaryFormulaCode_or_length_le (∼targetAtom) sourceAtom
  have hbranchRaw :=
    binaryFormulaCode_and_length_le forwardFormula backwardFormula
  have hsyntaxPositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold tokenSliceClosedTermBitBranchSyntaxPolynomial
    omega
  have hsourceSyntax :
      (binaryFormulaCode sourceAtom).length <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold tokenSliceClosedTermBitBranchSyntaxPolynomial
    omega
  have htargetSyntax :
      (binaryFormulaCode targetAtom).length <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold tokenSliceClosedTermBitBranchSyntaxPolynomial
    omega
  have hnegSourceSyntax :
      (binaryFormulaCode (∼sourceAtom)).length <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold tokenSliceClosedTermBitBranchSyntaxPolynomial
    omega
  have hnegTargetSyntax :
      (binaryFormulaCode (∼targetAtom)).length <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold tokenSliceClosedTermBitBranchSyntaxPolynomial
    omega
  have hforwardSyntax :
      (binaryFormulaCode forwardFormula).length <= syntaxResource := by
    dsimp only [forwardFormula, syntaxResource] at hforwardRaw ⊢
    unfold tokenSliceClosedTermBitBranchSyntaxPolynomial
    omega
  have hbackwardSyntax :
      (binaryFormulaCode backwardFormula).length <= syntaxResource := by
    dsimp only [backwardFormula, syntaxResource] at hbackwardRaw ⊢
    unfold tokenSliceClosedTermBitBranchSyntaxPolynomial
    omega
  have hbranchSyntax :
      (binaryFormulaCode branchFormula).length <= syntaxResource := by
    dsimp only [branchFormula, forwardFormula, backwardFormula,
      syntaxResource] at hbranchRaw ⊢
    unfold tokenSliceClosedTermBitBranchSyntaxPolynomial
    omega
  have hforwardContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext forwardFormula.freeVariables branchValuation) <=
        syntaxResource := by
    have hraw := tokenSliceBitBranchContext_formulaCodeSum_le valuation
      forwardFormula.freeVariables offset bitIndex numericBound hforwardVars
      hoffset hbitIndexBound
    exact hraw.trans (by
      dsimp only [syntaxResource]
      unfold tokenSliceClosedTermBitBranchSyntaxPolynomial
      omega)
  have hbackwardContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext backwardFormula.freeVariables branchValuation) <=
        syntaxResource := by
    have hraw := tokenSliceBitBranchContext_formulaCodeSum_le valuation
      backwardFormula.freeVariables offset bitIndex numericBound hbackwardVars
      hoffset hbitIndexBound
    exact hraw.trans (by
      dsimp only [syntaxResource]
      unfold tokenSliceClosedTermBitBranchSyntaxPolynomial
      omega)
  have hbranchContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext branchFormula.freeVariables branchValuation) <=
        syntaxResource := by
    have hraw := tokenSliceBitBranchContext_formulaCodeSum_le valuation
      branchFormula.freeVariables offset bitIndex numericBound hbranchVars
      hoffset hbitIndexBound
    exact hraw.trans (by
      dsimp only [syntaxResource]
      unfold tokenSliceClosedTermBitBranchSyntaxPolynomial
      omega)
  have hsourceResource :
      tokenSliceAtValuationBitAtomStructuralEnvelope expected valuation
          tokenTableTerm sourceStartTerm widthTerm offset bitIndex <=
        atomResource := by
    dsimp only [atomResource]
    exact tokenSliceAtValuationBitAtomStructuralEnvelope_le_closedFixed
      expected valuation tokenTableTerm widthTerm sourceStartTerm offset
      bitIndex numericBound termCode bitBound htableClosed hwidthClosed
      hsourceClosed htableCode hwidthCode hsourceCode hwidth hsource hoffset
      hbitIndex htableSize
  have htargetResource :
      tokenSliceAtValuationBitAtomStructuralEnvelope expected valuation
          tokenTableTerm targetStartTerm widthTerm offset bitIndex <=
        atomResource := by
    dsimp only [atomResource]
    exact tokenSliceAtValuationBitAtomStructuralEnvelope_le_closedFixed
      expected valuation tokenTableTerm widthTerm targetStartTerm offset
      bitIndex numericBound termCode bitBound htableClosed hwidthClosed
      htargetClosed htableCode hwidthCode htargetCode hwidth htarget hoffset
      hbitIndex htableSize
  have hconjunctionEnvelope :=
    hybridConjunctionStructuralPayloadEnvelope_le_general branchValuation
      forwardFormula backwardFormula disjunctionResource
      disjunctionResource syntaxResource hsyntaxPositive hbranchContext
      hforwardSyntax hbackwardSyntax hbranchSyntax
  cases expected with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hforwardEnvelope :=
        transparentHybridDisjunctionLeftPayloadEnvelope_le_general
          branchValuation (∼sourceAtom) targetAtom atomResource syntaxResource
          hsyntaxPositive hforwardContext hnegSourceSyntax htargetSyntax
          hforwardSyntax
      have hbackwardEnvelope :=
        transparentHybridDisjunctionLeftPayloadEnvelope_le_general
          branchValuation (∼targetAtom) sourceAtom atomResource syntaxResource
          hsyntaxPositive hbackwardContext hnegTargetSyntax hsourceSyntax
          hbackwardSyntax
      have hforwardFixed :=
        (transparentHybridDisjunctionLeftPayloadEnvelope_mono branchValuation
          (∼sourceAtom) targetAtom hsourceResource).trans hforwardEnvelope
      have hbackwardFixed :=
        (transparentHybridDisjunctionLeftPayloadEnvelope_mono branchValuation
          (∼targetAtom) sourceAtom htargetResource).trans hbackwardEnvelope
      unfold tokenSliceAtValuationBitFalseBranchStructuralEnvelope
      dsimp only [branchValuation, sourceAtom, targetAtom, forwardFormula,
        backwardFormula, branchFormula, atomResource, syntaxResource,
        disjunctionResource] at *
      exact
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
          hforwardFixed hbackwardFixed).trans
          (hconjunctionEnvelope.trans (by
            unfold tokenSliceClosedTermBitSingleBranchFixedPayloadPolynomial
            rfl))
  | true =>
      simp only [↓reduceIte]
      have hforwardEnvelope :=
        transparentHybridDisjunctionRightPayloadEnvelope_le_general
          branchValuation (∼sourceAtom) targetAtom atomResource syntaxResource
          hsyntaxPositive hforwardContext hnegSourceSyntax htargetSyntax
          hforwardSyntax
      have hbackwardEnvelope :=
        transparentHybridDisjunctionRightPayloadEnvelope_le_general
          branchValuation (∼targetAtom) sourceAtom atomResource syntaxResource
          hsyntaxPositive hbackwardContext hnegTargetSyntax hsourceSyntax
          hbackwardSyntax
      have hforwardFixed :=
        (transparentHybridDisjunctionRightPayloadEnvelope_mono branchValuation
          (∼sourceAtom) targetAtom htargetResource).trans hforwardEnvelope
      have hbackwardFixed :=
        (transparentHybridDisjunctionRightPayloadEnvelope_mono branchValuation
          (∼targetAtom) sourceAtom hsourceResource).trans hbackwardEnvelope
      unfold tokenSliceAtValuationBitTrueBranchStructuralEnvelope
      dsimp only [branchValuation, sourceAtom, targetAtom, forwardFormula,
        backwardFormula, branchFormula, atomResource, syntaxResource,
        disjunctionResource] at *
      exact
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
          hforwardFixed hbackwardFixed).trans
          (hconjunctionEnvelope.trans (by
            unfold tokenSliceClosedTermBitSingleBranchFixedPayloadPolynomial
            rfl))

theorem tokenSliceAtValuationBitBranchStructuralEnvelope_le_closedFixed
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset bitIndex numericBound termCode bitBound : Nat)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hsourceClosed : sourceStartTerm.freeVariables = ∅)
    (htargetClosed : targetStartTerm.freeVariables = ∅)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidthCode : (binaryTermCode widthTerm).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode)
    (hwidth : termValue valuation widthTerm <= numericBound)
    (hsource : termValue valuation sourceStartTerm <= numericBound)
    (htarget : termValue valuation targetStartTerm <= numericBound)
    (hoffset : offset <= numericBound)
    (hbitIndex : bitIndex < termValue valuation widthTerm)
    (htableSize : Nat.size (termValue valuation tokenTableTerm) <= bitBound) :
    tokenSliceAtValuationBitBranchStructuralEnvelope valuation tokenTableTerm
        widthTerm sourceStartTerm targetStartTerm offset bitIndex <=
      tokenSliceClosedTermBitBranchesFixedPayloadPolynomial numericBound
        termCode bitBound := by
  have hfalse :=
    tokenSliceAtValuationBitBranchStructuralEnvelope_le_closedFixed_aux false
      valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
      bitIndex numericBound termCode bitBound htableClosed hwidthClosed
      hsourceClosed htargetClosed htableCode hwidthCode hsourceCode htargetCode
      hwidth hsource htarget hoffset hbitIndex htableSize
  have htrue :=
    tokenSliceAtValuationBitBranchStructuralEnvelope_le_closedFixed_aux true
      valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
      bitIndex numericBound termCode bitBound htableClosed hwidthClosed
      hsourceClosed htargetClosed htableCode hwidthCode hsourceCode htargetCode
      hwidth hsource htarget hoffset hbitIndex htableSize
  have hfalse' :
      tokenSliceAtValuationBitFalseBranchStructuralEnvelope valuation
          tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
          bitIndex <=
        tokenSliceClosedTermBitSingleBranchFixedPayloadPolynomial numericBound
          termCode bitBound := by
    simpa using hfalse
  have htrue' :
      tokenSliceAtValuationBitTrueBranchStructuralEnvelope valuation
          tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
          bitIndex <=
        tokenSliceClosedTermBitSingleBranchFixedPayloadPolynomial numericBound
          termCode bitBound := by
    simpa using htrue
  unfold tokenSliceAtValuationBitBranchStructuralEnvelope
    tokenSliceClosedTermBitBranchesFixedPayloadPolynomial
  omega

theorem tokenSliceAtValuationBitBranchPayloadResourceSum_le_closedFixed
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset numericBound termCode bitBound : Nat)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hsourceClosed : sourceStartTerm.freeVariables = ∅)
    (htargetClosed : targetStartTerm.freeVariables = ∅)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidthCode : (binaryTermCode widthTerm).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode)
    (hwidth : termValue valuation widthTerm <= numericBound)
    (hsource : termValue valuation sourceStartTerm <= numericBound)
    (htarget : termValue valuation targetStartTerm <= numericBound)
    (hoffset : offset <= numericBound)
    (htableSize : Nat.size (termValue valuation tokenTableTerm) <= bitBound) :
    tokenSliceAtValuationBitBranchPayloadResourceSum valuation tokenTableTerm
        widthTerm sourceStartTerm targetStartTerm offset <=
      tokenSliceClosedTermBitBranchPayloadSumFixedPolynomial numericBound
        termCode bitBound := by
  unfold tokenSliceAtValuationBitBranchPayloadResourceSum
  calc
    (∑ bitIndex : Fin (termValue valuation widthTerm),
      tokenSliceAtValuationBitBranchStructuralEnvelope valuation
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
        bitIndex) <=
      ∑ _bitIndex : Fin (termValue valuation widthTerm),
        tokenSliceClosedTermBitBranchesFixedPayloadPolynomial numericBound
          termCode bitBound := by
      apply Finset.sum_le_sum
      intro bitIndex _
      exact tokenSliceAtValuationBitBranchStructuralEnvelope_le_closedFixed
        valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm
        offset bitIndex numericBound termCode bitBound htableClosed
        hwidthClosed hsourceClosed htargetClosed htableCode hwidthCode
        hsourceCode htargetCode hwidth hsource htarget hoffset bitIndex.isLt
        htableSize
    _ = termValue valuation widthTerm *
        tokenSliceClosedTermBitBranchesFixedPayloadPolynomial numericBound
          termCode bitBound := by simp
    _ <= numericBound *
        tokenSliceClosedTermBitBranchesFixedPayloadPolynomial numericBound
          termCode bitBound :=
      Nat.mul_le_mul_right
        (tokenSliceClosedTermBitBranchesFixedPayloadPolynomial numericBound
          termCode bitBound) hwidth
    _ = tokenSliceClosedTermBitBranchPayloadSumFixedPolynomial numericBound
        termCode bitBound := by rfl

#print axioms
  tokenSliceAtValuationBitBranchStructuralEnvelope_le_closedFixed_aux
#print axioms
  tokenSliceAtValuationBitBranchStructuralEnvelope_le_closedFixed
#print axioms
  tokenSliceAtValuationBitBranchPayloadResourceSum_le_closedFixed

end FoundationCompactNumericListedDirectTokenSliceBitClosedTermBranchesFixedBounds
