import integration.FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermBodyFixedBounds
import integration.FoundationCompactPATermBoundedUniversalFreeVariables

/-!
# Offset-universal leaves over arbitrary closed token-slice starts

The completed closed-term bit universal is summed over the short offset
range, and the resulting outer formula is proved closed.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermUniversalFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFreeFormulaVariableTransport
open FoundationCompactPATermBoundedUniversalFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceBitAtomClosedTermFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalOuterVariables
open FoundationCompactNumericListedDirectTokenSliceBitClosedTermUniversalEndpointFixedBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermBodyFixedBounds

def tokenSliceClosedTermOffsetUniversalLeafSumFixedPolynomial
    (numericBound termCode bitBound : Nat) : Nat :=
  numericBound *
    tokenSliceClosedTermBitUniversalFullyFixedPayloadPolynomial numericBound
      termCode bitBound

def tokenSliceClosedTermOffsetUniversalBodyCodePolynomial
    (termCode : Nat) : Nat :=
  tokenSliceClosedTermOffsetBodyCodePolynomial termCode

def tokenSliceClosedTermOffsetUniversalSyntaxFixedPolynomial
    (numericBound termCode : Nat) : Nat :=
  numericBound +
    tokenSliceClosedTermOffsetUniversalBodyCodePolynomial termCode

theorem
    tokenSliceAtValuationOffsetBranchPayloadResourceSum_le_closedFixed
    (valuation : Nat -> Nat)
    (tokenTable width count numericBound termCode bitBound : Nat)
    (sourceStartTerm targetStartTerm : ValuationTerm)
    (hsourceClosed : sourceStartTerm.freeVariables = ∅)
    (htargetClosed : targetStartTerm.freeVariables = ∅)
    (htableCode :
      (binaryTermCode (shortBinaryNumeralTerm tokenTable)).length <= termCode)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode)
    (hwidth : width <= numericBound)
    (hsource : termValue valuation sourceStartTerm <= numericBound)
    (htarget : termValue valuation targetStartTerm <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound) :
    tokenSliceAtValuationOffsetBranchPayloadResourceSum valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        sourceStartTerm targetStartTerm count <=
      tokenSliceClosedTermOffsetUniversalLeafSumFixedPolynomial numericBound
        termCode bitBound := by
  unfold tokenSliceAtValuationOffsetBranchPayloadResourceSum
    tokenSliceClosedTermOffsetUniversalLeafSumFixedPolynomial
  calc
    (∑ offset : Fin count,
      tokenSliceAtValuationBitUniversalPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        sourceStartTerm targetStartTerm offset) <=
      ∑ _offset : Fin count,
        tokenSliceClosedTermBitUniversalFullyFixedPayloadPolynomial
          numericBound termCode bitBound := by
      apply Finset.sum_le_sum
      intro offset _
      exact
        tokenSliceAtValuationBitUniversalPayloadEnvelope_le_closedFixed
          valuation tokenTable width offset numericBound termCode bitBound
          sourceStartTerm targetStartTerm hsourceClosed htargetClosed
          htableCode hwidthCode hsourceCode htargetCode hwidth hsource htarget
          ((Nat.le_of_lt offset.isLt).trans hcount) htableSize hwidthSize
    _ = count *
        tokenSliceClosedTermBitUniversalFullyFixedPayloadPolynomial
          numericBound termCode bitBound := by simp
    _ <= numericBound *
        tokenSliceClosedTermBitUniversalFullyFixedPayloadPolynomial
          numericBound termCode bitBound :=
      Nat.mul_le_mul_right
        (tokenSliceClosedTermBitUniversalFullyFixedPayloadPolynomial
          numericBound termCode bitBound) hcount

theorem tokenSliceAtValuationOffsetUniversal_freeVariables_eq_empty_closed
    (tokenTable width count : Nat)
    (sourceStartTerm targetStartTerm : ValuationTerm)
    (hsourceClosed : sourceStartTerm.freeVariables = ∅)
    (htargetClosed : targetStartTerm.freeVariables = ∅) :
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm count))
      (tokenSliceAtValuationOffsetBody
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        sourceStartTerm targetStartTerm)).freeVariables = ∅ := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let body := tokenSliceAtValuationOffsetBody tableTerm widthTerm
    sourceStartTerm targetStartTerm
  have htableClosed : tableTerm.freeVariables = ∅ := by
    dsimp only [tableTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hwidthTermClosed : widthTerm.freeVariables = ∅ := by
    dsimp only [widthTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  have hsource :
      (tokenSliceAtValuationBitAtom tableTerm sourceStartTerm
        widthTerm).freeVariables ⊆ {0, 1} :=
    tokenSliceClosedTermBitAtom_freeVariables_subset tableTerm widthTerm
      sourceStartTerm htableClosed hwidthTermClosed hsourceClosed
  have htarget :
      (tokenSliceAtValuationBitAtom tableTerm targetStartTerm
        widthTerm).freeVariables ⊆ {0, 1} :=
    tokenSliceClosedTermBitAtom_freeVariables_subset tableTerm widthTerm
      targetStartTerm htableClosed hwidthTermClosed htargetClosed
  have hwidthClosed : (Rew.shift widthTerm).freeVariables ⊆ {0} := by
    rw [shiftedTerm_freeVariables_eq_empty_of_closed widthTerm
      hwidthTermClosed]
    simp
  have hopened : (Rewriting.free body).freeVariables ⊆ {0} := by
    rw [tokenSliceAtValuationOffsetBody_free_alignment]
    exact
      tokenSliceAtValuationBitUniversalOuterVariables_subset_singleton_of_atoms
        tableTerm widthTerm sourceStartTerm targetStartTerm
        (Rew.shift widthTerm) hwidthClosed hsource htarget
  have hbodyClosed : body.freeVariables = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro coordinate hcoordinate
    have hopenedCoordinate :=
      freeFormula_succ_mem_of_mem body coordinate hcoordinate
    have hzero := hopened hopenedCoordinate
    simp only [Finset.mem_singleton] at hzero
    omega
  have hboundClosed :
      (Rew.bShift (shortBinaryNumeralTerm count) :
        LO.FirstOrder.ArithmeticSemiterm Nat 1).freeVariables ⊆ ∅ := by
    rw [bShiftTerm_freeVariables_eq,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
  apply Finset.Subset.antisymm
  · exact termBoundedUniversal_freeVariables_subset _ _ ∅ hboundClosed
      (by rw [hbodyClosed])
  · simp

#print axioms
  tokenSliceAtValuationOffsetBranchPayloadResourceSum_le_closedFixed
#print axioms
  tokenSliceAtValuationOffsetUniversal_freeVariables_eq_empty_closed

end FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermUniversalFixedBounds
