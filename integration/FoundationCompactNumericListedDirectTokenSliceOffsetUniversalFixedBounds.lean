import integration.FoundationCompactNumericListedDirectTokenSliceBitUniversalFullyFixedBounds
import integration.FoundationCompactNumericListedDirectTokenSliceOffsetBodyFixedBounds
import integration.FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
import integration.FoundationCompactPATermBoundedUniversalFreeVariables

/-!
# Fixed syntax and leaf bounds for the token-slice offset universal

This module lifts the completed bit-index universal bound through the finite
offset family.  It also proves that the outer offset universal is closed.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceOffsetUniversalFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFreeFormulaVariableTransport
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPATermBoundedUniversalFreeVariables
open FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalOuterVariables
open FoundationCompactNumericListedDirectTokenSliceBitUniversalFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitBranchesFixedAssembly
open FoundationCompactNumericListedDirectTokenSliceBitUniversalFullyFixedBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetBodyFixedBounds

def tokenSliceOffsetUniversalLeafSumFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound *
    tokenSliceBitUniversalFullyFixedPayloadPolynomial numericBound bitBound

def tokenSliceOffsetUniversalBodyCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  tokenSliceOffsetBodyCodePolynomial bitBound

def tokenSliceOffsetUniversalSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound +
    tokenSliceOffsetUniversalBodyCodePolynomial numericBound bitBound

theorem tokenSliceAtValuationOffsetBranchPayloadResourceSum_le_fullyFixed
    (valuation : Nat -> Nat)
    (tokenTable width sourceStart targetStart count numericBound bitBound :
      Nat)
    (hwidth : width <= numericBound)
    (hsourceStart : sourceStart <= numericBound)
    (htargetStart : targetStart <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound) :
    tokenSliceAtValuationOffsetBranchPayloadResourceSum valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm targetStart) count <=
      tokenSliceOffsetUniversalLeafSumFixedPolynomial numericBound
        bitBound := by
  unfold tokenSliceAtValuationOffsetBranchPayloadResourceSum
    tokenSliceOffsetUniversalLeafSumFixedPolynomial
  calc
    (∑ offset : Fin count,
      tokenSliceAtValuationBitUniversalPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm targetStart) offset) ≤
        ∑ _offset : Fin count,
          tokenSliceBitUniversalFullyFixedPayloadPolynomial numericBound
            bitBound := by
      apply Finset.sum_le_sum
      intro offset _
      exact tokenSliceAtValuationBitUniversalPayloadEnvelope_le_fullyFixed
        valuation tokenTable width sourceStart targetStart offset numericBound
        bitBound hwidth hsourceStart htargetStart
        ((Nat.le_of_lt offset.isLt).trans hcount) htableSize hwidthSize
        hsourceStartSize htargetStartSize
    _ = count *
        tokenSliceBitUniversalFullyFixedPayloadPolynomial numericBound
          bitBound := by
      simp
    _ ≤ numericBound *
        tokenSliceBitUniversalFullyFixedPayloadPolynomial numericBound
          bitBound :=
      Nat.mul_le_mul_right
        (tokenSliceBitUniversalFullyFixedPayloadPolynomial numericBound
          bitBound) hcount

theorem tokenSliceAtValuationOffsetUniversal_freeVariables_eq_empty
    (tokenTable width sourceStart targetStart count : Nat) :
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm count))
      (tokenSliceAtValuationOffsetBody
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm targetStart))).freeVariables = ∅ := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let sourceTerm := shortBinaryNumeralTerm sourceStart
  let targetTerm := shortBinaryNumeralTerm targetStart
  let body := tokenSliceAtValuationOffsetBody tableTerm widthTerm sourceTerm
    targetTerm
  have hsource :
      (tokenSliceAtValuationBitAtom tableTerm sourceTerm
        widthTerm).freeVariables ⊆ {0, 1} := by
    simpa only [tableTerm, sourceTerm, widthTerm] using
      tokenSliceBitAtom_freeVariables_subset tokenTable width sourceStart
  have htarget :
      (tokenSliceAtValuationBitAtom tableTerm targetTerm
        widthTerm).freeVariables ⊆ {0, 1} := by
    simpa only [tableTerm, targetTerm, widthTerm] using
      tokenSliceBitAtom_freeVariables_subset tokenTable width targetStart
  have hwidthClosed : (Rew.shift widthTerm).freeVariables ⊆ {0} := by
    have hclosed : widthTerm.freeVariables = ∅ := by
      dsimp only [widthTerm]
      exact shortBinaryNumeralTerm_freeVariables_eq_empty width
    rw [shiftedTerm_freeVariables_eq_empty_of_closed widthTerm hclosed]
    simp
  have hopened :
      (Rewriting.free body).freeVariables ⊆ {0} := by
    rw [tokenSliceAtValuationOffsetBody_free_alignment]
    exact
      tokenSliceAtValuationBitUniversalOuterVariables_subset_singleton_of_atoms
        tableTerm widthTerm sourceTerm targetTerm (Rew.shift widthTerm)
        hwidthClosed hsource htarget
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
  tokenSliceAtValuationOffsetBranchPayloadResourceSum_le_fullyFixed
#print axioms
  tokenSliceAtValuationOffsetUniversal_freeVariables_eq_empty

end FoundationCompactNumericListedDirectTokenSliceOffsetUniversalFixedBounds
