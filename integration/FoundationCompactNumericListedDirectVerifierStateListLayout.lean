import integration.FoundationCompactNumericListedDirectVerifierStateLayout

/-!
# Direct row layouts for complete verifier-state traces

The canonical structured-list table stores every public verifier state in one
shared fixed-width token table.  Its boundary table therefore gives the exact
slice used by row `i`, so consecutive verifier steps refer to the same middle
state rather than to unrelated copies in separate tables.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStateListLayout

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectStructuredListCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierStateLayout

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierStateAdditiveCodec

def CompactNumericVerifierStateListRowLayouts
    (tokenTable width tokenCount boundaryTable : Nat)
    (states : List CompactNumericVerifierState) : Prop :=
  CompactAdditiveStructuredListElementRowLayouts
    CompactNumericVerifierStateDirectLayout tokenTable width tokenCount
    boundaryTable states

def compactNumericVerifierStateBoundaryTable
    (tokenCount bodyStart : Nat)
    (states : List CompactNumericVerifierState) : Nat :=
  compactAdditiveStructuredListElementBoundaryTable
    tokenCount bodyStart states

theorem compactNumericVerifierStateListRows_canonical
    (frontTokens : List Nat) (states : List CompactNumericVerifierState)
    (backTokens : List Nat) :
    let listTokens := compactAdditiveEncode states
    let tokens := frontTokens ++ listTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let bodyStart := start + 1
    let finish := start + listTokens.length
    let boundaryTable :=
      compactNumericVerifierStateBoundaryTable
        tokens.length bodyStart states
    CompactAdditiveStructuredListLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length start states.length finish boundaryTable ∧
      CompactNumericVerifierStateListRowLayouts
        (compactFixedWidthTableCode width tokens)
        width tokens.length boundaryTable states ∧
      Nat.size boundaryTable ≤ (states.length + 1) * tokens.length := by
  simpa [CompactNumericVerifierStateListRowLayouts,
    compactNumericVerifierStateBoundaryTable] using
    compactAdditiveStructuredListElementLayouts_canonical
      CompactNumericVerifierStateDirectLayout
      compactNumericVerifierStateDirectLayout_canonical
      frontTokens states backTokens

#print axioms compactNumericVerifierStateListRows_canonical

end FoundationCompactNumericListedDirectVerifierStateListLayout
