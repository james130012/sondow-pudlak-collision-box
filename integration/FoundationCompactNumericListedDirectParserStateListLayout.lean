import integration.FoundationCompactNumericListedDirectParserStateLayout

/-!
# Direct row layouts for lists of compact parser states

The generic structured-list construction is instantiated with the complete
parser-state layout.  Its one canonical boundary table therefore delimits the
real additive encoding of every state and carries all state fields row by row.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserStateListLayout

open FoundationCompactAdditiveTokenCodec
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectStructuredListCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectParserStateLayout

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

def CompactUnifiedParserStateListRowLayouts
    (tokenTable width tokenCount boundaryTable : Nat)
    (states : List CompactUnifiedParserState) : Prop :=
  CompactAdditiveStructuredListElementRowLayouts
    CompactUnifiedParserStateDirectLayout tokenTable width tokenCount
    boundaryTable states

def compactUnifiedParserStateBoundaryTable
    (tokenCount bodyStart : Nat)
    (states : List CompactUnifiedParserState) : Nat :=
  compactAdditiveStructuredListElementBoundaryTable
    tokenCount bodyStart states

theorem compactUnifiedParserStateListDirectLayout_canonical
    (frontTokens : List Nat) (states : List CompactUnifiedParserState)
    (backTokens : List Nat) :
    let listTokens := compactAdditiveEncode states
    let tokens := frontTokens ++ listTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let bodyStart := start + 1
    let finish := start + listTokens.length
    let boundaryTable :=
      compactUnifiedParserStateBoundaryTable
        tokens.length bodyStart states
    CompactAdditiveStructuredListLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length start states.length finish boundaryTable ∧
      CompactUnifiedParserStateListRowLayouts
        (compactFixedWidthTableCode width tokens)
        width tokens.length boundaryTable states ∧
      Nat.size boundaryTable ≤ (states.length + 1) * tokens.length := by
  simpa [CompactUnifiedParserStateListRowLayouts,
    compactUnifiedParserStateBoundaryTable] using
    compactAdditiveStructuredListElementLayouts_canonical
      CompactUnifiedParserStateDirectLayout
      compactUnifiedParserStateDirectLayout_canonical
      frontTokens states backTokens

#print axioms compactUnifiedParserStateListDirectLayout_canonical

end FoundationCompactNumericListedDirectParserStateListLayout
