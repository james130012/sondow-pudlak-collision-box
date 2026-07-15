import integration.FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefix
import integration.FoundationCompactNumericListedDirectNatListAppendOneValue
import integration.FoundationCompactNumericListedDirectFormulaTransformStateAtRows
import integration.FoundationCompactNumericListedDirectParserSyntaxStepFormula

/-!
# Direct output-update primitives for formula transformations

These relations connect the parser-token and emitted-output fields already
exposed by formula-transform state rows.  Every relation has an exact typed
list semantics; no executable transformation is used as an opaque predicate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives

open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAppendSourcePrefix
open FoundationCompactNumericListedDirectNatListAppendTwoValues
open FoundationCompactNumericListedDirectNatListAppendOneValue
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefix

theorem compactUnifiedParserStateFixedLayout_tokensDirectLayout
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactUnifiedParserStateRowCoordinates}
    {state : FoundationCompactParserDirectTrace.CompactUnifiedParserState}
    (hlayout : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount coordinates state) :
    CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      coordinates.start coordinates.tokensFinish state.1 := by
  refine ⟨coordinates.tokensBoundary, ?_, hlayout.tokensRows, ?_⟩
  · simpa only [hlayout.tokensCount_eq] using hlayout.tokensLayout
  · simpa only [hlayout.tokensCount_eq] using hlayout.tokensBoundarySize

theorem compactFormulaTransformStateFixedLayout_outputDirectLayout
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactFormulaTransformStateRowCoordinates}
    {state : CompactFormulaTransformState}
    (hlayout : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount coordinates state) :
    CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      coordinates.parserFinish coordinates.finish state.2 := by
  refine ⟨coordinates.outputBoundary, ?_, hlayout.outputRows, ?_⟩
  · simpa only [hlayout.outputCount_eq] using hlayout.outputLayout
  · simpa only [hlayout.outputCount_eq] using hlayout.outputBoundarySize

def CompactFormulaTransformOutputSameRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates) : Prop :=
  CompactAdditiveNatListSameRows tokenTable width tokenCount
    current.outputBoundary current.outputCount
    next.outputBoundary next.outputCount

def CompactFormulaTransformOutputRawPrefixRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (consumedCount : Nat) : Prop :=
  CompactAdditiveNatListAppendSourcePrefix tokenTable width tokenCount
    current.parserFinish current.finish current.outputCount
    current.parser.start current.parser.tokensFinish
      current.parser.tokensCount consumedCount
    next.parserFinish next.finish next.outputCount

def CompactFormulaTransformOutputTwoValuesRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (first second : Nat) : Prop :=
  CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
    current.parserFinish current.finish current.outputCount
    next.parserFinish next.finish next.outputBoundary next.outputCount
    first second

def CompactFormulaTransformOutputOneValueRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (value : Nat) : Prop :=
  CompactAdditiveNatListAppendOneValue tokenTable width tokenCount
    current.parserFinish current.finish current.outputCount
    next.parserFinish next.finish next.outputBoundary next.outputCount value

def CompactFormulaTransformOutputWitnessRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (witnessStart witnessFinish witnessCount : Nat) : Prop :=
  CompactAdditiveNatListAppendSlices tokenTable width tokenCount
    current.parserFinish current.finish current.outputCount
    witnessStart witnessFinish witnessCount
    next.parserFinish next.finish next.outputCount

def CompactFormulaTransformOutputMappedPrefixRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (consumedCount mappedHead : Nat) : Prop :=
  CompactAdditiveNatListAppendMappedSourcePrefix tokenTable width tokenCount
    current.parserFinish current.finish current.outputCount
    current.parser.start current.parser.tokensFinish
      current.parser.tokensCount consumedCount
    next.parserFinish next.finish next.outputBoundary next.outputCount
    mappedHead

def CompactNegationFormulaTagGraph (tag mapped : Nat) : Prop :=
  (tag < 8 ∧
    ((∃ pair < 4, tag = 2 * pair ∧ mapped = tag + 1) ∨
     (∃ pair < 4, tag = 2 * pair + 1 ∧ tag = mapped + 1))) ∨
  (8 ≤ tag ∧ mapped = tag)

def compactNegationFormulaTagGraphDef : 𝚺₀.Semisentence 2 := .mkSigma
  “tag mapped.
    (tag < 8 ∧
      ((∃ pair < 4, tag = 2 * pair ∧ mapped = tag + 1) ∨
       (∃ pair < 4, tag = 2 * pair + 1 ∧ tag = mapped + 1))) ∨
    (8 ≤ tag ∧ mapped = tag)”

@[simp] theorem compactNegationFormulaTagGraphDef_spec
    (tag mapped : Nat) :
    compactNegationFormulaTagGraphDef.val.Evalb ![tag, mapped] ↔
      CompactNegationFormulaTagGraph tag mapped := by
  simp [compactNegationFormulaTagGraphDef,
    CompactNegationFormulaTagGraph]
  rfl

theorem compactNegationFormulaTagGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNegationFormulaTagGraphDef.val := by
  simp [compactNegationFormulaTagGraphDef]

theorem compactNegationFormulaTagGraph_iff
    (tag mapped : Nat) :
    CompactNegationFormulaTagGraph tag mapped ↔
      mapped =
        FoundationCompactNumericFormulaNegation.compactNegationFormulaTag
          tag := by
  constructor
  · rintro (⟨hsmall, heven | hodd⟩ | ⟨hlarge, hmapped⟩)
    · rcases heven with ⟨pair, hpair, htag, hmapped⟩
      have hpairs : pair = 0 ∨ pair = 1 ∨ pair = 2 ∨ pair = 3 := by
        omega
      rcases hpairs with rfl | rfl | rfl | rfl <;>
        simp_all [FoundationCompactNumericFormulaNegation.compactNegationFormulaTag]
    · rcases hodd with ⟨pair, hpair, htag, hmapped⟩
      have hpairs : pair = 0 ∨ pair = 1 ∨ pair = 2 ∨ pair = 3 := by
        omega
      rcases hpairs with rfl | rfl | rfl | rfl <;>
        simp_all [FoundationCompactNumericFormulaNegation.compactNegationFormulaTag]
    · have hzero : tag ≠ 0 := by omega
      have hone : tag ≠ 1 := by omega
      have htwo : tag ≠ 2 := by omega
      have hthree : tag ≠ 3 := by omega
      have hfour : tag ≠ 4 := by omega
      have hfive : tag ≠ 5 := by omega
      have hsix : tag ≠ 6 := by omega
      have hseven : tag ≠ 7 := by omega
      simpa [FoundationCompactNumericFormulaNegation.compactNegationFormulaTag,
        hzero, hone, htwo, hthree, hfour, hfive, hsix, hseven] using
          hmapped
  · intro hmapped
    by_cases hsmall : tag < 8
    · have htags : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨
          tag = 4 ∨ tag = 5 ∨ tag = 6 ∨ tag = 7 := by
        omega
      rcases htags with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine Or.inl ⟨by omega, Or.inl ⟨0, by omega, rfl, ?_⟩⟩
        simpa [FoundationCompactNumericFormulaNegation.compactNegationFormulaTag]
          using hmapped
      · refine Or.inl ⟨by omega, Or.inr ⟨0, by omega, rfl, ?_⟩⟩
        simpa [FoundationCompactNumericFormulaNegation.compactNegationFormulaTag]
          using hmapped
      · refine Or.inl ⟨by omega, Or.inl ⟨1, by omega, rfl, ?_⟩⟩
        simpa [FoundationCompactNumericFormulaNegation.compactNegationFormulaTag]
          using hmapped
      · refine Or.inl ⟨by omega, Or.inr ⟨1, by omega, rfl, ?_⟩⟩
        simpa [FoundationCompactNumericFormulaNegation.compactNegationFormulaTag]
          using hmapped
      · refine Or.inl ⟨by omega, Or.inl ⟨2, by omega, rfl, ?_⟩⟩
        simpa [FoundationCompactNumericFormulaNegation.compactNegationFormulaTag]
          using hmapped
      · refine Or.inl ⟨by omega, Or.inr ⟨2, by omega, rfl, ?_⟩⟩
        simpa [FoundationCompactNumericFormulaNegation.compactNegationFormulaTag]
          using hmapped
      · refine Or.inl ⟨by omega, Or.inl ⟨3, by omega, rfl, ?_⟩⟩
        simpa [FoundationCompactNumericFormulaNegation.compactNegationFormulaTag]
          using hmapped
      · refine Or.inl ⟨by omega, Or.inr ⟨3, by omega, rfl, ?_⟩⟩
        simpa [FoundationCompactNumericFormulaNegation.compactNegationFormulaTag]
          using hmapped
    · exact Or.inr ⟨by omega, by
        simpa [FoundationCompactNumericFormulaNegation.compactNegationFormulaTag,
          show tag ≠ 0 by omega, show tag ≠ 1 by omega,
          show tag ≠ 2 by omega, show tag ≠ 3 by omega,
          show tag ≠ 4 by omega, show tag ≠ 5 by omega,
          show tag ≠ 6 by omega, show tag ≠ 7 by omega] using hmapped⟩

theorem compactFormulaTransformOutputSameRows_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    CompactFormulaTransformOutputSameRows tokenTable width tokenCount
        currentCoordinates nextCoordinates ↔
      next.2 = current.2 := by
  have hrows := compactAdditiveNatListSameRows_iff_eq_of_rows
    hcurrent.outputRows hnext.outputRows
  simpa [CompactFormulaTransformOutputSameRows,
    hcurrent.outputCount_eq, hnext.outputCount_eq] using hrows

theorem compactFormulaTransformOutputRawPrefixRows_iff
    {tokenTable width tokenCount consumedCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    CompactFormulaTransformOutputRawPrefixRows tokenTable width tokenCount
        currentCoordinates nextCoordinates consumedCount ↔
      consumedCount ≤ current.1.1.length ∧
        next.2 = current.2 ++ current.1.1.take consumedCount := by
  have hiff := compactAdditiveNatListAppendSourcePrefix_iff
    (prefixCount := consumedCount)
    (compactFormulaTransformStateFixedLayout_outputDirectLayout hcurrent)
    (compactUnifiedParserStateFixedLayout_tokensDirectLayout
      hcurrent.parserLayout)
    (compactFormulaTransformStateFixedLayout_outputDirectLayout hnext)
  simpa [CompactFormulaTransformOutputRawPrefixRows,
    hcurrent.outputCount_eq, hnext.outputCount_eq,
    hcurrent.parserLayout.tokensCount_eq] using hiff

theorem compactFormulaTransformOutputTwoValuesRows_iff
    {tokenTable width tokenCount first second : Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    CompactFormulaTransformOutputTwoValuesRows tokenTable width tokenCount
        currentCoordinates nextCoordinates first second ↔
      next.2 = current.2 ++ [first, second] := by
  have hiff := compactAdditiveNatListAppendTwoValues_iff
    (first := first) (second := second)
    (compactFormulaTransformStateFixedLayout_outputDirectLayout hcurrent)
    (compactFormulaTransformStateFixedLayout_outputDirectLayout hnext)
    hnext.outputRows
  simpa [CompactFormulaTransformOutputTwoValuesRows,
    hcurrent.outputCount_eq, hnext.outputCount_eq] using hiff

theorem compactFormulaTransformOutputOneValueRows_iff
    {tokenTable width tokenCount value : Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    CompactFormulaTransformOutputOneValueRows tokenTable width tokenCount
        currentCoordinates nextCoordinates value ↔
      next.2 = current.2 ++ [value] := by
  have hiff := compactAdditiveNatListAppendOneValue_iff
    (value := value)
    (compactFormulaTransformStateFixedLayout_outputDirectLayout hcurrent)
    (compactFormulaTransformStateFixedLayout_outputDirectLayout hnext)
    hnext.outputRows
  simpa [CompactFormulaTransformOutputOneValueRows,
    hcurrent.outputCount_eq, hnext.outputCount_eq] using hiff

theorem compactFormulaTransformOutputWitnessRows_iff
    {tokenTable width tokenCount witnessStart witnessFinish : Nat}
    {witness : List Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness) :
    CompactFormulaTransformOutputWitnessRows tokenTable width tokenCount
        currentCoordinates nextCoordinates
          witnessStart witnessFinish witness.length ↔
      next.2 = current.2 ++ witness := by
  have hiff := compactAdditiveNatListAppendSlices_iff_append
    (compactFormulaTransformStateFixedLayout_outputDirectLayout hcurrent)
    hwitness
    (compactFormulaTransformStateFixedLayout_outputDirectLayout hnext)
  simpa [CompactFormulaTransformOutputWitnessRows,
    hcurrent.outputCount_eq, hnext.outputCount_eq] using hiff

theorem compactFormulaTransformOutputMappedPrefixRows_iff
    {tokenTable width tokenCount consumedCount mappedHead : Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    CompactFormulaTransformOutputMappedPrefixRows tokenTable width tokenCount
        currentCoordinates nextCoordinates consumedCount mappedHead ↔
      1 ≤ consumedCount ∧
        consumedCount ≤ current.1.1.length ∧
        next.2 = current.2 ++
          (mappedHead :: (current.1.1.take consumedCount).drop 1) := by
  have hiff := compactAdditiveNatListAppendMappedSourcePrefix_iff
    (prefixCount := consumedCount) (mappedHead := mappedHead)
    (compactFormulaTransformStateFixedLayout_outputDirectLayout hcurrent)
    (compactUnifiedParserStateFixedLayout_tokensDirectLayout
      hcurrent.parserLayout)
    (compactFormulaTransformStateFixedLayout_outputDirectLayout hnext)
    hnext.outputRows
  simpa [CompactFormulaTransformOutputMappedPrefixRows,
    hcurrent.outputCount_eq, hnext.outputCount_eq,
    hcurrent.parserLayout.tokensCount_eq] using hiff

#print axioms compactUnifiedParserStateFixedLayout_tokensDirectLayout
#print axioms compactFormulaTransformStateFixedLayout_outputDirectLayout
#print axioms compactNegationFormulaTagGraphDef_spec
#print axioms compactNegationFormulaTagGraphDef_sigmaZero
#print axioms compactNegationFormulaTagGraph_iff
#print axioms compactFormulaTransformOutputSameRows_iff
#print axioms compactFormulaTransformOutputRawPrefixRows_iff
#print axioms compactFormulaTransformOutputTwoValuesRows_iff
#print axioms compactFormulaTransformOutputOneValueRows_iff
#print axioms compactFormulaTransformOutputWitnessRows_iff
#print axioms compactFormulaTransformOutputMappedPrefixRows_iff

end FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
