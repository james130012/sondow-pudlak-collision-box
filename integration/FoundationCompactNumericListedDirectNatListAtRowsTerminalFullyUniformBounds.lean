import integration.FoundationCompactNumericListedDirectNatListAtRowsTerminalFixedChildrenBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsTerminalSyntaxFixedBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Data-independent resource bound for a row-lookup terminal

The two row values are used only to build the real certificate.  Their payload
resources and the two conjunction shells are bounded uniformly, so the public
envelope no longer contains either witness value.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAtRowsTerminalFullyUniformBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsTerminalSyntaxFixedBounds
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation

private theorem arithmeticAddTerm_eq_func_uniformTerminal
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem binaryFunctionTerm_freeVariables_uniformTerminal
    {boundArity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ArithmeticSemiterm Nat boundArity) :
    (LO.FirstOrder.Semiterm.func functionSymbol
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem arithmeticOneTerm_freeVariables_eq_empty_uniformTerminal
    {boundArity : Nat} :
    (‘1’ : ArithmeticSemiterm Nat boundArity).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem termValue_arithmeticAdd_uniformTerminal
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_uniformTerminal]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_uniformTerminal
    (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem binaryFormulaCode_left_length_le_and_uniformTerminal
    {arity : Nat} (left right : ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_length_le_and_uniformTerminal
    {arity : Nat} (left right : ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def natListAtRowsUniformEntryPayload
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate indexTerm
        numericBound bitBound))

def natListAtRowsInstalledTerminalSyntaxResource (bitBound : Nat) : Nat :=
  natListAtRowsInstalledTerminalCodePolynomial bitBound + 1

def compactAdditiveNatListAtRowsTerminalFullyUniformPayloadPolynomial
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  let successorTerm := natListAtSuccessorTermAtValuationIndex indexTerm
  let syntaxResource := natListAtRowsInstalledTerminalSyntaxResource bitBound
  let leftResource :=
    natListAtRowsUniformEntryPayload indexTerm numericBound bitBound
  let rightResource :=
    natListAtRowsUniformEntryPayload successorTerm numericBound bitBound
  let cellResource :=
    additiveTokenCellFullyUniformPayloadPolynomial numericBound bitBound
  hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
    (hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
      cellResource)

theorem
    compactAdditiveNatListAtRowsTerminalCertificate_structuralPayloadBound_le_fullyUniform
    (tokenTable width tokenCount boundaryTable count index value numericBound
      bitBound : Nat)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (hindex : index < count)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hindexSize : Nat.size index <= bitBound)
    (hvalueSize : Nat.size value <= bitBound) :
    let values : Fin 2 -> Nat := ![data.right, data.left]
    let terminalParts :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm index)
          (shortBinaryNumeralTerm data.left) (by
            simpa [termValue_shortBinaryNumeralTerm] using data.left_entry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (natListAtSuccessorTermAtValuationIndex
              (shortBinaryNumeralTerm index))
            (shortBinaryNumeralTerm data.right) (by
              simpa [natListAtSuccessorTermAtValuationIndex,
                termValue_shortBinaryNumeralTerm,
                termValue_arithmeticAdd_uniformTerminal,
                termValue_arithmeticOne_uniformTerminal] using
                  data.right_entry))
          (compactAdditiveTokenCellExplicitHybridCertificate tokenTable width
            tokenCount data.left value data.right data.cell))
    let terminal : CheckedHybridValuationBoundedFormulaCertificate
        atRowsZeroValuation
        ((compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
          tokenCount boundaryTable value (shortBinaryNumeralTerm index)) ⇜
          fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
      .cast (by
        have hvalueTerms :
            (fun coordinate : Fin 2 =>
              shortBinaryNumeralTerm (values coordinate)) =
              ![shortBinaryNumeralTerm data.right,
                shortBinaryNumeralTerm data.left] := by
          funext coordinate
          fin_cases coordinate <;> rfl
        rw [hvalueTerms]
        exact
          (compactAdditiveNatListAtRowsTerminalAtValuationIndex_substitution_alignment
            tokenTable width tokenCount boundaryTable value data.left
            data.right (shortBinaryNumeralTerm index)).symm) terminalParts
    hybridFormulaStructuralPayloadBound terminal <=
      compactAdditiveNatListAtRowsTerminalFullyUniformPayloadPolynomial
        (shortBinaryNumeralTerm index) numericBound bitBound := by
  dsimp only
  let indexTerm : ValuationTerm := shortBinaryNumeralTerm index
  let successorTerm := natListAtSuccessorTermAtValuationIndex indexTerm
  let leftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount) indexTerm
    (shortBinaryNumeralTerm data.left)
  let rightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount) successorTerm
    (shortBinaryNumeralTerm data.right)
  let cellFormula := compactAdditiveTokenCellClosedFormula tokenTable width
    tokenCount data.left value data.right
  let leftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm data.left) (by
        simpa [indexTerm, termValue_shortBinaryNumeralTerm] using
          data.left_entry)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) successorTerm
      (shortBinaryNumeralTerm data.right) (by
        simpa [successorTerm, indexTerm,
          natListAtSuccessorTermAtValuationIndex,
          termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd_uniformTerminal,
          termValue_arithmeticOne_uniformTerminal] using data.right_entry)
  let cellCertificate := compactAdditiveTokenCellExplicitHybridCertificate
    tokenTable width tokenCount data.left value data.right data.cell
  let syntaxResource := natListAtRowsInstalledTerminalSyntaxResource bitBound
  let leftResource :=
    natListAtRowsUniformEntryPayload indexTerm numericBound bitBound
  let rightResource :=
    natListAtRowsUniformEntryPayload successorTerm numericBound bitBound
  let cellResource :=
    additiveTokenCellFullyUniformPayloadPolynomial numericBound bitBound
  have hleftSize : Nat.size data.left <= bitBound :=
    (Nat.size_le_size data.left_le).trans htokenCountSize
  have hrightSize : Nat.size data.right <= bitBound :=
    (Nat.size_le_size data.right_le).trans htokenCountSize
  have hindexValue : index <= numericBound :=
    (Nat.le_of_lt hindex).trans hcountValue
  have hsuccessorValue : index + 1 <= numericBound :=
    (Nat.succ_le_iff.mpr hindex).trans hcountValue
  have hsuccessorSize : Nat.size (index + 1) <= bitBound :=
    (Nat.size_le_size (Nat.succ_le_iff.mpr hindex)).trans hcountSize
  have hleft : hybridFormulaStructuralPayloadBound leftCertificate <=
      leftResource := by
    simpa only [leftCertificate, leftResource, indexTerm,
      natListAtRowsUniformEntryPayload] using
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
        atRowsZeroValuation boundaryTable tokenCount data.left indexTerm
        numericBound bitBound htokenCountValue (by
          simpa only [indexTerm, termValue_shortBinaryNumeralTerm] using
            hindexValue) (by simp)
        hboundarySize htokenCountSize (by
          simpa only [indexTerm, termValue_shortBinaryNumeralTerm] using
            hindexSize) hleftSize (by
          rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
          simp) (by
            simpa only [indexTerm, termValue_shortBinaryNumeralTerm] using
              data.left_entry)
  have hright : hybridFormulaStructuralPayloadBound rightCertificate <=
      rightResource := by
    simpa only [rightCertificate, rightResource,
      natListAtRowsUniformEntryPayload, successorTerm, indexTerm,
      natListAtSuccessorTermAtValuationIndex,
      termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd_uniformTerminal,
      termValue_arithmeticOne_uniformTerminal] using
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
        atRowsZeroValuation boundaryTable tokenCount data.right successorTerm
        numericBound bitBound htokenCountValue (by
          simpa only [successorTerm, indexTerm,
            natListAtSuccessorTermAtValuationIndex,
            termValue_shortBinaryNumeralTerm,
            termValue_arithmeticAdd_uniformTerminal,
            termValue_arithmeticOne_uniformTerminal] using hsuccessorValue)
        (by simp)
        hboundarySize htokenCountSize (by
          simpa only [successorTerm, indexTerm,
            natListAtSuccessorTermAtValuationIndex,
            termValue_shortBinaryNumeralTerm,
            termValue_arithmeticAdd_uniformTerminal,
            termValue_arithmeticOne_uniformTerminal] using hsuccessorSize)
        hrightSize (by
          dsimp only [successorTerm, indexTerm]
          unfold natListAtSuccessorTermAtValuationIndex
          rw [arithmeticAddTerm_eq_func_uniformTerminal,
            binaryFunctionTerm_freeVariables_uniformTerminal,
            shortBinaryNumeralTerm_freeVariables_eq_empty,
            arithmeticOneTerm_freeVariables_eq_empty_uniformTerminal]
          simp) (by
            simpa only [successorTerm, indexTerm,
              natListAtSuccessorTermAtValuationIndex,
              termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd_uniformTerminal,
              termValue_arithmeticOne_uniformTerminal] using data.right_entry)
  have hcell : hybridFormulaStructuralPayloadBound cellCertificate <=
      cellResource := by
    change hybridFormulaStructuralPayloadBound
      (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm data.left)
        (shortBinaryNumeralTerm value)
        (shortBinaryNumeralTerm data.right) (by
          simpa only [termValue_shortBinaryNumeralTerm] using data.cell)) <=
        cellResource
    simpa only [cellResource] using
      compactAdditiveTokenCellShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount data.left value data.right numericBound
        bitBound hwidthValue (data.left_le.trans htokenCountValue) htableSize
        hwidthSize htokenCountSize hleftSize hvalueSize hrightSize data.cell
  have hleftClosed : leftFormula.freeVariables = ∅ := by
    dsimp only [leftFormula, indexTerm]
    unfold compactFixedWidthEntryAtValuationFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      apply shortBinaryNumeralTerm_freeVariables_eq_empty
  have hsuccessorClosed : successorTerm.freeVariables = ∅ := by
    dsimp only [successorTerm, indexTerm]
    unfold natListAtSuccessorTermAtValuationIndex
    rw [arithmeticAddTerm_eq_func_uniformTerminal,
      binaryFunctionTerm_freeVariables_uniformTerminal,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty_uniformTerminal]
    simp
  have hrightClosed : rightFormula.freeVariables = ∅ := by
    dsimp only [rightFormula]
    unfold compactFixedWidthEntryAtValuationFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate
    · apply shortBinaryNumeralTerm_freeVariables_eq_empty
    · apply shortBinaryNumeralTerm_freeVariables_eq_empty
    · exact hsuccessorClosed
    · apply shortBinaryNumeralTerm_freeVariables_eq_empty
  have hcellClosed : cellFormula.freeVariables = ∅ := by
    dsimp only [cellFormula]
    unfold compactAdditiveTokenCellClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      apply shortBinaryNumeralTerm_freeVariables_eq_empty
  have hwholeCodeRaw :=
    compactAdditiveNatListAtRowsInstalledTerminalAtShortIndex_code_length_le_fixed
      tokenTable width tokenCount boundaryTable count index value bitBound data
      htableSize hwidthSize htokenCountSize hboundarySize hcountSize hindexSize
      hvalueSize
  have hwholeCode :
      (binaryFormulaCode
        (leftFormula ⋏ (rightFormula ⋏ cellFormula))).length <=
          natListAtRowsInstalledTerminalCodePolynomial bitBound := by
    have halignment :=
      compactAdditiveNatListAtRowsTerminalAtValuationIndex_substitution_alignment
        tokenTable width tokenCount boundaryTable value data.left data.right
        indexTerm
    have hvalueTerms :
        (fun coordinate : Fin 2 =>
          shortBinaryNumeralTerm (![data.right, data.left] coordinate)) =
          ![shortBinaryNumeralTerm data.right,
            shortBinaryNumeralTerm data.left] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    dsimp only [indexTerm] at halignment
    rw [hvalueTerms, halignment] at hwholeCodeRaw
    simpa only [leftFormula, rightFormula, cellFormula, indexTerm] using
      hwholeCodeRaw
  have hrightTailCode :
      (binaryFormulaCode (rightFormula ⋏ cellFormula)).length <=
        syntaxResource :=
    (binaryFormulaCode_right_length_le_and_uniformTerminal leftFormula
      (rightFormula ⋏ cellFormula)).trans (hwholeCode.trans (by
        unfold syntaxResource natListAtRowsInstalledTerminalSyntaxResource
        omega))
  have hleftCode : (binaryFormulaCode leftFormula).length <=
      syntaxResource :=
    (binaryFormulaCode_left_length_le_and_uniformTerminal leftFormula
      (rightFormula ⋏ cellFormula)).trans (hwholeCode.trans (by
        unfold syntaxResource natListAtRowsInstalledTerminalSyntaxResource
        omega))
  have hrightCode : (binaryFormulaCode rightFormula).length <=
      syntaxResource :=
    (binaryFormulaCode_left_length_le_and_uniformTerminal rightFormula
      cellFormula).trans hrightTailCode
  have hcellCode : (binaryFormulaCode cellFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_and_uniformTerminal rightFormula
      cellFormula).trans hrightTailCode
  have hsyntaxPositive : 1 <= syntaxResource := by
    unfold syntaxResource natListAtRowsInstalledTerminalSyntaxResource
    omega
  let rightCell := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    rightCertificate cellCertificate
  have hrightCellTransparent := transparentHybridConjunctionPayloadBound_le
    rightCertificate cellCertificate _ _ hright hcell
  have hrightCellGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      atRowsZeroValuation rightFormula cellFormula rightResource cellResource
      syntaxResource hsyntaxPositive hrightClosed hcellClosed hrightCode
      hcellCode hrightTailCode
  have hrightCell : hybridFormulaStructuralPayloadBound rightCell <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
        cellResource := by
    exact hrightCellTransparent.trans hrightCellGeneral
  have hrightTailClosed :
      (rightFormula ⋏ cellFormula).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hrightClosed, hcellClosed]
    simp
  let terminalParts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    leftCertificate rightCell
  have hterminalTransparent := transparentHybridConjunctionPayloadBound_le
    leftCertificate rightCell _ _ hleft hrightCell
  have hterminalGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      atRowsZeroValuation leftFormula (rightFormula ⋏ cellFormula)
      leftResource
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
        cellResource)
      syntaxResource hsyntaxPositive hleftClosed hrightTailClosed hleftCode
      hrightTailCode (hwholeCode.trans (by
        unfold syntaxResource natListAtRowsInstalledTerminalSyntaxResource
        omega))
  have hterminalParts := hterminalTransparent.trans hterminalGeneral
  let values : Fin 2 -> Nat := ![data.right, data.left]
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.right,
          shortBinaryNumeralTerm data.left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal : CheckedHybridValuationBoundedFormulaCertificate
      atRowsZeroValuation
      ((compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
        tokenCount boundaryTable value indexTerm) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListAtRowsTerminalAtValuationIndex_substitution_alignment
          tokenTable width tokenCount boundaryTable value data.left data.right
          indexTerm).symm) terminalParts
  unfold compactAdditiveNatListAtRowsTerminalFullyUniformPayloadPolynomial
  simpa only [hybridFormulaStructuralPayloadBound, indexTerm, successorTerm,
    syntaxResource, leftResource, rightResource, cellResource, rightCell,
    terminalParts, values, terminal] using hterminalParts

#print axioms
  compactAdditiveNatListAtRowsTerminalCertificate_structuralPayloadBound_le_fullyUniform

end FoundationCompactNumericListedDirectNatListAtRowsTerminalFullyUniformBounds
