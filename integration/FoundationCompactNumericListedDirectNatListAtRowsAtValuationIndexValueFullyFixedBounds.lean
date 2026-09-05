import integration.FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueWitnessFullyFixedBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds

/-!
# Fully fixed row lookup with exact index and value terms

This closes the outer strict-index guard above the exact two-witness body.
The checked index and value expressions remain in the conclusion formula.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 120000

namespace FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
open FoundationCompactNumericListedDirectNatListAtRowsTerminalSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueWitnessFullyFixedBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

private abbrev atRowsValueZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation

private theorem arithmeticAddTerm_eq_func_fullValue
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd_fullValue
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_fullValue]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_fullValue
    (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem binaryFormulaCode_left_length_le_and_fullValue
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_length_le_and_fullValue
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def compactAdditiveNatListAtRowsExactValueGuardFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial numericBound
    (binaryNumeralTermCodeEnvelope bitBound)

def compactAdditiveNatListAtRowsExactValueFullyFixedSyntaxResource
    (bitBound : Nat) : Nat :=
  natListAtRowsFullFormulaCodePolynomial bitBound + 1

def compactAdditiveNatListAtRowsExactValueFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactAdditiveNatListAtRowsExactValueFullyFixedSyntaxResource bitBound)
    (compactAdditiveNatListAtRowsExactValueGuardFullyFixedPayloadPolynomial
      numericBound bitBound)
    (compactAdditiveNatListAtRowsExactValueWitnessFullyFixedPayloadPolynomial
      numericBound bitBound)

theorem
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitFormulaCertificateFromRowData_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount boundaryTable count index value numericBound
      bitBound : Nat)
    (indexTerm valueTerm : ValuationTerm)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value)
    (hindexValue : termValue atRowsValueZeroValuation indexTerm = index)
    (hvalueValue : termValue atRowsValueZeroValuation valueTerm = value)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hvalueClosed : valueTerm.freeVariables = ∅)
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
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <=
      natListAtRowsExactIndexCodeEnvelope bitBound)
    (hvalueCode : (binaryTermCode valueTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAtRowsAtValuationIndexValueExplicitFormulaCertificateFromRowData
          atRowsValueZeroValuation tokenTable width tokenCount boundaryTable
          count index value indexTerm valueTerm hindexValue hvalueValue hindex
          data) <=
      compactAdditiveNatListAtRowsExactValueFullyFixedPayloadPolynomial
        numericBound bitBound := by
  let terminalFormula :=
    compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable width
      tokenCount boundaryTable indexTerm valueTerm
  let values : Fin 2 -> Nat := ![data.right, data.left]
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        atRowsValueZeroValuation (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm data.left) (by
          simpa [termValue_shortBinaryNumeralTerm, hindexValue] using
            data.left_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          atRowsValueZeroValuation (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (natListAtSuccessorTermAtValuationIndex indexTerm)
          (shortBinaryNumeralTerm data.right) (by
            simpa [natListAtSuccessorTermAtValuationIndex,
              termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd_fullValue,
              termValue_arithmeticOne_fullValue, hindexValue] using
                data.right_entry))
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificateLocal
          atRowsValueZeroValuation (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm data.left) valueTerm
          (shortBinaryNumeralTerm data.right) (by
            simpa [termValue_shortBinaryNumeralTerm, hvalueValue] using
              data.cell)))
  have hvalueTerms :
      (fun coordinate : Fin 2 =>
        shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.right,
          shortBinaryNumeralTerm data.left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal : CheckedHybridValuationBoundedFormulaCertificate
      atRowsValueZeroValuation
      (terminalFormula ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListAtRowsTerminalAtValuationIndexValue_substitution_alignment
          tokenTable width tokenCount boundaryTable data.left data.right
          indexTerm valueTerm).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
    terminalFormula values (by
      intro coordinate
      fin_cases coordinate
      · exact data.right_le
      · exact data.left_le) terminal
  let body : CheckedHybridValuationBoundedFormulaCertificate
      atRowsValueZeroValuation
      (compactAdditiveNatListAtRowsWitnessBodyAtValuationIndexValue tokenTable
        width tokenCount boundaryTable indexTerm valueTerm) :=
    .cast (by
      rw [explicitBoundedWitnessFormula_two_eq]
      rfl) installed
  let guardFormula : ValuationFormula :=
    “!!indexTerm < !!(shortBinaryNumeralTerm count)”
  let witnessFormula :=
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndexValue tokenTable
      width tokenCount boundaryTable indexTerm valueTerm
  have hguardTruth : termValue atRowsValueZeroValuation indexTerm <
      termValue atRowsValueZeroValuation
        (shortBinaryNumeralTerm count) := by
    simpa [termValue_shortBinaryNumeralTerm, hindexValue] using hindex
  let guardDirect :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      atRowsValueZeroValuation Language.ORing.Rel.lt
      ![indexTerm, shortBinaryNumeralTerm count] hguardTruth
  let guard : CheckedHybridValuationBoundedFormulaCertificate
      atRowsValueZeroValuation guardFormula :=
    .cast (Semiformula.Operator.lt_def _ _).symm guardDirect
  let guardResource :=
    compactAdditiveNatListAtRowsExactValueGuardFullyFixedPayloadPolynomial
      numericBound bitBound
  let witnessResource :=
    compactAdditiveNatListAtRowsExactValueWitnessFullyFixedPayloadPolynomial
      numericBound bitBound
  let syntaxResource :=
    compactAdditiveNatListAtRowsExactValueFullyFixedSyntaxResource bitBound
  have hindexSubset : indexTerm.freeVariables ⊆ {0} := by
    rw [hindexClosed]
    exact Finset.empty_subset _
  have hcountSubset :
      (shortBinaryNumeralTerm count).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    exact Finset.empty_subset _
  have hguardPublic :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      atRowsValueZeroValuation Language.ORing.Rel.lt
      ![indexTerm, shortBinaryNumeralTerm count] hindexSubset hcountSubset
  have hguardFixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed atRowsValueZeroValuation
      Language.ORing.Rel.lt ![indexTerm, shortBinaryNumeralTerm count]
      numericBound (binaryNumeralTermCodeEnvelope bitBound) hindexSubset
      hcountSubset (by simp [atRowsValueZeroValuation])
      (by
        change (binaryTermCode indexTerm).length <=
          binaryNumeralTermCodeEnvelope bitBound
        simpa only [natListAtRowsExactIndexCodeEnvelope] using hindexCode)
      (by
        change (binaryTermCode (shortBinaryNumeralTerm count)).length <=
          binaryNumeralTermCodeEnvelope bitBound
        exact binaryNumeralTerm_code_length_le_envelope count bitBound
          hcountSize)
  have hguard : hybridFormulaStructuralPayloadBound guard <=
      guardResource := by
    change compilePositiveRelationPayloadResource atRowsValueZeroValuation
      Language.ORing.Rel.lt ![indexTerm, shortBinaryNumeralTerm count] <= _
    simpa only [guardResource,
      compactAdditiveNatListAtRowsExactValueGuardFullyFixedPayloadPolynomial]
      using hguardPublic.trans hguardFixed
  have hwitnessRaw :=
    compactAdditiveNatListAtRowsExactValueWitnessCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount boundaryTable count index value numericBound
      bitBound indexTerm valueTerm data hindexValue hvalueValue hindexClosed
      hvalueClosed hwidthValue htokenCountValue hcountValue hindex htableSize
      hwidthSize htokenCountSize hboundarySize hcountSize hindexSize hvalueSize
      hindexCode hvalueCode
  have hwitness : hybridFormulaStructuralPayloadBound body <=
      witnessResource := by
    change hybridFormulaStructuralPayloadBound installed <= witnessResource
    simpa only [installed, terminal, terminalParts, terminalFormula, values,
      witnessResource] using hwitnessRaw
  have hfullCode :=
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula_code_length_le_fixed
      tokenTable width tokenCount boundaryTable count bitBound indexTerm
      valueTerm htableSize hwidthSize htokenCountSize hboundarySize hcountSize
      (by simpa only [natListAtRowsExactIndexCodeEnvelope] using hindexCode)
      hvalueCode
  have halignment :=
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula_alignment
      tokenTable width tokenCount boundaryTable count indexTerm valueTerm
  have hfullCodeAligned :
      (binaryFormulaCode (guardFormula ⋏ witnessFormula)).length <=
        natListAtRowsFullFormulaCodePolynomial bitBound := by
    rw [halignment] at hfullCode
    unfold compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndexValue at hfullCode
    simpa only [guardFormula, witnessFormula] using hfullCode
  have hguardCode :
      (binaryFormulaCode guardFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_and_fullValue guardFormula
      witnessFormula).trans (hfullCodeAligned.trans (by
        unfold syntaxResource
          compactAdditiveNatListAtRowsExactValueFullyFixedSyntaxResource
        omega))
  have hwitnessCode :
      (binaryFormulaCode witnessFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_and_fullValue guardFormula
      witnessFormula).trans (hfullCodeAligned.trans (by
        unfold syntaxResource
          compactAdditiveNatListAtRowsExactValueFullyFixedSyntaxResource
        omega))
  have hfullClosed :=
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula_closed tokenTable
      width tokenCount boundaryTable count indexTerm valueTerm hindexClosed
      hvalueClosed
  have hpartsClosed :
      (guardFormula ⋏ witnessFormula).freeVariables = ∅ := by
    rw [halignment] at hfullClosed
    unfold compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndexValue at hfullClosed
    simpa only [guardFormula, witnessFormula] using hfullClosed
  have hguardClosed : guardFormula.freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hpartsClosed
    exact (Finset.union_eq_empty.mp hpartsClosed).1
  have hwitnessClosed : witnessFormula.freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hpartsClosed
    exact (Finset.union_eq_empty.mp hpartsClosed).2
  have hsyntaxPositive : 1 <= syntaxResource := by
    unfold syntaxResource
      compactAdditiveNatListAtRowsExactValueFullyFixedSyntaxResource
    omega
  have hpartsTransparent := transparentHybridConjunctionPayloadBound_le
    guard body guardResource witnessResource hguard hwitness
  have hpartsGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      atRowsValueZeroValuation guardFormula witnessFormula guardResource
      witnessResource syntaxResource hsyntaxPositive hguardClosed
      hwitnessClosed hguardCode hwitnessCode
      (hfullCodeAligned.trans (by
        unfold syntaxResource
          compactAdditiveNatListAtRowsExactValueFullyFixedSyntaxResource
        omega))
  have hparts := hpartsTransparent.trans hpartsGeneral
  unfold compactAdditiveNatListAtRowsExactValueFullyFixedPayloadPolynomial
  simpa only [
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitFormulaCertificateFromRowData,
    hybridFormulaStructuralPayloadBound, terminalFormula, values,
    terminalParts, terminal, installed, body, guardDirect, guard, guardFormula,
    witnessFormula, guardResource, witnessResource, syntaxResource] using hparts

theorem
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount boundaryTable count index value numericBound
      bitBound : Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hrows : CompactAdditiveNatListAtRows tokenTable width tokenCount
      boundaryTable count index value)
    (hindexValue : termValue atRowsValueZeroValuation indexTerm = index)
    (hvalueValue : termValue atRowsValueZeroValuation valueTerm = value)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hvalueClosed : valueTerm.freeVariables = ∅)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hindexSize : Nat.size index <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <=
      natListAtRowsExactIndexCodeEnvelope bitBound)
    (hvalueCode : (binaryTermCode valueTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph
          atRowsValueZeroValuation tokenTable width tokenCount boundaryTable
          count index value indexTerm valueTerm hindexValue hvalueValue hrows) <=
      compactAdditiveNatListAtRowsExactValueFullyFixedPayloadPolynomial
        numericBound bitBound := by
  let data :=
    compactAdditiveNatListAtRowDataOfGraph tokenTable width tokenCount
      boundaryTable count index value hrows
  have hfixed :=
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitFormulaCertificateFromRowData_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount boundaryTable count index value numericBound
      bitBound indexTerm valueTerm data hindexValue hvalueValue hindexClosed
      hvalueClosed hwidthValue htokenCountValue hcountValue hrows.1 htableSize
      hwidthSize htokenCountSize hboundarySize hcountSize hindexSize hvalueSize
      hindexCode hvalueCode
  simpa only [
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph,
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateFromRowData,
    hybridFormulaStructuralPayloadBound, data] using hfixed

#print axioms
  compactAdditiveNatListAtRowsAtValuationIndexValueExplicitFormulaCertificateFromRowData_structuralPayloadBound_le_fullyFixed
#print axioms
  compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueFullyFixedBounds
