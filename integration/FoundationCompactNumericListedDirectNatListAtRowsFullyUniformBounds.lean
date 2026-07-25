import integration.FoundationCompactNumericListedDirectNatListAtRowsWitnessFullyUniformBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds

/-!
# Fully uniform resource bound for a closed row lookup

This closes the outer index guard and conjunction after the two-witness body.
No row witness, finite witness sum, body-code parameter or context parameter
appears in the resulting resource polynomial.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAtRowsFullyUniformBounds

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
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
open FoundationCompactNumericListedDirectNatListAtRowsTerminalSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsWitnessFullyUniformBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation

private theorem arithmeticAddTerm_eq_func_fullyUniformRows
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd_fullyUniformRows
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_fullyUniformRows]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_fullyUniformRows
    (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem binaryFormulaCode_left_length_le_and_fullyUniformRows
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_length_le_and_fullyUniformRows
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def compactAdditiveNatListAtRowsGuardFullyUniformPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial numericBound
    (binaryNumeralTermCodeEnvelope bitBound)

def compactAdditiveNatListAtRowsFullyUniformSyntaxResource
    (bitBound : Nat) : Nat :=
  natListAtRowsFullFormulaCodePolynomial bitBound + 1

def compactAdditiveNatListAtRowsFullyUniformPayloadPolynomial
    (index numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactAdditiveNatListAtRowsFullyUniformSyntaxResource bitBound)
    (compactAdditiveNatListAtRowsGuardFullyUniformPayloadPolynomial
      numericBound bitBound)
    (compactAdditiveNatListAtRowsWitnessFullyUniformPayloadPolynomial index
      numericBound bitBound)

theorem
    compactAdditiveNatListAtRowsAtShortIndexExplicitFormulaCertificate_structuralPayloadBound_le_fullyUniform
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
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAtRowsAtValuationIndexExplicitFormulaCertificateFromRowData
          tokenTable width tokenCount boundaryTable count index value
          (shortBinaryNumeralTerm index) (by
            simp [termValue_shortBinaryNumeralTerm]) hindex data) <=
      compactAdditiveNatListAtRowsFullyUniformPayloadPolynomial index
        numericBound bitBound := by
  let indexTerm : ValuationTerm := shortBinaryNumeralTerm index
  let terminalFormula :=
    compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
      tokenCount boundaryTable value indexTerm
  let values : Fin 2 -> Nat := ![data.right, data.left]
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm data.left) (by
          simpa [indexTerm, termValue_shortBinaryNumeralTerm] using
            data.left_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (natListAtSuccessorTermAtValuationIndex indexTerm)
          (shortBinaryNumeralTerm data.right) (by
            simpa [indexTerm, natListAtSuccessorTermAtValuationIndex,
              termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd_fullyUniformRows,
              termValue_arithmeticOne_fullyUniformRows] using data.right_entry))
        (compactAdditiveTokenCellExplicitHybridCertificate tokenTable width
          tokenCount data.left value data.right data.cell))
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.right,
          shortBinaryNumeralTerm data.left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal : CheckedHybridValuationBoundedFormulaCertificate
      atRowsZeroValuation
      (terminalFormula ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListAtRowsTerminalAtValuationIndex_substitution_alignment
          tokenTable width tokenCount boundaryTable value data.left data.right
          indexTerm).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
    terminalFormula values (by
      intro coordinate
      fin_cases coordinate
      · exact data.right_le
      · exact data.left_le) terminal
  let body : CheckedHybridValuationBoundedFormulaCertificate
      atRowsZeroValuation
      (compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex tokenTable width
        tokenCount boundaryTable value indexTerm) :=
    .cast (by
      rw [explicitBoundedWitnessFormula_two_eq]
      rfl) installed
  let guardFormula : ValuationFormula :=
    “!!indexTerm < !!(shortBinaryNumeralTerm count)”
  let witnessFormula :=
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex tokenTable width
      tokenCount boundaryTable value indexTerm
  let guard := strictCertificate indexTerm (shortBinaryNumeralTerm count) (by
    simpa [indexTerm, termValue_shortBinaryNumeralTerm] using hindex)
  let guardResource :=
    compactAdditiveNatListAtRowsGuardFullyUniformPayloadPolynomial numericBound
      bitBound
  let witnessResource :=
    compactAdditiveNatListAtRowsWitnessFullyUniformPayloadPolynomial index
      numericBound bitBound
  let syntaxResource :=
    compactAdditiveNatListAtRowsFullyUniformSyntaxResource bitBound
  have hguardPublic :=
    strictCertificate_structuralPayloadBound_le_public count indexTerm (by
      dsimp only [indexTerm]
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
      simp) (by
        simpa only [indexTerm, termValue_shortBinaryNumeralTerm] using hindex)
  have hguardFixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed atRowsZeroValuation
      Language.ORing.Rel.lt
      ![indexTerm, shortBinaryNumeralTerm count] numericBound
      (binaryNumeralTermCodeEnvelope bitBound)
      (by
        change indexTerm.freeVariables ⊆ {0}
        dsimp only [indexTerm]
        rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
        simp)
      (by
        change (shortBinaryNumeralTerm count).freeVariables ⊆ {0}
        rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
        simp)
      (by simp)
      (binaryNumeralTerm_code_length_le_envelope index bitBound hindexSize)
      (binaryNumeralTerm_code_length_le_envelope count bitBound hcountSize)
  have hguard : hybridFormulaStructuralPayloadBound guard <= guardResource := by
    simpa only [guard, guardResource,
      compactAdditiveNatListAtRowsIndexGuardPayloadPolynomial,
      compactAdditiveNatListAtRowsGuardFullyUniformPayloadPolynomial] using
        hguardPublic.trans hguardFixed
  have hwitnessRaw :=
    compactAdditiveNatListAtRowsWitnessCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount boundaryTable count index value numericBound
      bitBound data hwidthValue htokenCountValue hcountValue hindex htableSize
      hwidthSize htokenCountSize hboundarySize hcountSize hindexSize hvalueSize
  have hwitness : hybridFormulaStructuralPayloadBound body <=
      witnessResource := by
    change hybridFormulaStructuralPayloadBound installed <= witnessResource
    simpa only [installed, terminal, terminalParts, terminalFormula, values,
      indexTerm, witnessResource] using hwitnessRaw
  have hfullCode :=
    compactAdditiveNatListAtRowsAtShortIndexFormula_code_length_le_fixed
      tokenTable width tokenCount boundaryTable count index value bitBound
      htableSize hwidthSize htokenCountSize hboundarySize hcountSize hindexSize
      hvalueSize
  have halignment :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula_alignment tokenTable
      width tokenCount boundaryTable count value indexTerm
  have hfullCodeAligned :
      (binaryFormulaCode (guardFormula ⋏ witnessFormula)).length <=
        natListAtRowsFullFormulaCodePolynomial bitBound := by
    dsimp only [indexTerm] at halignment
    rw [halignment] at hfullCode
    unfold compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndex at hfullCode
    simpa only [guardFormula, witnessFormula, indexTerm] using hfullCode
  have hguardCode : (binaryFormulaCode guardFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_and_fullyUniformRows guardFormula
      witnessFormula).trans (hfullCodeAligned.trans (by
        unfold syntaxResource
          compactAdditiveNatListAtRowsFullyUniformSyntaxResource
        omega))
  have hwitnessCode :
      (binaryFormulaCode witnessFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_and_fullyUniformRows guardFormula
      witnessFormula).trans (hfullCodeAligned.trans (by
        unfold syntaxResource
          compactAdditiveNatListAtRowsFullyUniformSyntaxResource
        omega))
  have hfullClosed :=
    compactAdditiveNatListAtRowsAtShortIndexFormula_closed tokenTable width
      tokenCount boundaryTable count index value
  have hpartsClosed :
      (guardFormula ⋏ witnessFormula).freeVariables = ∅ := by
    dsimp only [indexTerm] at halignment
    rw [halignment] at hfullClosed
    unfold compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndex at hfullClosed
    simpa only [guardFormula, witnessFormula, indexTerm] using hfullClosed
  have hguardClosed : guardFormula.freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hpartsClosed
    exact (Finset.union_eq_empty.mp hpartsClosed).1
  have hwitnessClosed : witnessFormula.freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hpartsClosed
    exact (Finset.union_eq_empty.mp hpartsClosed).2
  have hsyntaxPositive : 1 <= syntaxResource := by
    unfold syntaxResource compactAdditiveNatListAtRowsFullyUniformSyntaxResource
    omega
  have hpartsTransparent := transparentHybridConjunctionPayloadBound_le
    guard body guardResource witnessResource hguard hwitness
  have hpartsGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      atRowsZeroValuation guardFormula witnessFormula guardResource
      witnessResource syntaxResource hsyntaxPositive hguardClosed
      hwitnessClosed hguardCode hwitnessCode
      (hfullCodeAligned.trans (by
        unfold syntaxResource
          compactAdditiveNatListAtRowsFullyUniformSyntaxResource
        omega))
  have hparts := hpartsTransparent.trans hpartsGeneral
  unfold compactAdditiveNatListAtRowsFullyUniformPayloadPolynomial
  simpa only [
    compactAdditiveNatListAtRowsAtValuationIndexExplicitFormulaCertificateFromRowData,
    hybridFormulaStructuralPayloadBound, indexTerm, terminalFormula, values,
    terminalParts, terminal, installed, body, guard, guardFormula,
    witnessFormula, guardResource, witnessResource, syntaxResource] using hparts

theorem
    compactAdditiveNatListAtRowsAtShortIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyUniform
    (tokenTable width tokenCount boundaryTable count index value numericBound
      bitBound : Nat)
    (hrows : CompactAdditiveNatListAtRows tokenTable width tokenCount
      boundaryTable count index value)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hindexSize : Nat.size index <= bitBound)
    (hvalueSize : Nat.size value <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
          tokenTable width tokenCount boundaryTable count index value
          (shortBinaryNumeralTerm index) (by
            simp [termValue_shortBinaryNumeralTerm]) hrows) <=
      compactAdditiveNatListAtRowsFullyUniformPayloadPolynomial index
        numericBound bitBound := by
  let data :=
    compactAdditiveNatListAtRowDataOfGraph tokenTable width tokenCount
      boundaryTable count index value hrows
  have hfixed :=
    compactAdditiveNatListAtRowsAtShortIndexExplicitFormulaCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount boundaryTable count index value numericBound
      bitBound data hwidthValue htokenCountValue hcountValue hrows.1
      htableSize hwidthSize htokenCountSize hboundarySize hcountSize hindexSize
      hvalueSize
  simpa only [
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph,
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateFromRowData,
    hybridFormulaStructuralPayloadBound, data,
    termValue_shortBinaryNumeralTerm] using hfixed

#print axioms
  compactAdditiveNatListAtRowsAtShortIndexExplicitFormulaCertificate_structuralPayloadBound_le_fullyUniform
#print axioms
  compactAdditiveNatListAtRowsAtShortIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyUniform

end FoundationCompactNumericListedDirectNatListAtRowsFullyUniformBounds
