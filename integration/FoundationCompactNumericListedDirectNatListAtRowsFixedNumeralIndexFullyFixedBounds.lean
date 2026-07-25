import integration.FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexWitnessFullyFixedBounds

/-!
# Fully fixed row lookup at the parser's native numeral indices

The exact native index term is retained through the terminal, two bounded
witnesses, and outer strict guard.  Named intermediate certificates prevent
the dependent proof terms from being duplicated during elaboration.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 50000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation

private theorem termValue_fixedNumeralTerm_fixedRows
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (fixedNumeralTerm value) = value := by
  unfold termValue fixedNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘ (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) =
        (![] : Fin 0 -> Nat) by
      funext coordinate
      exact Fin.elim0 coordinate]
  simp

private theorem fixedNumeralTerm_freeVariables_eq_empty_fixedRows
    (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  simp [fixedNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]

private theorem arithmeticAddTerm_eq_func_fixedRows
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd_fixedRows
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_fixedRows]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_fixedRows
    (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem binaryFormulaCode_and_left_le_fixedRows
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_and_right_le_fixedRows
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def compactAdditiveNatListAtRowsFixedNumeralGuardFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial numericBound
    (natListAtRowsFixedIndexTermCodePolynomial bitBound)

def compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial
    (index numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (natListAtRowsFixedIndexFormulaCodePolynomial bitBound + 1)
    (compactAdditiveNatListAtRowsFixedNumeralGuardFullyFixedPayloadPolynomial
      numericBound bitBound)
    (compactAdditiveNatListAtRowsFixedNumeralWitnessFullyFixedPayloadPolynomial
      index numericBound bitBound)

noncomputable def fixedNumeralAtRowsCertificateFromRowData
    (tokenTable width tokenCount boundaryTable count index value : Nat)
    (hindex : index < count)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value) :
    CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
      (compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount boundaryTable count value (fixedNumeralTerm index)) := by
  let guard := strictCertificate (fixedNumeralTerm index)
    (shortBinaryNumeralTerm count) (by
      simpa [termValue_fixedNumeralTerm_fixedRows,
        termValue_shortBinaryNumeralTerm] using hindex)
  let body := fixedNumeralAtRowsWitnessCertificate tokenTable width tokenCount
    boundaryTable index value data
  apply CheckedHybridValuationBoundedFormulaCertificate.cast
  · exact
      (compactAdditiveNatListAtRowsAtValuationIndexFormula_alignment tokenTable
        width tokenCount boundaryTable count value
        (fixedNumeralTerm index)).symm
  · exact CheckedHybridValuationBoundedFormulaCertificate.conjunction guard body

set_option maxHeartbeats 300000 in
theorem fixedNumeralAtRowsPartsFromRowData_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount boundaryTable count index value numericBound
      bitBound : Nat)
    (hindex : index < count)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexFixed : index <= 2) :
    let guard := strictCertificate (fixedNumeralTerm index)
      (shortBinaryNumeralTerm count) (by
        simpa [termValue_fixedNumeralTerm_fixedRows,
          termValue_shortBinaryNumeralTerm] using hindex)
    let body := fixedNumeralAtRowsWitnessCertificate tokenTable width tokenCount
      boundaryTable index value data
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction guard
          body) <=
      compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial index
        numericBound bitBound := by
  dsimp only
  let indexTerm : ValuationTerm := fixedNumeralTerm index
  let guardFormula : ValuationFormula :=
    “!!indexTerm < !!(shortBinaryNumeralTerm count)”
  let bodyFormula :=
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex tokenTable width
      tokenCount boundaryTable value indexTerm
  let guard := strictCertificate indexTerm (shortBinaryNumeralTerm count) (by
    simpa [indexTerm, termValue_fixedNumeralTerm_fixedRows,
      termValue_shortBinaryNumeralTerm] using hindex)
  let body := fixedNumeralAtRowsWitnessCertificate tokenTable width tokenCount
    boundaryTable index value data
  let guardResource :=
    compactAdditiveNatListAtRowsFixedNumeralGuardFullyFixedPayloadPolynomial
      numericBound bitBound
  let bodyResource :=
    compactAdditiveNatListAtRowsFixedNumeralWitnessFullyFixedPayloadPolynomial
      index numericBound bitBound
  let syntaxResource :=
    natListAtRowsFixedIndexFormulaCodePolynomial bitBound + 1
  have hguardPublic :=
    strictCertificate_structuralPayloadBound_le_public count indexTerm (by
      dsimp only [indexTerm]
      rw [fixedNumeralTerm_freeVariables_eq_empty_fixedRows]
      simp) (by
        simpa only [indexTerm, termValue_fixedNumeralTerm_fixedRows,
          termValue_shortBinaryNumeralTerm] using hindex)
  have hguardFixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed atRowsZeroValuation
      Language.ORing.Rel.lt ![indexTerm, shortBinaryNumeralTerm count]
      numericBound (natListAtRowsFixedIndexTermCodePolynomial bitBound)
      (by
        change indexTerm.freeVariables ⊆ {0}
        dsimp only [indexTerm]
        rw [fixedNumeralTerm_freeVariables_eq_empty_fixedRows]
        simp)
      (by
        change (shortBinaryNumeralTerm count).freeVariables ⊆ {0}
        rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
        simp)
      (by simp)
      (by
        dsimp only [indexTerm]
        exact fixedNumeralTerm_code_length_le_relationIndex index bitBound
          hindexFixed)
      (shortNumeralTerm_code_length_le_relationIndex count bitBound hcountSize)
  have hguard :
      hybridFormulaStructuralPayloadBound guard <= guardResource := by
    simpa only [guard, guardResource,
      compactAdditiveNatListAtRowsIndexGuardPayloadPolynomial,
      compactAdditiveNatListAtRowsFixedNumeralGuardFullyFixedPayloadPolynomial]
      using hguardPublic.trans hguardFixed
  have hbody :
      hybridFormulaStructuralPayloadBound body <= bodyResource := by
    simpa only [body, bodyResource] using
      fixedNumeralAtRowsWitnessCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount boundaryTable count index value numericBound
        bitBound data hwidthValue htokenCountValue hcountValue hindex htableSize
        hwidthSize htokenCountSize hboundarySize hcountSize hvalueSize hindexFixed
  have hfullCode :=
    compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_code_length_le_fixed
      tokenTable width tokenCount boundaryTable count value index bitBound
      htableSize hwidthSize htokenCountSize hboundarySize hcountSize hvalueSize
      hindexFixed
  have halignment :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula_alignment tokenTable
      width tokenCount boundaryTable count value indexTerm
  have hfullCodeAligned :
      (binaryFormulaCode (guardFormula ⋏ bodyFormula)).length <=
        natListAtRowsFixedIndexFormulaCodePolynomial bitBound := by
    dsimp only [indexTerm] at halignment
    rw [halignment] at hfullCode
    unfold compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndex at hfullCode
    simpa only [guardFormula, bodyFormula, indexTerm] using hfullCode
  have hguardCode :
      (binaryFormulaCode guardFormula).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_fixedRows guardFormula bodyFormula).trans
      (hfullCodeAligned.trans (by
        dsimp only [syntaxResource]
        omega))
  have hbodyCode :
      (binaryFormulaCode bodyFormula).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_fixedRows guardFormula bodyFormula).trans
      (hfullCodeAligned.trans (by
        dsimp only [syntaxResource]
        omega))
  have hfullClosed :=
    compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_freeVariables_eq_empty
      tokenTable width tokenCount boundaryTable count value index
  have hpartsClosed :
      (guardFormula ⋏ bodyFormula).freeVariables = ∅ := by
    dsimp only [indexTerm] at halignment
    rw [halignment] at hfullClosed
    unfold compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndex at hfullClosed
    simpa only [guardFormula, bodyFormula, indexTerm] using hfullClosed
  have hclosed :=
    Finset.union_eq_empty.mp (by
      simpa only [LO.FirstOrder.Semiformula.freeVariables_and] using hpartsClosed)
  have hsyntaxPositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    omega
  have htransparent := transparentHybridConjunctionPayloadBound_le guard body
    guardResource bodyResource hguard hbody
  have hgeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      atRowsZeroValuation guardFormula bodyFormula guardResource bodyResource
      syntaxResource hsyntaxPositive hclosed.1 hclosed.2 hguardCode hbodyCode
      (hfullCodeAligned.trans (by
        dsimp only [syntaxResource]
        omega))
  have hparts := htransparent.trans hgeneral
  unfold
    compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial
  simpa only [hybridFormulaStructuralPayloadBound, indexTerm, guardFormula,
    bodyFormula, guard, body, guardResource, bodyResource, syntaxResource] using
      hparts

theorem
    compactAdditiveNatListAtRowsAtFixedNumeralIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
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
    (hvalueSize : Nat.size value <= bitBound)
    (hindexFixed : index <= 2) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
          tokenTable width tokenCount boundaryTable count index value
          (fixedNumeralTerm index) (by simp) hrows) <=
      compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial index
        numericBound bitBound := by
  let data :=
    compactAdditiveNatListAtRowDataOfGraph tokenTable width tokenCount
      boundaryTable count index value hrows
  have hnamed :=
    fixedNumeralAtRowsPartsFromRowData_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount boundaryTable count index value numericBound
      bitBound hrows.1 data hwidthValue htokenCountValue hcountValue htableSize
      hwidthSize htokenCountSize hboundarySize hcountSize hvalueSize hindexFixed
  dsimp only at hnamed
  unfold fixedNumeralAtRowsWitnessCertificate at hnamed
  unfold
    FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexTerminalFullyFixedBounds.fixedNumeralAtRowsTerminalCertificate
    at hnamed
  unfold
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateFromRowData
    compactAdditiveNatListAtRowsAtValuationIndexExplicitFormulaCertificateFromRowData
  simpa only [data, hybridFormulaStructuralPayloadBound] using hnamed

#print axioms
  fixedNumeralAtRowsPartsFromRowData_structuralPayloadBound_le_fullyFixed
#print axioms
  compactAdditiveNatListAtRowsAtFixedNumeralIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds
