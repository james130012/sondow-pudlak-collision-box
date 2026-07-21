import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveListHeaderPublicBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds

/-!
# Public structural resources for additive structured-list layouts

This layer opens the boundary-row branches, the boundary-table universal, and
the outer body-start witness.  Resource expressions depend only on concrete
layout data and public syntax, never on a generated proof payload.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveListHeaderPublicBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds

private abbrev layoutZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem binaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
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

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

def boundaryRowGuardStructuralPayloadResource
    (valuation : Nat -> Nat) (value bound : Nat) : Nat :=
  compilePositiveRelationPayloadResource valuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm value,
      (‘!!(shortBinaryNumeralTerm bound) + 1’ : ValuationTerm)]

theorem boundedWitnessGuardCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat) (value bound : Nat)
    (hvalue : value <= bound) :
    hybridFormulaStructuralPayloadBound
        (boundedWitnessGuardCertificate valuation value bound hvalue) <=
      boundaryRowGuardStructuralPayloadResource valuation value bound := by
  simp only [boundedWitnessGuardCertificate,
    hybridFormulaStructuralPayloadBound]
  exact le_rfl

def boundaryRowClosedLtStructuralPayloadResource
    (valuation : Nat -> Nat) (left right : Nat) : Nat :=
  compilePositiveRelationPayloadResource valuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right]

theorem closedLtCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat) (left right : Nat) (hlt : left < right) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.closedLtCertificate
          valuation left right hlt) <=
      boundaryRowClosedLtStructuralPayloadResource valuation left right := by
  simp only [
    FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.closedLtCertificate,
    hybridFormulaStructuralPayloadBound]
  exact le_rfl

def boundaryRowTerminalStructuralPayloadEnvelope
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index) : Nat :=
  let valuation := extendValuation index layoutZeroValuation
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm : ValuationTerm := &0
  let rightIndexTerm : ValuationTerm := ‘&0 + 1’
  let leftValueTerm := shortBinaryNumeralTerm data.left
  let rightValueTerm := shortBinaryNumeralTerm data.right
  let leftFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm leftIndexTerm leftValueTerm
  let rightFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm rightIndexTerm rightValueTerm
  let ltFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm data.left) <
      !!(shortBinaryNumeralTerm data.right)”
  let leftResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation tableTerm widthTerm leftIndexTerm leftValueTerm
  let rightResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation tableTerm widthTerm rightIndexTerm rightValueTerm
  let ltResource := boundaryRowClosedLtStructuralPayloadResource
    valuation data.left data.right
  let rightLtResource := hybridConjunctionStructuralPayloadEnvelope
    valuation rightFormula ltFormula rightResource ltResource
  hybridConjunctionStructuralPayloadEnvelope valuation leftFormula
    (rightFormula ⋏ ltFormula) leftResource rightLtResource

def boundaryRowBranchStructuralPayloadEnvelope
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index) : Nat :=
  let valuation := extendValuation index layoutZeroValuation
  let terminalFormula :=
    compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount)
        (&0 : ValuationTerm)
        (shortBinaryNumeralTerm data.left) ⋏
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (‘&0 + 1’ : ValuationTerm)
          (shortBinaryNumeralTerm data.right) ⋏
        “!!(shortBinaryNumeralTerm data.left) <
          !!(shortBinaryNumeralTerm data.right)”)
  let rightGuardFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm data.right) <
      !!(shortBinaryNumeralTerm tokenCount) + 1”
  let rightGuardedResource := hybridConjunctionStructuralPayloadEnvelope
    valuation rightGuardFormula terminalFormula
    (boundaryRowGuardStructuralPayloadResource
      valuation data.right tokenCount)
    (boundaryRowTerminalStructuralPayloadEnvelope
      tokenCount boundaryTable index data)
  let rightExistsFormula : ValuationFormula :=
    ∃⁰ boundaryRowRightWitnessBody tokenCount boundaryTable data.left
  let rightExistsResource := hybridExistsWitnessStructuralPayloadEnvelope
    valuation (boundaryRowRightWitnessBody
      tokenCount boundaryTable data.left) data.right rightGuardedResource
  let leftGuardFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm data.left) <
      !!(shortBinaryNumeralTerm tokenCount) + 1”
  let leftGuardedResource := hybridConjunctionStructuralPayloadEnvelope
    valuation leftGuardFormula rightExistsFormula
    (boundaryRowGuardStructuralPayloadResource
      valuation data.left tokenCount)
    rightExistsResource
  hybridExistsWitnessStructuralPayloadEnvelope valuation
    (boundaryRowLeftWitnessBody tokenCount boundaryTable)
    data.left leftGuardedResource

theorem boundaryRowBranchCertificate_structuralPayloadBound_le_transparent
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index) :
    hybridFormulaStructuralPayloadBound
        (boundaryRowBranchCertificate
          tokenCount boundaryTable index data) <=
      boundaryRowBranchStructuralPayloadEnvelope
        tokenCount boundaryTable index data := by
  let valuation := extendValuation index layoutZeroValuation
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm : ValuationTerm := &0
  let rightIndexTerm : ValuationTerm := ‘&0 + 1’
  let leftValueTerm := shortBinaryNumeralTerm data.left
  let rightValueTerm := shortBinaryNumeralTerm data.right
  let leftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      valuation tableTerm widthTerm leftIndexTerm leftValueTerm (by
        simpa [valuation, layoutZeroValuation, tableTerm, widthTerm,
          leftIndexTerm, leftValueTerm, termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.left_entry)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      valuation tableTerm widthTerm rightIndexTerm rightValueTerm (by
        simpa [valuation, layoutZeroValuation, tableTerm, widthTerm,
          rightIndexTerm, rightValueTerm, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.right_entry)
  let ltCertificate :=
    FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.closedLtCertificate
      valuation data.left data.right data.left_lt_right
  let rightLt :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      rightCertificate ltCertificate
  let terminal :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      leftCertificate rightLt
  have hwidth : widthTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have htable : tableTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
  have hleftIndex : leftIndexTerm.freeVariables ⊆ {0} := by
    simp [leftIndexTerm]
  have hrightIndex : rightIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [rightIndexTerm]
    rw [arithmeticAddTerm_eq_func,
      binaryFunctionTerm_freeVariables,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp
  have hleftValue : leftValueTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty data.left
  have hrightValue : rightValueTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty data.right
  have hleft :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation tableTerm widthTerm leftIndexTerm leftValueTerm
      htable hwidth hleftIndex hleftValue (by
        simpa [valuation, layoutZeroValuation, tableTerm, widthTerm,
          leftIndexTerm, leftValueTerm, termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.left_entry)
  have hright :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation tableTerm widthTerm rightIndexTerm rightValueTerm
      htable hwidth hrightIndex hrightValue (by
        simpa [valuation, layoutZeroValuation, tableTerm, widthTerm,
          rightIndexTerm, rightValueTerm, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.right_entry)
  have hlt := closedLtCertificate_structuralPayloadBound_le_transparent
    valuation data.left data.right data.left_lt_right
  have hrightLt := hybridConjunctionStructuralPayloadBound_le_envelope
    rightCertificate ltCertificate _ _ hright hlt
  have hterminal := hybridConjunctionStructuralPayloadBound_le_envelope
    leftCertificate rightLt _ _ hleft hrightLt
  have hterminalNamed : hybridFormulaStructuralPayloadBound terminal <=
      boundaryRowTerminalStructuralPayloadEnvelope
        tokenCount boundaryTable index data := by
    simpa only [boundaryRowTerminalStructuralPayloadEnvelope,
      valuation, tableTerm, widthTerm, leftIndexTerm, rightIndexTerm,
      leftValueTerm, rightValueTerm, terminal, rightLt,
      leftCertificate, rightCertificate, ltCertificate,
      boundaryRowClosedLtStructuralPayloadResource] using hterminal
  let rightGuard := boundedWitnessGuardCertificate valuation
    data.right tokenCount data.right_le
  let rightGuarded :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      rightGuard terminal
  have hrightGuard :=
    boundedWitnessGuardCertificate_structuralPayloadBound_le_transparent
      valuation data.right tokenCount data.right_le
  have hrightGuarded := hybridConjunctionStructuralPayloadBound_le_envelope
    rightGuard terminal
    (boundaryRowGuardStructuralPayloadResource
      valuation data.right tokenCount)
    (boundaryRowTerminalStructuralPayloadEnvelope
      tokenCount boundaryTable index data)
    hrightGuard hterminalNamed
  let rightBody := boundaryRowRightWitnessBody
    tokenCount boundaryTable data.left
  let rightInstalledBody := CheckedHybridValuationBoundedFormulaCertificate.cast
    (boundaryRowRightWitnessBody_subst tokenCount boundaryTable
      data.left data.right).symm rightGuarded
  let rightInstalled :=
    CheckedHybridValuationBoundedFormulaCertificate.existsWitness
      rightBody data.right rightInstalledBody
  have hrightInstalledBody :
      hybridFormulaStructuralPayloadBound rightInstalledBody <=
        hybridConjunctionStructuralPayloadEnvelope valuation
          (“!!(shortBinaryNumeralTerm data.right) <
            !!(shortBinaryNumeralTerm tokenCount) + 1” : ValuationFormula)
          (compactFixedWidthEntryAtValuationFormula
              tableTerm widthTerm leftIndexTerm leftValueTerm ⋏
            (compactFixedWidthEntryAtValuationFormula
                tableTerm widthTerm rightIndexTerm rightValueTerm ⋏
              “!!(shortBinaryNumeralTerm data.left) <
                !!(shortBinaryNumeralTerm data.right)”))
          (boundaryRowGuardStructuralPayloadResource
            valuation data.right tokenCount)
          (boundaryRowTerminalStructuralPayloadEnvelope
            tokenCount boundaryTable index data) := by
    simpa only [rightInstalledBody, hybridFormulaStructuralPayloadBound,
      valuation, tableTerm, widthTerm, leftIndexTerm, rightIndexTerm,
      leftValueTerm, rightValueTerm, rightGuarded, rightGuard, terminal,
      rightLt, leftCertificate, rightCertificate, ltCertificate] using
      hrightGuarded
  have hrightInstalled :=
    hybridExistsWitnessStructuralPayloadBound_le_envelope
      rightBody data.right rightInstalledBody _ hrightInstalledBody
  let leftGuard := boundedWitnessGuardCertificate valuation
    data.left tokenCount data.left_le
  let leftGuarded :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      leftGuard rightInstalled
  have hleftGuard :=
    boundedWitnessGuardCertificate_structuralPayloadBound_le_transparent
      valuation data.left tokenCount data.left_le
  have hleftGuarded := hybridConjunctionStructuralPayloadBound_le_envelope
    leftGuard rightInstalled _ _ hleftGuard hrightInstalled
  let leftBody := boundaryRowLeftWitnessBody tokenCount boundaryTable
  let leftInstalledBody := CheckedHybridValuationBoundedFormulaCertificate.cast
    (boundaryRowLeftWitnessBody_subst tokenCount boundaryTable
      data.left).symm leftGuarded
  have hleftInstalledBody :
      hybridFormulaStructuralPayloadBound leftInstalledBody <=
        hybridConjunctionStructuralPayloadEnvelope valuation
          (“!!(shortBinaryNumeralTerm data.left) <
            !!(shortBinaryNumeralTerm tokenCount) + 1” : ValuationFormula)
          (∃⁰ rightBody : ValuationFormula)
          (boundaryRowGuardStructuralPayloadResource
            valuation data.left tokenCount)
          (hybridExistsWitnessStructuralPayloadEnvelope valuation
            rightBody data.right
            (hybridConjunctionStructuralPayloadEnvelope valuation
              (“!!(shortBinaryNumeralTerm data.right) <
                !!(shortBinaryNumeralTerm tokenCount) + 1” :
                ValuationFormula)
              (compactFixedWidthEntryAtValuationFormula
                  tableTerm widthTerm leftIndexTerm leftValueTerm ⋏
                (compactFixedWidthEntryAtValuationFormula
                    tableTerm widthTerm rightIndexTerm rightValueTerm ⋏
                  “!!(shortBinaryNumeralTerm data.left) <
                    !!(shortBinaryNumeralTerm data.right)”))
              (boundaryRowGuardStructuralPayloadResource
                valuation data.right tokenCount)
              (boundaryRowTerminalStructuralPayloadEnvelope
                tokenCount boundaryTable index data))) := by
    simpa only [leftInstalledBody, hybridFormulaStructuralPayloadBound,
      leftGuarded, leftGuard, rightInstalled, rightBody] using hleftGuarded
  have hleftInstalled := hybridExistsWitnessStructuralPayloadBound_le_envelope
    leftBody data.left leftInstalledBody _ hleftInstalledBody
  simpa only [boundaryRowBranchCertificate,
    hybridFormulaStructuralPayloadBound,
    boundaryRowBranchStructuralPayloadEnvelope,
    valuation, tableTerm, widthTerm, leftIndexTerm, rightIndexTerm,
    leftValueTerm, rightValueTerm, leftCertificate, rightCertificate,
    ltCertificate, rightLt, terminal, rightGuard, rightGuarded, rightBody,
    rightInstalledBody, rightInstalled, leftGuard, leftGuarded, leftBody,
    leftInstalledBody] using hleftInstalled

noncomputable def boundaryTableBranchStructuralPayloadResourceSum
    (tokenCount partCount boundaryTable : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) : Nat :=
  ∑ index : Fin partCount,
    boundaryRowBranchStructuralPayloadEnvelope
      tokenCount boundaryTable index (rows index)

theorem boundaryTableDirectHybridBranchesAtCount_leafPayloadBound
    (tokenCount partCount boundaryTable : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    HybridBranchesLeafPayloadBound
      (boundaryTableBranchStructuralPayloadResourceSum
        tokenCount partCount boundaryTable rows)
      (boundaryTableDirectHybridBranchesAtCount
        tokenCount partCount boundaryTable rows) := by
  unfold boundaryTableDirectHybridBranchesAtCount
  apply buildExplicitHybridUniversalBranches_leafPayloadBound
  intro index hindex
  let finiteIndex : Fin partCount := ⟨index, hindex⟩
  have hbranch :=
    boundaryRowBranchCertificate_structuralPayloadBound_le_transparent
      tokenCount boundaryTable finiteIndex (rows finiteIndex)
  have hsum :
      boundaryRowBranchStructuralPayloadEnvelope
          tokenCount boundaryTable finiteIndex (rows finiteIndex) <=
        boundaryTableBranchStructuralPayloadResourceSum
          tokenCount partCount boundaryTable rows := by
    unfold boundaryTableBranchStructuralPayloadResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin partCount) _ => Nat.zero_le
        (boundaryRowBranchStructuralPayloadEnvelope
          tokenCount boundaryTable candidate (rows candidate)))
      (Finset.mem_univ finiteIndex)
  dsimp only [finiteIndex] at hbranch hsum ⊢
  exact hbranch.trans hsum

private theorem hybridBranchesLeafPayloadBound_transport
    {valuation : Nat -> Nat}
    {body : ArithmeticSemiformula Nat 1}
    {sourceBound targetBound leafBound : Nat}
    (hbound : sourceBound = targetBound)
    (branches : CheckedHybridValuationUniversalBranches
      valuation body sourceBound)
    (hleaves : HybridBranchesLeafPayloadBound leafBound branches) :
    HybridBranchesLeafPayloadBound leafBound (hbound ▸ branches) := by
  cases hbound
  exact hleaves

theorem boundaryTableDirectHybridBranches_leafPayloadBound
    (tokenCount partCount boundaryTable : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    HybridBranchesLeafPayloadBound
      (boundaryTableBranchStructuralPayloadResourceSum
        tokenCount partCount boundaryTable rows)
      (boundaryTableDirectHybridBranches
        tokenCount partCount boundaryTable rows) := by
  unfold boundaryTableDirectHybridBranches
  exact hybridBranchesLeafPayloadBound_transport
    (boundaryTableShortNumeralBound_eq_partCount partCount).symm
    (boundaryTableDirectHybridBranchesAtCount
      tokenCount partCount boundaryTable rows)
    (boundaryTableDirectHybridBranchesAtCount_leafPayloadBound
      tokenCount partCount boundaryTable rows)

noncomputable def boundaryTableBranchesTransparentStructuralEnvelope
    (tokenCount partCount boundaryTable : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) : Nat :=
  let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm partCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue layoutZeroValuation boundTerm
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    layoutZeroValuation body
    (boundaryTableBranchStructuralPayloadResourceSum
      tokenCount partCount boundaryTable rows)
    bound

theorem boundaryTableBranchesStructuralPayloadEnvelope_le_transparent
    (tokenCount partCount boundaryTable : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
    let boundTerm := shortBinaryNumeralTerm partCount
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift boundTerm) body
    hybridBranchesStructuralPayloadEnvelope
        (termValue layoutZeroValuation boundTerm)
        outerFormula.freeVariables
        (boundaryTableDirectHybridBranches
          tokenCount partCount boundaryTable rows) <=
      boundaryTableBranchesTransparentStructuralEnvelope
        tokenCount partCount boundaryTable rows := by
  let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm partCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue layoutZeroValuation boundTerm
  let branches := boundaryTableDirectHybridBranches
    tokenCount partCount boundaryTable rows
  have hleaves := boundaryTableDirectHybridBranches_leafPayloadBound
    tokenCount partCount boundaryTable rows
  have hbound := hybridBranchesStructuralPayloadEnvelope_le_uniformEnvelope
    bound outerVariables
    (boundaryTableBranchStructuralPayloadResourceSum
      tokenCount partCount boundaryTable rows)
    branches hleaves
  simpa only [boundaryTableBranchesTransparentStructuralEnvelope,
    body, boundTerm, outerFormula, outerVariables, bound, branches] using
    hbound

noncomputable def boundaryTableUniversalStructuralPayloadEnvelope
    (tokenCount partCount boundaryTable : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) : Nat :=
  let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm partCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables layoutZeroValuation
  let bound := termValue layoutZeroValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (boundaryTableBranchesTransparentStructuralEnvelope
      tokenCount partCount boundaryTable rows)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource layoutZeroValuation
      outerVariables boundTerm)
    branchResource

theorem boundaryTableUniversalCertificate_structuralPayloadBound_le_transparent
    (tokenCount partCount boundaryTable : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    hybridFormulaStructuralPayloadBound
        (boundaryTableUniversalCertificate
          tokenCount partCount boundaryTable rows) <=
      boundaryTableUniversalStructuralPayloadEnvelope
        tokenCount partCount boundaryTable rows := by
  let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm partCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables layoutZeroValuation
  let bound := termValue layoutZeroValuation boundTerm
  let branches := boundaryTableDirectHybridBranches
    tokenCount partCount boundaryTable rows
  let oldBranchCore := hybridBranchesStructuralPayloadEnvelope
    bound outerVariables branches
  let newBranchCore := boundaryTableBranchesTransparentStructuralEnvelope
    tokenCount partCount boundaryTable rows
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldBranchCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newBranchCore
  let boundResource := compileShiftedBoundEqualityPayloadResource
    layoutZeroValuation outerVariables boundTerm
  have hbranchCore : oldBranchCore <= newBranchCore := by
    dsimp only [oldBranchCore, newBranchCore, bound, branches,
      outerVariables, outerFormula, body, boundTerm]
    exact boundaryTableBranchesStructuralPayloadEnvelope_le_transparent
      tokenCount partCount boundaryTable rows
  have hbranchResource : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldBranchCore newBranchCore hbranchCore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift boundTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranchResource
  simpa only [boundaryTableUniversalCertificate,
    hybridFormulaStructuralPayloadBound,
    boundaryTableUniversalStructuralPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, branches,
    oldBranchCore, newBranchCore, oldBranchResource, newBranchResource,
    boundResource] using htotal

def boundaryValuationLeStructuralPayloadEnvelope
    (valuation : Nat -> Nat) (leftTerm rightTerm : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula := LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables valuation
  compilePositiveRelationPayloadResource valuation Language.Eq.eq args +
    compilePositiveRelationPayloadResource
      valuation Language.ORing.Rel.lt args +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert equalityFormula Gamma) +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert strictFormula Gamma) +
    FoundationCompactCertifiedContextProof.CertifiedPAContextProof.disjunctionFullAssemblyCost
      Gamma equalityFormula strictFormula

theorem valuationLeCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat) (leftTerm rightTerm : ValuationTerm)
    (hle : termValue valuation leftTerm <= termValue valuation rightTerm) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.valuationLeCertificate
          valuation leftTerm rightTerm hle) <=
      boundaryValuationLeStructuralPayloadEnvelope
        valuation leftTerm rightTerm := by
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  by_cases heq : termValue valuation leftTerm = termValue valuation rightTerm
  · simp only [
      FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.valuationLeCertificate]
    rw [dif_pos heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold boundaryValuationLeStructuralPayloadEnvelope
    dsimp only [args]
    omega
  · simp only [
      FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.valuationLeCertificate]
    rw [dif_neg heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold boundaryValuationLeStructuralPayloadEnvelope
    dsimp only [args]
    omega

def boundaryClosedLeStructuralPayloadEnvelope
    (valuation : Nat -> Nat) (left right : Nat) : Nat :=
  boundaryValuationLeStructuralPayloadEnvelope valuation
    (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right)

theorem closedLeCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat) (left right : Nat) (hle : left <= right) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.closedLeCertificate
          valuation left right hle) <=
      boundaryClosedLeStructuralPayloadEnvelope valuation left right := by
  let hterms : termValue valuation (shortBinaryNumeralTerm left) <=
      termValue valuation (shortBinaryNumeralTerm right) := by
    simpa only [termValue_shortBinaryNumeralTerm] using hle
  have hpublic := valuationLeCertificate_structuralPayloadBound_le_transparent
    valuation (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right)
    hterms
  change hybridFormulaStructuralPayloadBound
      (FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.valuationLeCertificate
        valuation (shortBinaryNumeralTerm left)
        (shortBinaryNumeralTerm right) hterms) <= _
  unfold boundaryClosedLeStructuralPayloadEnvelope
  exact hpublic

def compactAdditiveBoundaryTableStructuralPayloadEnvelope
    (tokenCount partCount start finish boundaryTable : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) : Nat :=
  let startFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm start) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let finishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let startEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount)
    (unaryNumeralTerm 0)
    (shortBinaryNumeralTerm start)
  let finishEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm partCount)
    (shortBinaryNumeralTerm finish)
  let universalFormula :=
    (compactAdditiveBoundaryTableRowBody
      tokenCount boundaryTable).ballLT
        (shortBinaryNumeralTerm partCount)
  let startResource := boundaryClosedLeStructuralPayloadEnvelope
    layoutZeroValuation start tokenCount
  let finishResource := boundaryClosedLeStructuralPayloadEnvelope
    layoutZeroValuation finish tokenCount
  let startEntryResource :=
    compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
      layoutZeroValuation
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount)
      (unaryNumeralTerm 0)
      (shortBinaryNumeralTerm start)
  let finishEntryResource :=
    compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
      layoutZeroValuation
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm partCount)
      (shortBinaryNumeralTerm finish)
  let universalResource := boundaryTableUniversalStructuralPayloadEnvelope
    tokenCount partCount boundaryTable rows
  let finishEntryUniversalResource :=
    hybridConjunctionStructuralPayloadEnvelope layoutZeroValuation
      finishEntryFormula universalFormula
      finishEntryResource universalResource
  let startEntryTailResource := hybridConjunctionStructuralPayloadEnvelope
    layoutZeroValuation startEntryFormula
    (finishEntryFormula ⋏ universalFormula)
    startEntryResource finishEntryUniversalResource
  let finishTailResource := hybridConjunctionStructuralPayloadEnvelope
    layoutZeroValuation finishFormula
    (startEntryFormula ⋏ (finishEntryFormula ⋏ universalFormula))
    finishResource startEntryTailResource
  hybridConjunctionStructuralPayloadEnvelope layoutZeroValuation
    startFormula
    (finishFormula ⋏
      (startEntryFormula ⋏ (finishEntryFormula ⋏ universalFormula)))
    startResource finishTailResource

theorem
    compactAdditiveBoundaryTableExplicitHybridCertificate_structuralPayloadBound_le_transparent
    (tokenCount partCount start finish boundaryTable : Nat)
    (hstartBound : start <= tokenCount)
    (hfinishBound : finish <= tokenCount)
    (hstartEntry : CompactFixedWidthEntry
      boundaryTable tokenCount 0 start)
    (hfinishEntry : CompactFixedWidthEntry
      boundaryTable tokenCount partCount finish)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveBoundaryTableExplicitHybridCertificate
          tokenCount partCount start finish boundaryTable
          hstartBound hfinishBound hstartEntry hfinishEntry rows) <=
      compactAdditiveBoundaryTableStructuralPayloadEnvelope
        tokenCount partCount start finish boundaryTable rows := by
  let startCertificate :=
    FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.closedLeCertificate
      layoutZeroValuation start tokenCount hstartBound
  let finishCertificate :=
    FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.closedLeCertificate
      layoutZeroValuation finish tokenCount hfinishBound
  let startEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      layoutZeroValuation
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount)
      (unaryNumeralTerm 0)
      (shortBinaryNumeralTerm start) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_unaryNumeralTerm] using hstartEntry)
  let finishEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      layoutZeroValuation
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm partCount)
      (shortBinaryNumeralTerm finish) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hfinishEntry)
  let universalCertificate := boundaryTableUniversalCertificate
    tokenCount partCount boundaryTable rows
  have hstart := closedLeCertificate_structuralPayloadBound_le_transparent
    layoutZeroValuation start tokenCount hstartBound
  have hfinish := closedLeCertificate_structuralPayloadBound_le_transparent
    layoutZeroValuation finish tokenCount hfinishBound
  have hwidth :
      (shortBinaryNumeralTerm tokenCount).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have htable :
      (shortBinaryNumeralTerm boundaryTable).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
  have hstartIndex : (unaryNumeralTerm 0).freeVariables = ∅ := by
    simp [unaryNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]
  have hfinishIndex :
      (shortBinaryNumeralTerm partCount).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty partCount
  have hstartValue :
      (shortBinaryNumeralTerm start).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty start
  have hfinishValue :
      (shortBinaryNumeralTerm finish).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty finish
  have hstartEntryResource :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      layoutZeroValuation
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount)
      (unaryNumeralTerm 0)
      (shortBinaryNumeralTerm start)
      htable hwidth hstartIndex hstartValue (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_unaryNumeralTerm] using hstartEntry)
  have hfinishEntryResource :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      layoutZeroValuation
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm partCount)
      (shortBinaryNumeralTerm finish)
      htable hwidth hfinishIndex hfinishValue (by
        simpa only [termValue_shortBinaryNumeralTerm] using hfinishEntry)
  have huniversal :=
    boundaryTableUniversalCertificate_structuralPayloadBound_le_transparent
      tokenCount partCount boundaryTable rows
  let finishEntryUniversal :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      finishEntryCertificate universalCertificate
  have hfinishEntryUniversal :=
    hybridConjunctionStructuralPayloadBound_le_envelope
      finishEntryCertificate universalCertificate _ _
      hfinishEntryResource huniversal
  let startEntryTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      startEntryCertificate finishEntryUniversal
  have hstartEntryTail := hybridConjunctionStructuralPayloadBound_le_envelope
    startEntryCertificate finishEntryUniversal _ _
    hstartEntryResource hfinishEntryUniversal
  let finishTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      finishCertificate startEntryTail
  have hfinishTail := hybridConjunctionStructuralPayloadBound_le_envelope
    finishCertificate startEntryTail _ _ hfinish hstartEntryTail
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    startCertificate finishTail
  have hparts := hybridConjunctionStructuralPayloadBound_le_envelope
    startCertificate finishTail _ _ hstart hfinishTail
  simpa only [compactAdditiveBoundaryTableExplicitHybridCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveBoundaryTableStructuralPayloadEnvelope,
    startCertificate, finishCertificate, startEntryCertificate,
    finishEntryCertificate, universalCertificate, finishEntryUniversal,
    startEntryTail, finishTail, parts] using hparts

def compactAdditiveStructuredListLayoutStructuralPayloadEnvelope
    (tokenTable width tokenCount start count finish boundaryTable bodyStart :
      Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) : Nat :=
  let witnessBody := compactAdditiveStructuredListLayoutWitnessBody
    tokenTable width tokenCount start count finish boundaryTable
  let guardFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm bodyStart) <
      !!(shortBinaryNumeralTerm tokenCount) + 1”
  let headerFormula :=
    FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.compactAdditiveListHeaderClosedFormula
      tokenTable width tokenCount start count bodyStart
  let boundaryFormula := compactAdditiveBoundaryTableClosedFormula
    tokenCount count bodyStart finish boundaryTable
  let headerResource :=
    compactAdditiveListHeaderStructuralPayloadPolynomial
      tokenTable width tokenCount start count bodyStart
  let boundaryResource :=
    compactAdditiveBoundaryTableStructuralPayloadEnvelope
      tokenCount count bodyStart finish boundaryTable rows
  let innerResource := hybridConjunctionStructuralPayloadEnvelope
    layoutZeroValuation headerFormula boundaryFormula
    headerResource boundaryResource
  let postResource := hybridConjunctionStructuralPayloadEnvelope
    layoutZeroValuation guardFormula (headerFormula ⋏ boundaryFormula)
    (boundaryRowGuardStructuralPayloadResource
      layoutZeroValuation bodyStart tokenCount)
    innerResource
  hybridExistsWitnessStructuralPayloadEnvelope layoutZeroValuation
    witnessBody bodyStart postResource

theorem
    compactAdditiveStructuredListLayoutExplicitHybridCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount start count finish boundaryTable bodyStart :
      Nat)
    (hbodyStart : bodyStart <= tokenCount)
    (hheader : CompactAdditiveListHeader
      tokenTable width tokenCount start count bodyStart)
    (hboundaryFinish : finish <= tokenCount)
    (hboundaryStartEntry : CompactFixedWidthEntry
      boundaryTable tokenCount 0 bodyStart)
    (hboundaryFinishEntry : CompactFixedWidthEntry
      boundaryTable tokenCount count finish)
    (rows : (index : Fin count) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveStructuredListLayoutExplicitHybridCertificate
          tokenTable width tokenCount start count finish boundaryTable
          bodyStart hbodyStart hheader hboundaryFinish
          hboundaryStartEntry hboundaryFinishEntry rows) <=
      compactAdditiveStructuredListLayoutStructuralPayloadEnvelope
        tokenTable width tokenCount start count finish boundaryTable
        bodyStart rows := by
  let witnessBody := compactAdditiveStructuredListLayoutWitnessBody
    tokenTable width tokenCount start count finish boundaryTable
  let guardCertificate := boundedWitnessGuardCertificate
    layoutZeroValuation bodyStart tokenCount hbodyStart
  let headerCertificate :=
    compactAdditiveListHeaderExplicitHybridCertificate
      tokenTable width tokenCount start count bodyStart hheader
  let boundaryCertificate :=
    compactAdditiveBoundaryTableExplicitHybridCertificate
      tokenCount count bodyStart finish boundaryTable
      hbodyStart hboundaryFinish hboundaryStartEntry
      hboundaryFinishEntry rows
  let inner := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    headerCertificate boundaryCertificate
  let post := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    guardCertificate inner
  have hguard :=
    boundedWitnessGuardCertificate_structuralPayloadBound_le_transparent
      layoutZeroValuation bodyStart tokenCount hbodyStart
  have hheaderResource :=
    compactAdditiveListHeaderExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount start count bodyStart hheader
  have hboundaryResource :=
    compactAdditiveBoundaryTableExplicitHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount count bodyStart finish boundaryTable
      hbodyStart hboundaryFinish hboundaryStartEntry
      hboundaryFinishEntry rows
  have hinner : hybridFormulaStructuralPayloadBound inner <=
      hybridConjunctionStructuralPayloadEnvelope layoutZeroValuation
        (FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.compactAdditiveListHeaderClosedFormula
          tokenTable width tokenCount start count bodyStart)
        (compactAdditiveBoundaryTableClosedFormula
          tokenCount count bodyStart finish boundaryTable)
        (compactAdditiveListHeaderStructuralPayloadPolynomial
          tokenTable width tokenCount start count bodyStart)
        (compactAdditiveBoundaryTableStructuralPayloadEnvelope
          tokenCount count bodyStart finish boundaryTable rows) := by
    have hraw := hybridConjunctionStructuralPayloadBound_le_envelope
      headerCertificate boundaryCertificate _ _
      hheaderResource hboundaryResource
    have hzero :
        FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation =
          FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation := by
      funext index
      rfl
    simpa only [inner, headerCertificate, boundaryCertificate,
      layoutZeroValuation, hzero]
      using hraw
  have hpost := hybridConjunctionStructuralPayloadBound_le_envelope
    guardCertificate inner _ _ hguard hinner
  let installed := CheckedHybridValuationBoundedFormulaCertificate.cast
    (compactAdditiveStructuredListLayoutWitnessBody_subst
      tokenTable width tokenCount start count finish boundaryTable
      bodyStart).symm post
  have hinstalled : hybridFormulaStructuralPayloadBound installed <=
      hybridConjunctionStructuralPayloadEnvelope layoutZeroValuation
        (“!!(shortBinaryNumeralTerm bodyStart) <
          !!(shortBinaryNumeralTerm tokenCount) + 1” : ValuationFormula)
        (FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.compactAdditiveListHeaderClosedFormula
            tokenTable width tokenCount start count bodyStart ⋏
          compactAdditiveBoundaryTableClosedFormula
            tokenCount count bodyStart finish boundaryTable)
        (boundaryRowGuardStructuralPayloadResource
          layoutZeroValuation bodyStart tokenCount)
        (hybridConjunctionStructuralPayloadEnvelope layoutZeroValuation
          (FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.compactAdditiveListHeaderClosedFormula
            tokenTable width tokenCount start count bodyStart)
          (compactAdditiveBoundaryTableClosedFormula
            tokenCount count bodyStart finish boundaryTable)
          (compactAdditiveListHeaderStructuralPayloadPolynomial
            tokenTable width tokenCount start count bodyStart)
          (compactAdditiveBoundaryTableStructuralPayloadEnvelope
            tokenCount count bodyStart finish boundaryTable rows)) := by
    simpa only [installed, hybridFormulaStructuralPayloadBound,
      post, inner, guardCertificate, headerCertificate,
      boundaryCertificate, layoutZeroValuation,
      FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation,
      FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation]
      using hpost
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.existsWitness
      witnessBody bodyStart installed
  have hdirect := hybridExistsWitnessStructuralPayloadBound_le_envelope
    witnessBody bodyStart installed _ hinstalled
  simpa only [compactAdditiveStructuredListLayoutExplicitHybridCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveStructuredListLayoutStructuralPayloadEnvelope,
    witnessBody, guardCertificate, headerCertificate, boundaryCertificate,
    inner, post, installed, direct] using hdirect

def compactAdditiveStructuredListLayoutDataStructuralPayloadEnvelope
    (tokenTable width tokenCount start count finish boundaryTable : Nat)
    (data : CompactAdditiveStructuredListLayoutData
      tokenTable width tokenCount start count finish boundaryTable) : Nat :=
  compactAdditiveStructuredListLayoutStructuralPayloadEnvelope
    tokenTable width tokenCount start count finish boundaryTable
    data.bodyStart data.rows

theorem
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfData_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount start count finish boundaryTable : Nat)
    (data : CompactAdditiveStructuredListLayoutData
      tokenTable width tokenCount start count finish boundaryTable) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfData
          tokenTable width tokenCount start count finish boundaryTable data) <=
      compactAdditiveStructuredListLayoutDataStructuralPayloadEnvelope
        tokenTable width tokenCount start count finish boundaryTable data := by
  exact
    compactAdditiveStructuredListLayoutExplicitHybridCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount start count finish boundaryTable
      data.bodyStart data.bodyStart_le_tokenCount data.header
      data.boundaryFinish_le_tokenCount data.boundaryStartEntry
      data.boundaryFinishEntry data.rows

theorem
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount start count finish boundaryTable : Nat)
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
          tokenTable width tokenCount start count finish boundaryTable hlayout) <=
      compactAdditiveStructuredListLayoutDataStructuralPayloadEnvelope
        tokenTable width tokenCount start count finish boundaryTable
        (compactAdditiveStructuredListLayoutDataOfLayout
          tokenTable width tokenCount start count finish boundaryTable
          hlayout) := by
  exact
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfData_structuralPayloadBound_le_transparent
      tokenTable width tokenCount start count finish boundaryTable
      (compactAdditiveStructuredListLayoutDataOfLayout
        tokenTable width tokenCount start count finish boundaryTable hlayout)

/-! ## Removing layout-data dependence by finite public envelopes -/

def boundaryRowTerminalStructuralPayloadEnvelopeOfValues
    (tokenCount boundaryTable index left right : Nat) : Nat :=
  let valuation := extendValuation index layoutZeroValuation
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm : ValuationTerm := &0
  let rightIndexTerm : ValuationTerm := ‘&0 + 1’
  let leftValueTerm := shortBinaryNumeralTerm left
  let rightValueTerm := shortBinaryNumeralTerm right
  let leftFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm leftIndexTerm leftValueTerm
  let rightFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm rightIndexTerm rightValueTerm
  let ltFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm left) <
      !!(shortBinaryNumeralTerm right)”
  let leftResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation tableTerm widthTerm leftIndexTerm leftValueTerm
  let rightResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation tableTerm widthTerm rightIndexTerm rightValueTerm
  let ltResource := boundaryRowClosedLtStructuralPayloadResource
    valuation left right
  let rightLtResource := hybridConjunctionStructuralPayloadEnvelope
    valuation rightFormula ltFormula rightResource ltResource
  hybridConjunctionStructuralPayloadEnvelope valuation leftFormula
    (rightFormula ⋏ ltFormula) leftResource rightLtResource

def boundaryRowBranchStructuralPayloadEnvelopeOfValues
    (tokenCount boundaryTable index left right : Nat) : Nat :=
  let valuation := extendValuation index layoutZeroValuation
  let terminalFormula :=
    compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount)
        (&0 : ValuationTerm)
        (shortBinaryNumeralTerm left) ⋏
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (‘&0 + 1’ : ValuationTerm)
          (shortBinaryNumeralTerm right) ⋏
        “!!(shortBinaryNumeralTerm left) <
          !!(shortBinaryNumeralTerm right)”)
  let rightGuardFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm right) <
      !!(shortBinaryNumeralTerm tokenCount) + 1”
  let rightGuardedResource := hybridConjunctionStructuralPayloadEnvelope
    valuation rightGuardFormula terminalFormula
    (boundaryRowGuardStructuralPayloadResource
      valuation right tokenCount)
    (boundaryRowTerminalStructuralPayloadEnvelopeOfValues
      tokenCount boundaryTable index left right)
  let rightExistsFormula : ValuationFormula :=
    ∃⁰ boundaryRowRightWitnessBody tokenCount boundaryTable left
  let rightExistsResource := hybridExistsWitnessStructuralPayloadEnvelope
    valuation (boundaryRowRightWitnessBody
      tokenCount boundaryTable left) right rightGuardedResource
  let leftGuardFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm left) <
      !!(shortBinaryNumeralTerm tokenCount) + 1”
  let leftGuardedResource := hybridConjunctionStructuralPayloadEnvelope
    valuation leftGuardFormula rightExistsFormula
    (boundaryRowGuardStructuralPayloadResource
      valuation left tokenCount)
    rightExistsResource
  hybridExistsWitnessStructuralPayloadEnvelope valuation
    (boundaryRowLeftWitnessBody tokenCount boundaryTable)
    left leftGuardedResource

theorem boundaryRowBranchStructuralPayloadEnvelope_eq_values
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index) :
    boundaryRowBranchStructuralPayloadEnvelope
        tokenCount boundaryTable index data =
      boundaryRowBranchStructuralPayloadEnvelopeOfValues
        tokenCount boundaryTable index data.left data.right := by
  rfl

def boundaryRowPublicFiniteBranchEnvelope
    (tokenCount boundaryTable index : Nat) : Nat :=
  (Finset.range (tokenCount + 1)).sum fun left =>
    (Finset.range (tokenCount + 1)).sum fun right =>
      boundaryRowBranchStructuralPayloadEnvelopeOfValues
        tokenCount boundaryTable index left right

theorem boundaryRowBranchStructuralPayloadEnvelope_le_publicFinite
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index) :
    boundaryRowBranchStructuralPayloadEnvelope
        tokenCount boundaryTable index data <=
      boundaryRowPublicFiniteBranchEnvelope
        tokenCount boundaryTable index := by
  rw [boundaryRowBranchStructuralPayloadEnvelope_eq_values]
  have hright :
      boundaryRowBranchStructuralPayloadEnvelopeOfValues
          tokenCount boundaryTable index data.left data.right <=
        (Finset.range (tokenCount + 1)).sum fun right =>
          boundaryRowBranchStructuralPayloadEnvelopeOfValues
            tokenCount boundaryTable index data.left right := by
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        (boundaryRowBranchStructuralPayloadEnvelopeOfValues
          tokenCount boundaryTable index data.left candidate))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le data.right_le))
  have hleft :
      ((Finset.range (tokenCount + 1)).sum fun right =>
          boundaryRowBranchStructuralPayloadEnvelopeOfValues
            tokenCount boundaryTable index data.left right) <=
        boundaryRowPublicFiniteBranchEnvelope
          tokenCount boundaryTable index := by
    unfold boundaryRowPublicFiniteBranchEnvelope
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        ((Finset.range (tokenCount + 1)).sum fun right =>
          boundaryRowBranchStructuralPayloadEnvelopeOfValues
            tokenCount boundaryTable index candidate right))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le data.left_le))
  exact hright.trans hleft

def boundaryTablePublicFiniteLeafPayloadResourceSum
    (tokenCount partCount boundaryTable : Nat) : Nat :=
  ∑ index : Fin partCount,
    boundaryRowPublicFiniteBranchEnvelope
      tokenCount boundaryTable index

theorem boundaryTableBranchStructuralPayloadResourceSum_le_publicFinite
    (tokenCount partCount boundaryTable : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    boundaryTableBranchStructuralPayloadResourceSum
        tokenCount partCount boundaryTable rows <=
      boundaryTablePublicFiniteLeafPayloadResourceSum
        tokenCount partCount boundaryTable := by
  unfold boundaryTableBranchStructuralPayloadResourceSum
    boundaryTablePublicFiniteLeafPayloadResourceSum
  exact Finset.sum_le_sum fun index _ =>
    boundaryRowBranchStructuralPayloadEnvelope_le_publicFinite
      tokenCount boundaryTable index (rows index)

private theorem hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf
    (totalBound : Nat) (outerVariables : Finset Nat)
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    {small large : Nat} (hresource : small <= large) :
    forall bound,
      hybridBranchesUniformStructuralPayloadEnvelope totalBound outerVariables
          valuation body small bound <=
        hybridBranchesUniformStructuralPayloadEnvelope totalBound
          outerVariables valuation body large bound
  | 0 => by rfl
  | bound + 1 => by
      simp only [hybridBranchesUniformStructuralPayloadEnvelope]
      have hinduction :=
        hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf totalBound
          outerVariables valuation body hresource bound
      omega

def boundaryTableBranchesPublicFiniteStructuralEnvelope
    (tokenCount partCount boundaryTable : Nat) : Nat :=
  let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm partCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue layoutZeroValuation boundTerm
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    layoutZeroValuation body
    (boundaryTablePublicFiniteLeafPayloadResourceSum
      tokenCount partCount boundaryTable)
    bound

theorem boundaryTableBranchesTransparentStructuralEnvelope_le_publicFinite
    (tokenCount partCount boundaryTable : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    boundaryTableBranchesTransparentStructuralEnvelope
        tokenCount partCount boundaryTable rows <=
      boundaryTableBranchesPublicFiniteStructuralEnvelope
        tokenCount partCount boundaryTable := by
  unfold boundaryTableBranchesTransparentStructuralEnvelope
    boundaryTableBranchesPublicFiniteStructuralEnvelope
  exact hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf
    (termValue layoutZeroValuation (shortBinaryNumeralTerm partCount))
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm partCount))
      (compactAdditiveBoundaryTableRowBody
        tokenCount boundaryTable)).freeVariables
    layoutZeroValuation
    (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable)
    (boundaryTableBranchStructuralPayloadResourceSum_le_publicFinite
      tokenCount partCount boundaryTable rows)
    (termValue layoutZeroValuation (shortBinaryNumeralTerm partCount))

def boundaryTablePublicFiniteUniversalStructuralPayloadEnvelope
    (tokenCount partCount boundaryTable : Nat) : Nat :=
  let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm partCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables layoutZeroValuation
  let bound := termValue layoutZeroValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (boundaryTableBranchesPublicFiniteStructuralEnvelope
      tokenCount partCount boundaryTable)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource layoutZeroValuation
      outerVariables boundTerm)
    branchResource

theorem boundaryTableUniversalStructuralPayloadEnvelope_le_publicFinite
    (tokenCount partCount boundaryTable : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    boundaryTableUniversalStructuralPayloadEnvelope
        tokenCount partCount boundaryTable rows <=
      boundaryTablePublicFiniteUniversalStructuralPayloadEnvelope
        tokenCount partCount boundaryTable := by
  let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm partCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables layoutZeroValuation
  let bound := termValue layoutZeroValuation boundTerm
  let oldCore := boundaryTableBranchesTransparentStructuralEnvelope
    tokenCount partCount boundaryTable rows
  let newCore := boundaryTableBranchesPublicFiniteStructuralEnvelope
    tokenCount partCount boundaryTable
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newCore
  let boundResource := compileShiftedBoundEqualityPayloadResource
    layoutZeroValuation outerVariables boundTerm
  have hcore : oldCore <= newCore := by
    exact boundaryTableBranchesTransparentStructuralEnvelope_le_publicFinite
      tokenCount partCount boundaryTable rows
  have hbranch : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldCore newCore hcore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift boundTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranch
  simpa only [boundaryTableUniversalStructuralPayloadEnvelope,
    boundaryTablePublicFiniteUniversalStructuralPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, oldCore,
    newCore, oldBranchResource, newBranchResource, boundResource] using htotal

private theorem hybridConjunctionStructuralPayloadEnvelope_mono
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    {leftSmall leftLarge rightSmall rightLarge : Nat}
    (hleft : leftSmall <= leftLarge)
    (hright : rightSmall <= rightLarge) :
    hybridConjunctionStructuralPayloadEnvelope valuation left right
        leftSmall rightSmall <=
      hybridConjunctionStructuralPayloadEnvelope valuation left right
        leftLarge rightLarge := by
  unfold hybridConjunctionStructuralPayloadEnvelope
  dsimp only
  omega

private theorem hybridExistsWitnessStructuralPayloadEnvelope_mono
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : Nat) {small large : Nat} (hresource : small <= large) :
    hybridExistsWitnessStructuralPayloadEnvelope valuation body witness small <=
      hybridExistsWitnessStructuralPayloadEnvelope
        valuation body witness large := by
  unfold hybridExistsWitnessStructuralPayloadEnvelope
  dsimp only
  omega

def compactAdditiveBoundaryTablePublicFiniteStructuralPayloadEnvelope
    (tokenCount partCount start finish boundaryTable : Nat) : Nat :=
  let startFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm start) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let finishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let startEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount)
    (unaryNumeralTerm 0)
    (shortBinaryNumeralTerm start)
  let finishEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm partCount)
    (shortBinaryNumeralTerm finish)
  let universalFormula :=
    (compactAdditiveBoundaryTableRowBody
      tokenCount boundaryTable).ballLT
        (shortBinaryNumeralTerm partCount)
  let startResource := boundaryClosedLeStructuralPayloadEnvelope
    layoutZeroValuation start tokenCount
  let finishResource := boundaryClosedLeStructuralPayloadEnvelope
    layoutZeroValuation finish tokenCount
  let startEntryResource :=
    compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
      layoutZeroValuation
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount)
      (unaryNumeralTerm 0)
      (shortBinaryNumeralTerm start)
  let finishEntryResource :=
    compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
      layoutZeroValuation
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm partCount)
      (shortBinaryNumeralTerm finish)
  let universalResource :=
    boundaryTablePublicFiniteUniversalStructuralPayloadEnvelope
      tokenCount partCount boundaryTable
  let finishEntryUniversalResource :=
    hybridConjunctionStructuralPayloadEnvelope layoutZeroValuation
      finishEntryFormula universalFormula finishEntryResource universalResource
  let startEntryTailResource := hybridConjunctionStructuralPayloadEnvelope
    layoutZeroValuation startEntryFormula
    (finishEntryFormula ⋏ universalFormula)
    startEntryResource finishEntryUniversalResource
  let finishTailResource := hybridConjunctionStructuralPayloadEnvelope
    layoutZeroValuation finishFormula
    (startEntryFormula ⋏ (finishEntryFormula ⋏ universalFormula))
    finishResource startEntryTailResource
  hybridConjunctionStructuralPayloadEnvelope layoutZeroValuation
    startFormula
    (finishFormula ⋏
      (startEntryFormula ⋏ (finishEntryFormula ⋏ universalFormula)))
    startResource finishTailResource

theorem compactAdditiveBoundaryTableStructuralPayloadEnvelope_le_publicFinite
    (tokenCount partCount start finish boundaryTable : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    compactAdditiveBoundaryTableStructuralPayloadEnvelope
        tokenCount partCount start finish boundaryTable rows <=
      compactAdditiveBoundaryTablePublicFiniteStructuralPayloadEnvelope
        tokenCount partCount start finish boundaryTable := by
  have huniversal :=
    boundaryTableUniversalStructuralPayloadEnvelope_le_publicFinite
      tokenCount partCount boundaryTable rows
  unfold compactAdditiveBoundaryTableStructuralPayloadEnvelope
    compactAdditiveBoundaryTablePublicFiniteStructuralPayloadEnvelope
  exact hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ le_rfl
    (hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ le_rfl
      (hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ le_rfl
        (hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ le_rfl
          huniversal)))

def compactAdditiveStructuredListLayoutPublicFiniteAtBodyStartEnvelope
    (tokenTable width tokenCount start count finish boundaryTable bodyStart :
      Nat) : Nat :=
  let witnessBody := compactAdditiveStructuredListLayoutWitnessBody
    tokenTable width tokenCount start count finish boundaryTable
  let guardFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm bodyStart) <
      !!(shortBinaryNumeralTerm tokenCount) + 1”
  let headerFormula :=
    FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.compactAdditiveListHeaderClosedFormula
      tokenTable width tokenCount start count bodyStart
  let boundaryFormula := compactAdditiveBoundaryTableClosedFormula
    tokenCount count bodyStart finish boundaryTable
  let headerResource :=
    compactAdditiveListHeaderStructuralPayloadPolynomial
      tokenTable width tokenCount start count bodyStart
  let boundaryResource :=
    compactAdditiveBoundaryTablePublicFiniteStructuralPayloadEnvelope
      tokenCount count bodyStart finish boundaryTable
  let innerResource := hybridConjunctionStructuralPayloadEnvelope
    layoutZeroValuation headerFormula boundaryFormula
    headerResource boundaryResource
  let postResource := hybridConjunctionStructuralPayloadEnvelope
    layoutZeroValuation guardFormula (headerFormula ⋏ boundaryFormula)
    (boundaryRowGuardStructuralPayloadResource
      layoutZeroValuation bodyStart tokenCount)
    innerResource
  hybridExistsWitnessStructuralPayloadEnvelope layoutZeroValuation
    witnessBody bodyStart postResource

theorem
    compactAdditiveStructuredListLayoutStructuralPayloadEnvelope_le_publicFiniteAtBodyStart
    (tokenTable width tokenCount start count finish boundaryTable bodyStart :
      Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    compactAdditiveStructuredListLayoutStructuralPayloadEnvelope
        tokenTable width tokenCount start count finish boundaryTable
        bodyStart rows <=
      compactAdditiveStructuredListLayoutPublicFiniteAtBodyStartEnvelope
        tokenTable width tokenCount start count finish boundaryTable
        bodyStart := by
  have hboundary :=
    compactAdditiveBoundaryTableStructuralPayloadEnvelope_le_publicFinite
      tokenCount count bodyStart finish boundaryTable rows
  unfold compactAdditiveStructuredListLayoutStructuralPayloadEnvelope
    compactAdditiveStructuredListLayoutPublicFiniteAtBodyStartEnvelope
  exact hybridExistsWitnessStructuralPayloadEnvelope_mono _ _ _
    (hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ le_rfl
      (hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ le_rfl
        hboundary))

def compactAdditiveStructuredListLayoutPublicFiniteStructuralPayloadEnvelope
    (tokenTable width tokenCount start count finish boundaryTable : Nat) :
    Nat :=
  (Finset.range (tokenCount + 1)).sum fun bodyStart =>
    compactAdditiveStructuredListLayoutPublicFiniteAtBodyStartEnvelope
      tokenTable width tokenCount start count finish boundaryTable bodyStart

theorem
    compactAdditiveStructuredListLayoutDataStructuralPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount start count finish boundaryTable : Nat)
    (data : CompactAdditiveStructuredListLayoutData
      tokenTable width tokenCount start count finish boundaryTable) :
    compactAdditiveStructuredListLayoutDataStructuralPayloadEnvelope
        tokenTable width tokenCount start count finish boundaryTable data <=
      compactAdditiveStructuredListLayoutPublicFiniteStructuralPayloadEnvelope
        tokenTable width tokenCount start count finish boundaryTable := by
  have hatBodyStart :=
    compactAdditiveStructuredListLayoutStructuralPayloadEnvelope_le_publicFiniteAtBodyStart
      tokenTable width tokenCount start count finish boundaryTable
      data.bodyStart data.rows
  have hsum :
      compactAdditiveStructuredListLayoutPublicFiniteAtBodyStartEnvelope
          tokenTable width tokenCount start count finish boundaryTable
          data.bodyStart <=
        compactAdditiveStructuredListLayoutPublicFiniteStructuralPayloadEnvelope
          tokenTable width tokenCount start count finish boundaryTable := by
    unfold compactAdditiveStructuredListLayoutPublicFiniteStructuralPayloadEnvelope
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        (compactAdditiveStructuredListLayoutPublicFiniteAtBodyStartEnvelope
          tokenTable width tokenCount start count finish boundaryTable
          candidate))
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_le data.bodyStart_le_tokenCount))
  unfold compactAdditiveStructuredListLayoutDataStructuralPayloadEnvelope
  exact hatBodyStart.trans hsum

theorem
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfData_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount start count finish boundaryTable : Nat)
    (data : CompactAdditiveStructuredListLayoutData
      tokenTable width tokenCount start count finish boundaryTable) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfData
          tokenTable width tokenCount start count finish boundaryTable data) <=
      compactAdditiveStructuredListLayoutPublicFiniteStructuralPayloadEnvelope
        tokenTable width tokenCount start count finish boundaryTable := by
  exact
    (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfData_structuralPayloadBound_le_transparent
      tokenTable width tokenCount start count finish boundaryTable data).trans
    (compactAdditiveStructuredListLayoutDataStructuralPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount start count finish boundaryTable data)

theorem
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount start count finish boundaryTable : Nat)
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
          tokenTable width tokenCount start count finish boundaryTable hlayout) <=
      compactAdditiveStructuredListLayoutPublicFiniteStructuralPayloadEnvelope
        tokenTable width tokenCount start count finish boundaryTable := by
  exact
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfData_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount start count finish boundaryTable
      (compactAdditiveStructuredListLayoutDataOfLayout
        tokenTable width tokenCount start count finish boundaryTable hlayout)

#print axioms
  boundedWitnessGuardCertificate_structuralPayloadBound_le_transparent
#print axioms closedLtCertificate_structuralPayloadBound_le_transparent
#print axioms
  boundaryRowBranchCertificate_structuralPayloadBound_le_transparent
#print axioms boundaryTableDirectHybridBranches_leafPayloadBound
#print axioms
  boundaryTableUniversalCertificate_structuralPayloadBound_le_transparent
#print axioms closedLeCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveBoundaryTableExplicitHybridCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveStructuredListLayoutExplicitHybridCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveStructuredListLayoutExplicitHybridCertificateOfData_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_transparent
#print axioms
  boundaryRowBranchStructuralPayloadEnvelope_le_publicFinite
#print axioms
  boundaryTableUniversalStructuralPayloadEnvelope_le_publicFinite
#print axioms
  compactAdditiveBoundaryTableStructuralPayloadEnvelope_le_publicFinite
#print axioms
  compactAdditiveStructuredListLayoutDataStructuralPayloadEnvelope_le_publicFinite
#print axioms
  compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
