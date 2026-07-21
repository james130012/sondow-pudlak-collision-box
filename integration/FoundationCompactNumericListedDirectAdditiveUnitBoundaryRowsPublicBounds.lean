import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds

/-!
# Public structural resources for additive unit-boundary rows

The two cursor witnesses are installed by the audited bounded-witness
recursion.  Their fixed-width entries are compiled at the open universal row
index, and the successor equation is compiled as a positive atomic formula.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
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
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate

private abbrev unitZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.zeroValuation

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

def unitBoundarySuccessorStructuralPayloadResource
    (valuation : Nat -> Nat) (left right : Nat) : Nat :=
  compilePositiveRelationPayloadResource valuation Language.Eq.eq
    ![shortBinaryNumeralTerm right,
      (‘!!(shortBinaryNumeralTerm left) + 1’ : ValuationTerm)]

theorem successorEqualityCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat) (left right : Nat)
    (hsuccessor : right = left + 1) :
    hybridFormulaStructuralPayloadBound
        (successorEqualityCertificate valuation left right hsuccessor) <=
      unitBoundarySuccessorStructuralPayloadResource valuation left right := by
  simp only [successorEqualityCertificate,
    hybridFormulaStructuralPayloadBound]
  exact le_rfl

def compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelope
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index) : Nat :=
  let valuation := extendValuation index unitZeroValuation
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
  let successorFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm data.right) =
      !!(shortBinaryNumeralTerm data.left) + 1”
  let leftResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation tableTerm widthTerm leftIndexTerm leftValueTerm
  let rightResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation tableTerm widthTerm rightIndexTerm rightValueTerm
  let successorResource := unitBoundarySuccessorStructuralPayloadResource
    valuation data.left data.right
  let rightSuccessorResource := hybridConjunctionStructuralPayloadEnvelope
    valuation rightFormula successorFormula rightResource successorResource
  hybridConjunctionStructuralPayloadEnvelope valuation leftFormula
    (rightFormula ⋏ successorFormula) leftResource rightSuccessorResource

def compactAdditiveUnitBoundaryRowsBranchStructuralPayloadEnvelope
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index) : Nat :=
  let valuation := extendValuation index unitZeroValuation
  let values : Fin 2 -> Nat := ![data.right, data.left]
  explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation tokenCount
    (compactAdditiveUnitBoundaryRowsBranchTerminal tokenCount boundaryTable)
    values
    (compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelope
      tokenCount boundaryTable index data)

theorem compactAdditiveUnitBoundaryRowsBranchCertificate_structuralPayloadBound_le_transparent
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveUnitBoundaryRowsBranchCertificate
          tokenCount boundaryTable index data) <=
      compactAdditiveUnitBoundaryRowsBranchStructuralPayloadEnvelope
        tokenCount boundaryTable index data := by
  let valuation := extendValuation index unitZeroValuation
  let values : Fin 2 -> Nat := ![data.right, data.left]
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm : ValuationTerm := &0
  let rightIndexTerm : ValuationTerm := ‘&0 + 1’
  let leftValueTerm := shortBinaryNumeralTerm data.left
  let rightValueTerm := shortBinaryNumeralTerm data.right
  let leftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      valuation tableTerm widthTerm leftIndexTerm leftValueTerm (by
        simpa [valuation, unitZeroValuation,
          tableTerm, widthTerm, leftIndexTerm, leftValueTerm,
          termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.left_entry)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      valuation tableTerm widthTerm rightIndexTerm rightValueTerm (by
        simpa [valuation, unitZeroValuation,
          tableTerm, widthTerm, rightIndexTerm, rightValueTerm,
          termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.right_entry)
  let successorCertificate := successorEqualityCertificate valuation
    data.left data.right data.successor
  let rightSuccessor :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      rightCertificate successorCertificate
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      leftCertificate rightSuccessor
  have hwidth : widthTerm.freeVariables = ∅ := by
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have htable : tableTerm.freeVariables = ∅ := by
    exact shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
  have hleftIndex : leftIndexTerm.freeVariables ⊆ {0} := by
    simp [leftIndexTerm]
  have hrightIndex : rightIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [rightIndexTerm]
    rw [arithmeticAddTerm_eq_func,
      binaryFunctionTerm_freeVariables,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp
  have hleftValue : leftValueTerm.freeVariables = ∅ := by
    exact shortBinaryNumeralTerm_freeVariables_eq_empty data.left
  have hrightValue : rightValueTerm.freeVariables = ∅ := by
    exact shortBinaryNumeralTerm_freeVariables_eq_empty data.right
  have hleft :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation tableTerm widthTerm leftIndexTerm leftValueTerm
      htable hwidth hleftIndex hleftValue (by
        simpa [valuation, unitZeroValuation,
          tableTerm, widthTerm, leftIndexTerm, leftValueTerm,
          termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.left_entry)
  have hright :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation tableTerm widthTerm rightIndexTerm rightValueTerm
      htable hwidth hrightIndex hrightValue (by
        simpa [valuation, unitZeroValuation,
          tableTerm, widthTerm, rightIndexTerm, rightValueTerm,
          termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.right_entry)
  have hsuccessor :=
    successorEqualityCertificate_structuralPayloadBound_le_transparent
      valuation data.left data.right data.successor
  have hrightSuccessor := hybridConjunctionStructuralPayloadBound_le_envelope
    rightCertificate successorCertificate _ _ hright hsuccessor
  have hterminalParts := hybridConjunctionStructuralPayloadBound_le_envelope
    leftCertificate rightSuccessor _ _ hleft hrightSuccessor
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.right,
          shortBinaryNumeralTerm data.left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal : CheckedHybridValuationBoundedFormulaCertificate valuation
      ((compactAdditiveUnitBoundaryRowsBranchTerminal
          tokenCount boundaryTable) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveUnitBoundaryRowsBranchTerminal_substitution_alignment
          tokenCount boundaryTable data.left data.right).symm) terminalParts
  have hterminal : hybridFormulaStructuralPayloadBound terminal <=
      compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelope
        tokenCount boundaryTable index data := by
    simpa only [terminal, hybridFormulaStructuralPayloadBound,
      compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelope,
      valuation, tableTerm, widthTerm, leftIndexTerm, rightIndexTerm,
      leftValueTerm, rightValueTerm, leftCertificate, rightCertificate,
      successorCertificate, rightSuccessor, terminalParts,
      unitBoundarySuccessorStructuralPayloadResource] using hterminalParts
  have hinstalled :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount
      (compactAdditiveUnitBoundaryRowsBranchTerminal tokenCount boundaryTable)
      values (by
        intro coordinate
        fin_cases coordinate
        · exact data.right_le
        · exact data.left_le)
      terminal
      (compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelope
        tokenCount boundaryTable index data)
      hterminal
  simpa only [compactAdditiveUnitBoundaryRowsBranchCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveUnitBoundaryRowsBranchStructuralPayloadEnvelope,
    valuation, values, terminal, terminalParts, rightSuccessor,
    leftCertificate, rightCertificate, successorCertificate] using hinstalled

noncomputable def
    compactAdditiveUnitBoundaryRowsBranchStructuralPayloadResourceSum
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData tokenCount boundaryTable index) : Nat :=
  ∑ index : Fin count,
    compactAdditiveUnitBoundaryRowsBranchStructuralPayloadEnvelope
      tokenCount boundaryTable index (rows index)

theorem
    compactAdditiveUnitBoundaryRowsDirectHybridBranchesAtCount_leafPayloadBound
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData tokenCount boundaryTable index) :
    HybridBranchesLeafPayloadBound
      (compactAdditiveUnitBoundaryRowsBranchStructuralPayloadResourceSum
        tokenCount count boundaryTable rows)
      (compactAdditiveUnitBoundaryRowsDirectHybridBranchesAtCount
        tokenCount count boundaryTable rows) := by
  unfold compactAdditiveUnitBoundaryRowsDirectHybridBranchesAtCount
  apply buildExplicitHybridUniversalBranches_leafPayloadBound
  intro index hindex
  let finiteIndex : Fin count := ⟨index, hindex⟩
  have hbranch :=
    compactAdditiveUnitBoundaryRowsBranchCertificate_structuralPayloadBound_le_transparent
      tokenCount boundaryTable finiteIndex (rows finiteIndex)
  have hsum :
      compactAdditiveUnitBoundaryRowsBranchStructuralPayloadEnvelope
          tokenCount boundaryTable finiteIndex (rows finiteIndex) <=
        compactAdditiveUnitBoundaryRowsBranchStructuralPayloadResourceSum
          tokenCount count boundaryTable rows := by
    unfold
      compactAdditiveUnitBoundaryRowsBranchStructuralPayloadResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin count) _ => Nat.zero_le
        (compactAdditiveUnitBoundaryRowsBranchStructuralPayloadEnvelope
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

theorem compactAdditiveUnitBoundaryRowsDirectHybridBranches_leafPayloadBound
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData tokenCount boundaryTable index) :
    HybridBranchesLeafPayloadBound
      (compactAdditiveUnitBoundaryRowsBranchStructuralPayloadResourceSum
        tokenCount count boundaryTable rows)
      (compactAdditiveUnitBoundaryRowsDirectHybridBranches
        tokenCount count boundaryTable rows) := by
  unfold compactAdditiveUnitBoundaryRowsDirectHybridBranches
  exact hybridBranchesLeafPayloadBound_transport
    (compactAdditiveUnitBoundaryRowsShortNumeralBound_eq_count count).symm
    (compactAdditiveUnitBoundaryRowsDirectHybridBranchesAtCount
      tokenCount count boundaryTable rows)
    (compactAdditiveUnitBoundaryRowsDirectHybridBranchesAtCount_leafPayloadBound
      tokenCount count boundaryTable rows)

noncomputable def
    compactAdditiveUnitBoundaryRowsBranchesTransparentStructuralEnvelope
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData tokenCount boundaryTable index) : Nat :=
  let body := compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm count)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue unitZeroValuation (shortBinaryNumeralTerm count)
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    unitZeroValuation body
    (compactAdditiveUnitBoundaryRowsBranchStructuralPayloadResourceSum
      tokenCount count boundaryTable rows)
    bound

theorem
    compactAdditiveUnitBoundaryRowsBranchesStructuralPayloadEnvelope_le_transparent
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData tokenCount boundaryTable index) :
    let body := compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm count)) body
    hybridBranchesStructuralPayloadEnvelope
        (termValue unitZeroValuation (shortBinaryNumeralTerm count))
        outerFormula.freeVariables
        (compactAdditiveUnitBoundaryRowsDirectHybridBranches
          tokenCount count boundaryTable rows) <=
      compactAdditiveUnitBoundaryRowsBranchesTransparentStructuralEnvelope
        tokenCount count boundaryTable rows := by
  let body := compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm count)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue unitZeroValuation (shortBinaryNumeralTerm count)
  let branches := compactAdditiveUnitBoundaryRowsDirectHybridBranches
    tokenCount count boundaryTable rows
  have hleaves :=
    compactAdditiveUnitBoundaryRowsDirectHybridBranches_leafPayloadBound
      tokenCount count boundaryTable rows
  have hbound := hybridBranchesStructuralPayloadEnvelope_le_uniformEnvelope
    bound outerVariables
    (compactAdditiveUnitBoundaryRowsBranchStructuralPayloadResourceSum
      tokenCount count boundaryTable rows)
    branches hleaves
  simpa only [
    compactAdditiveUnitBoundaryRowsBranchesTransparentStructuralEnvelope,
    body, outerFormula, outerVariables, bound, branches] using hbound

noncomputable def
    compactAdditiveUnitBoundaryRowsUniversalStructuralPayloadEnvelope
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData tokenCount boundaryTable index) : Nat :=
  let body := compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables unitZeroValuation
  let bound := termValue unitZeroValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (compactAdditiveUnitBoundaryRowsBranchesTransparentStructuralEnvelope
      tokenCount count boundaryTable rows)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource unitZeroValuation
      outerVariables boundTerm)
    branchResource

theorem
    compactAdditiveUnitBoundaryRowsUniversalCertificate_structuralPayloadBound_le_transparent
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData tokenCount boundaryTable index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveUnitBoundaryRowsUniversalCertificate
          tokenCount count boundaryTable rows) <=
      compactAdditiveUnitBoundaryRowsUniversalStructuralPayloadEnvelope
        tokenCount count boundaryTable rows := by
  let body := compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables unitZeroValuation
  let bound := termValue unitZeroValuation boundTerm
  let branches := compactAdditiveUnitBoundaryRowsDirectHybridBranches
    tokenCount count boundaryTable rows
  let oldBranchCore := hybridBranchesStructuralPayloadEnvelope
    bound outerVariables branches
  let newBranchCore :=
    compactAdditiveUnitBoundaryRowsBranchesTransparentStructuralEnvelope
      tokenCount count boundaryTable rows
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldBranchCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newBranchCore
  let boundResource := compileShiftedBoundEqualityPayloadResource
    unitZeroValuation outerVariables boundTerm
  have hbranchCore : oldBranchCore <= newBranchCore := by
    dsimp only [oldBranchCore, newBranchCore, bound, branches,
      outerVariables, outerFormula, body, boundTerm]
    exact
      compactAdditiveUnitBoundaryRowsBranchesStructuralPayloadEnvelope_le_transparent
        tokenCount count boundaryTable rows
  have hbranchResource : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldBranchCore newBranchCore hbranchCore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift boundTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranchResource
  simpa only [compactAdditiveUnitBoundaryRowsUniversalCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveUnitBoundaryRowsUniversalStructuralPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, branches,
    oldBranchCore, newBranchCore, oldBranchResource, newBranchResource,
    boundResource] using htotal

theorem
    compactAdditiveUnitBoundaryRowsFromRowDataExplicitHybridCertificate_structuralPayloadBound_le_transparent
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData tokenCount boundaryTable index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveUnitBoundaryRowsFromRowDataExplicitHybridCertificate
          tokenCount count boundaryTable rows) <=
      compactAdditiveUnitBoundaryRowsUniversalStructuralPayloadEnvelope
        tokenCount count boundaryTable rows := by
  simpa only [
    compactAdditiveUnitBoundaryRowsFromRowDataExplicitHybridCertificate,
    hybridFormulaStructuralPayloadBound] using
    compactAdditiveUnitBoundaryRowsUniversalCertificate_structuralPayloadBound_le_transparent
      tokenCount count boundaryTable rows

noncomputable def
    compactAdditiveUnitBoundaryRowsGraphStructuralPayloadEnvelope
    (tokenCount count boundaryTable : Nat)
    (hrows : CompactAdditiveUnitBoundaryRows
      tokenCount count boundaryTable) : Nat :=
  compactAdditiveUnitBoundaryRowsUniversalStructuralPayloadEnvelope
    tokenCount count boundaryTable
    (compactAdditiveUnitBoundaryRowDataOfGraph
      tokenCount count boundaryTable hrows)

theorem
    compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenCount count boundaryTable : Nat)
    (hrows : CompactAdditiveUnitBoundaryRows
      tokenCount count boundaryTable) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph
          tokenCount count boundaryTable hrows) <=
      compactAdditiveUnitBoundaryRowsGraphStructuralPayloadEnvelope
        tokenCount count boundaryTable hrows := by
  simpa only [
    compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph,
    compactAdditiveUnitBoundaryRowsGraphStructuralPayloadEnvelope] using
    compactAdditiveUnitBoundaryRowsFromRowDataExplicitHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount count boundaryTable
      (compactAdditiveUnitBoundaryRowDataOfGraph
        tokenCount count boundaryTable hrows)

#print axioms
  successorEqualityCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveUnitBoundaryRowsBranchCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveUnitBoundaryRowsDirectHybridBranches_leafPayloadBound
#print axioms
  compactAdditiveUnitBoundaryRowsUniversalCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveUnitBoundaryRowsFromRowDataExplicitHybridCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent

end FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds
