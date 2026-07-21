import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds

/-!
# Public structural resources for additive triple-boundary rows

The two cursor witnesses are installed by the audited bounded-witness
recursion.  Their fixed-width entries are compiled at the open universal row
index, and the triple equation is compiled as a positive atomic formula.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
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
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate

private abbrev tripleZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.zeroValuation

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

def tripleBoundarySpanStructuralPayloadResource
    (valuation : Nat -> Nat) (left right : Nat) : Nat :=
  compilePositiveRelationPayloadResource valuation Language.Eq.eq
    ![shortBinaryNumeralTerm right,
      (‘!!(shortBinaryNumeralTerm left) + 3’ : ValuationTerm)]

theorem tripleEqualityCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat) (left right : Nat)
    (htriple : right = left + 3) :
    hybridFormulaStructuralPayloadBound
        (tripleEqualityCertificate valuation left right htriple) <=
      tripleBoundarySpanStructuralPayloadResource valuation left right := by
  simp only [tripleEqualityCertificate,
    hybridFormulaStructuralPayloadBound]
  exact le_rfl

def compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index) : Nat :=
  let valuation := extendValuation index tripleZeroValuation
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
  let tripleFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm data.right) =
      !!(shortBinaryNumeralTerm data.left) + 3”
  let leftResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation tableTerm widthTerm leftIndexTerm leftValueTerm
  let rightResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation tableTerm widthTerm rightIndexTerm rightValueTerm
  let tripleResource := tripleBoundarySpanStructuralPayloadResource
    valuation data.left data.right
  let rightTripleResource := hybridConjunctionStructuralPayloadEnvelope
    valuation rightFormula tripleFormula rightResource tripleResource
  hybridConjunctionStructuralPayloadEnvelope valuation leftFormula
    (rightFormula ⋏ tripleFormula) leftResource rightTripleResource

def compactAdditiveTripleBoundaryRowsBranchStructuralPayloadEnvelope
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index) : Nat :=
  let valuation := extendValuation index tripleZeroValuation
  let values : Fin 2 -> Nat := ![data.right, data.left]
  explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation tokenCount
    (compactAdditiveTripleBoundaryRowsBranchTerminal tokenCount boundaryTable)
    values
    (compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope
      tokenCount boundaryTable index data)

theorem compactAdditiveTripleBoundaryRowsBranchCertificate_structuralPayloadBound_le_transparent
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveTripleBoundaryRowsBranchCertificate
          tokenCount boundaryTable index data) <=
      compactAdditiveTripleBoundaryRowsBranchStructuralPayloadEnvelope
        tokenCount boundaryTable index data := by
  let valuation := extendValuation index tripleZeroValuation
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
        simpa [valuation, tripleZeroValuation,
          tableTerm, widthTerm, leftIndexTerm, leftValueTerm,
          termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.left_entry)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      valuation tableTerm widthTerm rightIndexTerm rightValueTerm (by
        simpa [valuation, tripleZeroValuation,
          tableTerm, widthTerm, rightIndexTerm, rightValueTerm,
          termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.right_entry)
  let tripleCertificate := tripleEqualityCertificate valuation
    data.left data.right data.triple
  let rightTriple :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      rightCertificate tripleCertificate
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      leftCertificate rightTriple
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
        simpa [valuation, tripleZeroValuation,
          tableTerm, widthTerm, leftIndexTerm, leftValueTerm,
          termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.left_entry)
  have hright :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation tableTerm widthTerm rightIndexTerm rightValueTerm
      htable hwidth hrightIndex hrightValue (by
        simpa [valuation, tripleZeroValuation,
          tableTerm, widthTerm, rightIndexTerm, rightValueTerm,
          termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.right_entry)
  have htriple :=
    tripleEqualityCertificate_structuralPayloadBound_le_transparent
      valuation data.left data.right data.triple
  have hrightTriple := hybridConjunctionStructuralPayloadBound_le_envelope
    rightCertificate tripleCertificate _ _ hright htriple
  have hterminalParts := hybridConjunctionStructuralPayloadBound_le_envelope
    leftCertificate rightTriple _ _ hleft hrightTriple
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.right,
          shortBinaryNumeralTerm data.left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal : CheckedHybridValuationBoundedFormulaCertificate valuation
      ((compactAdditiveTripleBoundaryRowsBranchTerminal
          tokenCount boundaryTable) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveTripleBoundaryRowsBranchTerminal_substitution_alignment
          tokenCount boundaryTable data.left data.right).symm) terminalParts
  have hterminal : hybridFormulaStructuralPayloadBound terminal <=
      compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope
        tokenCount boundaryTable index data := by
    simpa only [terminal, hybridFormulaStructuralPayloadBound,
      compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope,
      valuation, tableTerm, widthTerm, leftIndexTerm, rightIndexTerm,
      leftValueTerm, rightValueTerm, leftCertificate, rightCertificate,
      tripleCertificate, rightTriple, terminalParts,
      tripleBoundarySpanStructuralPayloadResource] using hterminalParts
  have hinstalled :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount
      (compactAdditiveTripleBoundaryRowsBranchTerminal tokenCount boundaryTable)
      values (by
        intro coordinate
        fin_cases coordinate
        · exact data.right_le
        · exact data.left_le)
      terminal
      (compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope
        tokenCount boundaryTable index data)
      hterminal
  simpa only [compactAdditiveTripleBoundaryRowsBranchCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveTripleBoundaryRowsBranchStructuralPayloadEnvelope,
    valuation, values, terminal, terminalParts, rightTriple,
    leftCertificate, rightCertificate, tripleCertificate] using hinstalled

noncomputable def
    compactAdditiveTripleBoundaryRowsBranchStructuralPayloadResourceSum
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData tokenCount boundaryTable index) : Nat :=
  ∑ index : Fin count,
    compactAdditiveTripleBoundaryRowsBranchStructuralPayloadEnvelope
      tokenCount boundaryTable index (rows index)

theorem
    compactAdditiveTripleBoundaryRowsDirectHybridBranchesAtCount_leafPayloadBound
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData tokenCount boundaryTable index) :
    HybridBranchesLeafPayloadBound
      (compactAdditiveTripleBoundaryRowsBranchStructuralPayloadResourceSum
        tokenCount count boundaryTable rows)
      (compactAdditiveTripleBoundaryRowsDirectHybridBranchesAtCount
        tokenCount count boundaryTable rows) := by
  unfold compactAdditiveTripleBoundaryRowsDirectHybridBranchesAtCount
  apply buildExplicitHybridUniversalBranches_leafPayloadBound
  intro index hindex
  let finiteIndex : Fin count := ⟨index, hindex⟩
  have hbranch :=
    compactAdditiveTripleBoundaryRowsBranchCertificate_structuralPayloadBound_le_transparent
      tokenCount boundaryTable finiteIndex (rows finiteIndex)
  have hsum :
      compactAdditiveTripleBoundaryRowsBranchStructuralPayloadEnvelope
          tokenCount boundaryTable finiteIndex (rows finiteIndex) <=
        compactAdditiveTripleBoundaryRowsBranchStructuralPayloadResourceSum
          tokenCount count boundaryTable rows := by
    unfold
      compactAdditiveTripleBoundaryRowsBranchStructuralPayloadResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin count) _ => Nat.zero_le
        (compactAdditiveTripleBoundaryRowsBranchStructuralPayloadEnvelope
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

theorem compactAdditiveTripleBoundaryRowsDirectHybridBranches_leafPayloadBound
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData tokenCount boundaryTable index) :
    HybridBranchesLeafPayloadBound
      (compactAdditiveTripleBoundaryRowsBranchStructuralPayloadResourceSum
        tokenCount count boundaryTable rows)
      (compactAdditiveTripleBoundaryRowsDirectHybridBranches
        tokenCount count boundaryTable rows) := by
  unfold compactAdditiveTripleBoundaryRowsDirectHybridBranches
  exact hybridBranchesLeafPayloadBound_transport
    (compactAdditiveTripleBoundaryRowsShortNumeralBound_eq_count count).symm
    (compactAdditiveTripleBoundaryRowsDirectHybridBranchesAtCount
      tokenCount count boundaryTable rows)
    (compactAdditiveTripleBoundaryRowsDirectHybridBranchesAtCount_leafPayloadBound
      tokenCount count boundaryTable rows)

noncomputable def
    compactAdditiveTripleBoundaryRowsBranchesTransparentStructuralEnvelope
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData tokenCount boundaryTable index) : Nat :=
  let body := compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm count)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue tripleZeroValuation (shortBinaryNumeralTerm count)
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    tripleZeroValuation body
    (compactAdditiveTripleBoundaryRowsBranchStructuralPayloadResourceSum
      tokenCount count boundaryTable rows)
    bound

theorem
    compactAdditiveTripleBoundaryRowsBranchesStructuralPayloadEnvelope_le_transparent
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData tokenCount boundaryTable index) :
    let body := compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm count)) body
    hybridBranchesStructuralPayloadEnvelope
        (termValue tripleZeroValuation (shortBinaryNumeralTerm count))
        outerFormula.freeVariables
        (compactAdditiveTripleBoundaryRowsDirectHybridBranches
          tokenCount count boundaryTable rows) <=
      compactAdditiveTripleBoundaryRowsBranchesTransparentStructuralEnvelope
        tokenCount count boundaryTable rows := by
  let body := compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm count)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue tripleZeroValuation (shortBinaryNumeralTerm count)
  let branches := compactAdditiveTripleBoundaryRowsDirectHybridBranches
    tokenCount count boundaryTable rows
  have hleaves :=
    compactAdditiveTripleBoundaryRowsDirectHybridBranches_leafPayloadBound
      tokenCount count boundaryTable rows
  have hbound := hybridBranchesStructuralPayloadEnvelope_le_uniformEnvelope
    bound outerVariables
    (compactAdditiveTripleBoundaryRowsBranchStructuralPayloadResourceSum
      tokenCount count boundaryTable rows)
    branches hleaves
  simpa only [
    compactAdditiveTripleBoundaryRowsBranchesTransparentStructuralEnvelope,
    body, outerFormula, outerVariables, bound, branches] using hbound

noncomputable def
    compactAdditiveTripleBoundaryRowsUniversalStructuralPayloadEnvelope
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData tokenCount boundaryTable index) : Nat :=
  let body := compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables tripleZeroValuation
  let bound := termValue tripleZeroValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (compactAdditiveTripleBoundaryRowsBranchesTransparentStructuralEnvelope
      tokenCount count boundaryTable rows)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource tripleZeroValuation
      outerVariables boundTerm)
    branchResource

theorem
    compactAdditiveTripleBoundaryRowsUniversalCertificate_structuralPayloadBound_le_transparent
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData tokenCount boundaryTable index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveTripleBoundaryRowsUniversalCertificate
          tokenCount count boundaryTable rows) <=
      compactAdditiveTripleBoundaryRowsUniversalStructuralPayloadEnvelope
        tokenCount count boundaryTable rows := by
  let body := compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables tripleZeroValuation
  let bound := termValue tripleZeroValuation boundTerm
  let branches := compactAdditiveTripleBoundaryRowsDirectHybridBranches
    tokenCount count boundaryTable rows
  let oldBranchCore := hybridBranchesStructuralPayloadEnvelope
    bound outerVariables branches
  let newBranchCore :=
    compactAdditiveTripleBoundaryRowsBranchesTransparentStructuralEnvelope
      tokenCount count boundaryTable rows
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldBranchCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newBranchCore
  let boundResource := compileShiftedBoundEqualityPayloadResource
    tripleZeroValuation outerVariables boundTerm
  have hbranchCore : oldBranchCore <= newBranchCore := by
    dsimp only [oldBranchCore, newBranchCore, bound, branches,
      outerVariables, outerFormula, body, boundTerm]
    exact
      compactAdditiveTripleBoundaryRowsBranchesStructuralPayloadEnvelope_le_transparent
        tokenCount count boundaryTable rows
  have hbranchResource : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldBranchCore newBranchCore hbranchCore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift boundTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranchResource
  simpa only [compactAdditiveTripleBoundaryRowsUniversalCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveTripleBoundaryRowsUniversalStructuralPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, branches,
    oldBranchCore, newBranchCore, oldBranchResource, newBranchResource,
    boundResource] using htotal

theorem
    compactAdditiveTripleBoundaryRowsFromRowDataExplicitHybridCertificate_structuralPayloadBound_le_transparent
    (tokenCount count boundaryTable : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData tokenCount boundaryTable index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveTripleBoundaryRowsFromRowDataExplicitHybridCertificate
          tokenCount count boundaryTable rows) <=
      compactAdditiveTripleBoundaryRowsUniversalStructuralPayloadEnvelope
        tokenCount count boundaryTable rows := by
  simpa only [
    compactAdditiveTripleBoundaryRowsFromRowDataExplicitHybridCertificate,
    hybridFormulaStructuralPayloadBound] using
    compactAdditiveTripleBoundaryRowsUniversalCertificate_structuralPayloadBound_le_transparent
      tokenCount count boundaryTable rows

noncomputable def
    compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope
    (tokenCount count boundaryTable : Nat)
    (hrows : CompactAdditiveTripleBoundaryRows
      tokenCount count boundaryTable) : Nat :=
  compactAdditiveTripleBoundaryRowsUniversalStructuralPayloadEnvelope
    tokenCount count boundaryTable
    (compactAdditiveTripleBoundaryRowDataOfGraph
      tokenCount count boundaryTable hrows)

theorem
    compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenCount count boundaryTable : Nat)
    (hrows : CompactAdditiveTripleBoundaryRows
      tokenCount count boundaryTable) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph
          tokenCount count boundaryTable hrows) <=
      compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope
        tokenCount count boundaryTable hrows := by
  simpa only [
    compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph,
    compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope] using
    compactAdditiveTripleBoundaryRowsFromRowDataExplicitHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount count boundaryTable
      (compactAdditiveTripleBoundaryRowDataOfGraph
        tokenCount count boundaryTable hrows)

#print axioms
  tripleEqualityCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveTripleBoundaryRowsBranchCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveTripleBoundaryRowsDirectHybridBranches_leafPayloadBound
#print axioms
  compactAdditiveTripleBoundaryRowsUniversalCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveTripleBoundaryRowsFromRowDataExplicitHybridCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent

end FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
