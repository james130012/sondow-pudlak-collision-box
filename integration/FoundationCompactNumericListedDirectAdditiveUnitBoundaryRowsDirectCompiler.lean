import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsFixedWidthEntryBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity02
import integration.FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds

/-!
# Direct compiler for additive unit-boundary rows

The two cursor witnesses are installed by the public direct compiler.  The
terminal certificate is first compiled to a real contextual PA proof and is
charged to the bit-width-uniform terminal resource.  No concrete cursor value
occurs in the resulting branch resource.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsDirectCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity02
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAExplicitDirectUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsFixedWidthEntryBounds

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

private theorem arithmeticOneTerm_freeVariables_eq_empty
    {boundArity : Nat} :
    (‘1’ : ArithmeticSemiterm Nat boundArity).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticAddTerm_freeVariables_eq_union
    {boundArity : Nat}
    (left right : ArithmeticSemiterm Nat boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Nat boundArity).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [arithmeticAddTerm_eq_func,
    binaryFunctionTerm_freeVariables]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

def compactAdditiveUnitBoundaryRowsDirectValues
    {tokenCount boundaryTable index : Nat}
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index) : Fin 2 -> Nat :=
  ![data.right, data.left]

theorem compactAdditiveUnitBoundaryRowsDirectValues_le
    {tokenCount boundaryTable index : Nat}
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index)
    (coordinate : Fin 2) :
    compactAdditiveUnitBoundaryRowsDirectValues data coordinate <=
      tokenCount := by
  fin_cases coordinate
  · exact data.right_le
  · exact data.left_le

noncomputable def compactAdditiveUnitBoundaryRowsDirectTerminalCertificate
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index) :
    CheckedHybridValuationBoundedFormulaCertificate
      (extendValuation index unitZeroValuation)
      ((compactAdditiveUnitBoundaryRowsBranchTerminal
          tokenCount boundaryTable) ⇜
        fun coordinate => shortBinaryNumeralTerm
          (compactAdditiveUnitBoundaryRowsDirectValues data coordinate)) := by
  let valuation := extendValuation index unitZeroValuation
  let values := compactAdditiveUnitBoundaryRowsDirectValues data
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.right,
          shortBinaryNumeralTerm data.left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let leftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      valuation
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount)
      (&0 : ValuationTerm)
      (shortBinaryNumeralTerm data.left) (by
        simpa [valuation, unitZeroValuation,
          termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.left_entry)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      valuation
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount)
      (‘&0 + 1’ : ValuationTerm)
      (shortBinaryNumeralTerm data.right) (by
        simpa [valuation, unitZeroValuation,
          termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.right_entry)
  let successorCertificate := successorEqualityCertificate valuation
    data.left data.right data.successor
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      leftCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        rightCertificate successorCertificate)
  exact .cast (by
    rw [hvalueTerms]
    exact
      (compactAdditiveUnitBoundaryRowsBranchTerminal_substitution_alignment
        tokenCount boundaryTable data.left data.right).symm) terminalParts

theorem
    compactAdditiveUnitBoundaryRowsDirectTerminalCertificate_structuralPayloadBound_le
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveUnitBoundaryRowsDirectTerminalCertificate
          tokenCount boundaryTable index data) <=
      compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelope
        tokenCount boundaryTable index data := by
  let valuation := extendValuation index unitZeroValuation
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
  simpa only [compactAdditiveUnitBoundaryRowsDirectTerminalCertificate,
    compactAdditiveUnitBoundaryRowsDirectValues,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelope,
    valuation, tableTerm, widthTerm, leftIndexTerm, rightIndexTerm,
    leftValueTerm, rightValueTerm, leftCertificate, rightCertificate,
    successorCertificate, rightSuccessor, terminalParts,
    unitBoundarySuccessorStructuralPayloadResource] using hterminalParts

def compactAdditiveUnitBoundaryRowsBranchDirectPayloadEnvelope
    (tokenCount boundaryTable index numericBound bitBound : Nat) : Nat :=
  let valuation := extendValuation index unitZeroValuation
  let body := compactAdditiveUnitBoundaryRowsBranchTerminal
    tokenCount boundaryTable
  let contextCodeBound := formulaCodeSum
    (valuationContext body.freeVariables valuation)
  let bodyCodeBound := (binaryFormulaCode body).length
  let terminalResource :=
    unitBoundaryTerminalFullyUniformPayloadPolynomial numericBound bitBound
  explicitBoundedWitnessDirectPublicPayloadEnvelope 2 contextCodeBound
    tokenCount bodyCodeBound terminalResource

noncomputable def compactAdditiveUnitBoundaryRowsBranchDirectBound
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound
      (extendValuation index unitZeroValuation)
      (Rewriting.free
        (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable))
      (compactAdditiveUnitBoundaryRowsBranchDirectPayloadEnvelope
        tokenCount boundaryTable index numericBound bitBound) := by
  let valuation := extendValuation index unitZeroValuation
  let body := compactAdditiveUnitBoundaryRowsBranchTerminal
    tokenCount boundaryTable
  let values := compactAdditiveUnitBoundaryRowsDirectValues data
  let contextCodeBound := formulaCodeSum
    (valuationContext body.freeVariables valuation)
  let bodyCodeBound := (binaryFormulaCode body).length
  let terminalResource :=
    unitBoundaryTerminalFullyUniformPayloadPolynomial numericBound bitBound
  let terminalCertificate :=
    compactAdditiveUnitBoundaryRowsDirectTerminalCertificate
      tokenCount boundaryTable index data
  have hterminalStructural :
      hybridFormulaStructuralPayloadBound terminalCertificate <=
        compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelope
          tokenCount boundaryTable index data := by
    exact
      compactAdditiveUnitBoundaryRowsDirectTerminalCertificate_structuralPayloadBound_le
        tokenCount boundaryTable index data
  have hterminalUniform :
      hybridFormulaStructuralPayloadBound terminalCertificate <=
        terminalResource :=
    hterminalStructural.trans
      (compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelope_le_fullyUniform
        tokenCount boundaryTable index numericBound bitBound data htokenCount
        hindexSuccessor htableSize hnumericSize)
  have hterminal : terminalCertificate.compile.payloadLength <=
      terminalResource :=
    (compile_payloadLength_le_structuralPayloadBound
      terminalCertificate).trans hterminalUniform
  have hbody : (binaryFormulaCode body).length <= bodyCodeBound :=
    Nat.le_refl _
  have hcontext : formulaCodeSum
      (valuationContext body.freeVariables valuation) <= contextCodeBound :=
    Nat.le_refl _
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm tokenCount) 2 body
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound tokenCount bodyCodeBound body values
      (compactAdditiveUnitBoundaryRowsDirectValues_le data) hbody hcontext
      terminalResource terminalCertificate.compile hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity02
      contextCodeBound tokenCount bodyCodeBound body values
      (compactAdditiveUnitBoundaryRowsDirectValues_le data) hbody hcontext
      terminalResource terminalCertificate.compile hterminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      Rewriting.free
        (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable) :=
    (compactAdditiveUnitBoundaryRowsBody_free_alignment
      tokenCount boundaryTable).symm
  let proof := castValuationContextProof hformula rawProof
  refine { proof := proof, payloadLength_le := ?_ }
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [compactAdditiveUnitBoundaryRowsBranchDirectPayloadEnvelope,
    valuation, body, contextCodeBound, bodyCodeBound, terminalResource]
    using hcoordinates.2

noncomputable def compileCompactAdditiveUnitBoundaryRowsBranchDirect
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (Rewriting.free
          (compactAdditiveUnitBoundaryRowsBody
            tokenCount boundaryTable)).freeVariables
        (extendValuation index unitZeroValuation))
      (Rewriting.free
        (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable)) :=
  (compactAdditiveUnitBoundaryRowsBranchDirectBound tokenCount boundaryTable
    index numericBound bitBound data htokenCount hindexSuccessor htableSize
    hnumericSize).proof

theorem compileCompactAdditiveUnitBoundaryRowsBranchDirect_payloadLength_le
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveUnitBoundaryRowsBranchDirect tokenCount
      boundaryTable index numericBound bitBound data htokenCount
      hindexSuccessor htableSize hnumericSize).payloadLength <=
      compactAdditiveUnitBoundaryRowsBranchDirectPayloadEnvelope
        tokenCount boundaryTable index numericBound bitBound :=
  (compactAdditiveUnitBoundaryRowsBranchDirectBound tokenCount boundaryTable
    index numericBound bitBound data htokenCount hindexSuccessor htableSize
    hnumericSize).payloadLength_le

private theorem unitBoundaryClosedShift_freeVariables_eq_empty
    (arity : Nat) (term : ValuationTerm)
    (hterm : term.freeVariables = ∅) :
    (FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.closedShift
      arity term).freeVariables = ∅ := by
  induction arity with
  | zero => simpa [
      FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.closedShift]
  | succ arity inductionHypothesis =>
      simp only [
        FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.closedShift]
      exact bShift_freeVariables_eq_empty_of_empty _ inductionHypothesis

private theorem bexsLTSucc_freeVariables_eq_empty_of_empty
    {arity : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (bound : ArithmeticSemiterm Nat arity)
    (hbody : body.freeVariables = ∅)
    (hbound : bound.freeVariables = ∅) :
    (body.bexsLTSucc bound).freeVariables = ∅ := by
  have hone : (‘1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ :=
    arithmeticOneTerm_freeVariables_eq_empty
  have hsuccessor :
      (‘!!bound + 1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
    rw [arithmeticAddTerm_freeVariables_eq_union, hbound, hone]
    simp
  have hshifted :
      (Rew.bShift
        (‘!!bound + 1’ : ArithmeticSemiterm Nat arity)).freeVariables = ∅ :=
    bShift_freeVariables_eq_empty_of_empty _ hsuccessor
  unfold Semiformula.bexsLTSucc Semiformula.bexsLT LO.FirstOrder.bexs
  rw [LO.FirstOrder.Semiformula.freeVariables_exs,
    LO.FirstOrder.Semiformula.freeVariables_and,
    lessThanFormula_freeVariables, hshifted, hbody]
  simp

theorem compactAdditiveUnitBoundaryRowsTerminal_freeVariables_eq_empty
    (tokenCount boundaryTable : Nat) :
    (compactAdditiveUnitBoundaryRowsTerminal
      tokenCount boundaryTable).freeVariables = ∅ := by
  let tableTerm : ArithmeticSemiterm Nat 3 :=
    FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.closedShift
      3 (shortBinaryNumeralTerm boundaryTable)
  let widthTerm : ArithmeticSemiterm Nat 3 :=
    FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.closedShift
      3 (shortBinaryNumeralTerm tokenCount)
  let leftTerms : Fin 4 -> ArithmeticSemiterm Nat 3 :=
    ![tableTerm, widthTerm, #2, #1]
  let rightTerms : Fin 4 -> ArithmeticSemiterm Nat 3 :=
    ![tableTerm, widthTerm, ‘#2 + 1’, #0]
  let leftFormula : ArithmeticSemiformula Nat 3 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ leftTerms
  let rightFormula : ArithmeticSemiformula Nat 3 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ rightTerms
  let successorFormula : ArithmeticSemiformula Nat 3 := “#0 = #1 + 1”
  have htable : tableTerm.freeVariables = ∅ := by
    exact unitBoundaryClosedShift_freeVariables_eq_empty 3 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable)
  have hwidth : widthTerm.freeVariables = ∅ := by
    exact unitBoundaryClosedShift_freeVariables_eq_empty 3 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
  have hleftTerms : forall coordinate,
      (leftTerms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate
    · exact htable
    · exact hwidth
    · simp [leftTerms]
    · simp [leftTerms]
  have hrightTerms : forall coordinate,
      (rightTerms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate
    · exact htable
    · exact hwidth
    · change (‘#2 + 1’ : ArithmeticSemiterm Nat 3).freeVariables = ∅
      rw [arithmeticAddTerm_freeVariables_eq_union,
        arithmeticOneTerm_freeVariables_eq_empty]
      simp
    · simp [rightTerms]
  have hleft : leftFormula.freeVariables = ∅ := by
    exact embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      compactFixedWidthEntryDef.val leftTerms hleftTerms
  have hright : rightFormula.freeVariables = ∅ := by
    exact embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      compactFixedWidthEntryDef.val rightTerms hrightTerms
  have hsuccessor : successorFormula.freeVariables = ∅ := by
    have hadd : (‘#1 + 1’ : ArithmeticSemiterm Nat 3).freeVariables = ∅ := by
      rw [arithmeticAddTerm_freeVariables_eq_union,
        arithmeticOneTerm_freeVariables_eq_empty]
      simp
    rw [show successorFormula =
        (“#0 = #1 + 1” : ArithmeticSemiformula Nat 3) by rfl,
      equalityFormula_freeVariables, hadd]
    simp
  change (leftFormula ⋏ (rightFormula ⋏ successorFormula)).freeVariables = ∅
  rw [LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_and,
    hleft, hright, hsuccessor]
  simp

theorem compactAdditiveUnitBoundaryRowsBody_freeVariables_eq_empty
    (tokenCount boundaryTable : Nat) :
    (compactAdditiveUnitBoundaryRowsBody
      tokenCount boundaryTable).freeVariables = ∅ := by
  let terminal := compactAdditiveUnitBoundaryRowsTerminal
    tokenCount boundaryTable
  have hterminal : terminal.freeVariables = ∅ :=
    compactAdditiveUnitBoundaryRowsTerminal_freeVariables_eq_empty
      tokenCount boundaryTable
  let innerBound :=
    FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.closedShift
      2 (shortBinaryNumeralTerm tokenCount)
  let outerBound :=
    FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.closedShift
      1 (shortBinaryNumeralTerm tokenCount)
  have hinnerBound : innerBound.freeVariables = ∅ :=
    unitBoundaryClosedShift_freeVariables_eq_empty 2 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
  have houterBound : outerBound.freeVariables = ∅ :=
    unitBoundaryClosedShift_freeVariables_eq_empty 1 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
  have hinner := bexsLTSucc_freeVariables_eq_empty_of_empty terminal
    innerBound hterminal hinnerBound
  have houter := bexsLTSucc_freeVariables_eq_empty_of_empty
    (terminal.bexsLTSucc innerBound) outerBound hinner houterBound
  simpa only [compactAdditiveUnitBoundaryRowsBody, terminal, innerBound,
    outerBound] using houter

def compactAdditiveUnitBoundaryRowsDirectLeafPayloadResourceSum
    (tokenCount count boundaryTable numericBound bitBound : Nat) : Nat :=
  ∑ index : Fin count,
    compactAdditiveUnitBoundaryRowsBranchDirectPayloadEnvelope
      tokenCount boundaryTable index numericBound bitBound

theorem compileCompactAdditiveUnitBoundaryRowsBranchDirect_le_leafSum
    (tokenCount count boundaryTable numericBound bitBound index : Nat)
    (rows : (coordinate : Fin count) ->
      CompactAdditiveUnitBoundaryRowData
        tokenCount boundaryTable coordinate)
    (hindex : index < count)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveUnitBoundaryRowsBranchDirect tokenCount
      boundaryTable index numericBound bitBound (rows ⟨index, hindex⟩)
      htokenCount (by omega) htableSize hnumericSize).payloadLength <=
      compactAdditiveUnitBoundaryRowsDirectLeafPayloadResourceSum
        tokenCount count boundaryTable numericBound bitBound := by
  let finiteIndex : Fin count := ⟨index, hindex⟩
  have hleaf :=
    compileCompactAdditiveUnitBoundaryRowsBranchDirect_payloadLength_le
      tokenCount boundaryTable index numericBound bitBound
      (rows finiteIndex) htokenCount (by omega) htableSize hnumericSize
  have hmember :
      compactAdditiveUnitBoundaryRowsBranchDirectPayloadEnvelope tokenCount
          boundaryTable finiteIndex numericBound bitBound <=
        compactAdditiveUnitBoundaryRowsDirectLeafPayloadResourceSum
          tokenCount count boundaryTable numericBound bitBound := by
    unfold compactAdditiveUnitBoundaryRowsDirectLeafPayloadResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin count) _ => Nat.zero_le
        (compactAdditiveUnitBoundaryRowsBranchDirectPayloadEnvelope
          tokenCount boundaryTable candidate numericBound bitBound))
      (Finset.mem_univ finiteIndex)
  dsimp only [finiteIndex] at hleaf hmember ⊢
  exact hleaf.trans hmember

noncomputable def compactAdditiveUnitBoundaryRowsFullyDirectBranches
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedContextFiniteUniversalBranches
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (Rewriting.free
        (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable))
      count := by
  have hbodyVariables :
      (compactAdditiveUnitBoundaryRowsBody
        tokenCount boundaryTable).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [compactAdditiveUnitBoundaryRowsBody_freeVariables_eq_empty]
  exact buildExplicitDirectUniversalBranches ∅ hbodyVariables count
    (fun index hindex =>
      compileCompactAdditiveUnitBoundaryRowsBranchDirect tokenCount
        boundaryTable index numericBound bitBound (rows ⟨index, hindex⟩)
        htokenCount (by omega) htableSize hnumericSize)

def compactAdditiveUnitBoundaryRowsFullyDirectBranchesStructuralEnvelope
    (tokenCount count boundaryTable numericBound bitBound : Nat) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope unitZeroValuation count
    (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable) ∅
    (fun _ =>
      compactAdditiveUnitBoundaryRowsDirectLeafPayloadResourceSum tokenCount
        count boundaryTable numericBound bitBound)
    count

theorem
    compactAdditiveUnitBoundaryRowsFullyDirectBranches_structuralPayloadBound_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compactAdditiveUnitBoundaryRowsFullyDirectBranches tokenCount count
      boundaryTable numericBound bitBound rows htokenCount hcount htableSize
      hnumericSize).structuralPayloadBound count <=
      compactAdditiveUnitBoundaryRowsFullyDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound := by
  have hbodyVariables :
      (compactAdditiveUnitBoundaryRowsBody
        tokenCount boundaryTable).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [compactAdditiveUnitBoundaryRowsBody_freeVariables_eq_empty]
  unfold compactAdditiveUnitBoundaryRowsFullyDirectBranches
    compactAdditiveUnitBoundaryRowsFullyDirectBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables count
    (fun _ =>
      compactAdditiveUnitBoundaryRowsDirectLeafPayloadResourceSum tokenCount
        count boundaryTable numericBound bitBound)
    count
    (fun index hindex =>
      compileCompactAdditiveUnitBoundaryRowsBranchDirect tokenCount
        boundaryTable index numericBound bitBound (rows ⟨index, hindex⟩)
        htokenCount (by omega) htableSize hnumericSize)
    (fun index hindex =>
      compileCompactAdditiveUnitBoundaryRowsBranchDirect_le_leafSum
        tokenCount count boundaryTable numericBound bitBound index rows
        hindex htokenCount hcount htableSize hnumericSize)

theorem
    compactAdditiveUnitBoundaryRowsFullyDirectBranchesStructuralEnvelope_le_polynomial
    (tokenCount count boundaryTable numericBound bitBound : Nat) :
    compactAdditiveUnitBoundaryRowsFullyDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound <=
      explicitDirectUniversalBranchesPayloadPolynomial count
        (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable)
        (compactAdditiveUnitBoundaryRowsDirectLeafPayloadResourceSum
          tokenCount count boundaryTable numericBound bitBound) := by
  unfold compactAdditiveUnitBoundaryRowsFullyDirectBranchesStructuralEnvelope
  exact directBranchesStructuralPayloadEnvelope_le_polynomial
    (compactAdditiveUnitBoundaryRowsDirectLeafPayloadResourceSum tokenCount
      count boundaryTable numericBound bitBound)
    (fun _ =>
      compactAdditiveUnitBoundaryRowsDirectLeafPayloadResourceSum tokenCount
        count boundaryTable numericBound bitBound)
    (fun _ => Nat.le_refl _)

noncomputable def compactAdditiveUnitBoundaryRowsDirectBoundEquality
    (count : Nat) :
    CertifiedPAContextProof
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (“!!(iteratedSuccessorTerm 0 count) =
        !!(Rew.free
          (Rew.bShift (shortBinaryNumeralTerm count)))” :
        ValuationFormula) := by
  let raw := compileClosedShortBoundEquality count
  have hformula :
      (“!!(iteratedSuccessorTerm 0 count) =
        !!(shortBinaryNumeralTerm count)” : ValuationFormula) =
      (“!!(iteratedSuccessorTerm 0 count) =
        !!(Rew.free
          (Rew.bShift (shortBinaryNumeralTerm count)))” :
        ValuationFormula) := by
    simp
  exact CertifiedPAContextProof.castContext (by simp)
    (CertifiedPAContextProof.cast hformula raw)

noncomputable def compileCompactAdditiveUnitBoundaryRowsDirectUniversalContext
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      ((compactAdditiveUnitBoundaryRowsBody
        tokenCount boundaryTable).ballLT
          (shortBinaryNumeralTerm count)) := by
  let body := compactAdditiveUnitBoundaryRowsBody
    tokenCount boundaryTable
  let branches := compactAdditiveUnitBoundaryRowsFullyDirectBranches
    tokenCount count boundaryTable numericBound bitBound rows htokenCount
    hcount htableSize hnumericSize
  let boundEquality := compactAdditiveUnitBoundaryRowsDirectBoundEquality count
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) count
    (Rew.bShift (shortBinaryNumeralTerm count)) body boundEquality branches
  exact CertifiedPAContextProof.cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm count)) body) =
        body.ballLT (shortBinaryNumeralTerm count)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

def compactAdditiveUnitBoundaryRowsDirectUniversalResource
    (tokenCount count boundaryTable numericBound bitBound : Nat) : Nat :=
  compileContextualTermBoundedUniversalPayloadEnvelope ∅ count
    (Rew.bShift (shortBinaryNumeralTerm count))
    (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable)
    (closedShortBoundEqualityPayloadPolynomial count)
    (contextualBranchesUnderBoundPayloadEnvelope ∅ count
      (Rewriting.free
        (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable))
      (compactAdditiveUnitBoundaryRowsFullyDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound))

theorem
    compileCompactAdditiveUnitBoundaryRowsDirectUniversalContext_payloadLength_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveUnitBoundaryRowsDirectUniversalContext tokenCount
      count boundaryTable numericBound bitBound rows htokenCount hcount
      htableSize hnumericSize).payloadLength <=
      compactAdditiveUnitBoundaryRowsDirectUniversalResource tokenCount count
        boundaryTable numericBound bitBound := by
  let body := compactAdditiveUnitBoundaryRowsBody
    tokenCount boundaryTable
  let branches := compactAdditiveUnitBoundaryRowsFullyDirectBranches
    tokenCount count boundaryTable numericBound bitBound rows htokenCount
    hcount htableSize hnumericSize
  let boundEquality := compactAdditiveUnitBoundaryRowsDirectBoundEquality count
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) count
    (Rew.bShift (shortBinaryNumeralTerm count)) body boundEquality branches
  have hboundRaw :=
    compileClosedShortBoundEquality_payloadLength_le_publicPolynomial count
  have hbound : boundEquality.payloadLength <=
      closedShortBoundEqualityPayloadPolynomial count := by
    simpa only [boundEquality,
      compactAdditiveUnitBoundaryRowsDirectBoundEquality,
      CertifiedPAContextProof.castContext_payloadLength,
      CertifiedPAContextProof.cast_payloadLength] using hboundRaw
  have hbranchesCore : branches.structuralPayloadBound count <=
      compactAdditiveUnitBoundaryRowsFullyDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound := by
    exact
      compactAdditiveUnitBoundaryRowsFullyDirectBranches_structuralPayloadBound_le
        tokenCount count boundaryTable numericBound bitBound rows htokenCount
        hcount htableSize hnumericSize
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ count
    (Rewriting.free body)
    (compactAdditiveUnitBoundaryRowsFullyDirectBranchesStructuralEnvelope
      tokenCount count boundaryTable numericBound bitBound)
  have hbranches :
      branches.compileUnderBoundAssumptionStructuralPayloadBound <=
        branchResource := by
    unfold branchResource contextualBranchesUnderBoundPayloadEnvelope
      CertifiedContextFiniteUniversalBranches.compileUnderBoundAssumptionStructuralPayloadBound
      CertifiedContextFiniteUniversalBranches.underExhaustionStructuralPayloadBound
    dsimp only [body] at hbranchesCore ⊢
    simp only [Finset.image_empty] at hbranchesCore ⊢
    omega
  have hstructural :=
    compileContextualTermBoundedUniversal_payloadLength_le_structural
      (Gamma := ∅) count
      (Rew.bShift (shortBinaryNumeralTerm count)) body
      boundEquality branches
  have henvelope :=
    compileContextualTermBoundedUniversalStructuralPayloadBound_le_envelope
      (Gamma := ∅) count
      (Rew.bShift (shortBinaryNumeralTerm count)) body
      boundEquality branches
      (closedShortBoundEqualityPayloadPolynomial count)
      branchResource hbound hbranches
  unfold compileCompactAdditiveUnitBoundaryRowsDirectUniversalContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change direct.payloadLength <= _
  exact hstructural.trans (henvelope.trans (by rfl))

noncomputable def compileCompactAdditiveUnitBoundaryRowsDirectClosedContext
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      (compactAdditiveUnitBoundaryRowsClosedFormula
        tokenCount count boundaryTable) := by
  let direct := compileCompactAdditiveUnitBoundaryRowsDirectUniversalContext
    tokenCount count boundaryTable numericBound bitBound rows htokenCount
    hcount htableSize hnumericSize
  exact CertifiedPAContextProof.cast
    (compactAdditiveUnitBoundaryRowsClosedFormula_alignment
      tokenCount count boundaryTable).symm direct

theorem
    compileCompactAdditiveUnitBoundaryRowsDirectClosedContext_payloadLength_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveUnitBoundaryRowsDirectClosedContext tokenCount count
      boundaryTable numericBound bitBound rows htokenCount hcount htableSize
      hnumericSize).payloadLength <=
      compactAdditiveUnitBoundaryRowsDirectUniversalResource tokenCount count
        boundaryTable numericBound bitBound := by
  unfold compileCompactAdditiveUnitBoundaryRowsDirectClosedContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  exact
    compileCompactAdditiveUnitBoundaryRowsDirectUniversalContext_payloadLength_le
      tokenCount count boundaryTable numericBound bitBound rows htokenCount
      hcount htableSize hnumericSize

noncomputable def
    compileCompactAdditiveUnitBoundaryRowsDirectClosedContextOfGraph
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (hrows : CompactAdditiveUnitBoundaryRows
      tokenCount count boundaryTable)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      (compactAdditiveUnitBoundaryRowsClosedFormula
        tokenCount count boundaryTable) :=
  compileCompactAdditiveUnitBoundaryRowsDirectClosedContext tokenCount count
    boundaryTable numericBound bitBound
    (compactAdditiveUnitBoundaryRowDataOfGraph
      tokenCount count boundaryTable hrows)
    htokenCount hcount htableSize hnumericSize

theorem
    compileCompactAdditiveUnitBoundaryRowsDirectClosedContextOfGraph_payloadLength_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (hrows : CompactAdditiveUnitBoundaryRows
      tokenCount count boundaryTable)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveUnitBoundaryRowsDirectClosedContextOfGraph
      tokenCount count boundaryTable numericBound bitBound hrows htokenCount
      hcount htableSize hnumericSize).payloadLength <=
      compactAdditiveUnitBoundaryRowsDirectUniversalResource tokenCount count
        boundaryTable numericBound bitBound :=
  compileCompactAdditiveUnitBoundaryRowsDirectClosedContext_payloadLength_le
    tokenCount count boundaryTable numericBound bitBound
    (compactAdditiveUnitBoundaryRowDataOfGraph
      tokenCount count boundaryTable hrows)
    htokenCount hcount htableSize hnumericSize

#print axioms compactAdditiveUnitBoundaryRowsDirectValues_le
#print axioms
  compactAdditiveUnitBoundaryRowsDirectTerminalCertificate_structuralPayloadBound_le
#print axioms compactAdditiveUnitBoundaryRowsBranchDirectBound
#print axioms
  compileCompactAdditiveUnitBoundaryRowsBranchDirect_payloadLength_le
#print axioms compactAdditiveUnitBoundaryRowsBody_freeVariables_eq_empty
#print axioms
  compactAdditiveUnitBoundaryRowsFullyDirectBranches_structuralPayloadBound_le
#print axioms
  compactAdditiveUnitBoundaryRowsFullyDirectBranchesStructuralEnvelope_le_polynomial
#print axioms
  compileCompactAdditiveUnitBoundaryRowsDirectUniversalContext_payloadLength_le
#print axioms
  compileCompactAdditiveUnitBoundaryRowsDirectClosedContext_payloadLength_le
#print axioms
  compileCompactAdditiveUnitBoundaryRowsDirectClosedContextOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsDirectCompiler
