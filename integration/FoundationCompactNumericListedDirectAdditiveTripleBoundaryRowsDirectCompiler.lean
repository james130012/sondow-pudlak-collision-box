import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsFixedWidthEntryBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity02
import integration.FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds

/-!
# Direct compiler for additive triple-boundary rows

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

namespace FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsDirectCompiler

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
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsFixedWidthEntryBounds

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

private theorem arithmeticConstTerm_freeVariables_eq_empty
    {boundArity : Nat} (constant : LO.FirstOrder.Semiterm.Const ℒₒᵣ) :
    (constant : ArithmeticSemiterm Nat boundArity).freeVariables = ∅ := by
  unfold LO.FirstOrder.Semiterm.Operator.const
  unfold LO.FirstOrder.Semiterm.Operator.operator
  ext candidate
  constructor
  · intro hcandidate
    rcases LO.FirstOrder.Semiterm.fvar?_rew hcandidate with
        hbound | ⟨source, hsource, _⟩
    · rcases hbound with ⟨coordinate, _⟩
      exact Fin.elim0 coordinate
    · simpa [LO.FirstOrder.Semiterm.FVar?] using hsource
  · intro hcandidate
    simp at hcandidate

private theorem arithmeticThreeTerm_freeVariables_eq_empty
    {boundArity : Nat} :
    (‘3’ : ArithmeticSemiterm Nat boundArity).freeVariables = ∅ := by
  exact arithmeticConstTerm_freeVariables_eq_empty
    (LO.FirstOrder.Semiterm.Operator.numeral ℒₒᵣ 3)

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

def compactAdditiveTripleBoundaryRowsDirectValues
    {tokenCount boundaryTable index : Nat}
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index) : Fin 2 -> Nat :=
  ![data.right, data.left]

theorem compactAdditiveTripleBoundaryRowsDirectValues_le
    {tokenCount boundaryTable index : Nat}
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index)
    (coordinate : Fin 2) :
    compactAdditiveTripleBoundaryRowsDirectValues data coordinate <=
      tokenCount := by
  fin_cases coordinate
  · exact data.right_le
  · exact data.left_le

noncomputable def compactAdditiveTripleBoundaryRowsDirectTerminalCertificate
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index) :
    CheckedHybridValuationBoundedFormulaCertificate
      (extendValuation index tripleZeroValuation)
      ((compactAdditiveTripleBoundaryRowsBranchTerminal
          tokenCount boundaryTable) ⇜
        fun coordinate => shortBinaryNumeralTerm
          (compactAdditiveTripleBoundaryRowsDirectValues data coordinate)) := by
  let valuation := extendValuation index tripleZeroValuation
  let values := compactAdditiveTripleBoundaryRowsDirectValues data
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
        simpa [valuation, tripleZeroValuation,
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
        simpa [valuation, tripleZeroValuation,
          termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.right_entry)
  let successorCertificate := tripleEqualityCertificate valuation
    data.left data.right data.triple
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      leftCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        rightCertificate successorCertificate)
  exact .cast (by
    rw [hvalueTerms]
    exact
      (compactAdditiveTripleBoundaryRowsBranchTerminal_substitution_alignment
        tokenCount boundaryTable data.left data.right).symm) terminalParts

theorem
    compactAdditiveTripleBoundaryRowsDirectTerminalCertificate_structuralPayloadBound_le
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveTripleBoundaryRowsDirectTerminalCertificate
          tokenCount boundaryTable index data) <=
      compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope
        tokenCount boundaryTable index data := by
  let valuation := extendValuation index tripleZeroValuation
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
  let successorCertificate := tripleEqualityCertificate valuation
    data.left data.right data.triple
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
  have hsuccessor :=
    tripleEqualityCertificate_structuralPayloadBound_le_transparent
      valuation data.left data.right data.triple
  have hrightSuccessor := hybridConjunctionStructuralPayloadBound_le_envelope
    rightCertificate successorCertificate _ _ hright hsuccessor
  have hterminalParts := hybridConjunctionStructuralPayloadBound_le_envelope
    leftCertificate rightSuccessor _ _ hleft hrightSuccessor
  simpa only [compactAdditiveTripleBoundaryRowsDirectTerminalCertificate,
    compactAdditiveTripleBoundaryRowsDirectValues,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope,
    valuation, tableTerm, widthTerm, leftIndexTerm, rightIndexTerm,
    leftValueTerm, rightValueTerm, leftCertificate, rightCertificate,
    successorCertificate, rightSuccessor, terminalParts,
    tripleBoundarySpanStructuralPayloadResource] using hterminalParts

def compactAdditiveTripleBoundaryRowsBranchDirectPayloadEnvelope
    (tokenCount boundaryTable index numericBound bitBound : Nat) : Nat :=
  let valuation := extendValuation index tripleZeroValuation
  let body := compactAdditiveTripleBoundaryRowsBranchTerminal
    tokenCount boundaryTable
  let contextCodeBound := formulaCodeSum
    (valuationContext body.freeVariables valuation)
  let bodyCodeBound := (binaryFormulaCode body).length
  let terminalResource :=
    tripleBoundaryTerminalFullyUniformPayloadPolynomial numericBound bitBound
  explicitBoundedWitnessDirectPublicPayloadEnvelope 2 contextCodeBound
    tokenCount bodyCodeBound terminalResource

noncomputable def compactAdditiveTripleBoundaryRowsBranchDirectBound
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound
      (extendValuation index tripleZeroValuation)
      (Rewriting.free
        (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable))
      (compactAdditiveTripleBoundaryRowsBranchDirectPayloadEnvelope
        tokenCount boundaryTable index numericBound bitBound) := by
  let valuation := extendValuation index tripleZeroValuation
  let body := compactAdditiveTripleBoundaryRowsBranchTerminal
    tokenCount boundaryTable
  let values := compactAdditiveTripleBoundaryRowsDirectValues data
  let contextCodeBound := formulaCodeSum
    (valuationContext body.freeVariables valuation)
  let bodyCodeBound := (binaryFormulaCode body).length
  let terminalResource :=
    tripleBoundaryTerminalFullyUniformPayloadPolynomial numericBound bitBound
  let terminalCertificate :=
    compactAdditiveTripleBoundaryRowsDirectTerminalCertificate
      tokenCount boundaryTable index data
  have hterminalStructural :
      hybridFormulaStructuralPayloadBound terminalCertificate <=
        compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope
          tokenCount boundaryTable index data := by
    exact
      compactAdditiveTripleBoundaryRowsDirectTerminalCertificate_structuralPayloadBound_le
        tokenCount boundaryTable index data
  have hterminalUniform :
      hybridFormulaStructuralPayloadBound terminalCertificate <=
        terminalResource :=
    hterminalStructural.trans
      (compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope_le_fullyUniform
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
      (compactAdditiveTripleBoundaryRowsDirectValues_le data) hbody hcontext
      terminalResource terminalCertificate.compile hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity02
      contextCodeBound tokenCount bodyCodeBound body values
      (compactAdditiveTripleBoundaryRowsDirectValues_le data) hbody hcontext
      terminalResource terminalCertificate.compile hterminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      Rewriting.free
        (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable) :=
    (compactAdditiveTripleBoundaryRowsBody_free_alignment
      tokenCount boundaryTable).symm
  let proof := castValuationContextProof hformula rawProof
  refine { proof := proof, payloadLength_le := ?_ }
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [compactAdditiveTripleBoundaryRowsBranchDirectPayloadEnvelope,
    valuation, body, contextCodeBound, bodyCodeBound, terminalResource]
    using hcoordinates.2

noncomputable def compileCompactAdditiveTripleBoundaryRowsBranchDirect
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (Rewriting.free
          (compactAdditiveTripleBoundaryRowsBody
            tokenCount boundaryTable)).freeVariables
        (extendValuation index tripleZeroValuation))
      (Rewriting.free
        (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable)) :=
  (compactAdditiveTripleBoundaryRowsBranchDirectBound tokenCount boundaryTable
    index numericBound bitBound data htokenCount hindexSuccessor htableSize
    hnumericSize).proof

theorem compileCompactAdditiveTripleBoundaryRowsBranchDirect_payloadLength_le
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveTripleBoundaryRowsBranchDirect tokenCount
      boundaryTable index numericBound bitBound data htokenCount
      hindexSuccessor htableSize hnumericSize).payloadLength <=
      compactAdditiveTripleBoundaryRowsBranchDirectPayloadEnvelope
        tokenCount boundaryTable index numericBound bitBound :=
  (compactAdditiveTripleBoundaryRowsBranchDirectBound tokenCount boundaryTable
    index numericBound bitBound data htokenCount hindexSuccessor htableSize
    hnumericSize).payloadLength_le

private theorem tripleBoundaryClosedShift_freeVariables_eq_empty
    (arity : Nat) (term : ValuationTerm)
    (hterm : term.freeVariables = ∅) :
    (FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.closedShift
      arity term).freeVariables = ∅ := by
  induction arity with
  | zero => simpa [
      FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.closedShift]
  | succ arity inductionHypothesis =>
      simp only [
        FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.closedShift]
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

theorem compactAdditiveTripleBoundaryRowsTerminal_freeVariables_eq_empty
    (tokenCount boundaryTable : Nat) :
    (compactAdditiveTripleBoundaryRowsTerminal
      tokenCount boundaryTable).freeVariables = ∅ := by
  let tableTerm : ArithmeticSemiterm Nat 3 :=
    FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.closedShift
      3 (shortBinaryNumeralTerm boundaryTable)
  let widthTerm : ArithmeticSemiterm Nat 3 :=
    FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.closedShift
      3 (shortBinaryNumeralTerm tokenCount)
  let leftTerms : Fin 4 -> ArithmeticSemiterm Nat 3 :=
    ![tableTerm, widthTerm, #2, #1]
  let rightTerms : Fin 4 -> ArithmeticSemiterm Nat 3 :=
    ![tableTerm, widthTerm, ‘#2 + 1’, #0]
  let leftFormula : ArithmeticSemiformula Nat 3 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ leftTerms
  let rightFormula : ArithmeticSemiformula Nat 3 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ rightTerms
  let successorFormula : ArithmeticSemiformula Nat 3 := “#0 = #1 + 3”
  have htable : tableTerm.freeVariables = ∅ := by
    exact tripleBoundaryClosedShift_freeVariables_eq_empty 3 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable)
  have hwidth : widthTerm.freeVariables = ∅ := by
    exact tripleBoundaryClosedShift_freeVariables_eq_empty 3 _
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
    have hadd : (‘#1 + 3’ : ArithmeticSemiterm Nat 3).freeVariables = ∅ := by
      rw [arithmeticAddTerm_freeVariables_eq_union,
        arithmeticThreeTerm_freeVariables_eq_empty]
      simp
    rw [show successorFormula =
        (“#0 = #1 + 3” : ArithmeticSemiformula Nat 3) by rfl,
      equalityFormula_freeVariables, hadd]
    simp
  change (leftFormula ⋏ (rightFormula ⋏ successorFormula)).freeVariables = ∅
  rw [LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_and,
    hleft, hright, hsuccessor]
  simp

theorem compactAdditiveTripleBoundaryRowsBody_freeVariables_eq_empty
    (tokenCount boundaryTable : Nat) :
    (compactAdditiveTripleBoundaryRowsBody
      tokenCount boundaryTable).freeVariables = ∅ := by
  let terminal := compactAdditiveTripleBoundaryRowsTerminal
    tokenCount boundaryTable
  have hterminal : terminal.freeVariables = ∅ :=
    compactAdditiveTripleBoundaryRowsTerminal_freeVariables_eq_empty
      tokenCount boundaryTable
  let innerBound :=
    FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.closedShift
      2 (shortBinaryNumeralTerm tokenCount)
  let outerBound :=
    FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.closedShift
      1 (shortBinaryNumeralTerm tokenCount)
  have hinnerBound : innerBound.freeVariables = ∅ :=
    tripleBoundaryClosedShift_freeVariables_eq_empty 2 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
  have houterBound : outerBound.freeVariables = ∅ :=
    tripleBoundaryClosedShift_freeVariables_eq_empty 1 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
  have hinner := bexsLTSucc_freeVariables_eq_empty_of_empty terminal
    innerBound hterminal hinnerBound
  have houter := bexsLTSucc_freeVariables_eq_empty_of_empty
    (terminal.bexsLTSucc innerBound) outerBound hinner houterBound
  simpa only [compactAdditiveTripleBoundaryRowsBody, terminal, innerBound,
    outerBound] using houter

def compactAdditiveTripleBoundaryRowsDirectLeafPayloadResourceSum
    (tokenCount count boundaryTable numericBound bitBound : Nat) : Nat :=
  ∑ index : Fin count,
    compactAdditiveTripleBoundaryRowsBranchDirectPayloadEnvelope
      tokenCount boundaryTable index numericBound bitBound

theorem compileCompactAdditiveTripleBoundaryRowsBranchDirect_le_leafSum
    (tokenCount count boundaryTable numericBound bitBound index : Nat)
    (rows : (coordinate : Fin count) ->
      CompactAdditiveTripleBoundaryRowData
        tokenCount boundaryTable coordinate)
    (hindex : index < count)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveTripleBoundaryRowsBranchDirect tokenCount
      boundaryTable index numericBound bitBound (rows ⟨index, hindex⟩)
      htokenCount (by omega) htableSize hnumericSize).payloadLength <=
      compactAdditiveTripleBoundaryRowsDirectLeafPayloadResourceSum
        tokenCount count boundaryTable numericBound bitBound := by
  let finiteIndex : Fin count := ⟨index, hindex⟩
  have hleaf :=
    compileCompactAdditiveTripleBoundaryRowsBranchDirect_payloadLength_le
      tokenCount boundaryTable index numericBound bitBound
      (rows finiteIndex) htokenCount (by omega) htableSize hnumericSize
  have hmember :
      compactAdditiveTripleBoundaryRowsBranchDirectPayloadEnvelope tokenCount
          boundaryTable finiteIndex numericBound bitBound <=
        compactAdditiveTripleBoundaryRowsDirectLeafPayloadResourceSum
          tokenCount count boundaryTable numericBound bitBound := by
    unfold compactAdditiveTripleBoundaryRowsDirectLeafPayloadResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin count) _ => Nat.zero_le
        (compactAdditiveTripleBoundaryRowsBranchDirectPayloadEnvelope
          tokenCount boundaryTable candidate numericBound bitBound))
      (Finset.mem_univ finiteIndex)
  dsimp only [finiteIndex] at hleaf hmember ⊢
  exact hleaf.trans hmember

noncomputable def compactAdditiveTripleBoundaryRowsFullyDirectBranches
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedContextFiniteUniversalBranches
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (Rewriting.free
        (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable))
      count := by
  have hbodyVariables :
      (compactAdditiveTripleBoundaryRowsBody
        tokenCount boundaryTable).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [compactAdditiveTripleBoundaryRowsBody_freeVariables_eq_empty]
  exact buildExplicitDirectUniversalBranches ∅ hbodyVariables count
    (fun index hindex =>
      compileCompactAdditiveTripleBoundaryRowsBranchDirect tokenCount
        boundaryTable index numericBound bitBound (rows ⟨index, hindex⟩)
        htokenCount (by omega) htableSize hnumericSize)

def compactAdditiveTripleBoundaryRowsFullyDirectBranchesStructuralEnvelope
    (tokenCount count boundaryTable numericBound bitBound : Nat) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope tripleZeroValuation count
    (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable) ∅
    (fun _ =>
      compactAdditiveTripleBoundaryRowsDirectLeafPayloadResourceSum tokenCount
        count boundaryTable numericBound bitBound)
    count

theorem
    compactAdditiveTripleBoundaryRowsFullyDirectBranches_structuralPayloadBound_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compactAdditiveTripleBoundaryRowsFullyDirectBranches tokenCount count
      boundaryTable numericBound bitBound rows htokenCount hcount htableSize
      hnumericSize).structuralPayloadBound count <=
      compactAdditiveTripleBoundaryRowsFullyDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound := by
  have hbodyVariables :
      (compactAdditiveTripleBoundaryRowsBody
        tokenCount boundaryTable).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [compactAdditiveTripleBoundaryRowsBody_freeVariables_eq_empty]
  unfold compactAdditiveTripleBoundaryRowsFullyDirectBranches
    compactAdditiveTripleBoundaryRowsFullyDirectBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables count
    (fun _ =>
      compactAdditiveTripleBoundaryRowsDirectLeafPayloadResourceSum tokenCount
        count boundaryTable numericBound bitBound)
    count
    (fun index hindex =>
      compileCompactAdditiveTripleBoundaryRowsBranchDirect tokenCount
        boundaryTable index numericBound bitBound (rows ⟨index, hindex⟩)
        htokenCount (by omega) htableSize hnumericSize)
    (fun index hindex =>
      compileCompactAdditiveTripleBoundaryRowsBranchDirect_le_leafSum
        tokenCount count boundaryTable numericBound bitBound index rows
        hindex htokenCount hcount htableSize hnumericSize)

theorem
    compactAdditiveTripleBoundaryRowsFullyDirectBranchesStructuralEnvelope_le_polynomial
    (tokenCount count boundaryTable numericBound bitBound : Nat) :
    compactAdditiveTripleBoundaryRowsFullyDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound <=
      explicitDirectUniversalBranchesPayloadPolynomial count
        (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable)
        (compactAdditiveTripleBoundaryRowsDirectLeafPayloadResourceSum
          tokenCount count boundaryTable numericBound bitBound) := by
  unfold compactAdditiveTripleBoundaryRowsFullyDirectBranchesStructuralEnvelope
  exact directBranchesStructuralPayloadEnvelope_le_polynomial
    (compactAdditiveTripleBoundaryRowsDirectLeafPayloadResourceSum tokenCount
      count boundaryTable numericBound bitBound)
    (fun _ =>
      compactAdditiveTripleBoundaryRowsDirectLeafPayloadResourceSum tokenCount
        count boundaryTable numericBound bitBound)
    (fun _ => Nat.le_refl _)

noncomputable def compactAdditiveTripleBoundaryRowsDirectBoundEquality
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

noncomputable def compileCompactAdditiveTripleBoundaryRowsDirectUniversalContext
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      ((compactAdditiveTripleBoundaryRowsBody
        tokenCount boundaryTable).ballLT
          (shortBinaryNumeralTerm count)) := by
  let body := compactAdditiveTripleBoundaryRowsBody
    tokenCount boundaryTable
  let branches := compactAdditiveTripleBoundaryRowsFullyDirectBranches
    tokenCount count boundaryTable numericBound bitBound rows htokenCount
    hcount htableSize hnumericSize
  let boundEquality := compactAdditiveTripleBoundaryRowsDirectBoundEquality count
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) count
    (Rew.bShift (shortBinaryNumeralTerm count)) body boundEquality branches
  exact CertifiedPAContextProof.cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm count)) body) =
        body.ballLT (shortBinaryNumeralTerm count)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

def compactAdditiveTripleBoundaryRowsDirectUniversalResource
    (tokenCount count boundaryTable numericBound bitBound : Nat) : Nat :=
  compileContextualTermBoundedUniversalPayloadEnvelope ∅ count
    (Rew.bShift (shortBinaryNumeralTerm count))
    (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable)
    (closedShortBoundEqualityPayloadPolynomial count)
    (contextualBranchesUnderBoundPayloadEnvelope ∅ count
      (Rewriting.free
        (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable))
      (compactAdditiveTripleBoundaryRowsFullyDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound))

theorem
    compileCompactAdditiveTripleBoundaryRowsDirectUniversalContext_payloadLength_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveTripleBoundaryRowsDirectUniversalContext tokenCount
      count boundaryTable numericBound bitBound rows htokenCount hcount
      htableSize hnumericSize).payloadLength <=
      compactAdditiveTripleBoundaryRowsDirectUniversalResource tokenCount count
        boundaryTable numericBound bitBound := by
  let body := compactAdditiveTripleBoundaryRowsBody
    tokenCount boundaryTable
  let branches := compactAdditiveTripleBoundaryRowsFullyDirectBranches
    tokenCount count boundaryTable numericBound bitBound rows htokenCount
    hcount htableSize hnumericSize
  let boundEquality := compactAdditiveTripleBoundaryRowsDirectBoundEquality count
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) count
    (Rew.bShift (shortBinaryNumeralTerm count)) body boundEquality branches
  have hboundRaw :=
    compileClosedShortBoundEquality_payloadLength_le_publicPolynomial count
  have hbound : boundEquality.payloadLength <=
      closedShortBoundEqualityPayloadPolynomial count := by
    simpa only [boundEquality,
      compactAdditiveTripleBoundaryRowsDirectBoundEquality,
      CertifiedPAContextProof.castContext_payloadLength,
      CertifiedPAContextProof.cast_payloadLength] using hboundRaw
  have hbranchesCore : branches.structuralPayloadBound count <=
      compactAdditiveTripleBoundaryRowsFullyDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound := by
    exact
      compactAdditiveTripleBoundaryRowsFullyDirectBranches_structuralPayloadBound_le
        tokenCount count boundaryTable numericBound bitBound rows htokenCount
        hcount htableSize hnumericSize
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ count
    (Rewriting.free body)
    (compactAdditiveTripleBoundaryRowsFullyDirectBranchesStructuralEnvelope
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
  unfold compileCompactAdditiveTripleBoundaryRowsDirectUniversalContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change direct.payloadLength <= _
  exact hstructural.trans (henvelope.trans (by rfl))

noncomputable def compileCompactAdditiveTripleBoundaryRowsDirectClosedContext
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      (compactAdditiveTripleBoundaryRowsClosedFormula
        tokenCount count boundaryTable) := by
  let direct := compileCompactAdditiveTripleBoundaryRowsDirectUniversalContext
    tokenCount count boundaryTable numericBound bitBound rows htokenCount
    hcount htableSize hnumericSize
  exact CertifiedPAContextProof.cast
    (compactAdditiveTripleBoundaryRowsClosedFormula_alignment
      tokenCount count boundaryTable).symm direct

theorem
    compileCompactAdditiveTripleBoundaryRowsDirectClosedContext_payloadLength_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveTripleBoundaryRowsDirectClosedContext tokenCount count
      boundaryTable numericBound bitBound rows htokenCount hcount htableSize
      hnumericSize).payloadLength <=
      compactAdditiveTripleBoundaryRowsDirectUniversalResource tokenCount count
        boundaryTable numericBound bitBound := by
  unfold compileCompactAdditiveTripleBoundaryRowsDirectClosedContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  exact
    compileCompactAdditiveTripleBoundaryRowsDirectUniversalContext_payloadLength_le
      tokenCount count boundaryTable numericBound bitBound rows htokenCount
      hcount htableSize hnumericSize

noncomputable def
    compileCompactAdditiveTripleBoundaryRowsDirectClosedContextOfGraph
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (hrows : CompactAdditiveTripleBoundaryRows
      tokenCount count boundaryTable)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      (compactAdditiveTripleBoundaryRowsClosedFormula
        tokenCount count boundaryTable) :=
  compileCompactAdditiveTripleBoundaryRowsDirectClosedContext tokenCount count
    boundaryTable numericBound bitBound
    (compactAdditiveTripleBoundaryRowDataOfGraph
      tokenCount count boundaryTable hrows)
    htokenCount hcount htableSize hnumericSize

theorem
    compileCompactAdditiveTripleBoundaryRowsDirectClosedContextOfGraph_payloadLength_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (hrows : CompactAdditiveTripleBoundaryRows
      tokenCount count boundaryTable)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveTripleBoundaryRowsDirectClosedContextOfGraph
      tokenCount count boundaryTable numericBound bitBound hrows htokenCount
      hcount htableSize hnumericSize).payloadLength <=
      compactAdditiveTripleBoundaryRowsDirectUniversalResource tokenCount count
        boundaryTable numericBound bitBound :=
  compileCompactAdditiveTripleBoundaryRowsDirectClosedContext_payloadLength_le
    tokenCount count boundaryTable numericBound bitBound
    (compactAdditiveTripleBoundaryRowDataOfGraph
      tokenCount count boundaryTable hrows)
    htokenCount hcount htableSize hnumericSize

#print axioms compactAdditiveTripleBoundaryRowsDirectValues_le
#print axioms
  compactAdditiveTripleBoundaryRowsDirectTerminalCertificate_structuralPayloadBound_le
#print axioms compactAdditiveTripleBoundaryRowsBranchDirectBound
#print axioms
  compileCompactAdditiveTripleBoundaryRowsBranchDirect_payloadLength_le
#print axioms compactAdditiveTripleBoundaryRowsBody_freeVariables_eq_empty
#print axioms
  compactAdditiveTripleBoundaryRowsFullyDirectBranches_structuralPayloadBound_le
#print axioms
  compactAdditiveTripleBoundaryRowsFullyDirectBranchesStructuralEnvelope_le_polynomial
#print axioms
  compileCompactAdditiveTripleBoundaryRowsDirectUniversalContext_payloadLength_le
#print axioms
  compileCompactAdditiveTripleBoundaryRowsDirectClosedContext_payloadLength_le
#print axioms
  compileCompactAdditiveTripleBoundaryRowsDirectClosedContextOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsDirectCompiler
