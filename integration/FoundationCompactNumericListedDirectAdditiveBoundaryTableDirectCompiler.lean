import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveBoundaryTableFixedPolynomialBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity02
import integration.FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds

/-!
# Direct compiler for additive boundary-table rows

The two adjacent boundary values are installed by the public arity-two direct
compiler.  The terminal certificate consists of the two fixed-width entries
and their strict order.  Its resource depends only on the common numeric and
bit-width coordinates, never on the concrete witnesses.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveBoundaryTableDirectCompiler

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
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsFixedWidthEntryBounds
open FoundationCompactNumericListedDirectAdditiveBoundaryTableFixedPolynomialBounds

private abbrev boundaryZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation

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

def compactAdditiveBoundaryTableRowDirectValues
    {tokenCount boundaryTable index : Nat}
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index) : Fin 2 -> Nat :=
  ![data.right, data.left]

theorem compactAdditiveBoundaryTableRowDirectValues_le
    {tokenCount boundaryTable index : Nat}
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index)
    (coordinate : Fin 2) :
    compactAdditiveBoundaryTableRowDirectValues data coordinate <=
      tokenCount := by
  fin_cases coordinate
  · exact data.right_le
  · exact data.left_le

noncomputable def compactAdditiveBoundaryTableRowDirectTerminalCertificate
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index) :
    CheckedHybridValuationBoundedFormulaCertificate
      (extendValuation index boundaryZeroValuation)
      ((compactAdditiveBoundaryTableRowDirectTerminal
          tokenCount boundaryTable) ⇜
        fun coordinate => shortBinaryNumeralTerm
          (compactAdditiveBoundaryTableRowDirectValues data coordinate)) := by
  let valuation := extendValuation index boundaryZeroValuation
  let values := compactAdditiveBoundaryTableRowDirectValues data
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
        simpa [valuation, boundaryZeroValuation,
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
        simpa [valuation, boundaryZeroValuation,
          termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.right_entry)
  let ltCertificate := closedLtCertificate valuation
    data.left data.right data.left_lt_right
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      leftCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        rightCertificate ltCertificate)
  exact .cast (by
    rw [hvalueTerms]
    exact
      (compactAdditiveBoundaryTableRowDirectTerminal_substitution_alignment
        tokenCount boundaryTable data.left data.right).symm) terminalParts

theorem
    compactAdditiveBoundaryTableRowDirectTerminalCertificate_structuralPayloadBound_le
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveBoundaryTableRowDirectTerminalCertificate
          tokenCount boundaryTable index data) <=
      boundaryRowTerminalStructuralPayloadEnvelope
        tokenCount boundaryTable index data := by
  let valuation := extendValuation index boundaryZeroValuation
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm : ValuationTerm := &0
  let rightIndexTerm : ValuationTerm := ‘&0 + 1’
  let leftValueTerm := shortBinaryNumeralTerm data.left
  let rightValueTerm := shortBinaryNumeralTerm data.right
  let leftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      valuation tableTerm widthTerm leftIndexTerm leftValueTerm (by
        simpa [valuation, boundaryZeroValuation,
          tableTerm, widthTerm, leftIndexTerm, leftValueTerm,
          termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.left_entry)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      valuation tableTerm widthTerm rightIndexTerm rightValueTerm (by
        simpa [valuation, boundaryZeroValuation,
          tableTerm, widthTerm, rightIndexTerm, rightValueTerm,
          termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.right_entry)
  let ltCertificate := closedLtCertificate valuation
    data.left data.right data.left_lt_right
  let rightLt :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      rightCertificate ltCertificate
  let terminalParts :=
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
        simpa [valuation, boundaryZeroValuation,
          tableTerm, widthTerm, leftIndexTerm, leftValueTerm,
          termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.left_entry)
  have hright :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation tableTerm widthTerm rightIndexTerm rightValueTerm
      htable hwidth hrightIndex hrightValue (by
        simpa [valuation, boundaryZeroValuation,
          tableTerm, widthTerm, rightIndexTerm, rightValueTerm,
          termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.right_entry)
  have hlt := closedLtCertificate_structuralPayloadBound_le_transparent
    valuation data.left data.right data.left_lt_right
  have hrightLt := hybridConjunctionStructuralPayloadBound_le_envelope
    rightCertificate ltCertificate _ _ hright hlt
  have hterminalParts := hybridConjunctionStructuralPayloadBound_le_envelope
    leftCertificate rightLt _ _ hleft hrightLt
  simpa only [compactAdditiveBoundaryTableRowDirectTerminalCertificate,
    compactAdditiveBoundaryTableRowDirectValues,
    hybridFormulaStructuralPayloadBound,
    boundaryRowTerminalStructuralPayloadEnvelope,
    valuation, tableTerm, widthTerm, leftIndexTerm, rightIndexTerm,
    leftValueTerm, rightValueTerm, leftCertificate, rightCertificate,
    ltCertificate, rightLt, terminalParts,
    boundaryRowClosedLtStructuralPayloadResource] using hterminalParts

def compactAdditiveBoundaryTableRowBranchDirectPayloadEnvelope
    (tokenCount boundaryTable index numericBound bitBound : Nat) : Nat :=
  let valuation := extendValuation index boundaryZeroValuation
  let body := compactAdditiveBoundaryTableRowDirectTerminal
    tokenCount boundaryTable
  let contextCodeBound := formulaCodeSum
    (valuationContext body.freeVariables valuation)
  let bodyCodeBound := (binaryFormulaCode body).length
  let terminalResource :=
    boundaryRowTerminalFullyUniformPayloadPolynomial numericBound bitBound
  explicitBoundedWitnessDirectPublicPayloadEnvelope 2 contextCodeBound
    tokenCount bodyCodeBound terminalResource

noncomputable def compactAdditiveBoundaryTableRowBranchDirectBound
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound
      (extendValuation index boundaryZeroValuation)
      (Rewriting.free
        (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable))
      (compactAdditiveBoundaryTableRowBranchDirectPayloadEnvelope
        tokenCount boundaryTable index numericBound bitBound) := by
  let valuation := extendValuation index boundaryZeroValuation
  let body := compactAdditiveBoundaryTableRowDirectTerminal
    tokenCount boundaryTable
  let values := compactAdditiveBoundaryTableRowDirectValues data
  let contextCodeBound := formulaCodeSum
    (valuationContext body.freeVariables valuation)
  let bodyCodeBound := (binaryFormulaCode body).length
  let terminalResource :=
    boundaryRowTerminalFullyUniformPayloadPolynomial numericBound bitBound
  let terminalCertificate :=
    compactAdditiveBoundaryTableRowDirectTerminalCertificate
      tokenCount boundaryTable index data
  have hterminalStructural :
      hybridFormulaStructuralPayloadBound terminalCertificate <=
        boundaryRowTerminalStructuralPayloadEnvelope
          tokenCount boundaryTable index data := by
    exact
      compactAdditiveBoundaryTableRowDirectTerminalCertificate_structuralPayloadBound_le
        tokenCount boundaryTable index data
  have hterminalUniform :
      hybridFormulaStructuralPayloadBound terminalCertificate <=
        terminalResource :=
    hterminalStructural.trans
      (boundaryRowTerminalStructuralPayloadEnvelope_le_fullyUniform
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
      (compactAdditiveBoundaryTableRowDirectValues_le data) hbody hcontext
      terminalResource terminalCertificate.compile hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity02
      contextCodeBound tokenCount bodyCodeBound body values
      (compactAdditiveBoundaryTableRowDirectValues_le data) hbody hcontext
      terminalResource terminalCertificate.compile hterminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      Rewriting.free
        (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable) :=
    (compactAdditiveBoundaryTableRowBody_direct_free_alignment
      tokenCount boundaryTable).symm
  let proof := castValuationContextProof hformula rawProof
  refine { proof := proof, payloadLength_le := ?_ }
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [compactAdditiveBoundaryTableRowBranchDirectPayloadEnvelope,
    valuation, body, contextCodeBound, bodyCodeBound, terminalResource]
    using hcoordinates.2

noncomputable def compileCompactAdditiveBoundaryTableRowBranchDirect
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (Rewriting.free
          (compactAdditiveBoundaryTableRowBody
            tokenCount boundaryTable)).freeVariables
        (extendValuation index boundaryZeroValuation))
      (Rewriting.free
        (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable)) :=
  (compactAdditiveBoundaryTableRowBranchDirectBound tokenCount boundaryTable
    index numericBound bitBound data htokenCount hindexSuccessor htableSize
    hnumericSize).proof

theorem compileCompactAdditiveBoundaryTableRowBranchDirect_payloadLength_le
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveBoundaryTableRowBranchDirect tokenCount
      boundaryTable index numericBound bitBound data htokenCount
      hindexSuccessor htableSize hnumericSize).payloadLength <=
      compactAdditiveBoundaryTableRowBranchDirectPayloadEnvelope
        tokenCount boundaryTable index numericBound bitBound :=
  (compactAdditiveBoundaryTableRowBranchDirectBound tokenCount boundaryTable
    index numericBound bitBound data htokenCount hindexSuccessor htableSize
    hnumericSize).payloadLength_le

private theorem boundaryClosedShift_freeVariables_eq_empty
    (arity : Nat) (term : ValuationTerm)
    (hterm : term.freeVariables = ∅) :
    (boundaryTableClosedShift arity term).freeVariables = ∅ := by
  induction arity with
  | zero => simpa using hterm
  | succ arity inductionHypothesis =>
      rw [boundaryTableClosedShift_succ]
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

theorem compactAdditiveBoundaryTableRowTerminal_freeVariables_eq_empty
    (tokenCount boundaryTable : Nat) :
    (compactAdditiveBoundaryTableRowTerminal
      tokenCount boundaryTable).freeVariables = ∅ := by
  let tableTerm : ArithmeticSemiterm Nat 3 :=
    boundaryTableClosedShift 3 (shortBinaryNumeralTerm boundaryTable)
  let widthTerm : ArithmeticSemiterm Nat 3 :=
    boundaryTableClosedShift 3 (shortBinaryNumeralTerm tokenCount)
  let leftTerms : Fin 4 -> ArithmeticSemiterm Nat 3 :=
    ![tableTerm, widthTerm, #2, #1]
  let rightTerms : Fin 4 -> ArithmeticSemiterm Nat 3 :=
    ![tableTerm, widthTerm, ‘#2 + 1’, #0]
  let leftFormula : ArithmeticSemiformula Nat 3 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ leftTerms
  let rightFormula : ArithmeticSemiformula Nat 3 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ rightTerms
  let ltFormula : ArithmeticSemiformula Nat 3 := “#1 < #0”
  have htable : tableTerm.freeVariables = ∅ := by
    exact boundaryClosedShift_freeVariables_eq_empty 3 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable)
  have hwidth : widthTerm.freeVariables = ∅ := by
    exact boundaryClosedShift_freeVariables_eq_empty 3 _
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
  have hlt : ltFormula.freeVariables = ∅ := by
    rw [show ltFormula =
        (“#1 < #0” : ArithmeticSemiformula Nat 3) by rfl,
      lessThanFormula_freeVariables]
    simp
  change (leftFormula ⋏ (rightFormula ⋏ ltFormula)).freeVariables = ∅
  rw [LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_and,
    hleft, hright, hlt]
  simp

theorem compactAdditiveBoundaryTableRowBody_freeVariables_eq_empty
    (tokenCount boundaryTable : Nat) :
    (compactAdditiveBoundaryTableRowBody
      tokenCount boundaryTable).freeVariables = ∅ := by
  let terminal := compactAdditiveBoundaryTableRowTerminal
    tokenCount boundaryTable
  have hterminal : terminal.freeVariables = ∅ :=
    compactAdditiveBoundaryTableRowTerminal_freeVariables_eq_empty
      tokenCount boundaryTable
  let innerBound :=
    boundaryTableClosedShift 2 (shortBinaryNumeralTerm tokenCount)
  let outerBound :=
    boundaryTableClosedShift 1 (shortBinaryNumeralTerm tokenCount)
  have hinnerBound : innerBound.freeVariables = ∅ :=
    boundaryClosedShift_freeVariables_eq_empty 2 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
  have houterBound : outerBound.freeVariables = ∅ :=
    boundaryClosedShift_freeVariables_eq_empty 1 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
  have hinner := bexsLTSucc_freeVariables_eq_empty_of_empty terminal
    innerBound hterminal hinnerBound
  have houter := bexsLTSucc_freeVariables_eq_empty_of_empty
    (terminal.bexsLTSucc innerBound) outerBound hinner houterBound
  simpa only [compactAdditiveBoundaryTableRowBody, terminal, innerBound,
    outerBound, boundaryTableClosedShift] using houter

def compactAdditiveBoundaryTableRowDirectLeafPayloadResourceSum
    (tokenCount partCount boundaryTable numericBound bitBound : Nat) : Nat :=
  ∑ index : Fin partCount,
    compactAdditiveBoundaryTableRowBranchDirectPayloadEnvelope
      tokenCount boundaryTable index numericBound bitBound

theorem compileCompactAdditiveBoundaryTableRowBranchDirect_le_leafSum
    (tokenCount partCount boundaryTable numericBound bitBound index : Nat)
    (rows : (coordinate : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable coordinate)
    (hindex : index < partCount)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveBoundaryTableRowBranchDirect tokenCount
      boundaryTable index numericBound bitBound (rows ⟨index, hindex⟩)
      htokenCount (by omega) htableSize hnumericSize).payloadLength <=
      compactAdditiveBoundaryTableRowDirectLeafPayloadResourceSum
        tokenCount partCount boundaryTable numericBound bitBound := by
  let finiteIndex : Fin partCount := ⟨index, hindex⟩
  have hleaf :=
    compileCompactAdditiveBoundaryTableRowBranchDirect_payloadLength_le
      tokenCount boundaryTable index numericBound bitBound
      (rows finiteIndex) htokenCount (by omega) htableSize hnumericSize
  have hmember :
      compactAdditiveBoundaryTableRowBranchDirectPayloadEnvelope tokenCount
          boundaryTable finiteIndex numericBound bitBound <=
        compactAdditiveBoundaryTableRowDirectLeafPayloadResourceSum
          tokenCount partCount boundaryTable numericBound bitBound := by
    unfold compactAdditiveBoundaryTableRowDirectLeafPayloadResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin partCount) _ => Nat.zero_le
        (compactAdditiveBoundaryTableRowBranchDirectPayloadEnvelope
          tokenCount boundaryTable candidate numericBound bitBound))
      (Finset.mem_univ finiteIndex)
  dsimp only [finiteIndex] at hleaf hmember ⊢
  exact hleaf.trans hmember

noncomputable def compactAdditiveBoundaryTableRowsFullyDirectBranches
    (tokenCount partCount boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedContextFiniteUniversalBranches
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (Rewriting.free
        (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable))
      partCount := by
  have hbodyVariables :
      (compactAdditiveBoundaryTableRowBody
        tokenCount boundaryTable).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [compactAdditiveBoundaryTableRowBody_freeVariables_eq_empty]
  exact buildExplicitDirectUniversalBranches ∅ hbodyVariables partCount
    (fun index hindex =>
      compileCompactAdditiveBoundaryTableRowBranchDirect tokenCount
        boundaryTable index numericBound bitBound (rows ⟨index, hindex⟩)
        htokenCount (by omega) htableSize hnumericSize)

def compactAdditiveBoundaryTableRowsFullyDirectBranchesStructuralEnvelope
    (tokenCount partCount boundaryTable numericBound bitBound : Nat) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope boundaryZeroValuation
    partCount
    (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable) ∅
    (fun _ =>
      compactAdditiveBoundaryTableRowDirectLeafPayloadResourceSum tokenCount
        partCount boundaryTable numericBound bitBound)
    partCount

theorem
    compactAdditiveBoundaryTableRowsFullyDirectBranches_structuralPayloadBound_le
    (tokenCount partCount boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compactAdditiveBoundaryTableRowsFullyDirectBranches tokenCount partCount
      boundaryTable numericBound bitBound rows htokenCount hpartCount
      htableSize hnumericSize).structuralPayloadBound partCount <=
      compactAdditiveBoundaryTableRowsFullyDirectBranchesStructuralEnvelope
        tokenCount partCount boundaryTable numericBound bitBound := by
  have hbodyVariables :
      (compactAdditiveBoundaryTableRowBody
        tokenCount boundaryTable).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [compactAdditiveBoundaryTableRowBody_freeVariables_eq_empty]
  unfold compactAdditiveBoundaryTableRowsFullyDirectBranches
    compactAdditiveBoundaryTableRowsFullyDirectBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables partCount
    (fun _ =>
      compactAdditiveBoundaryTableRowDirectLeafPayloadResourceSum tokenCount
        partCount boundaryTable numericBound bitBound)
    partCount
    (fun index hindex =>
      compileCompactAdditiveBoundaryTableRowBranchDirect tokenCount
        boundaryTable index numericBound bitBound (rows ⟨index, hindex⟩)
        htokenCount (by omega) htableSize hnumericSize)
    (fun index hindex =>
      compileCompactAdditiveBoundaryTableRowBranchDirect_le_leafSum
        tokenCount partCount boundaryTable numericBound bitBound index rows
        hindex htokenCount hpartCount htableSize hnumericSize)

theorem
    compactAdditiveBoundaryTableRowsFullyDirectBranchesStructuralEnvelope_le_polynomial
    (tokenCount partCount boundaryTable numericBound bitBound : Nat) :
    compactAdditiveBoundaryTableRowsFullyDirectBranchesStructuralEnvelope
        tokenCount partCount boundaryTable numericBound bitBound <=
      explicitDirectUniversalBranchesPayloadPolynomial partCount
        (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable)
        (compactAdditiveBoundaryTableRowDirectLeafPayloadResourceSum
          tokenCount partCount boundaryTable numericBound bitBound) := by
  unfold compactAdditiveBoundaryTableRowsFullyDirectBranchesStructuralEnvelope
  exact directBranchesStructuralPayloadEnvelope_le_polynomial
    (compactAdditiveBoundaryTableRowDirectLeafPayloadResourceSum tokenCount
      partCount boundaryTable numericBound bitBound)
    (fun _ =>
      compactAdditiveBoundaryTableRowDirectLeafPayloadResourceSum tokenCount
        partCount boundaryTable numericBound bitBound)
    (fun _ => Nat.le_refl _)

noncomputable def compactAdditiveBoundaryTableRowsDirectBoundEquality
    (partCount : Nat) :
    CertifiedPAContextProof
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (“!!(iteratedSuccessorTerm 0 partCount) =
        !!(Rew.free
          (Rew.bShift (shortBinaryNumeralTerm partCount)))” :
        ValuationFormula) := by
  let raw := compileClosedShortBoundEquality partCount
  have hformula :
      (“!!(iteratedSuccessorTerm 0 partCount) =
        !!(shortBinaryNumeralTerm partCount)” : ValuationFormula) =
      (“!!(iteratedSuccessorTerm 0 partCount) =
        !!(Rew.free
          (Rew.bShift (shortBinaryNumeralTerm partCount)))” :
        ValuationFormula) := by
    simp
  exact CertifiedPAContextProof.castContext (by simp)
    (CertifiedPAContextProof.cast hformula raw)

noncomputable def compileCompactAdditiveBoundaryTableRowsDirectUniversalContext
    (tokenCount partCount boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      ((compactAdditiveBoundaryTableRowBody
        tokenCount boundaryTable).ballLT
          (shortBinaryNumeralTerm partCount)) := by
  let body := compactAdditiveBoundaryTableRowBody
    tokenCount boundaryTable
  let branches := compactAdditiveBoundaryTableRowsFullyDirectBranches
    tokenCount partCount boundaryTable numericBound bitBound rows htokenCount
    hpartCount htableSize hnumericSize
  let boundEquality :=
    compactAdditiveBoundaryTableRowsDirectBoundEquality partCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) partCount
    (Rew.bShift (shortBinaryNumeralTerm partCount)) body boundEquality branches
  exact CertifiedPAContextProof.cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm partCount)) body) =
        body.ballLT (shortBinaryNumeralTerm partCount)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

def compactAdditiveBoundaryTableRowsDirectUniversalResource
    (tokenCount partCount boundaryTable numericBound bitBound : Nat) : Nat :=
  compileContextualTermBoundedUniversalPayloadEnvelope ∅ partCount
    (Rew.bShift (shortBinaryNumeralTerm partCount))
    (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable)
    (closedShortBoundEqualityPayloadPolynomial partCount)
    (contextualBranchesUnderBoundPayloadEnvelope ∅ partCount
      (Rewriting.free
        (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable))
      (compactAdditiveBoundaryTableRowsFullyDirectBranchesStructuralEnvelope
        tokenCount partCount boundaryTable numericBound bitBound))

theorem
    compileCompactAdditiveBoundaryTableRowsDirectUniversalContext_payloadLength_le
    (tokenCount partCount boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveBoundaryTableRowsDirectUniversalContext tokenCount
      partCount boundaryTable numericBound bitBound rows htokenCount
      hpartCount htableSize hnumericSize).payloadLength <=
      compactAdditiveBoundaryTableRowsDirectUniversalResource tokenCount
        partCount boundaryTable numericBound bitBound := by
  let body := compactAdditiveBoundaryTableRowBody
    tokenCount boundaryTable
  let branches := compactAdditiveBoundaryTableRowsFullyDirectBranches
    tokenCount partCount boundaryTable numericBound bitBound rows htokenCount
    hpartCount htableSize hnumericSize
  let boundEquality :=
    compactAdditiveBoundaryTableRowsDirectBoundEquality partCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) partCount
    (Rew.bShift (shortBinaryNumeralTerm partCount)) body boundEquality branches
  have hboundRaw :=
    compileClosedShortBoundEquality_payloadLength_le_publicPolynomial partCount
  have hbound : boundEquality.payloadLength <=
      closedShortBoundEqualityPayloadPolynomial partCount := by
    simpa only [boundEquality,
      compactAdditiveBoundaryTableRowsDirectBoundEquality,
      CertifiedPAContextProof.castContext_payloadLength,
      CertifiedPAContextProof.cast_payloadLength] using hboundRaw
  have hbranchesCore : branches.structuralPayloadBound partCount <=
      compactAdditiveBoundaryTableRowsFullyDirectBranchesStructuralEnvelope
        tokenCount partCount boundaryTable numericBound bitBound := by
    exact
      compactAdditiveBoundaryTableRowsFullyDirectBranches_structuralPayloadBound_le
        tokenCount partCount boundaryTable numericBound bitBound rows
        htokenCount hpartCount htableSize hnumericSize
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅
    partCount (Rewriting.free body)
    (compactAdditiveBoundaryTableRowsFullyDirectBranchesStructuralEnvelope
      tokenCount partCount boundaryTable numericBound bitBound)
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
      (Gamma := ∅) partCount
      (Rew.bShift (shortBinaryNumeralTerm partCount)) body
      boundEquality branches
  have henvelope :=
    compileContextualTermBoundedUniversalStructuralPayloadBound_le_envelope
      (Gamma := ∅) partCount
      (Rew.bShift (shortBinaryNumeralTerm partCount)) body
      boundEquality branches
      (closedShortBoundEqualityPayloadPolynomial partCount)
      branchResource hbound hbranches
  unfold compileCompactAdditiveBoundaryTableRowsDirectUniversalContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change direct.payloadLength <= _
  exact hstructural.trans (henvelope.trans (by rfl))

private theorem freeFormulaAtArity_freeVariables_subset
    {arity : Nat}
    (formula : ArithmeticSemiformula Nat (arity + 1)) :
    (Rewriting.free formula).freeVariables ⊆
      insert 0 (formula.freeVariables.image Nat.succ) := by
  intro index hindex
  have hrewritten : (Rewriting.free formula).FVar? index := hindex
  rcases LO.FirstOrder.Semiformula.fvar?_rew hrewritten with
      hbound | hfree
  · rcases hbound with ⟨boundIndex, hboundIndex⟩
    cases boundIndex using Fin.lastCases with
    | last =>
        have hindexZero : index = 0 := by
          have hzeroIndex : 0 = index := by
            simpa [LO.FirstOrder.Semiformula.FVar?] using hboundIndex
          exact hzeroIndex.symm
        subst index
        exact Finset.mem_insert_self _ _
    | cast previous =>
        simp at hboundIndex
  · rcases hfree with ⟨sourceIndex, hsource, himage⟩
    have hindexSucc : index = sourceIndex + 1 := by
      have hsuccIndex : sourceIndex + 1 = index := by
        simpa [LO.FirstOrder.Semiformula.FVar?] using himage
      exact hsuccIndex.symm
    subst index
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨sourceIndex, hsource, rfl⟩)

theorem
    compactAdditiveBoundaryTableRowDirectTerminal_freeVariables_subset_singleton
    (tokenCount boundaryTable : Nat) :
    (compactAdditiveBoundaryTableRowDirectTerminal
      tokenCount boundaryTable).freeVariables ⊆ {0} := by
  rw [← compactAdditiveBoundaryTableRowTerminal_free_alignment]
  have hsubset := freeFormulaAtArity_freeVariables_subset
    (compactAdditiveBoundaryTableRowTerminal tokenCount boundaryTable)
  rw [compactAdditiveBoundaryTableRowTerminal_freeVariables_eq_empty] at hsubset
  simpa using hsubset

private theorem valuationContext_formulaCodeSum_le_singleton
    (vars : Finset Nat) (valuation : Nat -> Nat) (numericBound : Nat)
    (hvariables : vars ⊆ {0})
    (hvaluation : valuation 0 <= numericBound) :
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum
        (valuationContext vars valuation) <=
      unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound := by
  have hcard : vars.card <= 1 :=
    (Finset.card_le_card hvariables).trans (by simp)
  have hvalues : forall coordinate, coordinate ∈ vars ->
      valuation coordinate <= numericBound := by
    intro coordinate hcoordinate
    have hsingleton := hvariables hcoordinate
    simp only [Finset.mem_singleton] at hsingleton
    subst coordinate
    exact hvaluation
  have htermCodes : forall coordinate, coordinate ∈ vars ->
      (binaryTermCode (&coordinate : ValuationTerm)).length <=
        (binaryTermCode (&0 : ValuationTerm)).length := by
    intro coordinate hcoordinate
    have hsingleton := hvariables hcoordinate
    simp only [Finset.mem_singleton] at hsingleton
    subst coordinate
    exact le_rfl
  have hraw :=
    FoundationCompactPAValuationTermCompilerPublicBounds.valuationContext_formulaCodeSum_le_uniform
      vars valuation 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length hcard hvalues htermCodes
  change
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum
        (valuationContext vars valuation) <=
      FoundationCompactPAValuationTermCompilerPublicBounds.valuationContextFormulaCodeSumEnvelope
        1 numericBound (binaryTermCode (&0 : ValuationTerm)).length
  exact hraw

theorem compactAdditiveBoundaryTableRowDirectTerminal_contextCodeSum_le
    (tokenCount boundaryTable index numericBound : Nat)
    (hindex : index <= numericBound) :
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum
        (valuationContext
          (compactAdditiveBoundaryTableRowDirectTerminal
            tokenCount boundaryTable).freeVariables
          (extendValuation index boundaryZeroValuation)) <=
      unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound := by
  let vars := (compactAdditiveBoundaryTableRowDirectTerminal
    tokenCount boundaryTable).freeVariables
  let valuation := extendValuation index boundaryZeroValuation
  have hvariables : vars ⊆ {0} :=
    compactAdditiveBoundaryTableRowDirectTerminal_freeVariables_subset_singleton
      tokenCount boundaryTable
  have hvaluation : valuation 0 <= numericBound := by
    change index <= numericBound
    exact hindex
  exact valuationContext_formulaCodeSum_le_singleton vars valuation numericBound
    hvariables hvaluation

def compactAdditiveBoundaryTableRowUniformBranchDirectPayloadEnvelope
    (tokenCount boundaryTable numericBound bitBound : Nat) : Nat :=
  let body := compactAdditiveBoundaryTableRowDirectTerminal
    tokenCount boundaryTable
  let contextCodeBound :=
    unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound
  let bodyCodeBound := (binaryFormulaCode body).length
  let terminalResource :=
    boundaryRowTerminalFullyUniformPayloadPolynomial numericBound bitBound
  explicitBoundedWitnessDirectPublicPayloadEnvelope 2 contextCodeBound
    tokenCount bodyCodeBound terminalResource

noncomputable def compactAdditiveBoundaryTableRowUniformBranchDirectBound
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound
      (extendValuation index boundaryZeroValuation)
      (Rewriting.free
        (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable))
      (compactAdditiveBoundaryTableRowUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound) := by
  let valuation := extendValuation index boundaryZeroValuation
  let body := compactAdditiveBoundaryTableRowDirectTerminal
    tokenCount boundaryTable
  let values := compactAdditiveBoundaryTableRowDirectValues data
  let contextCodeBound :=
    unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound
  let bodyCodeBound := (binaryFormulaCode body).length
  let terminalResource :=
    boundaryRowTerminalFullyUniformPayloadPolynomial numericBound bitBound
  let terminalCertificate :=
    compactAdditiveBoundaryTableRowDirectTerminalCertificate
      tokenCount boundaryTable index data
  have hterminalStructural :
      hybridFormulaStructuralPayloadBound terminalCertificate <=
        boundaryRowTerminalStructuralPayloadEnvelope
          tokenCount boundaryTable index data :=
    compactAdditiveBoundaryTableRowDirectTerminalCertificate_structuralPayloadBound_le
      tokenCount boundaryTable index data
  have hterminalUniform :
      hybridFormulaStructuralPayloadBound terminalCertificate <=
        terminalResource :=
    hterminalStructural.trans
      (boundaryRowTerminalStructuralPayloadEnvelope_le_fullyUniform
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
    compactAdditiveBoundaryTableRowDirectTerminal_contextCodeSum_le
      tokenCount boundaryTable index numericBound (by omega)
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm tokenCount) 2 body
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound tokenCount bodyCodeBound body values
      (compactAdditiveBoundaryTableRowDirectValues_le data) hbody hcontext
      terminalResource terminalCertificate.compile hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity02
      contextCodeBound tokenCount bodyCodeBound body values
      (compactAdditiveBoundaryTableRowDirectValues_le data) hbody hcontext
      terminalResource terminalCertificate.compile hterminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      Rewriting.free
        (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable) :=
    (compactAdditiveBoundaryTableRowBody_direct_free_alignment
      tokenCount boundaryTable).symm
  let proof := castValuationContextProof hformula rawProof
  refine { proof := proof, payloadLength_le := ?_ }
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [
    compactAdditiveBoundaryTableRowUniformBranchDirectPayloadEnvelope,
    valuation, body, contextCodeBound, bodyCodeBound, terminalResource]
    using hcoordinates.2

noncomputable def compileCompactAdditiveBoundaryTableRowUniformBranchDirect
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (Rewriting.free
          (compactAdditiveBoundaryTableRowBody
            tokenCount boundaryTable)).freeVariables
        (extendValuation index boundaryZeroValuation))
      (Rewriting.free
        (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable)) :=
  (compactAdditiveBoundaryTableRowUniformBranchDirectBound tokenCount
    boundaryTable index numericBound bitBound data htokenCount
    hindexSuccessor htableSize hnumericSize).proof

theorem
    compileCompactAdditiveBoundaryTableRowUniformBranchDirect_payloadLength_le
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveBoundaryTableRowUniformBranchDirect tokenCount
      boundaryTable index numericBound bitBound data htokenCount
      hindexSuccessor htableSize hnumericSize).payloadLength <=
      compactAdditiveBoundaryTableRowUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound :=
  (compactAdditiveBoundaryTableRowUniformBranchDirectBound tokenCount
    boundaryTable index numericBound bitBound data htokenCount
    hindexSuccessor htableSize hnumericSize).payloadLength_le

noncomputable def compactAdditiveBoundaryTableRowsUniformDirectBranches
    (tokenCount partCount boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedContextFiniteUniversalBranches
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (Rewriting.free
        (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable))
      partCount := by
  have hbodyVariables :
      (compactAdditiveBoundaryTableRowBody
        tokenCount boundaryTable).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [compactAdditiveBoundaryTableRowBody_freeVariables_eq_empty]
  exact buildExplicitDirectUniversalBranches ∅ hbodyVariables partCount
    (fun index hindex =>
      compileCompactAdditiveBoundaryTableRowUniformBranchDirect tokenCount
        boundaryTable index numericBound bitBound (rows ⟨index, hindex⟩)
        htokenCount (by omega) htableSize hnumericSize)

def compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope
    (tokenCount partCount boundaryTable numericBound bitBound : Nat) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope boundaryZeroValuation
    partCount
    (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable) ∅
    (fun _ =>
      compactAdditiveBoundaryTableRowUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound)
    partCount

theorem
    compactAdditiveBoundaryTableRowsUniformDirectBranches_structuralPayloadBound_le
    (tokenCount partCount boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compactAdditiveBoundaryTableRowsUniformDirectBranches tokenCount
      partCount boundaryTable numericBound bitBound rows htokenCount
      hpartCount htableSize hnumericSize).structuralPayloadBound partCount <=
      compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope
        tokenCount partCount boundaryTable numericBound bitBound := by
  have hbodyVariables :
      (compactAdditiveBoundaryTableRowBody
        tokenCount boundaryTable).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [compactAdditiveBoundaryTableRowBody_freeVariables_eq_empty]
  unfold compactAdditiveBoundaryTableRowsUniformDirectBranches
    compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables partCount
    (fun _ =>
      compactAdditiveBoundaryTableRowUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound)
    partCount
    (fun index hindex =>
      compileCompactAdditiveBoundaryTableRowUniformBranchDirect tokenCount
        boundaryTable index numericBound bitBound (rows ⟨index, hindex⟩)
        htokenCount (by omega) htableSize hnumericSize)
    (fun index hindex =>
      compileCompactAdditiveBoundaryTableRowUniformBranchDirect_payloadLength_le
        tokenCount boundaryTable index numericBound bitBound
        (rows ⟨index, hindex⟩) htokenCount (by omega) htableSize
        hnumericSize)

theorem
    compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope_le_polynomial
    (tokenCount partCount boundaryTable numericBound bitBound : Nat) :
    compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope
        tokenCount partCount boundaryTable numericBound bitBound <=
      explicitDirectUniversalBranchesPayloadPolynomial partCount
        (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable)
        (compactAdditiveBoundaryTableRowUniformBranchDirectPayloadEnvelope
          tokenCount boundaryTable numericBound bitBound) := by
  unfold compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope
  exact directBranchesStructuralPayloadEnvelope_le_polynomial
    (compactAdditiveBoundaryTableRowUniformBranchDirectPayloadEnvelope
      tokenCount boundaryTable numericBound bitBound)
    (fun _ =>
      compactAdditiveBoundaryTableRowUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound)
    (fun _ => Nat.le_refl _)

noncomputable def
    compileCompactAdditiveBoundaryTableRowsUniformDirectUniversalContext
    (tokenCount partCount boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      ((compactAdditiveBoundaryTableRowBody
        tokenCount boundaryTable).ballLT
          (shortBinaryNumeralTerm partCount)) := by
  let body := compactAdditiveBoundaryTableRowBody
    tokenCount boundaryTable
  let branches := compactAdditiveBoundaryTableRowsUniformDirectBranches
    tokenCount partCount boundaryTable numericBound bitBound rows htokenCount
    hpartCount htableSize hnumericSize
  let boundEquality :=
    compactAdditiveBoundaryTableRowsDirectBoundEquality partCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) partCount
    (Rew.bShift (shortBinaryNumeralTerm partCount)) body boundEquality branches
  exact CertifiedPAContextProof.cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm partCount)) body) =
        body.ballLT (shortBinaryNumeralTerm partCount)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

def compactAdditiveBoundaryTableRowsUniformDirectUniversalResource
    (tokenCount partCount boundaryTable numericBound bitBound : Nat) : Nat :=
  compileContextualTermBoundedUniversalPayloadEnvelope ∅ partCount
    (Rew.bShift (shortBinaryNumeralTerm partCount))
    (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable)
    (closedShortBoundEqualityPayloadPolynomial partCount)
    (contextualBranchesUnderBoundPayloadEnvelope ∅ partCount
      (Rewriting.free
        (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable))
      (compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope
        tokenCount partCount boundaryTable numericBound bitBound))

theorem
    compileCompactAdditiveBoundaryTableRowsUniformDirectUniversalContext_payloadLength_le
    (tokenCount partCount boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveBoundaryTableRowsUniformDirectUniversalContext
      tokenCount partCount boundaryTable numericBound bitBound rows htokenCount
      hpartCount htableSize hnumericSize).payloadLength <=
      compactAdditiveBoundaryTableRowsUniformDirectUniversalResource tokenCount
        partCount boundaryTable numericBound bitBound := by
  let body := compactAdditiveBoundaryTableRowBody
    tokenCount boundaryTable
  let branches := compactAdditiveBoundaryTableRowsUniformDirectBranches
    tokenCount partCount boundaryTable numericBound bitBound rows htokenCount
    hpartCount htableSize hnumericSize
  let boundEquality :=
    compactAdditiveBoundaryTableRowsDirectBoundEquality partCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) partCount
    (Rew.bShift (shortBinaryNumeralTerm partCount)) body boundEquality branches
  have hboundRaw :=
    compileClosedShortBoundEquality_payloadLength_le_publicPolynomial partCount
  have hbound : boundEquality.payloadLength <=
      closedShortBoundEqualityPayloadPolynomial partCount := by
    simpa only [boundEquality,
      compactAdditiveBoundaryTableRowsDirectBoundEquality,
      CertifiedPAContextProof.castContext_payloadLength,
      CertifiedPAContextProof.cast_payloadLength] using hboundRaw
  have hbranchesCore : branches.structuralPayloadBound partCount <=
      compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope
        tokenCount partCount boundaryTable numericBound bitBound :=
    compactAdditiveBoundaryTableRowsUniformDirectBranches_structuralPayloadBound_le
      tokenCount partCount boundaryTable numericBound bitBound rows htokenCount
      hpartCount htableSize hnumericSize
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅
    partCount (Rewriting.free body)
    (compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope
      tokenCount partCount boundaryTable numericBound bitBound)
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
      (Gamma := ∅) partCount
      (Rew.bShift (shortBinaryNumeralTerm partCount)) body
      boundEquality branches
  have henvelope :=
    compileContextualTermBoundedUniversalStructuralPayloadBound_le_envelope
      (Gamma := ∅) partCount
      (Rew.bShift (shortBinaryNumeralTerm partCount)) body
      boundEquality branches
      (closedShortBoundEqualityPayloadPolynomial partCount)
      branchResource hbound hbranches
  unfold compileCompactAdditiveBoundaryTableRowsUniformDirectUniversalContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change direct.payloadLength <= _
  exact hstructural.trans (henvelope.trans (by rfl))

#print axioms compactAdditiveBoundaryTableRowDirectValues_le
#print axioms
  compactAdditiveBoundaryTableRowDirectTerminalCertificate_structuralPayloadBound_le
#print axioms compactAdditiveBoundaryTableRowBranchDirectBound
#print axioms
  compileCompactAdditiveBoundaryTableRowBranchDirect_payloadLength_le
#print axioms compactAdditiveBoundaryTableRowBody_freeVariables_eq_empty
#print axioms
  compactAdditiveBoundaryTableRowsFullyDirectBranches_structuralPayloadBound_le
#print axioms
  compileCompactAdditiveBoundaryTableRowsDirectUniversalContext_payloadLength_le
#print axioms
  compactAdditiveBoundaryTableRowDirectTerminal_freeVariables_subset_singleton
#print axioms
  compactAdditiveBoundaryTableRowDirectTerminal_contextCodeSum_le
#print axioms compactAdditiveBoundaryTableRowUniformBranchDirectBound
#print axioms
  compileCompactAdditiveBoundaryTableRowUniformBranchDirect_payloadLength_le
#print axioms
  compactAdditiveBoundaryTableRowsUniformDirectBranches_structuralPayloadBound_le
#print axioms
  compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope_le_polynomial
#print axioms
  compileCompactAdditiveBoundaryTableRowsUniformDirectUniversalContext_payloadLength_le

end FoundationCompactNumericListedDirectAdditiveBoundaryTableDirectCompiler
