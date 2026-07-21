import integration.FoundationCompactNumericListedDirectFormulaTransformTraceFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsBoundedExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
import integration.FoundationCompactPAContextCostPolynomialBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactPABinaryNumeralAdditionBounds

/-!
# Explicit certificate for a complete bounded formula-transform trace

The original nineteen-coordinate trace formula is assembled from its exact
initial/final endpoint certificate and its exact bounded adjacent-row
certificate.  The source unary `1` in the state-count equation is retained.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformTraceBoundedExplicitHybridCertificate

open FoundationCompactNumericListedDirectFormulaTransformTraceFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsBoundedExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactSyntaxTransformationCodeBounds

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      Rewriting.app right := by
  cases h
  rfl

def compactFormulaTransformTraceBoundedGraphClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformTraceBoundedGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      shortBinaryNumeralTerm fuel,
      shortBinaryNumeralTerm mode,
      shortBinaryNumeralTerm witnessStart,
      shortBinaryNumeralTerm witnessFinish,
      shortBinaryNumeralTerm witnessCount,
      shortBinaryNumeralTerm inputBoundary,
      shortBinaryNumeralTerm inputCount,
      shortBinaryNumeralTerm expectedOutputBoundary,
      shortBinaryNumeralTerm expectedOutputCount,
      shortBinaryNumeralTerm expectedSuffixBoundary,
      shortBinaryNumeralTerm expectedSuffixCount,
      shortBinaryNumeralTerm binderArity,
      shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm valueBound]

def compactFormulaTransformTraceBoundedGraphExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm stateCount) =
      !!(shortBinaryNumeralTerm fuel) + 1” ⋏
    (compactFormulaTransformInitialFinalBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound ⋏
      compactFormulaTransformAdjacentRowsBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount tableWidth valueBound)

theorem compactFormulaTransformTraceBoundedGraphClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat) :
    compactFormulaTransformTraceBoundedGraphClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity tableWidth valueBound =
      compactFormulaTransformTraceBoundedGraphExplicitFormula
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity tableWidth valueBound := by
  unfold compactFormulaTransformTraceBoundedGraphClosedFormula
  unfold compactFormulaTransformTraceBoundedGraphExplicitFormula
  unfold compactFormulaTransformTraceBoundedGraphDef
  unfold compactFormulaTransformInitialFinalBoundedClosedFormula
  unfold compactFormulaTransformAdjacentRowsBoundedClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
      all_goals rfl
    · intro coordinate
      exact Empty.elim coordinate

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem binaryFunction_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    {boundArity : Nat}
    (left right : ArithmeticSemiterm Nat boundArity) :
    (Semiterm.func functionSymbol ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero =>
        exact Finset.mem_union_left right.freeVariables hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            exact Finset.mem_union_right left.freeVariables hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr
        ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr
        ⟨1, Finset.mem_univ 1, hright⟩

private theorem arithmeticAddTerm_freeVariables
    {boundArity : Nat}
    (left right : ArithmeticSemiterm Nat boundArity) :
    (‘!!left + !!right’ :
      ArithmeticSemiterm Nat boundArity).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  rw [arithmeticAddTerm_eq_func]
  exact binaryFunction_freeVariables Language.Add.add left right

private theorem arithmeticOneTerm_freeVariables_eq_empty
    {boundArity : Nat} :
    (‘1’ : ArithmeticSemiterm Nat boundArity).freeVariables = ∅ := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.numeral_one,
    Semiterm.Operator.One.term_eq]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private noncomputable def stateCountCertificate
    (stateCount fuel : Nat) (hcount : stateCount = fuel + 1) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm stateCount) =
        !!(shortBinaryNumeralTerm fuel) + 1” := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm fuel) + 1’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm stateCount, rightTerm] (by
      change termValue zeroValuation (shortBinaryNumeralTerm stateCount) =
        termValue zeroValuation rightTerm
      simpa [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticOne] using hcount)
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

private def stateCountClosedFormula (stateCount fuel : Nat) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm stateCount) =
    !!(shortBinaryNumeralTerm fuel) + 1”

private theorem stateCountClosedFormula_freeVariables_eq_empty
    (stateCount fuel : Nat) :
    (stateCountClosedFormula stateCount fuel).freeVariables = ∅ := by
  have hright :
      (‘!!(shortBinaryNumeralTerm fuel) + 1’ :
        ValuationTerm).freeVariables = ∅ := by
    rw [arithmeticAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty]
    rfl
  simp [stateCountClosedFormula,
    shortBinaryNumeralTerm_freeVariables_eq_empty, hright]

private theorem stateCountIncrementSymmetry_formula (fuel : Nat) :
    (“!!(shortBinaryNumeralTerm (fuel + 1)) =
      !!(paAddTerm (shortBinaryNumeralTerm fuel) paOneTerm)” :
      ArithmeticProposition) =
      stateCountClosedFormula (fuel + 1) fuel := by
  unfold stateCountClosedFormula paAddTerm paOneTerm arithmeticOneTerm
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.numeral_one,
    Semiterm.Operator.One.term_eq,
    Rew.func]

/-- Direct proof of the state-count equation through the checked binary
increment compiler.  No valuation-compiler resource is needed for this leaf. -/
private noncomputable def stateCountDirectProof
    (stateCount fuel : Nat) (hcount : stateCount = fuel + 1) :
    CertifiedPAProof (stateCountClosedFormula stateCount fuel) := by
  subst stateCount
  exact CertifiedPAProof.cast (stateCountIncrementSymmetry_formula fuel)
    (proveEqualitySymmetry
      (paAddTerm (shortBinaryNumeralTerm fuel) paOneTerm)
      (shortBinaryNumeralTerm (fuel + 1))
      (proveBinaryNumeralIncrement fuel))

/-- Fixed polynomial resource for the direct state-count proof, expressed
only in the binary input width of `fuel`. -/
def stateCountDirectPayloadPolynomial (fuel : Nat) : Nat :=
  binaryNumeralIncrementPayloadPolynomial (Nat.size fuel) +
    paPrimitiveCostEnvelope
      (paCompilerTermCodeEnvelope (Nat.size fuel + 1))

theorem stateCountDirectProof_payloadLength_le_polynomial
    (stateCount fuel : Nat) (hcount : stateCount = fuel + 1) :
    (stateCountDirectProof stateCount fuel hcount).payloadLength ≤
      stateCountDirectPayloadPolynomial fuel := by
  subst stateCount
  let inputWidth := Nat.size fuel + 1
  let source := paAddTerm (shortBinaryNumeralTerm fuel) paOneTerm
  let result := shortBinaryNumeralTerm (fuel + 1)
  let increment := proveBinaryNumeralIncrement fuel
  have hfuelSize : Nat.size fuel ≤ inputWidth := by
    simp only [inputWidth]
    omega
  have hresultSize : Nat.size (fuel + 1) ≤ inputWidth := by
    exact natSize_add_one_le fuel
  have hfuelCode :
      (binaryTermCode (shortBinaryNumeralTerm fuel)).length ≤
        paTermCodeStage 0 inputWidth :=
    binaryNumeralTerm_code_length_le_stage0 fuel inputWidth hfuelSize
  have honeCode : (binaryTermCode paOneTerm).length ≤
      paTermCodeStage 0 inputWidth :=
    paOneTerm_code_length_le_stage0 inputWidth
  have hsourceStage : (binaryTermCode source).length ≤
      paTermCodeStage 1 inputWidth := by
    exact paAddTerm_code_length_le_nextStage
      (shortBinaryNumeralTerm fuel) paOneTerm 0 inputWidth
      hfuelCode honeCode
  have hsource : (binaryTermCode source).length ≤
      paCompilerTermCodeEnvelope inputWidth :=
    paTermCodeStage_to_compilerEnvelope hsourceStage (by omega)
  have hresultStage : (binaryTermCode result).length ≤
      paTermCodeStage 0 inputWidth :=
    binaryNumeralTerm_code_length_le_stage0
      (fuel + 1) inputWidth hresultSize
  have hresult : (binaryTermCode result).length ≤
      paCompilerTermCodeEnvelope inputWidth :=
    paTermCodeStage_to_compilerEnvelope hresultStage (by omega)
  have hincrement : increment.payloadLength ≤
      binaryNumeralIncrementPayloadPolynomial (Nat.size fuel) :=
    proveBinaryNumeralIncrement_payloadLength_le_polynomial fuel
  have hsymmetry := proveEqualitySymmetry_payloadLength_le_primitive
    source result increment (paCompilerTermCodeEnvelope inputWidth)
    hsource hresult
  change (CertifiedPAProof.cast _
    (proveEqualitySymmetry source result increment)).payloadLength ≤
      stateCountDirectPayloadPolynomial fuel
  rw [CertifiedPAProof.cast_payloadLength]
  unfold stateCountDirectPayloadPolynomial
  dsimp only [inputWidth] at hsymmetry ⊢
  omega

private theorem
    compactFormulaTransformInitialFinalBoundedClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    (compactFormulaTransformInitialFinalBoundedClosedFormula
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      valueBound).freeVariables = ∅ := by
  unfold compactFormulaTransformInitialFinalBoundedClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

private theorem
    compactFormulaTransformAdjacentRowsBoundedClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound : Nat) :
    (compactFormulaTransformAdjacentRowsBoundedClosedFormula
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth
      valueBound).freeVariables = ∅ := by
  unfold compactFormulaTransformAdjacentRowsBoundedClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

private noncomputable def initialFinalChildCertificate
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    (hinitialFinal : CompactFormulaTransformInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound) :
    HybridCertificate
      (compactFormulaTransformInitialFinalBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound) :=
  compactFormulaTransformInitialFinalBoundedExplicitHybridCertificateOfGraph
    tokenTable width tokenCount stateBoundary stateCount fuel
    inputBoundary inputCount expectedOutputBoundary expectedOutputCount
    expectedSuffixBoundary expectedSuffixCount binderArity valueBound
    hinitialFinal

private noncomputable def adjacentRowsChildCertificate
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount tableWidth valueBound : Nat)
    (hadjacent : CompactFormulaTransformAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount tableWidth valueBound) :
    HybridCertificate
      (compactFormulaTransformAdjacentRowsBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount tableWidth valueBound) :=
  compactFormulaTransformAdjacentRowsBoundedExplicitHybridCertificateOfGraph
    tokenTable width tokenCount stateBoundary stateCount fuel mode
    witnessStart witnessFinish witnessCount tableWidth valueBound hadjacent

private def certifiedEmptyContextProofOfGlobal
    {formula : ArithmeticProposition}
    (proof : CertifiedPAProof formula) :
    CertifiedPAContextProof ∅ formula where
  derivation := by simpa using proof.derivation
  certificate := proof.certificate
  certificate_valid := by simpa using proof.certificate_valid

private theorem certifiedEmptyContextProofOfGlobal_payloadLength_eq
    {formula : ArithmeticProposition}
    (proof : CertifiedPAProof formula) :
    (certifiedEmptyContextProofOfGlobal proof).payloadLength =
      proof.payloadLength := by
  rw [CertifiedPAProof.payloadLength_eq]
  rfl

private noncomputable def compileInitialFinalChildClosedContext
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    (hinitialFinal : CompactFormulaTransformInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound) :
    CertifiedPAContextProof ∅
      (compactFormulaTransformInitialFinalBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound) := by
  let raw :=
    compileCompactFormulaTransformInitialFinalBoundedExplicitHybridContext
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound
      hinitialFinal
  have hcontext :
      valuationContext
          (compactFormulaTransformInitialFinalBoundedClosedFormula
            tokenTable width tokenCount stateBoundary stateCount fuel
            inputBoundary inputCount expectedOutputBoundary expectedOutputCount
            expectedSuffixBoundary expectedSuffixCount binderArity
            valueBound).freeVariables zeroValuation = ∅ := by
    rw [
      compactFormulaTransformInitialFinalBoundedClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext raw

private noncomputable def compileAdjacentRowsChildClosedContext
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount tableWidth valueBound : Nat)
    (hadjacent : CompactFormulaTransformAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount tableWidth valueBound) :
    CertifiedPAContextProof ∅
      (compactFormulaTransformAdjacentRowsBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount tableWidth valueBound) := by
  let raw :=
    compileCompactFormulaTransformAdjacentRowsBoundedExplicitHybridContext
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount tableWidth valueBound hadjacent
  have hcontext :
      valuationContext
          (compactFormulaTransformAdjacentRowsBoundedClosedFormula
            tokenTable width tokenCount stateBoundary stateCount fuel mode
            witnessStart witnessFinish witnessCount tableWidth
            valueBound).freeVariables zeroValuation = ∅ := by
    rw [
      compactFormulaTransformAdjacentRowsBoundedClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext raw

/-- Direct empty-context assembly of the three trace components.  The state
count leaf uses the binary increment compiler, while the two large children
retain their exact explicit hybrid certificates. -/
noncomputable def compileCompactFormulaTransformTraceBoundedDirectContext
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat) :
    CompactFormulaTransformTraceBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity tableWidth valueBound ->
      CertifiedPAContextProof ∅
        (compactFormulaTransformTraceBoundedGraphClosedFormula
          tokenTable width tokenCount stateBoundary stateCount fuel mode
          witnessStart witnessFinish witnessCount inputBoundary inputCount
          expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
          expectedSuffixCount binderArity tableWidth valueBound)
  | ⟨hcount, hinitialFinal, hadjacent⟩ => by
      let countProof := certifiedEmptyContextProofOfGlobal
        (stateCountDirectProof stateCount fuel hcount)
      let initialFinalProof := compileInitialFinalChildClosedContext
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound
        hinitialFinal
      let adjacentProof := compileAdjacentRowsChildClosedContext
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount tableWidth valueBound
        hadjacent
      let pairProof := CertifiedPAContextProof.conjunction
        initialFinalProof adjacentProof
      let outerProof := CertifiedPAContextProof.conjunction countProof pairProof
      exact CertifiedPAContextProof.cast
        (compactFormulaTransformTraceBoundedGraphClosedFormula_alignment
          tokenTable width tokenCount stateBoundary stateCount fuel mode
          witnessStart witnessFinish witnessCount inputBoundary inputCount
          expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
          expectedSuffixCount binderArity tableWidth valueBound).symm
        outerProof

/-- Structural budget for the direct empty-context assembly.  It exposes the
two child resources and charges exactly two conjunction constructors. -/
noncomputable def compactFormulaTransformTraceBoundedDirectStructuralResource
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat) :
    CompactFormulaTransformTraceBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity tableWidth valueBound -> Nat
  | ⟨_, hinitialFinal, hadjacent⟩ =>
      let countFormula := stateCountClosedFormula stateCount fuel
      let initialFinalFormula :=
        compactFormulaTransformInitialFinalBoundedClosedFormula
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity valueBound
      let adjacentFormula :=
        compactFormulaTransformAdjacentRowsBoundedClosedFormula
          tokenTable width tokenCount stateBoundary stateCount fuel mode
          witnessStart witnessFinish witnessCount tableWidth valueBound
      stateCountDirectPayloadPolynomial fuel +
        compactFormulaTransformInitialFinalBoundedExplicitStructuralResource
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity valueBound
          hinitialFinal +
        compactFormulaTransformAdjacentRowsBoundedExplicitStructuralResource
          tokenTable width tokenCount stateBoundary stateCount fuel mode
          witnessStart witnessFinish witnessCount tableWidth valueBound
          hadjacent +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
          initialFinalFormula adjacentFormula +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ countFormula
          (initialFinalFormula ⋏ adjacentFormula)

theorem compileCompactFormulaTransformTraceBoundedDirectContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat)
    (hgraph : CompactFormulaTransformTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound) :
    (compileCompactFormulaTransformTraceBoundedDirectContext
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound
      hgraph).payloadLength ≤
    compactFormulaTransformTraceBoundedDirectStructuralResource
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound hgraph := by
  rcases hgraph with ⟨hcount, hinitialFinal, hadjacent⟩
  let countProof := certifiedEmptyContextProofOfGlobal
    (stateCountDirectProof stateCount fuel hcount)
  let initialFinalProof := compileInitialFinalChildClosedContext
    tokenTable width tokenCount stateBoundary stateCount fuel
    inputBoundary inputCount expectedOutputBoundary expectedOutputCount
    expectedSuffixBoundary expectedSuffixCount binderArity valueBound
    hinitialFinal
  let adjacentProof := compileAdjacentRowsChildClosedContext
    tokenTable width tokenCount stateBoundary stateCount fuel mode
    witnessStart witnessFinish witnessCount tableWidth valueBound hadjacent
  let pairProof := CertifiedPAContextProof.conjunction
    initialFinalProof adjacentProof
  let outerProof := CertifiedPAContextProof.conjunction countProof pairProof
  have hcountPayload : countProof.payloadLength ≤
      stateCountDirectPayloadPolynomial fuel := by
    rw [certifiedEmptyContextProofOfGlobal_payloadLength_eq]
    exact stateCountDirectProof_payloadLength_le_polynomial
      stateCount fuel hcount
  have hinitialFinalPayload : initialFinalProof.payloadLength ≤
      compactFormulaTransformInitialFinalBoundedExplicitStructuralResource
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound
        hinitialFinal := by
    unfold initialFinalProof compileInitialFinalChildClosedContext
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact
      compileCompactFormulaTransformInitialFinalBoundedExplicitHybridContext_payloadLength_le
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound
        hinitialFinal
  have hadjacentPayload : adjacentProof.payloadLength ≤
      compactFormulaTransformAdjacentRowsBoundedExplicitStructuralResource
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount tableWidth valueBound
        hadjacent := by
    unfold adjacentProof compileAdjacentRowsChildClosedContext
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact
      compileCompactFormulaTransformAdjacentRowsBoundedExplicitHybridContext_payloadLength_le
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount tableWidth valueBound
        hadjacent
  have hpair := CertifiedPAContextProof.conjunction_payloadLength_le
    initialFinalProof adjacentProof
  have hpairPayload : pairProof.payloadLength ≤
      compactFormulaTransformInitialFinalBoundedExplicitStructuralResource
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity valueBound
          hinitialFinal +
        compactFormulaTransformAdjacentRowsBoundedExplicitStructuralResource
          tokenTable width tokenCount stateBoundary stateCount fuel mode
          witnessStart witnessFinish witnessCount tableWidth valueBound
          hadjacent +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
          (compactFormulaTransformInitialFinalBoundedClosedFormula
            tokenTable width tokenCount stateBoundary stateCount fuel
            inputBoundary inputCount expectedOutputBoundary expectedOutputCount
            expectedSuffixBoundary expectedSuffixCount binderArity valueBound)
          (compactFormulaTransformAdjacentRowsBoundedClosedFormula
            tokenTable width tokenCount stateBoundary stateCount fuel mode
            witnessStart witnessFinish witnessCount tableWidth valueBound) := by
    dsimp only [pairProof] at hpair ⊢
    omega
  have houter := CertifiedPAContextProof.conjunction_payloadLength_le
    countProof pairProof
  change (CertifiedPAContextProof.cast _ outerProof).payloadLength ≤ _
  rw [CertifiedPAContextProof.cast_payloadLength]
  dsimp only [outerProof] at houter ⊢
  simp only [compactFormulaTransformTraceBoundedDirectStructuralResource]
  omega

/-- Exact formula-code coordinate for the five formulas used by the outer
two conjunction nodes.  It is intentionally not advertised as a polynomial
in the public numeric inputs; that separate syntax bound remains explicit. -/
def compactFormulaTransformTraceBoundedOuterFormulaCodeEnvelope
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat) : Nat :=
  let countFormula := stateCountClosedFormula stateCount fuel
  let initialFinalFormula :=
    compactFormulaTransformInitialFinalBoundedClosedFormula
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound
  let adjacentFormula :=
    compactFormulaTransformAdjacentRowsBoundedClosedFormula
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount tableWidth valueBound
  let pairFormula := initialFinalFormula ⋏ adjacentFormula
  let outerFormula := countFormula ⋏ pairFormula
  (binaryFormulaCode countFormula).length +
    (binaryFormulaCode initialFinalFormula).length +
    (binaryFormulaCode adjacentFormula).length +
    (binaryFormulaCode pairFormula).length +
    (binaryFormulaCode outerFormula).length + 1

/-- The six proof-assembly charges contributed only by the two outer
conjunction nodes.  This deliberately excludes all three child certificates,
so later bounds cannot hide a child resource inside an "outer polynomial". -/
noncomputable def compactFormulaTransformTraceBoundedOuterAssemblyResource
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat) : Nat :=
  let countFormula := stateCountClosedFormula stateCount fuel
  let initialFinalFormula :=
    compactFormulaTransformInitialFinalBoundedClosedFormula
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound
  let adjacentFormula :=
    compactFormulaTransformAdjacentRowsBoundedClosedFormula
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount tableWidth valueBound
  let pairFormula := initialFinalFormula ⋏ adjacentFormula
  let outerFormula := countFormula ⋏ pairFormula
  let outerContext := valuationContext outerFormula.freeVariables zeroValuation
  let pairContext := valuationContext pairFormula.freeVariables zeroValuation
  weakeningFullAssemblyCost (insert countFormula outerContext) +
    weakeningFullAssemblyCost (insert initialFinalFormula pairContext) +
    weakeningFullAssemblyCost (insert adjacentFormula pairContext) +
    CertifiedPAContextProof.conjunctionFullAssemblyCost pairContext
      initialFinalFormula adjacentFormula +
    weakeningFullAssemblyCost (insert pairFormula outerContext) +
    CertifiedPAContextProof.conjunctionFullAssemblyCost outerContext
      countFormula pairFormula

/-- The two fixed outer conjunction nodes cost at most six copies of one
honest formula-code envelope.  All child-certificate resources remain outside
this bound. -/
theorem compactFormulaTransformTraceBoundedOuterAssemblyResource_le_envelope
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat) :
    compactFormulaTransformTraceBoundedOuterAssemblyResource
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity tableWidth valueBound ≤
      6 * smallContextAssemblyEnvelope
        (compactFormulaTransformTraceBoundedOuterFormulaCodeEnvelope
          tokenTable width tokenCount stateBoundary stateCount fuel mode
          witnessStart witnessFinish witnessCount inputBoundary inputCount
          expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
          expectedSuffixCount binderArity tableWidth valueBound) := by
  let countFormula := stateCountClosedFormula stateCount fuel
  let initialFinalFormula :=
    compactFormulaTransformInitialFinalBoundedClosedFormula
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound
  let adjacentFormula :=
    compactFormulaTransformAdjacentRowsBoundedClosedFormula
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount tableWidth valueBound
  let pairFormula := initialFinalFormula ⋏ adjacentFormula
  let outerFormula := countFormula ⋏ pairFormula
  let formulaEnvelope :=
    (binaryFormulaCode countFormula).length +
      (binaryFormulaCode initialFinalFormula).length +
      (binaryFormulaCode adjacentFormula).length +
      (binaryFormulaCode pairFormula).length +
      (binaryFormulaCode outerFormula).length + 1
  have henvelope :
      compactFormulaTransformTraceBoundedOuterFormulaCodeEnvelope
          tokenTable width tokenCount stateBoundary stateCount fuel mode
          witnessStart witnessFinish witnessCount inputBoundary inputCount
          expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
          expectedSuffixCount binderArity tableWidth valueBound =
        formulaEnvelope := by
    rfl
  rw [henvelope]
  have hcountClosed : countFormula.freeVariables = ∅ := by
    exact stateCountClosedFormula_freeVariables_eq_empty stateCount fuel
  have hinitialFinalClosed : initialFinalFormula.freeVariables = ∅ := by
    exact
      compactFormulaTransformInitialFinalBoundedClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound
  have hadjacentClosed : adjacentFormula.freeVariables = ∅ := by
    exact
      compactFormulaTransformAdjacentRowsBoundedClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount tableWidth valueBound
  have hpairClosed : pairFormula.freeVariables = ∅ := by
    simp [pairFormula, hinitialFinalClosed, hadjacentClosed]
  have houterClosed : outerFormula.freeVariables = ∅ := by
    simp [outerFormula, hcountClosed, hpairClosed]
  have hpairContext :
      valuationContext pairFormula.freeVariables zeroValuation = ∅ := by
    rw [hpairClosed]
    simp [valuationContext]
  have houterContext :
      valuationContext outerFormula.freeVariables zeroValuation = ∅ := by
    rw [houterClosed]
    simp [valuationContext]
  have hcountCode :
      (binaryFormulaCode countFormula).length ≤ formulaEnvelope := by
    dsimp only [formulaEnvelope]
    omega
  have hinitialFinalCode :
      (binaryFormulaCode initialFinalFormula).length ≤ formulaEnvelope := by
    dsimp only [formulaEnvelope]
    omega
  have hadjacentCode :
      (binaryFormulaCode adjacentFormula).length ≤ formulaEnvelope := by
    dsimp only [formulaEnvelope]
    omega
  have hpairCode :
      (binaryFormulaCode pairFormula).length ≤ formulaEnvelope := by
    dsimp only [formulaEnvelope]
    omega
  have houterCode :
      (binaryFormulaCode outerFormula).length ≤ formulaEnvelope := by
    dsimp only [formulaEnvelope]
    omega
  have hempty :
      FormulaCodeBound (∅ : Finset ValuationFormula) formulaEnvelope := by
    simp [FormulaCodeBound]
  have hcountWeakening := weakeningFullAssemblyCost_le_small
    (insert countFormula ∅) formulaEnvelope (by simp)
    (hempty.insert hcountCode)
  have hinitialFinalWeakening := weakeningFullAssemblyCost_le_small
    (insert initialFinalFormula ∅) formulaEnvelope (by simp)
    (hempty.insert hinitialFinalCode)
  have hadjacentWeakening := weakeningFullAssemblyCost_le_small
    (insert adjacentFormula ∅) formulaEnvelope (by simp)
    (hempty.insert hadjacentCode)
  have hpairConjunction := conjunctionFullAssemblyCost_le_small
    ∅ initialFinalFormula adjacentFormula formulaEnvelope (by simp)
    hempty hinitialFinalCode hadjacentCode hpairCode
  have hpairWeakening := weakeningFullAssemblyCost_le_small
    (insert pairFormula ∅) formulaEnvelope (by simp)
    (hempty.insert hpairCode)
  have houterConjunction := conjunctionFullAssemblyCost_le_small
    ∅ countFormula pairFormula formulaEnvelope (by simp)
    hempty hcountCode hpairCode houterCode
  simp only [compactFormulaTransformTraceBoundedOuterAssemblyResource]
  rw [houterContext, hpairContext]
  dsimp only [countFormula, initialFinalFormula, adjacentFormula,
    pairFormula] at hcountWeakening
  dsimp only [countFormula, initialFinalFormula, adjacentFormula,
    pairFormula] at hinitialFinalWeakening
  dsimp only [countFormula, initialFinalFormula, adjacentFormula,
    pairFormula] at hadjacentWeakening
  dsimp only [countFormula, initialFinalFormula, adjacentFormula,
    pairFormula] at hpairConjunction
  dsimp only [countFormula, initialFinalFormula, adjacentFormula,
    pairFormula] at hpairWeakening
  dsimp only [countFormula, initialFinalFormula, adjacentFormula,
    pairFormula] at houterConjunction
  omega

/-- After replacing the state-count hybrid leaf by its direct increment proof,
the complete trace resource is bounded by the two genuine child resources,
the direct state polynomial, and the published outer formula-code envelope. -/
theorem compactFormulaTransformTraceBoundedDirectStructuralResource_le_envelope
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat)
    (hgraph : CompactFormulaTransformTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound) :
    compactFormulaTransformTraceBoundedDirectStructuralResource
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity tableWidth valueBound hgraph ≤
      stateCountDirectPayloadPolynomial fuel +
        compactFormulaTransformInitialFinalBoundedExplicitStructuralResource
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity valueBound
          hgraph.2.1 +
        compactFormulaTransformAdjacentRowsBoundedExplicitStructuralResource
          tokenTable width tokenCount stateBoundary stateCount fuel mode
          witnessStart witnessFinish witnessCount tableWidth valueBound
          hgraph.2.2 +
        6 * smallContextAssemblyEnvelope
          (compactFormulaTransformTraceBoundedOuterFormulaCodeEnvelope
            tokenTable width tokenCount stateBoundary stateCount fuel mode
            witnessStart witnessFinish witnessCount inputBoundary inputCount
            expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
            expectedSuffixCount binderArity tableWidth valueBound) := by
  rcases hgraph with ⟨hcount, hinitialFinal, hadjacent⟩
  have houter :=
    compactFormulaTransformTraceBoundedOuterAssemblyResource_le_envelope
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound
  simp only [compactFormulaTransformTraceBoundedDirectStructuralResource]
  simp only [compactFormulaTransformTraceBoundedOuterAssemblyResource] at houter
  simp [stateCountClosedFormula_freeVariables_eq_empty,
    compactFormulaTransformInitialFinalBoundedClosedFormula_freeVariables_eq_empty,
    compactFormulaTransformAdjacentRowsBoundedClosedFormula_freeVariables_eq_empty,
    valuationContext] at houter
  omega

/-- Sum of the three genuine child-certificate resources.  The graph proof is
used only to construct those certificates; no proof length or caller-supplied
resource enters this definition. -/
noncomputable def compactFormulaTransformTraceBoundedChildStructuralResource
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat) :
    CompactFormulaTransformTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound -> Nat
  | ⟨hcount, hinitialFinal, hadjacent⟩ =>
      hybridFormulaStructuralPayloadBound
          (stateCountCertificate stateCount fuel hcount) +
        hybridFormulaStructuralPayloadBound
          (initialFinalChildCertificate
            tokenTable width tokenCount stateBoundary stateCount fuel
            inputBoundary inputCount expectedOutputBoundary expectedOutputCount
            expectedSuffixBoundary expectedSuffixCount binderArity valueBound
            hinitialFinal) +
        hybridFormulaStructuralPayloadBound
          (adjacentRowsChildCertificate
            tokenTable width tokenCount stateBoundary stateCount fuel mode
            witnessStart witnessFinish witnessCount tableWidth valueBound
            hadjacent)

noncomputable def
    compactFormulaTransformTraceBoundedGraphExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat)
    (hgraph : CompactFormulaTransformTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound) :
    HybridCertificate
      (compactFormulaTransformTraceBoundedGraphClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity tableWidth valueBound) := by
  rcases hgraph with ⟨hcount, hinitialFinal, hadjacent⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (stateCountCertificate stateCount fuel hcount)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (initialFinalChildCertificate
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound
        hinitialFinal)
      (adjacentRowsChildCertificate
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount tableWidth valueBound
        hadjacent))
  exact .cast
    (compactFormulaTransformTraceBoundedGraphClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound).symm parts

noncomputable def
    compileCompactFormulaTransformTraceBoundedGraphExplicitHybridContext
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat)
    (hgraph : CompactFormulaTransformTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformTraceBoundedGraphClosedFormula
          tokenTable width tokenCount stateBoundary stateCount fuel mode
          witnessStart witnessFinish witnessCount inputBoundary inputCount
          expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
          expectedSuffixCount binderArity tableWidth
          valueBound).freeVariables zeroValuation)
      (compactFormulaTransformTraceBoundedGraphClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity tableWidth valueBound) :=
  (compactFormulaTransformTraceBoundedGraphExplicitHybridCertificateOfGraph
    tokenTable width tokenCount stateBoundary stateCount fuel mode
    witnessStart witnessFinish witnessCount inputBoundary inputCount
    expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
    expectedSuffixCount binderArity tableWidth valueBound hgraph).compile

noncomputable def
    compactFormulaTransformTraceBoundedGraphExplicitStructuralResource
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat)
    (hgraph : CompactFormulaTransformTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactFormulaTransformTraceBoundedGraphExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound hgraph)

private theorem
    compactFormulaTransformTraceBoundedGraphExplicitStructuralResource_eq_of_components
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat)
    (hcount : stateCount = fuel + 1)
    (hinitialFinal : CompactFormulaTransformInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound)
    (hadjacent : CompactFormulaTransformAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount tableWidth valueBound) :
    compactFormulaTransformTraceBoundedGraphExplicitStructuralResource
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity tableWidth valueBound
        ⟨hcount, hinitialFinal, hadjacent⟩ =
      compactFormulaTransformTraceBoundedChildStructuralResource
          tokenTable width tokenCount stateBoundary stateCount fuel mode
          witnessStart witnessFinish witnessCount inputBoundary inputCount
          expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
          expectedSuffixCount binderArity tableWidth valueBound
          ⟨hcount, hinitialFinal, hadjacent⟩ +
        compactFormulaTransformTraceBoundedOuterAssemblyResource
          tokenTable width tokenCount stateBoundary stateCount fuel mode
          witnessStart witnessFinish witnessCount inputBoundary inputCount
          expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
          expectedSuffixCount binderArity tableWidth valueBound := by
  simp only [
    compactFormulaTransformTraceBoundedGraphExplicitStructuralResource,
    compactFormulaTransformTraceBoundedGraphExplicitHybridCertificateOfGraph,
    compactFormulaTransformTraceBoundedChildStructuralResource,
    compactFormulaTransformTraceBoundedOuterAssemblyResource,
    hybridFormulaStructuralPayloadBound,
    stateCountClosedFormula]
  omega

/-- Exact decomposition of the complete trace resource.  In particular, the
bounded-universal row cost remains entirely in the adjacent-row child and is
not obscured by the constant-size outer conjunction assembly. -/
theorem compactFormulaTransformTraceBoundedGraphExplicitStructuralResource_eq
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat)
    (hgraph : CompactFormulaTransformTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound) :
    compactFormulaTransformTraceBoundedGraphExplicitStructuralResource
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity tableWidth valueBound hgraph =
      compactFormulaTransformTraceBoundedChildStructuralResource
          tokenTable width tokenCount stateBoundary stateCount fuel mode
          witnessStart witnessFinish witnessCount inputBoundary inputCount
          expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
          expectedSuffixCount binderArity tableWidth valueBound hgraph +
        compactFormulaTransformTraceBoundedOuterAssemblyResource
          tokenTable width tokenCount stateBoundary stateCount fuel mode
          witnessStart witnessFinish witnessCount inputBoundary inputCount
          expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
          expectedSuffixCount binderArity tableWidth valueBound := by
  let canonicalGraph : CompactFormulaTransformTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound :=
    ⟨hgraph.1, hgraph.2.1, hgraph.2.2⟩
  have hcanonical : hgraph = canonicalGraph := Subsingleton.elim _ _
  rw [hcanonical]
  simpa only [canonicalGraph] using
    (compactFormulaTransformTraceBoundedGraphExplicitStructuralResource_eq_of_components
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound
      hgraph.1 hgraph.2.1 hgraph.2.2)

theorem
    compileCompactFormulaTransformTraceBoundedGraphExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat)
    (hgraph : CompactFormulaTransformTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound) :
    (compileCompactFormulaTransformTraceBoundedGraphExplicitHybridContext
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound hgraph).payloadLength ≤
    compactFormulaTransformTraceBoundedGraphExplicitStructuralResource
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactFormulaTransformTraceBoundedGraphExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound hgraph)

#print axioms compactFormulaTransformTraceBoundedGraphClosedFormula_alignment
#print axioms
  compactFormulaTransformTraceBoundedGraphExplicitHybridCertificateOfGraph
#print axioms
  compactFormulaTransformTraceBoundedGraphExplicitStructuralResource_eq
#print axioms
  compactFormulaTransformTraceBoundedOuterAssemblyResource_le_envelope
#print axioms stateCountDirectProof_payloadLength_le_polynomial
#print axioms
  compileCompactFormulaTransformTraceBoundedDirectContext_payloadLength_le
#print axioms
  compactFormulaTransformTraceBoundedDirectStructuralResource_le_envelope
#print axioms
  compileCompactFormulaTransformTraceBoundedGraphExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformTraceBoundedExplicitHybridCertificate
