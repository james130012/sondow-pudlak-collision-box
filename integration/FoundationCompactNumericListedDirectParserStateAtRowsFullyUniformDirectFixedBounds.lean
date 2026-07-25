import integration.FoundationCompactNumericListedDirectParserStateAtRowsPublicBounds
import integration.FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds

/-!
# Fully uniform direct bound for one parser-state row

The index comparison, two fixed-width entries, and parser-state core are
compiled on the same valuation and bounded by one coordinate-independent
resource.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

namespace FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsPublicBounds
open FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds

private theorem arithmeticAddTerm_freeVariables_uniformRow
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables
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

private theorem arithmeticOneTerm_freeVariables_uniformRow :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticAddTerm_eq_func_uniformRow
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd_uniformRow
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_uniformRow]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_uniformRow (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

theorem compactParserValuationContextFormulaCodeSum_le_singleton
    (valuation : Nat -> Nat) (formula : ValuationFormula)
    (numericBound : Nat)
    (hvariables : formula.freeVariables ⊆ {0})
    (hzero : valuation 0 <= numericBound) :
    formulaCodeSum (valuationContext formula.freeVariables valuation) <=
      valuationContextFormulaCodeSumEnvelope 1 numericBound
        (binaryTermCode (&0 : ValuationTerm)).length := by
  apply valuationContext_formulaCodeSum_le_uniform formula.freeVariables
    valuation 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length
  · exact (Finset.card_le_card hvariables).trans (by simp)
  · intro index hindex
    have hzeroIndex := hvariables hindex
    simp only [Finset.mem_singleton] at hzeroIndex
    subst index
    exact hzero
  · intro index hindex
    have hzeroIndex := hvariables hindex
    simp only [Finset.mem_singleton] at hzeroIndex
    subst index
    exact Nat.le_refl _

theorem
    compactUnifiedParserStateAtRowsAtValuationIndexFormula_freeVariables_subset_singleton
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hindexVariables : indexTerm.freeVariables ⊆ {0}) :
    (compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount indexTerm coordinates
      sizeWitness).freeVariables ⊆ {0} := by
  unfold compactUnifiedParserStateAtRowsAtValuationIndexFormula
  apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
  intro coordinate
  fin_cases coordinate <;>
    simp [shortBinaryNumeralTerm_freeVariables_eq_empty, hindexVariables]

def compactParserStateAtRowsUniformTermCodeBound
    (indexTerm : ValuationTerm) (bitBound : Nat) : Nat :=
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  (binaryTermCode indexTerm).length +
    (binaryTermCode nextIndexTerm).length +
    binaryNumeralTermCodeEnvelope bitBound + 1

def compactParserStateAtRowsUniformEntryResource
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate indexTerm
        numericBound bitBound))

def compactParserStateAtRowsUniformStartEntryResource
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  compactParserStateAtRowsUniformEntryResource indexTerm numericBound bitBound

def compactParserStateAtRowsUniformFinishEntryResource
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  compactParserStateAtRowsUniformEntryResource nextIndexTerm numericBound
    bitBound

def compactParserStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  let contextResource :=
    valuationContextFormulaCodeSumEnvelope 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length
  let indexResource := compilePositiveRelationFixedPayloadPolynomial
    numericBound
    (compactParserStateAtRowsUniformTermCodeBound indexTerm bitBound)
  let startResource := compactParserStateAtRowsUniformStartEntryResource
    indexTerm numericBound bitBound
  let finishResource := compactParserStateAtRowsUniformFinishEntryResource
    indexTerm numericBound bitBound
  let coreResource :=
    compactUnifiedParserStateCoreFullyUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  contextResource + indexResource + startResource + finishResource +
    coreResource + 3 * (binaryNatCode 4).length + 1

def compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactParserStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
      indexTerm numericBound bitBound
  let indexResource := compilePositiveRelationFixedPayloadPolynomial
    numericBound
    (compactParserStateAtRowsUniformTermCodeBound indexTerm bitBound)
  let startResource := compactParserStateAtRowsUniformStartEntryResource
    indexTerm numericBound bitBound
  let finishResource := compactParserStateAtRowsUniformFinishEntryResource
    indexTerm numericBound bitBound
  let coreResource :=
    compactUnifiedParserStateCoreFullyUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let finishCoreResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource finishResource coreResource
  let startTailResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource startResource finishCoreResource
  hybridConjunctionGeneralPayloadEnvelope syntaxResource indexResource
    startTailResource

noncomputable def compactParserStateAtRowsIndexFullyUniformDirectFixedBound
    (indexTerm : ValuationTerm) (stateCount numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hindex :
      termValue compactParserStateAtRowsZeroValuation indexTerm < stateCount)
    (hstateCount : stateCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound compactParserStateAtRowsZeroValuation
      “!!indexTerm < !!(shortBinaryNumeralTerm stateCount)”
      (compilePositiveRelationFixedPayloadPolynomial numericBound
        (compactParserStateAtRowsUniformTermCodeBound indexTerm bitBound)) := by
  let termCodeBound :=
    compactParserStateAtRowsUniformTermCodeBound indexTerm bitBound
  let resource :=
    compilePositiveRelationFixedPayloadPolynomial numericBound termCodeBound
  let certificate :=
    compactParserStateAtRowsValuationLtCertificate indexTerm stateCount hindex
  let proof := certificate.compile
  have hstateCountSize : Nat.size stateCount <= bitBound :=
    (Nat.size_le_size hstateCount).trans hnumericSize
  have hindexTermCode :
      (binaryTermCode indexTerm).length <= termCodeBound := by
    dsimp only [termCodeBound,
      compactParserStateAtRowsUniformTermCodeBound]
    omega
  have hstateCountCode :
      (binaryTermCode
        (shortBinaryNumeralTerm stateCount : ValuationTerm)).length <=
        termCodeBound := by
    have hcode := binaryNumeralTerm_code_length_le_envelope stateCount
      bitBound hstateCountSize
    dsimp only [termCodeBound,
      compactParserStateAtRowsUniformTermCodeBound]
    exact hcode.trans (by omega)
  have hpolynomial :
      compactParserStateAtRowsLtStructuralPayloadPolynomial indexTerm
          stateCount <= resource := by
    have hfixed := compilePositiveRelationPayloadPolynomial_le_fixed
      compactParserStateAtRowsZeroValuation Language.ORing.Rel.lt
      ![indexTerm, shortBinaryNumeralTerm stateCount] numericBound
      termCodeBound hindexVariables (by
        change
          (shortBinaryNumeralTerm stateCount :
            ValuationTerm).freeVariables ⊆ {0}
        rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
        simp) (by simp [compactParserStateAtRowsZeroValuation])
      hindexTermCode hstateCountCode
    simpa only [resource,
      compactParserStateAtRowsLtStructuralPayloadPolynomial] using hfixed
  refine ⟨proof, ?_⟩
  exact
    (compile_payloadLength_le_structuralPayloadBound certificate).trans
      ((compactParserStateAtRowsValuationLtCertificate_structuralPayloadBound_le_public
        indexTerm stateCount hindexVariables hindex).trans hpolynomial)

noncomputable def compactParserStateAtRowsEntryFullyUniformDirectFixedBound
    (table width value : Nat) (indexTerm : ValuationTerm)
    (numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hentry : CompactFixedWidthEntry table width
      (termValue compactParserStateAtRowsZeroValuation indexTerm) value)
    (hwidthValue : width <= numericBound)
    (hindexValue :
      termValue compactParserStateAtRowsZeroValuation indexTerm <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize :
      Nat.size (termValue compactParserStateAtRowsZeroValuation indexTerm) <=
        bitBound)
    (hvalueSize : Nat.size value <= bitBound) :
    ExplicitDirectFormulaBound compactParserStateAtRowsZeroValuation
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width) indexTerm
        (shortBinaryNumeralTerm value))
      (compactParserStateAtRowsUniformEntryResource indexTerm numericBound
        bitBound) := by
  let tableTerm := shortBinaryNumeralTerm table
  let widthTerm := shortBinaryNumeralTerm width
  let valueTerm := shortBinaryNumeralTerm value
  have hentryTerms : CompactFixedWidthEntry
      (termValue compactParserStateAtRowsZeroValuation tableTerm)
      (termValue compactParserStateAtRowsZeroValuation widthTerm)
      (termValue compactParserStateAtRowsZeroValuation indexTerm)
      (termValue compactParserStateAtRowsZeroValuation valueTerm) := by
    simpa only [tableTerm, widthTerm, valueTerm,
      termValue_shortBinaryNumeralTerm] using hentry
  let certificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      compactParserStateAtRowsZeroValuation tableTerm widthTerm indexTerm
      valueTerm hentryTerms
  let proof := certificate.compile
  have hcertificate :
      hybridFormulaStructuralPayloadBound certificate <=
        compactParserStateAtRowsUniformEntryResource indexTerm numericBound
          bitBound := by
    have huniform :=
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
        compactParserStateAtRowsZeroValuation table width value indexTerm
        numericBound bitBound hwidthValue hindexValue
        (by simp [compactParserStateAtRowsZeroValuation]) htableSize hwidthSize
        hindexSize hvalueSize hindexVariables hentry
    simpa only [certificate, tableTerm, widthTerm, valueTerm,
      compactParserStateAtRowsUniformEntryResource, hentryTerms] using
      huniform
  refine ⟨proof, ?_⟩
  exact
    (compile_payloadLength_le_structuralPayloadBound certificate).trans
      hcertificate

def directFourConjunctionGeneralPayloadEnvelope
    (syntaxResource resource1 resource2 resource3 resource4 : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope syntaxResource resource1
    (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource2
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource3
        resource4))

noncomputable def compileDirectFourConjunctionSingletonGeneralBound
    (valuation : Nat -> Nat)
    (formula1 formula2 formula3 formula4 : ValuationFormula)
    (resource1 resource2 resource3 resource4 syntaxResource
      numericBound : Nat)
    (bound1 : ExplicitDirectFormulaBound valuation formula1 resource1)
    (bound2 : ExplicitDirectFormulaBound valuation formula2 resource2)
    (bound3 : ExplicitDirectFormulaBound valuation formula3 resource3)
    (bound4 : ExplicitDirectFormulaBound valuation formula4 resource4)
    (hvariables1 : formula1.freeVariables ⊆ {0})
    (hvariables2 : formula2.freeVariables ⊆ {0})
    (hvariables3 : formula3.freeVariables ⊆ {0})
    (hvariables4 : formula4.freeVariables ⊆ {0})
    (hzero : valuation 0 <= numericBound)
    (hsyntax :
      valuationContextFormulaCodeSumEnvelope 1 numericBound
          (binaryTermCode (&0 : ValuationTerm)).length +
        resource1 + resource2 + resource3 + resource4 +
        3 * (binaryNatCode 4).length + 1 <= syntaxResource) :
    ExplicitDirectFormulaBound valuation
      (formula1 ⋏ (formula2 ⋏ (formula3 ⋏ formula4)))
      (directFourConjunctionGeneralPayloadEnvelope syntaxResource resource1
        resource2 resource3 resource4) := by
  let formula34 := formula3 ⋏ formula4
  let formula234 := formula2 ⋏ formula34
  let formula1234 := formula1 ⋏ formula234
  let resource34 :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource resource3 resource4
  let resource234 :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource resource2 resource34
  have hpositive : 1 <= syntaxResource := by omega
  have hcode1 :
      (binaryFormulaCode formula1).length <= resource1 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      bound1.proof).trans bound1.payloadLength_le
  have hcode2 :
      (binaryFormulaCode formula2).length <= resource2 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      bound2.proof).trans bound2.payloadLength_le
  have hcode3 :
      (binaryFormulaCode formula3).length <= resource3 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      bound3.proof).trans bound3.payloadLength_le
  have hcode4 :
      (binaryFormulaCode formula4).length <= resource4 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      bound4.proof).trans bound4.payloadLength_le
  have hcode34 :
      (binaryFormulaCode formula34).length <=
        resource3 + resource4 + (binaryNatCode 4).length := by
    dsimp only [formula34]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hcode234 :
      (binaryFormulaCode formula234).length <=
        resource2 + resource3 + resource4 +
          2 * (binaryNatCode 4).length := by
    dsimp only [formula234, formula34]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hcode1234 :
      (binaryFormulaCode formula1234).length <=
        resource1 + resource2 + resource3 + resource4 +
          3 * (binaryNatCode 4).length := by
    dsimp only [formula1234, formula234, formula34]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hvariables34 : formula34.freeVariables ⊆ {0} := by
    dsimp only [formula34]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hvariables3 hvariables4
  have hvariables234 : formula234.freeVariables ⊆ {0} := by
    dsimp only [formula234]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hvariables2 hvariables34
  have hvariables1234 : formula1234.freeVariables ⊆ {0} := by
    dsimp only [formula1234]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hvariables1 hvariables234
  have hcontext34 :
      formulaCodeSum
          (valuationContext formula34.freeVariables valuation) <=
        syntaxResource :=
    (compactParserValuationContextFormulaCodeSum_le_singleton valuation
      formula34 numericBound hvariables34 hzero).trans (by omega)
  have hcontext234 :
      formulaCodeSum
          (valuationContext formula234.freeVariables valuation) <=
        syntaxResource :=
    (compactParserValuationContextFormulaCodeSum_le_singleton valuation
      formula234 numericBound hvariables234 hzero).trans (by omega)
  have hcontext1234 :
      formulaCodeSum
          (valuationContext formula1234.freeVariables valuation) <=
        syntaxResource :=
    (compactParserValuationContextFormulaCodeSum_le_singleton valuation
      formula1234 numericBound hvariables1234 hzero).trans (by omega)
  have hcode1Syntax : (binaryFormulaCode formula1).length <= syntaxResource :=
    hcode1.trans (by omega)
  have hcode2Syntax : (binaryFormulaCode formula2).length <= syntaxResource :=
    hcode2.trans (by omega)
  have hcode3Syntax : (binaryFormulaCode formula3).length <= syntaxResource :=
    hcode3.trans (by omega)
  have hcode4Syntax : (binaryFormulaCode formula4).length <= syntaxResource :=
    hcode4.trans (by omega)
  have hcode34Syntax :
      (binaryFormulaCode formula34).length <= syntaxResource :=
    hcode34.trans (by omega)
  have hcode234Syntax :
      (binaryFormulaCode formula234).length <= syntaxResource :=
    hcode234.trans (by omega)
  have hcode1234Syntax :
      (binaryFormulaCode formula1234).length <= syntaxResource :=
    hcode1234.trans (by omega)
  let proof34 := compileDirectConjunction bound3.proof bound4.proof
  have hproof34Raw := compileDirectConjunction_payloadLength_le bound3.proof
    bound4.proof resource3 resource4 bound3.payloadLength_le
    bound4.payloadLength_le
  have henvelope34 :
      transparentHybridConjunctionPayloadEnvelope valuation formula3 formula4
          resource3 resource4 <= resource34 := by
    change hybridConjunctionStructuralPayloadEnvelope valuation formula3
        formula4 resource3 resource4 <= _
    exact hybridConjunctionStructuralPayloadEnvelope_le_general valuation
      formula3 formula4 resource3 resource4 syntaxResource hpositive
      hcontext34 hcode3Syntax hcode4Syntax hcode34Syntax
  have hproof34 : proof34.payloadLength <= resource34 :=
    hproof34Raw.trans henvelope34
  let proof234 := compileDirectConjunction bound2.proof proof34
  have hproof234Raw := compileDirectConjunction_payloadLength_le bound2.proof
    proof34 resource2 resource34 bound2.payloadLength_le hproof34
  have henvelope234 :
      transparentHybridConjunctionPayloadEnvelope valuation formula2 formula34
          resource2 resource34 <= resource234 := by
    change hybridConjunctionStructuralPayloadEnvelope valuation formula2
        formula34 resource2 resource34 <= _
    exact hybridConjunctionStructuralPayloadEnvelope_le_general valuation
      formula2 formula34 resource2 resource34 syntaxResource hpositive
      hcontext234 hcode2Syntax hcode34Syntax hcode234Syntax
  have hproof234 : proof234.payloadLength <= resource234 :=
    hproof234Raw.trans henvelope234
  let proof1234 := compileDirectConjunction bound1.proof proof234
  have hproof1234Raw := compileDirectConjunction_payloadLength_le bound1.proof
    proof234 resource1 resource234 bound1.payloadLength_le hproof234
  have henvelope1234 :
      transparentHybridConjunctionPayloadEnvelope valuation formula1 formula234
          resource1 resource234 <=
        directFourConjunctionGeneralPayloadEnvelope syntaxResource resource1
          resource2 resource3 resource4 := by
    change hybridConjunctionStructuralPayloadEnvelope valuation formula1
        formula234 resource1 resource234 <= _
    exact hybridConjunctionStructuralPayloadEnvelope_le_general valuation
      formula1 formula234 resource1 resource234 syntaxResource hpositive
      hcontext1234 hcode1Syntax hcode234Syntax hcode1234Syntax
  refine ⟨proof1234, ?_⟩
  exact hproof1234Raw.trans henvelope1234

noncomputable def
    compactUnifiedParserStateAtRowsAtValuationIndexFullyUniformDirectFixedBound
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hgraph : CompactUnifiedParserStateAtRows tokenTable width tokenCount
      stateBoundary stateCount
      (termValue compactParserStateAtRowsZeroValuation indexTerm)
      coordinates sizeWitness)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hcoordinatesValue :
      CompactUnifiedParserStateCoordinateValueBound coordinates numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hcoordinatesSize :
      CompactUnifiedParserStateCoordinateSizeBound coordinates bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound compactParserStateAtRowsZeroValuation
      (compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
        tokenCount stateBoundary stateCount indexTerm coordinates sizeWitness)
      (compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
        indexTerm numericBound bitBound) := by
  rcases hgraph with ⟨hindex, hstart, hfinish, hcore⟩
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let indexFormula : ValuationFormula :=
    “!!indexTerm < !!(shortBinaryNumeralTerm stateCount)”
  let startFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm stateBoundary)
    (shortBinaryNumeralTerm tokenCount) indexTerm
    (shortBinaryNumeralTerm coordinates.start)
  let finishFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm stateBoundary)
    (shortBinaryNumeralTerm tokenCount) nextIndexTerm
    (shortBinaryNumeralTerm coordinates.finish)
  let coreFormula := compactUnifiedParserStateCoreClosedFormula tokenTable
    width tokenCount coordinates.start coordinates.finish
    coordinates.tokensFinish coordinates.tasksFinish
    coordinates.tokensBoundary coordinates.tokensCount
    coordinates.tasksBoundary coordinates.tasksCount
    sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize
  let explicitFormula :=
    indexFormula ⋏ (startFormula ⋏ (finishFormula ⋏ coreFormula))
  let indexResource := compilePositiveRelationFixedPayloadPolynomial
    numericBound
    (compactParserStateAtRowsUniformTermCodeBound indexTerm bitBound)
  let startResource := compactParserStateAtRowsUniformStartEntryResource
    indexTerm numericBound bitBound
  let finishResource := compactParserStateAtRowsUniformFinishEntryResource
    indexTerm numericBound bitBound
  let coreResource :=
    compactUnifiedParserStateCoreFullyUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let syntaxResource :=
    compactParserStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
      indexTerm numericBound bitBound
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables_uniformRow,
      arithmeticOneTerm_freeVariables_uniformRow]
    simpa using hindexVariables
  have hindexValue :
      termValue compactParserStateAtRowsZeroValuation indexTerm <=
        numericBound :=
    (Nat.le_of_lt hindex).trans hstateCount
  have hnextIndexValue :
      termValue compactParserStateAtRowsZeroValuation nextIndexTerm <=
        numericBound := by
    have hstep :
        termValue compactParserStateAtRowsZeroValuation indexTerm + 1 <=
          stateCount := by
      omega
    simpa only [nextIndexTerm, termValue_arithmeticAdd_uniformRow,
      termValue_arithmeticOne_uniformRow] using hstep.trans hstateCount
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hindexSize :
      Nat.size
          (termValue compactParserStateAtRowsZeroValuation indexTerm) <=
        bitBound :=
    (Nat.size_le_size hindexValue).trans hnumericSize
  have hnextIndexSize :
      Nat.size
          (termValue compactParserStateAtRowsZeroValuation nextIndexTerm) <=
        bitBound :=
    (Nat.size_le_size hnextIndexValue).trans hnumericSize
  have hstartSize : Nat.size coordinates.start <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcoordinatesSize (0 : Fin 8)
  have hfinishSize : Nat.size coordinates.finish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcoordinatesSize (1 : Fin 8)
  have htokensCount : coordinates.tokensCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcoordinatesValue (5 : Fin 8)
  have htasksCount : coordinates.tasksCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcoordinatesValue (7 : Fin 8)
  have htokensBoundarySize :
      Nat.size coordinates.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcoordinatesSize (4 : Fin 8)
  have htasksBoundarySize :
      Nat.size coordinates.tasksBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcoordinatesSize (6 : Fin 8)
  let indexBound :=
    compactParserStateAtRowsIndexFullyUniformDirectFixedBound indexTerm
      stateCount numericBound bitBound hindexVariables hindex hstateCount
      hnumericSize
  let startBound :=
    compactParserStateAtRowsEntryFullyUniformDirectFixedBound stateBoundary
      tokenCount coordinates.start indexTerm numericBound bitBound
      hindexVariables hstart htokenCount hindexValue hstateBoundarySize
      htokenCountSize hindexSize hstartSize
  have hfinishAtTerm : CompactFixedWidthEntry stateBoundary tokenCount
      (termValue compactParserStateAtRowsZeroValuation nextIndexTerm)
      coordinates.finish := by
    simpa only [nextIndexTerm, termValue_arithmeticAdd_uniformRow,
      termValue_arithmeticOne_uniformRow] using hfinish
  let finishBound :=
    compactParserStateAtRowsEntryFullyUniformDirectFixedBound stateBoundary
      tokenCount coordinates.finish nextIndexTerm numericBound bitBound
      hnextIndexVariables hfinishAtTerm htokenCount hnextIndexValue
      hstateBoundarySize htokenCountSize hnextIndexSize hfinishSize
  let coreClosedBound :=
    compactUnifiedParserStateCoreFullyUniformDirectFixedBound tokenTable width
      tokenCount coordinates sizeWitness hcore numericBound bitBound hwidth
      htokenCount htokensCount htasksCount htokenTableSize
      htokensBoundarySize htasksBoundarySize hnumericSize
  have hcoreContext :
      (∅ : Finset ValuationFormula) =
        valuationContext coreFormula.freeVariables
          compactParserStateAtRowsZeroValuation := by
    dsimp only [coreFormula]
    rw [compactUnifiedParserStateCoreClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  let coreProof := CertifiedPAContextProof.castContext hcoreContext
    coreClosedBound.proof
  let coreBound : ExplicitDirectFormulaBound
      compactParserStateAtRowsZeroValuation coreFormula coreResource :=
    { proof := coreProof
      payloadLength_le := by
        dsimp only [coreProof]
        rw [CertifiedPAContextProof.castContext_payloadLength]
        exact coreClosedBound.payloadLength_le }
  have hindexFormulaVariables : indexFormula.freeVariables ⊆ {0} := by
    dsimp only [indexFormula]
    rw [LO.FirstOrder.Semiformula.Operator.lt_def]
    intro candidate hcandidate
    rw [LO.FirstOrder.Semiformula.freeVariables_rel] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact hindexVariables hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            change candidate ∈
              (shortBinaryNumeralTerm stateCount :
                ValuationTerm).freeVariables at hcoordinate
            rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at hcoordinate
            simp at hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  have hstartFormulaVariables : startFormula.freeVariables ⊆ {0} := by
    exact
      compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
        (shortBinaryNumeralTerm stateBoundary)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm coordinates.start)
        (shortBinaryNumeralTerm_freeVariables_eq_empty stateBoundary)
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
        hindexVariables
        (shortBinaryNumeralTerm_freeVariables_eq_empty coordinates.start)
  have hfinishFormulaVariables : finishFormula.freeVariables ⊆ {0} := by
    exact
      compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
        (shortBinaryNumeralTerm stateBoundary)
        (shortBinaryNumeralTerm tokenCount) nextIndexTerm
        (shortBinaryNumeralTerm coordinates.finish)
        (shortBinaryNumeralTerm_freeVariables_eq_empty stateBoundary)
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
        hnextIndexVariables
        (shortBinaryNumeralTerm_freeVariables_eq_empty coordinates.finish)
  have hcoreFormulaVariables : coreFormula.freeVariables ⊆ {0} := by
    dsimp only [coreFormula]
    rw [compactUnifiedParserStateCoreClosedFormula_freeVariables_eq_empty]
    simp
  let explicitBound :=
    compileDirectFourConjunctionSingletonGeneralBound
      compactParserStateAtRowsZeroValuation indexFormula startFormula
      finishFormula coreFormula indexResource startResource finishResource
      coreResource syntaxResource numericBound indexBound startBound
      finishBound coreBound hindexFormulaVariables hstartFormulaVariables
      hfinishFormulaVariables hcoreFormulaVariables
      (by simp [compactParserStateAtRowsZeroValuation])
      (by
        unfold syntaxResource
          compactParserStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
        dsimp only [indexResource, startResource, finishResource, coreResource]
        omega)
  have hformula :
      explicitFormula =
        compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
          tokenCount stateBoundary stateCount indexTerm coordinates
          sizeWitness := by
    exact
      (compactUnifiedParserStateAtRowsAtValuationIndexFormula_alignment
        tokenTable width tokenCount stateBoundary stateCount indexTerm
        coordinates sizeWitness).symm
  let proof := castValuationContextProof hformula explicitBound.proof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = explicitBound.proof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula
      explicitBound.proof]
  simpa only [
    compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial,
    directFourConjunctionGeneralPayloadEnvelope, syntaxResource,
    indexResource, startResource, finishResource, coreResource] using
    explicitBound.payloadLength_le

def directThreeConjunctionGeneralPayloadEnvelope
    (syntaxResource resource1 resource2 resource3 : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope syntaxResource resource1
    (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource2
      resource3)

noncomputable def compileDirectThreeConjunctionSingletonGeneralBound
    (valuation : Nat -> Nat)
    (formula1 formula2 formula3 : ValuationFormula)
    (resource1 resource2 resource3 syntaxResource numericBound : Nat)
    (bound1 : ExplicitDirectFormulaBound valuation formula1 resource1)
    (bound2 : ExplicitDirectFormulaBound valuation formula2 resource2)
    (bound3 : ExplicitDirectFormulaBound valuation formula3 resource3)
    (hvariables1 : formula1.freeVariables ⊆ {0})
    (hvariables2 : formula2.freeVariables ⊆ {0})
    (hvariables3 : formula3.freeVariables ⊆ {0})
    (hzero : valuation 0 <= numericBound)
    (hsyntax :
      valuationContextFormulaCodeSumEnvelope 1 numericBound
          (binaryTermCode (&0 : ValuationTerm)).length +
        resource1 + resource2 + resource3 +
        2 * (binaryNatCode 4).length + 1 <= syntaxResource) :
    ExplicitDirectFormulaBound valuation
      (formula1 ⋏ (formula2 ⋏ formula3))
      (directThreeConjunctionGeneralPayloadEnvelope syntaxResource resource1
        resource2 resource3) := by
  let formula23 := formula2 ⋏ formula3
  let formula123 := formula1 ⋏ formula23
  let resource23 :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource resource2 resource3
  have hpositive : 1 <= syntaxResource := by omega
  have hcode1 :
      (binaryFormulaCode formula1).length <= resource1 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      bound1.proof).trans bound1.payloadLength_le
  have hcode2 :
      (binaryFormulaCode formula2).length <= resource2 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      bound2.proof).trans bound2.payloadLength_le
  have hcode3 :
      (binaryFormulaCode formula3).length <= resource3 :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      bound3.proof).trans bound3.payloadLength_le
  have hcode23 :
      (binaryFormulaCode formula23).length <=
        resource2 + resource3 + (binaryNatCode 4).length := by
    dsimp only [formula23]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hcode123 :
      (binaryFormulaCode formula123).length <=
        resource1 + resource2 + resource3 +
          2 * (binaryNatCode 4).length := by
    dsimp only [formula123, formula23]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hvariables23 : formula23.freeVariables ⊆ {0} := by
    dsimp only [formula23]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hvariables2 hvariables3
  have hvariables123 : formula123.freeVariables ⊆ {0} := by
    dsimp only [formula123]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hvariables1 hvariables23
  have hcontext23 :
      formulaCodeSum
          (valuationContext formula23.freeVariables valuation) <=
        syntaxResource :=
    (compactParserValuationContextFormulaCodeSum_le_singleton valuation
      formula23 numericBound hvariables23 hzero).trans (by omega)
  have hcontext123 :
      formulaCodeSum
          (valuationContext formula123.freeVariables valuation) <=
        syntaxResource :=
    (compactParserValuationContextFormulaCodeSum_le_singleton valuation
      formula123 numericBound hvariables123 hzero).trans (by omega)
  have hcode1Syntax : (binaryFormulaCode formula1).length <= syntaxResource :=
    hcode1.trans (by omega)
  have hcode2Syntax : (binaryFormulaCode formula2).length <= syntaxResource :=
    hcode2.trans (by omega)
  have hcode3Syntax : (binaryFormulaCode formula3).length <= syntaxResource :=
    hcode3.trans (by omega)
  have hcode23Syntax :
      (binaryFormulaCode formula23).length <= syntaxResource :=
    hcode23.trans (by omega)
  have hcode123Syntax :
      (binaryFormulaCode formula123).length <= syntaxResource :=
    hcode123.trans (by omega)
  let proof23 := compileDirectConjunction bound2.proof bound3.proof
  have hproof23Raw := compileDirectConjunction_payloadLength_le bound2.proof
    bound3.proof resource2 resource3 bound2.payloadLength_le
    bound3.payloadLength_le
  have henvelope23 :
      transparentHybridConjunctionPayloadEnvelope valuation formula2 formula3
          resource2 resource3 <= resource23 := by
    change hybridConjunctionStructuralPayloadEnvelope valuation formula2
        formula3 resource2 resource3 <= _
    exact hybridConjunctionStructuralPayloadEnvelope_le_general valuation
      formula2 formula3 resource2 resource3 syntaxResource hpositive
      hcontext23 hcode2Syntax hcode3Syntax hcode23Syntax
  have hproof23 : proof23.payloadLength <= resource23 :=
    hproof23Raw.trans henvelope23
  let proof123 := compileDirectConjunction bound1.proof proof23
  have hproof123Raw := compileDirectConjunction_payloadLength_le bound1.proof
    proof23 resource1 resource23 bound1.payloadLength_le hproof23
  have henvelope123 :
      transparentHybridConjunctionPayloadEnvelope valuation formula1 formula23
          resource1 resource23 <=
        directThreeConjunctionGeneralPayloadEnvelope syntaxResource resource1
          resource2 resource3 := by
    change hybridConjunctionStructuralPayloadEnvelope valuation formula1
        formula23 resource1 resource23 <= _
    exact hybridConjunctionStructuralPayloadEnvelope_le_general valuation
      formula1 formula23 resource1 resource23 syntaxResource hpositive
      hcontext123 hcode1Syntax hcode23Syntax hcode123Syntax
  refine ⟨proof123, ?_⟩
  exact hproof123Raw.trans henvelope123

end FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
