import integration.FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedBounds

/-! # Term-code fixed parser-state leaves at an arbitrary valuation -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedValuationLeaves

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTermCodeBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedBounds

noncomputable def compactParserStateAtRowsIndexTermCodeFixedBoundAtValuation
    (valuation : Nat -> Nat)
    (indexTerm : ValuationTerm) (stateCount termCodeBound numericBound
      bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound)
    (hindex : termValue valuation indexTerm < stateCount)
    (hstateCount : stateCount <= numericBound)
    (hzero : valuation 0 <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound valuation
      “!!indexTerm < !!(shortBinaryNumeralTerm stateCount)”
      (compilePositiveRelationFixedPayloadPolynomial numericBound
        (compactParserStateAtRowsTermCodeFixedRelationTermBound termCodeBound
          bitBound)) := by
  let relationTermBound :=
    compactParserStateAtRowsTermCodeFixedRelationTermBound termCodeBound bitBound
  let args : Fin 2 -> ValuationTerm :=
    ![indexTerm, shortBinaryNumeralTerm stateCount]
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic valuation
      Language.ORing.Rel.lt args (by
        change termValue valuation indexTerm <
          termValue valuation (shortBinaryNumeralTerm stateCount)
        simpa only [termValue_shortBinaryNumeralTerm] using hindex)
  let certificate :=
    CheckedHybridValuationBoundedFormulaCertificate.cast
      (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct
  let proof := certificate.compile
  have hstateCountSize : Nat.size stateCount <= bitBound :=
    (Nat.size_le_size hstateCount).trans hnumericSize
  have hindexCode' : (binaryTermCode indexTerm).length <= relationTermBound :=
    hindexCode.trans (by
      unfold relationTermBound
        compactParserStateAtRowsTermCodeFixedRelationTermBound
      omega)
  have hstateCountCode :
      (binaryTermCode
        (shortBinaryNumeralTerm stateCount : ValuationTerm)).length <=
        relationTermBound := by
    have hcode := binaryNumeralTerm_code_length_le_envelope stateCount bitBound
      hstateCountSize
    exact hcode.trans (by
      unfold relationTermBound
        compactParserStateAtRowsTermCodeFixedRelationTermBound
      omega)
  have hrightVariables :
      (shortBinaryNumeralTerm stateCount : ValuationTerm).freeVariables ⊆
        {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic :
      hybridFormulaStructuralPayloadBound certificate <=
        compilePositiveRelationPayloadPolynomial valuation
          Language.ORing.Rel.lt args := by
    have hraw := compilePositiveRelationPayloadResource_le_publicPolynomial
      valuation Language.ORing.Rel.lt args hindexVariables hrightVariables
    simpa only [certificate, direct, args,
      hybridFormulaStructuralPayloadBound] using hraw
  have hfixed :
      compilePositiveRelationPayloadPolynomial valuation
          Language.ORing.Rel.lt args <=
        compilePositiveRelationFixedPayloadPolynomial numericBound
          relationTermBound := by
    exact compilePositiveRelationPayloadPolynomial_le_fixed
      valuation Language.ORing.Rel.lt
      args numericBound relationTermBound hindexVariables hrightVariables
      hzero hindexCode' hstateCountCode
  refine ⟨proof, ?_⟩
  exact
    (compile_payloadLength_le_structuralPayloadBound certificate).trans
      (hpublic.trans hfixed)

noncomputable def compactParserStateAtRowsEntryTermCodeFixedBoundAtValuation
    (valuation : Nat -> Nat)
    (table width value : Nat) (indexTerm : ValuationTerm)
    (termCodeBound numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound)
    (hentry : CompactFixedWidthEntry table width
      (termValue valuation indexTerm) value)
    (hwidthValue : width <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hzero : valuation 0 <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound) :
    ExplicitDirectFormulaBound valuation
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width) indexTerm
        (shortBinaryNumeralTerm value))
      (compactParserStateAtRowsTermCodeFixedEntryResource termCodeBound
        numericBound bitBound) := by
  let tableTerm := shortBinaryNumeralTerm table
  let widthTerm := shortBinaryNumeralTerm width
  let valueTerm := shortBinaryNumeralTerm value
  have hentryTerms : CompactFixedWidthEntry
      (termValue valuation tableTerm)
      (termValue valuation widthTerm)
      (termValue valuation indexTerm)
      (termValue valuation valueTerm) := by
    simpa only [tableTerm, widthTerm, valueTerm,
      termValue_shortBinaryNumeralTerm] using hentry
  let certificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      tableTerm widthTerm indexTerm valueTerm hentryTerms
  let proof := certificate.compile
  have hcertificate :
      hybridFormulaStructuralPayloadBound certificate <=
        compactParserStateAtRowsTermCodeFixedEntryResource termCodeBound
          numericBound bitBound := by
    have huniform :=
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_termCodeBound
        valuation table width value indexTerm termCodeBound numericBound
        bitBound hwidthValue hindexValue hzero htableSize hwidthSize hindexSize
        hvalueSize hindexCode hindexVariables hentry
    simpa only [certificate, tableTerm, widthTerm, valueTerm, hentryTerms,
      compactParserStateAtRowsTermCodeFixedEntryResource] using huniform
  refine ⟨proof, ?_⟩
  exact (compile_payloadLength_le_structuralPayloadBound certificate).trans
    hcertificate

#print axioms compactParserStateAtRowsIndexTermCodeFixedBoundAtValuation
#print axioms compactParserStateAtRowsEntryTermCodeFixedBoundAtValuation

end FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedValuationLeaves
