import integration.FoundationCompactNumericListedDirectParserSyntaxInvalidPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds

/-! # Fixed native-tag disequality resource for the invalid parser branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxInvalidAtomicFixedBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds

private abbrev invalidZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate.zeroValuation

theorem fixedNeCertificate_structuralPayloadBound_le_fullyFixed
    (value expected bitBound : Nat)
    (hne : value ≠ expected)
    (hvalueSize : Nat.size value <= bitBound)
    (hexpected : expected <= 7) :
    hybridFormulaStructuralPayloadBound
        (fixedNeCertificate value expected hne) <=
      parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound := by
  have hnative :=
    nativeNeCertificate_structuralPayloadBound_le_fixed value expected bitBound
      hne hvalueSize hexpected
  change compileNegativeRelationPayloadResource invalidZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] <= _
  exact hnative

#print axioms fixedNeCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxInvalidAtomicFixedBounds
