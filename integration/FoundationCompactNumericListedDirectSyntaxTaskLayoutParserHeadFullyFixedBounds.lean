import integration.FoundationCompactNumericListedDirectNativeNumeralTermCompatibility

/-!
# Fully fixed layout certificate for the parser formula-task head

This is the exact `native 1 / short binder / native 0` syntax used by the
clean parser certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskLayoutParserHeadFullyFixedBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutBinaryInstalledFullyFixedBounds
open FoundationCompactNumericListedDirectNativeNumeralTermCompatibility

theorem
    parserHeadTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount start finish binderArity numericBound
      bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hlayout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      start finish (1, binderArity, 0)) :
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
          tokenTable width tokenCount start finish 1 binderArity 0
          (fixedNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
          (fixedNumeralTerm 0)
          (fun valuation => by simp [fixedNumeralTerm, termValue])
          (termValue_shortBinaryNumeralTerm · binderArity)
          (fun valuation => by simp [fixedNumeralTerm, termValue]) hlayout) <=
      binaryTaskLayoutInstalledPayloadEnvelope numericBound bitBound := by
  exact
    binaryTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount start finish binderArity numericBound bitBound
      hwidthValue htokenCountValue htableSize hwidthSize htokenCountSize
      hstartSize hfinishSize hbinderSize hlayout

end FoundationCompactNumericListedDirectSyntaxTaskLayoutParserHeadFullyFixedBounds
