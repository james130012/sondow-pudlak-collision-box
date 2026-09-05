import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsCountFullyFixedBounds
import integration.FoundationCompactPAHybridFormulaStructuralPayloadTransport

/-! # Public fixed count-equality leaf for natural-list cons rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsCountCertificateFixedBound

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridFormulaStructuralPayloadTransport
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsCountFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds

theorem natListConsRowsZeroValuation_eq_taskConsRowsZeroValuation :
    FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation =
      FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation := by
  funext coordinate
  rfl

noncomputable def natListConsRowsCountEqualityCertificate
    (sourceCount targetCount : Nat)
    (hcount : targetCount = sourceCount + 1) :
    CheckedHybridValuationBoundedFormulaCertificate
      natListConsRowsTailUniversalZeroValuation
      “!!(shortBinaryNumeralTerm targetCount) =
        !!(shortBinaryNumeralTerm sourceCount) + 1” := by
  change CheckedHybridValuationBoundedFormulaCertificate
    FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount) + 1”
  exact natListConsRowsZeroValuation_eq_taskConsRowsZeroValuation ▸
    FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.countEqualityCertificate
      sourceCount targetCount hcount

theorem natListConsRowsCountEqualityCertificate_payload_le_fullyFixed
    (sourceCount targetCount bitBound : Nat)
    (hcount : targetCount = sourceCount + 1)
    (hsourceSize : Nat.size sourceCount <= bitBound)
    (htargetSize : Nat.size targetCount <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (natListConsRowsCountEqualityCertificate sourceCount targetCount
          hcount) <=
      taskConsCountFullyFixedPayloadPolynomial bitBound := by
  have hpublic := consCountEqualityCertificate_structuralPayloadBound_le_public
    sourceCount targetCount hcount
  have hfixed := taskConsCountPayloadPolynomial_le_fullyFixed sourceCount
    targetCount bitBound hsourceSize htargetSize
  unfold natListConsRowsCountEqualityCertificate
  change hybridFormulaStructuralPayloadBound
      (natListConsRowsZeroValuation_eq_taskConsRowsZeroValuation ▸
        FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.countEqualityCertificate
          sourceCount targetCount hcount) <= _
  have htransport := hybridFormulaStructuralPayloadBound_valuation_transport
    FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation
    FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation
    natListConsRowsZeroValuation_eq_taskConsRowsZeroValuation
    (“!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount) + 1” : ValuationFormula)
    (FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.countEqualityCertificate
      sourceCount targetCount hcount)
  exact (Nat.le_of_eq htransport).trans (hpublic.trans hfixed)

#print axioms natListConsRowsCountEqualityCertificate
#print axioms
  natListConsRowsCountEqualityCertificate_payload_le_fullyFixed

end FoundationCompactNumericListedDirectNatListConsRowsCountCertificateFixedBound
