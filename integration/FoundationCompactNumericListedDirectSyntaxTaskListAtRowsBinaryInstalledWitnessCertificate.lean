import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedTerminalFullyFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Installed binary syntax-task row witness certificate

This module isolates elaboration of the dependent two-witness certificate.
Quantitative bounds are proved downstream against the compiled definition.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryInstalledWitnessCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate

noncomputable def syntaxTaskAtRowsBinaryInstalledWitnessCertificateOfGraph
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index 1 binderArity 0) :=
  let left := Classical.choose hgraph.2
  let leftData := Classical.choose_spec hgraph.2
  let right := Classical.choose leftData.2
  let rightData := Classical.choose_spec leftData.2
  let indexTerm := nativeNumeralTerm index
  let values : Fin 2 -> Nat := ![right, left]
  let body :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
      width tokenCount boundaryTable indexTerm (nativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0)
  buildExplicitBoundedWitnessHybridCertificate tokenCount body values (by
    intro coordinate
    fin_cases coordinate
    · exact rightData.1
    · exact leftData.1)
    (syntaxTaskAtRowsBinaryTerminalCertificateOfGraph tokenTable width
      tokenCount boundaryTable count index binderArity hgraph)

end FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryInstalledWitnessCertificate
