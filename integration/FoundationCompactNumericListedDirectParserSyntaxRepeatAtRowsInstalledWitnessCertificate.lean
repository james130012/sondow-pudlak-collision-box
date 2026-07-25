import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreCertificate
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-! # Installed exact two-witness certificate for Repeat task rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsInstalledWitnessCertificate

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

noncomputable def repeatAtRowsInstalledWitnessCertificateOfGraph
    (tokenTable width tokenCount boundaryTable count index kind binderArity
      repeatCount : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hindexValue : termValue atRowsZeroValuation indexTerm = index)
    (hkindValue : forall valuation, termValue valuation kindTerm = kind)
    (hbinderValue :
      forall valuation, termValue valuation binderArityTerm = binderArity)
    (hrepeatValue :
      forall valuation, termValue valuation repeatCountTerm = repeatCount)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index kind binderArity repeatCount) :=
  let left := Classical.choose hgraph.2
  let leftData := Classical.choose_spec hgraph.2
  let right := Classical.choose leftData.2
  let rightData := Classical.choose_spec leftData.2
  let values : Fin 2 -> Nat := ![right, left]
  let body :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable width
      tokenCount boundaryTable indexTerm kindTerm binderArityTerm repeatCountTerm
  buildExplicitBoundedWitnessHybridCertificate tokenCount body values (by
    intro coordinate
    fin_cases coordinate
    · exact rightData.1
    · exact leftData.1)
    (repeatAtRowsTerminalCertificateOfGraph tokenTable width tokenCount
      boundaryTable count index kind binderArity repeatCount indexTerm kindTerm
      binderArityTerm repeatCountTerm hindexValue hkindValue hbinderValue
      hrepeatValue hgraph)

end FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsInstalledWitnessCertificate
