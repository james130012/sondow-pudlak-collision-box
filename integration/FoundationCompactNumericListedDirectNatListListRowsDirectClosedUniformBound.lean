import integration.FoundationCompactNumericListedDirectNatListListRowsDirectUniversalUniformBound

/-! # Closed direct proof for additive natural-list-list rows -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectNatListListRowsDirectClosedUniformBound

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsDirectUniversalUniformBound

noncomputable def compileCompactAdditiveNatListListRowsDirectUniformClosed
    (tokenTable width tokenCount boundaryTable count numericBound
      bitBound : Nat)
    (hrows : CompactAdditiveNatListListRowsWellFormed tokenTable width
      tokenCount boundaryTable count)
    (hcount : count <= numericBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      (compactAdditiveNatListListRowsClosedFormula tokenTable width tokenCount
        boundaryTable count) := by
  let raw := compileCompactAdditiveNatListListRowsDirectUniformUniversal
    tokenTable width tokenCount boundaryTable count numericBound bitBound hrows
    hcount hwidth htokenCount htableSize hboundarySize hnumericSize
  exact CertifiedPAContextProof.cast
    (compactAdditiveNatListListRowsClosedFormula_alignment tokenTable width
      tokenCount boundaryTable count).symm
    raw

theorem compileCompactAdditiveNatListListRowsDirectUniformClosed_payloadLength_le
    (tokenTable width tokenCount boundaryTable count numericBound
      bitBound : Nat)
    (hrows : CompactAdditiveNatListListRowsWellFormed tokenTable width
      tokenCount boundaryTable count)
    (hcount : count <= numericBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveNatListListRowsDirectUniformClosed tokenTable width
      tokenCount boundaryTable count numericBound bitBound hrows hcount hwidth
      htokenCount htableSize hboundarySize hnumericSize).payloadLength <=
      compactAdditiveNatListListRowsDirectUniformUniversalResource tokenTable
        width tokenCount boundaryTable count numericBound bitBound := by
  unfold compileCompactAdditiveNatListListRowsDirectUniformClosed
  rw [CertifiedPAContextProof.cast_payloadLength]
  exact
    compileCompactAdditiveNatListListRowsDirectUniformUniversal_payloadLength_le
      tokenTable width tokenCount boundaryTable count numericBound bitBound
      hrows hcount hwidth htokenCount htableSize hboundarySize hnumericSize

#print axioms compileCompactAdditiveNatListListRowsDirectUniformClosed
#print axioms
  compileCompactAdditiveNatListListRowsDirectUniformClosed_payloadLength_le

end FoundationCompactNumericListedDirectNatListListRowsDirectClosedUniformBound
