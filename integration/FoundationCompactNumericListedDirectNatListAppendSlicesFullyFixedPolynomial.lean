import integration.FoundationCompactNumericListedDirectNatListAppendSlicesFormulaFixedBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-! # Fully fixed polynomial for the append-slices leaf -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 200000

namespace FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedPolynomial

open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesFormulaFixedBounds

def appendSlicesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (appendSlicesFullFormulaCodePolynomial bitBound + 1)
    (appendSlicesCountFixedPayloadPolynomial bitBound)
    (appendSlicesTokenSlicesFixedPayloadPolynomial numericBound bitBound)
    (appendSlicesTokenSlicesFixedPayloadPolynomial numericBound bitBound)

theorem appendSlicesHybridThreeConjunctionGeneralPayloadEnvelope_mono
    {syntaxResource
      resource1Small resource1Large
      resource2Small resource2Large
      resource3Small resource3Large : Nat}
    (h1 : resource1Small <= resource1Large)
    (h2 : resource2Small <= resource2Large)
    (h3 : resource3Small <= resource3Large) :
    hybridThreeConjunctionGeneralPayloadEnvelope syntaxResource resource1Small
        resource2Small resource3Small <=
      hybridThreeConjunctionGeneralPayloadEnvelope syntaxResource resource1Large
        resource2Large resource3Large := by
  unfold hybridThreeConjunctionGeneralPayloadEnvelope
    hybridConjunctionGeneralPayloadEnvelope
  omega

#print axioms appendSlicesHybridThreeConjunctionGeneralPayloadEnvelope_mono

end FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedPolynomial
