import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds

open LO FirstOrder

namespace FoundationCompactPAHybridBranchesLeafResourceMonotonicity

open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds

theorem hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf
    (totalBound : Nat) (outerVariables : Finset Nat)
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    {small large : Nat} (hresource : small <= large) :
    forall bound,
      hybridBranchesUniformStructuralPayloadEnvelope totalBound outerVariables
          valuation body small bound <=
        hybridBranchesUniformStructuralPayloadEnvelope totalBound
          outerVariables valuation body large bound
  | 0 => by rfl
  | bound + 1 => by
      simp only [hybridBranchesUniformStructuralPayloadEnvelope]
      have hinduction :=
        hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf totalBound
          outerVariables valuation body hresource bound
      omega

#print axioms hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf

end FoundationCompactPAHybridBranchesLeafResourceMonotonicity
