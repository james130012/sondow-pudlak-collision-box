import integration.SondowProjectMonth11Month12HardResidualElimination

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth11Month12ActualTransportExactness

open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth9Month10ProofLengthGapFrontier
open SondowProjectMonth9Month10Month11ExactProofGapHandoff
open SondowProjectMonth11Month12HardResidualElimination

/-- Actual proof-length transport only.  This file deliberately does not state
or use any equality between checked proof-code length and the project scale. -/
theorem your_actual_transport_theorem
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker) :
    ActualProofLengthGapTransportBlocker checker where
  checked_eq_actual := by
    intro n
    simpa [actualProofLengthMeasured,
      month9_month10_checkedProofCodeMeasured,
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt]
      using (family.proof_length_eq_minProofCodeSizeAt n).symm

end SondowProjectMonth11Month12ActualTransportExactness
end SondowMainCheckedCodeBridge
