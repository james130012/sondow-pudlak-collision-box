/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.ProjectionBridge

/-!
# Gamma Irrationality Input Core

Shared top-level input records for the Euler-Mascheroni irrationality routes.
-/

open Filter MiniHilbert

structure GammaIrrationalityMainInputs where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  hilbert_soundness : HilbertProofLengthSoundnessBridge

structure GammaIrrationalityVerifiedMainInputs where
  sondow_forward : SondowForwardInputs
  collapse_verification : SondowCollapseVerificationBridgePackage
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  hilbert_soundness : HilbertProofLengthSoundnessBridge

def GammaIrrationalityVerifiedMainInputs.toMainInputs
    (h : GammaIrrationalityVerifiedMainInputs) :
    GammaIrrationalityMainInputs where
  sondow_forward := h.sondow_forward
  concrete_verification :=
    h.collapse_verification.toReflectionGraftConcreteVerification
  partial_payload_truth :=
    h.collapse_verification.toPayloadSpec.toPayloadTruth
  partial_payload_reading :=
    h.collapse_verification.toPayloadSpec.toIntendedReading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  hilbert_soundness := h.hilbert_soundness

structure GammaIrrationalityExactProjectionInputs where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  hilbert_alignment : HilbertProjectionCodeAlignment
  hilbert_exact_projection :
    HilbertProofLengthExactProjectionRealization hilbert_alignment

def GammaIrrationalityExactProjectionInputs.toMainInputs
    (h : GammaIrrationalityExactProjectionInputs) :
    GammaIrrationalityMainInputs where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  hilbert_soundness := h.hilbert_exact_projection.toBridge

structure GammaIrrationalityVerifiedExactProjectionInputs where
  sondow_forward : SondowForwardInputs
  collapse_verification : SondowCollapseVerificationBridgePackage
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  hilbert_alignment : HilbertProjectionCodeAlignment
  hilbert_exact_projection :
    HilbertProofLengthExactProjectionRealization hilbert_alignment

def GammaIrrationalityVerifiedExactProjectionInputs.toExactProjectionInputs
    (h : GammaIrrationalityVerifiedExactProjectionInputs) :
    GammaIrrationalityExactProjectionInputs where
  sondow_forward := h.sondow_forward
  concrete_verification :=
    h.collapse_verification.toReflectionGraftConcreteVerification
  partial_payload_truth :=
    h.collapse_verification.toPayloadSpec.toPayloadTruth
  partial_payload_reading :=
    h.collapse_verification.toPayloadSpec.toIntendedReading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  hilbert_alignment := h.hilbert_alignment
  hilbert_exact_projection := h.hilbert_exact_projection

def GammaIrrationalityVerifiedExactProjectionInputs.toMainInputs
    (h : GammaIrrationalityVerifiedExactProjectionInputs) :
    GammaIrrationalityMainInputs :=
  h.toExactProjectionInputs.toMainInputs

structure GammaIrrationalityTargetExactProjectionInputs where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  hilbert_alignment : HilbertProjectionCodeAlignment
  hilbert_target_exact_projection :
    HilbertProofLengthTargetExactProjectionRealization hilbert_alignment

def GammaIrrationalityTargetExactProjectionInputs.toMainInputs
    (h : GammaIrrationalityTargetExactProjectionInputs) :
    GammaIrrationalityMainInputs where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  hilbert_soundness := h.hilbert_target_exact_projection.toBridge

structure GammaIrrationalityVerifiedTargetExactProjectionInputs where
  sondow_forward : SondowForwardInputs
  collapse_verification : SondowCollapseVerificationBridgePackage
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  hilbert_alignment : HilbertProjectionCodeAlignment
  hilbert_target_exact_projection :
    HilbertProofLengthTargetExactProjectionRealization hilbert_alignment

def GammaIrrationalityVerifiedTargetExactProjectionInputs.toTargetExactProjectionInputs
    (h : GammaIrrationalityVerifiedTargetExactProjectionInputs) :
    GammaIrrationalityTargetExactProjectionInputs where
  sondow_forward := h.sondow_forward
  concrete_verification :=
    h.collapse_verification.toReflectionGraftConcreteVerification
  partial_payload_truth :=
    h.collapse_verification.toPayloadSpec.toPayloadTruth
  partial_payload_reading :=
    h.collapse_verification.toPayloadSpec.toIntendedReading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  hilbert_alignment := h.hilbert_alignment
  hilbert_target_exact_projection := h.hilbert_target_exact_projection

def GammaIrrationalityVerifiedTargetExactProjectionInputs.toMainInputs
    (h : GammaIrrationalityVerifiedTargetExactProjectionInputs) :
    GammaIrrationalityMainInputs :=
  h.toTargetExactProjectionInputs.toMainInputs
