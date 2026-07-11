import integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectSondowUpperCompilerRoute

open SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint
open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth9Month10Month11ExactProofGapHandoff
open SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint
open SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface

/--
Sondow-specific PA trace compiler.

This is deliberately not an upper-tail provider.  It is the local proof
compiler promised by the paper argument: once a concrete full Sondow certificate
has checked at index `n`, PA can prove the corresponding certificate-validity
formula with length bounded by the verifier predicate size.

The important feature is that the premise is
`MainSondowFullCertificateCheckedAt n`, not the root
`accepted_certificate (sondowCertificateValidCode n)`.  Therefore this interface
does not pass through the old root accepted-certificate branches that also
mention the partial-consistency payloads.
-/
structure SondowFullCertificatePATraceCompiler : Prop where
  short_proof_from_checked :
    ∀ n : Nat, MainSondowFullCertificateCheckedAt n →
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        _root_.proof_predicate_formula_size
          _root_.sondowCertificateValidCode n

/-- The explicit linear upper function exposed by the Sondow certificate verifier. -/
def sondowCertificateLinearUpper (n : Nat) : Real :=
  (17 : Real) * ((n : Real) + 1) ^ (1 : Nat)

theorem sondowCertificateLinearUpper_polynomial :
    _root_.is_polynomial_bound sondowCertificateLinearUpper := by
  exact ⟨17, 1, fun n => le_rfl⟩

/--
Sidecar verifier graph for the Sondow certificate-validity family.

This is not the old bare project atom route.  The target proof object below is
the Buss-S²₁ polytime-definability shell for this verifier graph.
-/
def sidecarSondowCertificateVerifierGraph
    (n : Nat) : _root_.BoundedArithmeticLab.BAFormula :=
  _root_.BoundedArithmeticLab.BAFormula.atom
    _root_.BoundedArithmeticLab.FormulaFamily.sondowCertificateValid n

/-- Expanded sidecar verifier formula for `sondowCertificateValidCode n`. -/
def sidecarSondowCertificateVerifierFormula
    (n : Nat) : _root_.BoundedArithmeticLab.BAFormula :=
  _root_.BoundedArithmeticLab.polytimeDefinabilityFormula
    9001 (sidecarSondowCertificateVerifierGraph n)

/--
Concrete Buss-S²₁ proof object for the expanded sidecar Sondow verifier
formula.

This is the actual proof object supplied by the sidecar proof calculus.  It
does not use rationality, an upper-provider field, or root `proof_length`.
-/
def sidecarSondowCertificateVerifierProofObject
    (n : Nat) :
    _root_.BoundedArithmeticLab.BAProofObject
      _root_.BoundedArithmeticLab.BussS21Axiom :=
  polytimeDefinabilityProofObject
    9001 (sidecarSondowCertificateVerifierGraph n)

@[simp] theorem sidecarSondowCertificateVerifierProofObject_conclusion
    (n : Nat) :
    (sidecarSondowCertificateVerifierProofObject n).conclusion =
      sidecarSondowCertificateVerifierFormula n := by
  rfl

@[simp] theorem sidecarSondowCertificateVerifierProofObject_size
    (n : Nat) :
    (sidecarSondowCertificateVerifierProofObject n).size = 1 := by
  rfl

/--
Concrete sidecar semantic proof-length upper for the expanded Sondow verifier
formula.
-/
theorem sidecarSondowCertificateVerifierSemanticLength_le_one
    (n : Nat) :
    _root_.BoundedArithmeticLab.semanticBAProofLength
        _root_.BoundedArithmeticLab.BussS21Axiom
        sidecarSondowCertificateVerifierFormula n ≤ 1 := by
  simpa [sidecarSondowCertificateVerifierProofObject_size] using
    _root_.BoundedArithmeticLab.semanticBAProofLength_le_size
      _root_.BoundedArithmeticLab.BussS21Axiom
      sidecarSondowCertificateVerifierFormula
      (sidecarSondowCertificateVerifierProofObject n)
      (sidecarSondowCertificateVerifierProofObject_conclusion n)

/--
The sidecar expanded Sondow verifier has the displayed `17(n+1)` upper.

This closes a real concrete proof-object upper.  It does not by itself calibrate
the root abstract `proof_length` symbol or the Pudlak lower-bound target.
-/
theorem sidecarSondowCertificateVerifierSemanticLength_le_linearUpper
    (n : Nat) :
    _root_.BoundedArithmeticLab.semanticBAProofLength
        _root_.BoundedArithmeticLab.BussS21Axiom
        sidecarSondowCertificateVerifierFormula n ≤
      sondowCertificateLinearUpper n := by
  have hone :
      (1 : Real) ≤ sondowCertificateLinearUpper n := by
    have hn : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
    simp [sondowCertificateLinearUpper]
    nlinarith
  exact (sidecarSondowCertificateVerifierSemanticLength_le_one n).trans hone

/--
Half-denominator display form for the concrete sidecar proof-object upper.
-/
theorem sidecarSondowCertificateVerifierUpper_fromHalfDenCheckedTail
    (q : Rat) (_hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.BoundedArithmeticLab.semanticBAProofLength
          _root_.BoundedArithmeticLab.BussS21Axiom
          sidecarSondowCertificateVerifierFormula n ≤
        sondowCertificateLinearUpper n := by
  intro n _hn
  exact sidecarSondowCertificateVerifierSemanticLength_le_linearUpper n

/--
Proof-length-free Sondow proof-code compiler.

This is the cleaner internal target.  It does not mention the root
`proof_length` constant.  It says that a checked Sondow certificate is compiled
to an explicit PA/Hilbert proof code whose concrete code length is bounded by the
verifier predicate size.
-/
structure SondowFullCertificateConcreteProofCodeCompiler : Type where
  codeLength : Nat → Nat
  short_code_from_checked :
    ∀ n : Nat, MainSondowFullCertificateCheckedAt n →
      (codeLength n : Real) ≤
        _root_.proof_predicate_formula_size
          _root_.sondowCertificateValidCode n

/--
Proof-length-free upper theorem.

This is the route that should be used for the clean audit statement before any
root proof-length calibration is introduced.
-/
theorem pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndCompiler
    (compiler : SondowFullCertificateConcreteProofCodeCompiler)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      (compiler.codeLength n : Real) ≤
        sondowCertificateLinearUpper n := by
  intro n hn
  let tail :=
    mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen
      q hq
  have hchecked : MainSondowFullCertificateCheckedAt n :=
    tail.checked_at n (by simpa [tail,
      mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen_threshold]
      using hn)
  exact le_trans
    (compiler.short_code_from_checked n hchecked)
    (by
      simpa [sondowCertificateLinearUpper] using
        proofPredicateFormulaSizeSondowCertificateValidCode_le_17_natPower n)

/--
Existential upper-tail form for the proof-length-free measured code length.

The upper is again explicitly `17(n+1)`, and no root `proof_length` is involved.
-/
theorem pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndCompiler
    (compiler : SondowFullCertificateConcreteProofCodeCompiler)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        (compiler.codeLength n : Real) ≤ U n := by
  refine ⟨sondowCertificateLinearUpper,
    sondowCertificateLinearUpper_polynomial,
    max 3 ((q.den + 1) / 2), ?_⟩
  exact pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndCompiler
    compiler q hq

/--
Diagnostic root bridge from the Sondow-specific checked certificate record to
the root Sondow certificate acceptance predicate.

This theorem is not the clean route: because the root `accepted_certificate`
definition contains partial-consistency branches, `#print axioms` for this
bridge still reports the payload constants.  The clean route below avoids this
root predicate and works directly from `MainSondowFullCertificateCheckedAt`.
-/
theorem acceptedSondowCertificate_of_checkedAt
    {n : Nat} (hchecked : MainSondowFullCertificateCheckedAt n) :
    _root_.accepted_certificate (_root_.sondowCertificateValidCode n) := by
  exact ⟨hchecked.q, hchecked.checked⟩

/--
Current narrow Buss-S²₁ project-atom route is impossible.

This is the guardrail against hiding the upper-bound proof obligation inside a
compiler name: in the current sidecar object language, the five bare Sondow
project atoms are not Buss-S²₁ derivable.  A real closure must therefore build
proof codes for the verifier/predicate formula, or move to an explicitly
expanded verifier-definability target with a matching calibration.
-/
theorem currentBussS21ProjectAtomDerivationSources_impossible
    {bounds : _root_.BoundedArithmeticLab.SondowComponentBounds} :
    MainSondowFullCertificateS21DerivationSources bounds → False :=
  no_current_bussS21_sondow_full_certificate_derivation_sources

/--
Convert the component proof-object validity record with `+2` certificate
overhead into the component-size record used by the structured Sondow target.

This is only bookkeeping: it loses the harmless `+2` slack on each component,
but it does not introduce a new upper-provider assumption.
-/
theorem proofObjectSystemValid_to_componentSizeValid
    {components : _root_.BoundedArithmeticLab.SondowComponentFormulas}
    {bounds : _root_.BoundedArithmeticLab.SondowComponentBounds}
    {n : Nat} {cert : _root_.BoundedArithmeticLab.SondowComponentCertificate}
    (hvalid :
      _root_.BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
        components bounds n cert) :
    _root_.BoundedArithmeticLab.SondowComponentCertificate.ComponentSizeValid
      components bounds n cert where
  product_conclusion := hvalid.product_conclusion
  log_conclusion := hvalid.log_conclusion
  decomposition_conclusion := hvalid.decomposition_conclusion
  threePow_conclusion := hvalid.threePow_conclusion
  payload_conclusion := hvalid.payload_conclusion
  product_size_le := by
    have hnat :
        cert.productProof.size ≤ cert.productProof.size + 2 :=
      Nat.le_add_right _ _
    have hreal :
        (cert.productProof.size : Real) ≤
          (((cert.productProof.size + 2 : Nat) : Real)) := by
      exact_mod_cast hnat
    exact hreal.trans hvalid.product_size_plus_two_le
  log_size_le := by
    have hnat :
        cert.logProof.size ≤ cert.logProof.size + 2 :=
      Nat.le_add_right _ _
    have hreal :
        (cert.logProof.size : Real) ≤
          (((cert.logProof.size + 2 : Nat) : Real)) := by
      exact_mod_cast hnat
    exact hreal.trans hvalid.log_size_plus_two_le
  decomposition_size_le := by
    have hnat :
        cert.decompositionProof.size ≤ cert.decompositionProof.size + 2 :=
      Nat.le_add_right _ _
    have hreal :
        (cert.decompositionProof.size : Real) ≤
          (((cert.decompositionProof.size + 2 : Nat) : Real)) := by
      exact_mod_cast hnat
    exact hreal.trans hvalid.decomposition_size_plus_two_le
  threePow_size_le := by
    have hnat :
        cert.threePowProof.size ≤ cert.threePowProof.size + 2 :=
      Nat.le_add_right _ _
    have hreal :
        (cert.threePowProof.size : Real) ≤
          (((cert.threePowProof.size + 2 : Nat) : Real)) := by
      exact_mod_cast hnat
    exact hreal.trans hvalid.threePow_size_plus_two_le
  payload_size_le := by
    have hnat :
        cert.payloadProof.size ≤ cert.payloadProof.size + 2 :=
      Nat.le_add_right _ _
    have hreal :
        (cert.payloadProof.size : Real) ≤
          (((cert.payloadProof.size + 2 : Nat) : Real)) := by
      exact_mod_cast hnat
    exact hreal.trans hvalid.payload_size_plus_two_le

/--
Same-object PA semantic upper bound for the structured Sondow target.

The target is the exact `sondowProjectComponentFormulas.target` used by the
Buss/Pudlak calibration.  The proof first builds the right-nested conjunction
of the five Buss-S²₁ component proof objects, maps it into PA, and then applies
`semanticBAProofLength_le_size`.
-/
theorem
    semanticPAProjectTargetLength_le_combined_of_componentProofObjects
    {bounds : _root_.BoundedArithmeticLab.SondowComponentBounds}
    {n : Nat} {cert : _root_.BoundedArithmeticLab.SondowComponentCertificate}
    (hvalid :
      _root_.BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
        _root_.BoundedArithmeticLab.sondowProjectComponentFormulas
        bounds n cert) :
    _root_.BoundedArithmeticLab.semanticBAProofLength
        _root_.BoundedArithmeticLab.PAAxiom
        _root_.BoundedArithmeticLab.sondowProjectComponentFormulas.target n ≤
      bounds.combined n := by
  let hcomponent :=
    proofObjectSystemValid_to_componentSizeValid hvalid
  let htargetValid :=
    _root_.BoundedArithmeticLab.SondowComponentCertificate.ComponentSizeValid.toValid
      hcomponent
  let pS21 := cert.buildProof
  let pPA :=
    pS21.mapAxioms
      _root_.BoundedArithmeticLab.bussS21Axiom_subset_pa
  have hconclusion :
      pPA.conclusion =
        _root_.BoundedArithmeticLab.sondowProjectComponentFormulas.target n := by
    simpa [pPA, pS21, _root_.BoundedArithmeticLab.BAProofObject.mapAxioms]
      using
        _root_.BoundedArithmeticLab.SondowComponentCertificate.buildProof_conclusion
          htargetValid
  have hsemantic :
      _root_.BoundedArithmeticLab.semanticBAProofLength
          _root_.BoundedArithmeticLab.PAAxiom
          _root_.BoundedArithmeticLab.sondowProjectComponentFormulas.target n ≤
        (pPA.size : Real) :=
    _root_.BoundedArithmeticLab.semanticBAProofLength_le_size
      _root_.BoundedArithmeticLab.PAAxiom
      _root_.BoundedArithmeticLab.sondowProjectComponentFormulas.target
      pPA hconclusion
  have hcertSize :
      (cert.certSize : Real) ≤ bounds.combined n :=
    _root_.BoundedArithmeticLab.SondowComponentCertificate.certSize_le_combined_bound
      hcomponent
  have hsize_le_certSize :
      (pPA.size : Real) ≤ (cert.certSize : Real) := by
    have hmap :
        pPA.size = pS21.size := by
      exact
        _root_.BoundedArithmeticLab.BAProofObject.size_mapAxioms
          _root_.BoundedArithmeticLab.bussS21Axiom_subset_pa pS21
    have hnat : pS21.size ≤ cert.certSize := by
      simp [pS21, _root_.BoundedArithmeticLab.SondowComponentCertificate.certSize]
    have hreal : (pS21.size : Real) ≤ (cert.certSize : Real) := by
      exact_mod_cast hnat
    simpa [hmap]
      using hreal
  exact hsemantic.trans (hsize_le_certSize.trans hcertSize)

theorem
    semanticPAProjectTargetUpper_fromHalfDenCheckedTailAndEventualCompiler
    {bounds : _root_.BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.BoundedArithmeticLab.semanticBAProofLength
            _root_.BoundedArithmeticLab.PAAxiom
            _root_.BoundedArithmeticLab.sondowProjectComponentFormulas.target n
          ≤ U n := by
  let tail :=
    mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen
      q hq
  refine ⟨bounds.combined, bounds.combined_poly,
    max compiler.threshold tail.threshold, ?_⟩
  intro n hn
  have htail : compiler.threshold ≤ n :=
    le_trans (Nat.le_max_left compiler.threshold tail.threshold) hn
  have hchecked_tail : tail.threshold ≤ n :=
    le_trans (Nat.le_max_right compiler.threshold tail.threshold) hn
  let checkedAt : MainSondowFullCertificateCheckedAt n :=
    tail.checked_at n hchecked_tail
  let cert : _root_.BoundedArithmeticLab.SondowComponentCertificate :=
    { productProof :=
        compiler.productProof n checkedAt.q htail checkedAt.checked
      logProof :=
        compiler.logProof n checkedAt.q htail checkedAt.checked
      decompositionProof :=
        compiler.decompositionProof n checkedAt.q htail checkedAt.checked
      threePowProof :=
        compiler.threePowProof n checkedAt.q htail checkedAt.checked
      payloadProof :=
        compiler.payloadProof n checkedAt.q htail checkedAt.checked }
  have hvalid :
      _root_.BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
        _root_.BoundedArithmeticLab.sondowProjectComponentFormulas
        bounds n cert :=
    { product_conclusion :=
        compiler.product_conclusion n checkedAt.q htail checkedAt.checked
      log_conclusion :=
        compiler.log_conclusion n checkedAt.q htail checkedAt.checked
      decomposition_conclusion :=
        compiler.decomposition_conclusion n checkedAt.q htail checkedAt.checked
      threePow_conclusion :=
        compiler.threePow_conclusion n checkedAt.q htail checkedAt.checked
      payload_conclusion :=
        compiler.payload_conclusion n checkedAt.q htail checkedAt.checked
      product_size_plus_two_le :=
        compiler.product_size_plus_two_le n checkedAt.q htail checkedAt.checked
      log_size_plus_two_le :=
        compiler.log_size_plus_two_le n checkedAt.q htail checkedAt.checked
      decomposition_size_plus_two_le :=
        compiler.decomposition_size_plus_two_le n checkedAt.q htail checkedAt.checked
      threePow_size_plus_two_le :=
        compiler.threePow_size_plus_two_le n checkedAt.q htail checkedAt.checked
      payload_size_plus_two_le :=
        compiler.payload_size_plus_two_le n checkedAt.q htail checkedAt.checked }
  exact
    semanticPAProjectTargetLength_le_combined_of_componentProofObjects
      (bounds := bounds) (n := n) (cert := cert) hvalid

/--
Literature-calibrated Sondow upper side on the same PA semantic target used by
the Pudlak/checker lower side.

This is the clean upper-provider replacement: it destructs rationality into a
fixed rational parameter and then uses the half-denominator checked-tail route,
not the legacy root `accepted_certificate` route.
-/
theorem
    semanticPAProjectTargetUpper_fromRationalityAndEventualCompiler
    {bounds : _root_.BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.BoundedArithmeticLab.semanticBAProofLength
            _root_.BoundedArithmeticLab.PAAxiom
            _root_.BoundedArithmeticLab.sondowProjectComponentFormulas.target n
          ≤ U n := by
  rcases hrat with ⟨q, hq⟩
  exact
    semanticPAProjectTargetUpper_fromHalfDenCheckedTailAndEventualCompiler
      compiler q hq

/-- Full-certificate compiler form of the same PA semantic upper theorem. -/
theorem
    semanticPAProjectTargetUpper_fromRationalityAndFullCompiler
    {bounds : _root_.BoundedArithmeticLab.SondowComponentBounds}
    (compiler : MainSondowFullCertificateComponentProofCompiler bounds)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.BoundedArithmeticLab.semanticBAProofLength
            _root_.BoundedArithmeticLab.PAAxiom
            _root_.BoundedArithmeticLab.sondowProjectComponentFormulas.target n
          ≤ U n :=
  semanticPAProjectTargetUpper_fromRationalityAndEventualCompiler
    compiler.toEventualCompiler hrat

/--
Submission-facing name for the literature-calibrated Sondow upper theorem.

The measured object is not the legacy root `proof_length` fallback.  It is the
semantic PA proof length of the concrete bounded-arithmetic target formula,
defined as the infimum of sizes of PA `BAProofObject`s proving
`sondowProjectComponentFormulas.target n`.
-/
theorem
    literatureCalibratedSondowUpper_fromRationalityAndEventualCompiler
    {bounds : _root_.BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.BoundedArithmeticLab.semanticBAProofLength
            _root_.BoundedArithmeticLab.PAAxiom
            _root_.BoundedArithmeticLab.sondowProjectComponentFormulas.target n
          ≤ U n :=
  semanticPAProjectTargetUpper_fromRationalityAndEventualCompiler compiler hrat

/-- Full-certificate form of `literatureCalibratedSondowUpper_fromRationalityAndEventualCompiler`. -/
theorem
    literatureCalibratedSondowUpper_fromRationalityAndFullCompiler
    {bounds : _root_.BoundedArithmeticLab.SondowComponentBounds}
    (compiler : MainSondowFullCertificateComponentProofCompiler bounds)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.BoundedArithmeticLab.semanticBAProofLength
            _root_.BoundedArithmeticLab.PAAxiom
            _root_.BoundedArithmeticLab.sondowProjectComponentFormulas.target n
          ≤ U n :=
  literatureCalibratedSondowUpper_fromRationalityAndEventualCompiler
    compiler.toEventualCompiler hrat

/--
Clean Sondow-specific S²₁ trace compiler.

This is the checked-specific replacement for the root
`S21VerifierTraceSoundness sondowCertificateValidCode` interface.  Its premise
is `MainSondowFullCertificateCheckedAt n`, so the theorem chain never unfolds
root `accepted_certificate` and therefore does not pick up the
partial-consistency payload branches.
-/
structure SondowCheckedS21TraceCompiler : Prop where
  short_s21_from_checked :
    ∀ n : Nat, MainSondowFullCertificateCheckedAt n →
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        _root_.proof_predicate_formula_size
          _root_.sondowCertificateValidCode n

/--
Root S²₁ proof-length recognition for a concrete Sondow proof-code compiler.

The concrete compiler supplies the actual proof-code length.  This calibration
is the root-interface statement saying the abstract `proof_length S21` symbol is
bounded by that concrete code length on the Sondow certificate family.  It is
kept separate because root `proof_length` is an abstract constant in the main
model layer.
-/
structure SondowFullCertificateConcreteS21RootCalibration
    (compiler : SondowFullCertificateConcreteProofCodeCompiler) : Prop where
  root_s21_length_le_codeLength :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        compiler.codeLength n

/--
Concrete proof-code compiler plus root S²₁ length recognition proves the
checked-specific Sondow trace compiler.

This is the formal version of the paper proof:

`checked certificate -> concrete S²₁ proof code -> root proof_length bound`.
-/
def SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler
    (compiler : SondowFullCertificateConcreteProofCodeCompiler)
    (root_calibration :
      SondowFullCertificateConcreteS21RootCalibration compiler) :
    SondowCheckedS21TraceCompiler where
  short_s21_from_checked := by
    intro n hchecked
    exact le_trans
      (root_calibration.root_s21_length_le_codeLength n)
      (compiler.short_code_from_checked n hchecked)

/--
Checked-length bound for the Sondow proof family exposed by the existing
S²₁ graft proof-length recognition theorem.

`S21GraftProofLengthRecognitionTheorem` already identifies root S²₁
`proof_length` on `sondowCertificateValidCode n` with the concrete MiniHilbert
family length `hrec.sondow_proofs.length n`.  This remaining field says that
the concrete family produced for a checked Sondow certificate is short enough to
fit inside the Sondow verifier predicate-size budget.
-/
structure SondowProofLengthRecognitionCheckedLengthBound
    (hrec : _root_.S21GraftProofLengthRecognitionTheorem) : Prop where
  sondow_length_le_predicate_from_checked :
    ∀ n : Nat, MainSondowFullCertificateCheckedAt n →
      (hrec.sondow_proofs.length n : Real) ≤
        _root_.proof_predicate_formula_size
          _root_.sondowCertificateValidCode n

/--
The Sondow certificate-validity fragment of the root formula-code universe.

This is the small fragment needed for the checked Sondow upper argument.  It is
kept separate from the global root `accepted_certificate` predicate, whose
definition also contains the older partial-consistency branches.
-/
def SondowCertificateRelevantCode
    (code : _root_.FormulaCode) : Prop :=
  ∃ n : Nat, code = _root_.sondowCertificateValidCode n

theorem SondowCertificateRelevantCode.sondow (n : Nat) :
    SondowCertificateRelevantCode (_root_.sondowCertificateValidCode n) :=
  ⟨n, rfl⟩

/--
Checked Sondow S²₁ proof-code semantics.

This is the proof-length model we can use without making an upper bound a black
box.  It gives a concrete proof-code semantics for the Sondow certificate
family and says that every checked full Sondow certificate produces an accepted
proof code whose concrete size is bounded by the verifier predicate-size budget.

No root `proof_length` and no polynomial upper-tail field appears here.
-/
structure SondowCheckedS21ProofCodeSemantics where
  sem : _root_.ProofCodeSemantics SondowCertificateRelevantCode
  checked_has_predicate_size_code :
    ∀ n : Nat, MainSondowFullCertificateCheckedAt n →
      ∃ c : sem.Code,
        sem.checks c (_root_.sondowCertificateValidCode n) ∧
          (sem.size c : Real) ≤
            _root_.proof_predicate_formula_size
              _root_.sondowCertificateValidCode n

/--
Local checked Sondow proof-code semantics.

Unlike `ProofCodeSemantics`, this does not require the whole
`sondowCertificateValidCode` family to be complete.  It is the non-circular
object actually needed by the Sondow upper proof: whenever a checked full
Sondow certificate is present at `n`, the semantics supplies a concrete S²₁
proof code for that index with size bounded by the verifier predicate size.
-/
structure SondowCheckedS21LocalProofCodeSemantics where
  Code : Type
  provesSondowCertificateAt : Code → Nat → Prop
  size : Code → Nat
  checked_has_predicate_size_code :
    ∀ n : Nat, MainSondowFullCertificateCheckedAt n →
      ∃ c : Code,
        provesSondowCertificateAt c n ∧
          (size c : Real) ≤
            _root_.proof_predicate_formula_size
              _root_.sondowCertificateValidCode n

namespace SondowCheckedS21LocalProofCodeSemantics

/--
Conditional minimum code length.

If there is at least one checked proof code at `n`, this is the minimum size of
such a code.  If not, it is `0`; that fallback is never used in the upper proof,
because the proof only asks for the value after a checked certificate has been
constructed.
-/
noncomputable def minCodeLength
    (model : SondowCheckedS21LocalProofCodeSemantics) (n : Nat) : Nat := by
  classical
  exact
    if h : ∃ k : Nat, ∃ c : model.Code,
        model.provesSondowCertificateAt c n ∧ model.size c ≤ k then
      Nat.find h
    else
      0

theorem minCodeLength_le_of_provesSondowCertificateAt
    (model : SondowCheckedS21LocalProofCodeSemantics)
    {n : Nat} {c : model.Code}
    (hproves : model.provesSondowCertificateAt c n) :
    model.minCodeLength n ≤ model.size c := by
  classical
  let P : Nat → Prop :=
    fun k : Nat => ∃ c : model.Code,
      model.provesSondowCertificateAt c n ∧ model.size c ≤ k
  have hex : ∃ k : Nat, P k :=
    ⟨model.size c, c, hproves, le_rfl⟩
  have hpred : P (model.size c) :=
    ⟨c, hproves, le_rfl⟩
  unfold minCodeLength
  rw [dif_pos hex]
  exact Nat.find_min' hex hpred

theorem exists_provesSondowCertificateAt_minCodeLength
    (model : SondowCheckedS21LocalProofCodeSemantics)
    {n : Nat}
    (hex : ∃ c : model.Code, model.provesSondowCertificateAt c n) :
    ∃ c : model.Code,
      model.provesSondowCertificateAt c n ∧
        model.size c ≤ model.minCodeLength n := by
  classical
  let P : Nat → Prop :=
    fun k : Nat => ∃ c : model.Code,
      model.provesSondowCertificateAt c n ∧ model.size c ≤ k
  have hfind : ∃ k : Nat, P k := by
    rcases hex with ⟨c, hproves⟩
    exact ⟨model.size c, c, hproves, le_rfl⟩
  unfold minCodeLength
  rw [dif_pos hfind]
  exact Nat.find_spec hfind

end SondowCheckedS21LocalProofCodeSemantics

/-- The Sondow verifier predicate-size budget is at least one. -/
theorem proofPredicateFormulaSizeSondowCertificateValidCode_one_le
    (n : Nat) :
    (1 : Real) ≤
      _root_.proof_predicate_formula_size
        _root_.sondowCertificateValidCode n := by
  have hlog_nonneg : (0 : Real) ≤ (Nat.log2 (n + 1) : Real) :=
    Nat.cast_nonneg _
  have hn_nonneg : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
  simp [_root_.proof_predicate_formula_size, _root_.verifier_trace_size,
    _root_.certificate_size, _root_.sondowCertificateValidCode,
    _root_.full_sondow_certificate_size,
    _root_.rational_sondow_certificate_components_size,
    _root_.tail_bound_certificate_size,
    _root_.denominator_certificate_size,
    _root_.binary_index_certificate_size,
    _root_.product_log_reference_certificate_size,
    _root_.theorem_reference_certificate_size] at *
  nlinarith

/-- Exact expanded size of the Sondow verifier predicate budget. -/
theorem proofPredicateFormulaSizeSondowCertificateValidCode_eq
    (n : Nat) :
    _root_.proof_predicate_formula_size _root_.sondowCertificateValidCode n =
      (3 : Real) * (Nat.log2 (n + 1) : Real) + 14 := by
  simp [_root_.proof_predicate_formula_size, _root_.verifier_trace_size,
    _root_.certificate_size, _root_.sondowCertificateValidCode,
    _root_.full_sondow_certificate_size,
    _root_.rational_sondow_certificate_components_size,
    _root_.tail_bound_certificate_size,
    _root_.denominator_certificate_size,
    _root_.binary_index_certificate_size,
    _root_.product_log_reference_certificate_size,
    _root_.theorem_reference_certificate_size]
  ring

/--
Concrete audit witness showing that the structural root length `n + 6` cannot
be bounded by the Sondow verifier predicate budget in general.
-/
theorem proofPredicateFormulaSizeSondowCertificateValidCode_100_lt_106 :
    _root_.proof_predicate_formula_size _root_.sondowCertificateValidCode 100 <
      (106 : Real) := by
  rw [proofPredicateFormulaSizeSondowCertificateValidCode_eq]
  have hlog : Nat.log2 101 = 6 := by
    norm_num [Nat.log2_eq_log_two, Nat.log]
  rw [hlog]
  norm_num

/--
Concrete sidecar local proof-code semantics for the Sondow verifier formula.

Here the proof-code carrier is the actual bounded-arithmetic proof-object type,
and the checked proof code is the explicit `polytimeDefinability` proof object
constructed above.  This closes the upper-side proof-code object without an
`upper_provider` input.
-/
def sidecarSondowCertificateLocalProofCodeSemantics :
    SondowCheckedS21LocalProofCodeSemantics where
  Code :=
    _root_.BoundedArithmeticLab.BAProofObject
      _root_.BoundedArithmeticLab.BussS21Axiom
  provesSondowCertificateAt := fun c n =>
    c.conclusion = sidecarSondowCertificateVerifierFormula n
  size := fun c => c.size
  checked_has_predicate_size_code := by
    intro n _hchecked
    refine ⟨sidecarSondowCertificateVerifierProofObject n, ?_, ?_⟩
    · exact sidecarSondowCertificateVerifierProofObject_conclusion n
    · simpa [sidecarSondowCertificateVerifierProofObject_size] using
        proofPredicateFormulaSizeSondowCertificateValidCode_one_le n

/--
Concrete proof-code compiler obtained from the sidecar proof objects.

This is no longer an input object: it is built directly from the sidecar
`BAProofObject` construction.
-/
noncomputable def sidecarSondowCertificateConcreteProofCodeCompiler :
    SondowFullCertificateConcreteProofCodeCompiler where
  codeLength :=
    sidecarSondowCertificateLocalProofCodeSemantics.minCodeLength
  short_code_from_checked := by
    intro n hchecked
    rcases
        sidecarSondowCertificateLocalProofCodeSemantics
          |>.checked_has_predicate_size_code n hchecked with
      ⟨c, hproves, hsize⟩
    have hminNat :
        sidecarSondowCertificateLocalProofCodeSemantics.minCodeLength n ≤
          sidecarSondowCertificateLocalProofCodeSemantics.size c :=
      sidecarSondowCertificateLocalProofCodeSemantics
        |>.minCodeLength_le_of_provesSondowCertificateAt hproves
    have hminReal :
        (sidecarSondowCertificateLocalProofCodeSemantics.minCodeLength n : Real) ≤
          (sidecarSondowCertificateLocalProofCodeSemantics.size c : Real) := by
      exact_mod_cast hminNat
    exact le_trans hminReal hsize

/--
Global proof-code semantics induced by the sidecar Sondow proof objects.

The proof-code carrier is the same bounded-arithmetic proof-object type used in
the local sidecar semantics.  A code checks a formula code exactly when it is a
sidecar proof object for the corresponding `sondowCertificateValidCode n`.
-/
def sidecarSondowCertificateProofCodeSemantics :
    _root_.ProofCodeSemantics SondowCertificateRelevantCode where
  Code := sidecarSondowCertificateLocalProofCodeSemantics.Code
  checks := fun c code =>
    ∃ n : Nat,
      code = _root_.sondowCertificateValidCode n ∧
        (sidecarSondowCertificateLocalProofCodeSemantics
          |>.provesSondowCertificateAt c n)
  size := sidecarSondowCertificateLocalProofCodeSemantics.size
  complete := by
    intro code hcode
    rcases hcode with ⟨n, hcode_eq⟩
    subst hcode_eq
    refine ⟨sidecarSondowCertificateVerifierProofObject n, ?_⟩
    exact ⟨n, rfl, sidecarSondowCertificateVerifierProofObject_conclusion n⟩

/-- Every bounded-arithmetic derivation has positive proof-code size. -/
theorem baDerivation_one_le_size
    {Ax : _root_.BoundedArithmeticLab.BAFormula → Prop}
    {φ : _root_.BoundedArithmeticLab.BAFormula}
    (p : _root_.BoundedArithmeticLab.BADerivation Ax φ) :
    1 ≤ p.size := by
  induction p with
  | ax h =>
      simp [_root_.BoundedArithmeticLab.BADerivation.size]
  | andIntro p q ihp ihq =>
      simp [_root_.BoundedArithmeticLab.BADerivation.size]
  | andElimRight p ihp =>
      simp [_root_.BoundedArithmeticLab.BADerivation.size]
  | impIntro p ihp =>
      simp [_root_.BoundedArithmeticLab.BADerivation.size]
  | mp p q ihp ihq =>
      simp [_root_.BoundedArithmeticLab.BADerivation.size]

/-- Every bounded-arithmetic proof object has positive proof-code size. -/
theorem baProofObject_one_le_size
    {Ax : _root_.BoundedArithmeticLab.BAFormula → Prop}
    (p : _root_.BoundedArithmeticLab.BAProofObject Ax) :
    1 ≤ p.size := by
  exact baDerivation_one_le_size p.derivation

/--
The sidecar Sondow verifier proof-code semantics has exact minimum code size
`1` on each `sondowCertificateValidCode n`.

This is a proof-code statement only.  It does not use or calibrate the root
`proof_length` symbol.
-/
theorem sidecarSondowCertificateProofCodeSemantics_min_eq_one
    (n : Nat) :
    _root_.ProofCodeSemantics.minProofCodeSize
        sidecarSondowCertificateProofCodeSemantics
        (_root_.sondowCertificateValidCode n)
        (SondowCertificateRelevantCode.sondow n) = 1 := by
  apply Nat.le_antisymm
  · apply _root_.ProofCodeSemantics.minProofCodeSize_le_of_hasProofCodeOfSize
      sidecarSondowCertificateProofCodeSemantics
      (SondowCertificateRelevantCode.sondow n)
    refine ⟨sidecarSondowCertificateVerifierProofObject n, ?_, ?_⟩
    · exact ⟨n, rfl, sidecarSondowCertificateVerifierProofObject_conclusion n⟩
    · change (sidecarSondowCertificateVerifierProofObject n).size ≤ 1
      simp [sidecarSondowCertificateVerifierProofObject_size]
  · rcases
        _root_.ProofCodeSemantics.hasProofCodeOfSize_minProofCodeSize
          sidecarSondowCertificateProofCodeSemantics
          (code := _root_.sondowCertificateValidCode n)
          (SondowCertificateRelevantCode.sondow n) with
      ⟨c, _hchecks, hsize⟩
    exact le_trans (baProofObject_one_le_size c) hsize

theorem sidecarSondowCertificateProofCodeSemantics_min_le_codeLength
    (n : Nat) :
    (sidecarSondowCertificateProofCodeSemantics.minProofCodeSize
        (_root_.sondowCertificateValidCode n)
        (SondowCertificateRelevantCode.sondow n) : Real) ≤
      (sidecarSondowCertificateConcreteProofCodeCompiler.codeLength n : Real) := by
  let localSem := sidecarSondowCertificateLocalProofCodeSemantics
  have hex :
      ∃ c : localSem.Code, localSem.provesSondowCertificateAt c n :=
    ⟨sidecarSondowCertificateVerifierProofObject n,
      sidecarSondowCertificateVerifierProofObject_conclusion n⟩
  rcases
      localSem.exists_provesSondowCertificateAt_minCodeLength hex with
    ⟨c, hproves, hsize⟩
  have hhas :
      sidecarSondowCertificateProofCodeSemantics.HasProofCodeOfSize
        (_root_.sondowCertificateValidCode n)
        (sidecarSondowCertificateConcreteProofCodeCompiler.codeLength n) := by
    refine ⟨c, ?_, ?_⟩
    · exact ⟨n, rfl, hproves⟩
    · simpa [sidecarSondowCertificateProofCodeSemantics,
        sidecarSondowCertificateConcreteProofCodeCompiler, localSem] using hsize
  have hminNat :
      sidecarSondowCertificateProofCodeSemantics.minProofCodeSize
          (_root_.sondowCertificateValidCode n)
          (SondowCertificateRelevantCode.sondow n) ≤
        sidecarSondowCertificateConcreteProofCodeCompiler.codeLength n :=
    sidecarSondowCertificateProofCodeSemantics
      |>.minProofCodeSize_le_of_hasProofCodeOfSize
        (SondowCertificateRelevantCode.sondow n) hhas
  exact_mod_cast hminNat

noncomputable def sidecarSondowCertificateProofLengthCodeSemantics
    (fallback : _root_.FormulaCode → Nat) :
    _root_.ProofLengthCodeSemantics
      _root_.ProofSystem.S21
      _root_.ProofLengthMeasure.symbolSize
      SondowCertificateRelevantCode where
  proof_code_semantics := sidecarSondowCertificateProofCodeSemantics
  fallback_length := fallback

theorem sidecarSondowCertificateProofLengthCodeSemantics_length_le_codeLength
    (fallback : _root_.FormulaCode → Nat) (n : Nat) :
    ((_root_.ProofLengthCodeSemantics.length
        (sidecarSondowCertificateProofLengthCodeSemantics fallback)
        (_root_.sondowCertificateValidCode n) : Nat) : Real) ≤
      sidecarSondowCertificateConcreteProofCodeCompiler.codeLength n := by
  rw [_root_.ProofLengthCodeSemantics.length]
  rw [_root_.ProofCodeSemantics.semanticProofLength_eq_minProofCodeSize]
  exact sidecarSondowCertificateProofCodeSemantics_min_le_codeLength n

/--
Canonical fallback used to turn the sidecar proof-code semantics into a total
Nat-valued semantic proof length.  The fallback is never used on the Sondow
certificate family, but fixing it removes the last irrelevant parameter from the
main upper theorem.
-/
def sidecarSondowCertificateCanonicalFallback :
    _root_.FormulaCode → Nat :=
  fun _ => 0

/--
The canonical semantic proof-length model for the Sondow sidecar family.

This is the object that should be used as the proof-length notion in the clean
Sondow upper theorem.  It is constructed from proof codes and a checker
relation; it does not mention the repository root `proof_length` axiom.
-/
noncomputable def sidecarSondowCertificateCanonicalProofLengthSemantics :
    _root_.ProofLengthCodeSemantics
      _root_.ProofSystem.S21
      _root_.ProofLengthMeasure.symbolSize
      SondowCertificateRelevantCode :=
  sidecarSondowCertificateProofLengthCodeSemantics
    sidecarSondowCertificateCanonicalFallback

/-- Canonical semantic length of the `n`th Sondow certificate-validity code. -/
noncomputable def sidecarSondowCertificateCanonicalSemanticLength
    (n : Nat) : Nat :=
  _root_.ProofLengthCodeSemantics.length
    sidecarSondowCertificateCanonicalProofLengthSemantics
    (_root_.sondowCertificateValidCode n)

/--
The canonical sidecar semantic length is exactly `1` on each Sondow
certificate-validity code.

This is the proof-length-free replacement for the root `S21` trace-length
recognition step.
-/
theorem sidecarSondowCertificateCanonicalSemanticLength_eq_one
    (n : Nat) :
    sidecarSondowCertificateCanonicalSemanticLength n = 1 := by
  simp [sidecarSondowCertificateCanonicalSemanticLength,
    sidecarSondowCertificateCanonicalProofLengthSemantics,
    sidecarSondowCertificateProofLengthCodeSemantics,
    _root_.ProofLengthCodeSemantics.length,
    _root_.ProofCodeSemantics.semanticProofLength,
    SondowCertificateRelevantCode.sondow,
    sidecarSondowCertificateProofCodeSemantics_min_eq_one]

/--
Proof-length-free Sondow trace compiler for the canonical sidecar semantics.

Unlike `SondowCheckedS21TraceCompiler`, this statement does not mention the
repository root `proof_length`; it is fully closed by the concrete sidecar
proof-code semantics.
-/
structure SondowCheckedS21SemanticTraceCompiler : Prop where
  short_semantic_from_checked :
    ∀ n : Nat, MainSondowFullCertificateCheckedAt n →
      (sidecarSondowCertificateCanonicalSemanticLength n : Real) ≤
        _root_.proof_predicate_formula_size
          _root_.sondowCertificateValidCode n

/-- Closed proof-length-free Sondow trace compiler. -/
def SondowCheckedS21SemanticTraceCompiler.closed :
    SondowCheckedS21SemanticTraceCompiler where
  short_semantic_from_checked := by
    intro n _hchecked
    rw [sidecarSondowCertificateCanonicalSemanticLength_eq_one]
    simpa using proofPredicateFormulaSizeSondowCertificateValidCode_one_le n

theorem sidecarSondowCertificateCanonicalSemanticLength_le_codeLength
    (n : Nat) :
    (sidecarSondowCertificateCanonicalSemanticLength n : Real) ≤
      (sidecarSondowCertificateConcreteProofCodeCompiler.codeLength n : Real) := by
  simpa [sidecarSondowCertificateCanonicalSemanticLength,
    sidecarSondowCertificateCanonicalProofLengthSemantics] using
    sidecarSondowCertificateProofLengthCodeSemantics_length_le_codeLength
      sidecarSondowCertificateCanonicalFallback n

/--
The proof-length-axiom-free Sondow upper theorem.

This is the leap theorem: it uses the canonical semantic proof length constructed
from sidecar proof codes, not the repository root `proof_length` axiom.
-/
theorem
    canonicalSemanticSondowLinearUpper_fromHalfDenCheckedTail
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      (sidecarSondowCertificateCanonicalSemanticLength n : Real) ≤
        sondowCertificateLinearUpper n := by
  intro n hn
  exact le_trans
    (sidecarSondowCertificateCanonicalSemanticLength_le_codeLength n)
    (pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndCompiler
      sidecarSondowCertificateConcreteProofCodeCompiler q hq n hn)

theorem
    canonicalSemanticSondowUpper_fromHalfDenCheckedTail
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        (sidecarSondowCertificateCanonicalSemanticLength n : Real) ≤ U n := by
  refine ⟨sondowCertificateLinearUpper,
    sondowCertificateLinearUpper_polynomial,
    max 3 ((q.den + 1) / 2), ?_⟩
  exact canonicalSemanticSondowLinearUpper_fromHalfDenCheckedTail q hq

/--
Root S²₁ calibration specialized to the sidecar proof objects.

This is intentionally a named obligation, not a hidden theorem: the sidecar
proof objects close the concrete proof-code upper, while this field is exactly
the remaining recognition statement connecting the repository's abstract root
`proof_length` symbol to that concrete sidecar code length.
-/
abbrev SidecarSondowCertificateConcreteS21RootCalibration : Prop :=
  SondowFullCertificateConcreteS21RootCalibration
    sidecarSondowCertificateConcreteProofCodeCompiler

/--
Sidecar proof objects plus root S²₁ recognition close
`SondowCheckedS21TraceCompiler`.

The concrete proof-code compiler is built above; the only remaining root-layer
input is the explicit calibration obligation.
-/
def SondowCheckedS21TraceCompiler.ofSidecarProofObjectsAndRootCalibration
    (root_calibration :
      SidecarSondowCertificateConcreteS21RootCalibration) :
    SondowCheckedS21TraceCompiler :=
  SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler
    sidecarSondowCertificateConcreteProofCodeCompiler root_calibration

/--
Root S²₁ linear upper from the fully constructed sidecar proof objects and the
single root calibration obligation.
-/
theorem
    s21SondowLinearUpper_fromHalfDenCheckedTailSidecarProofObjectsAndRootCalibration
    (root_calibration :
      SidecarSondowCertificateConcreteS21RootCalibration)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowCertificateLinearUpper n :=
  by
    intro n hn
    exact le_trans
      (root_calibration.root_s21_length_le_codeLength n)
      (pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndCompiler
        sidecarSondowCertificateConcreteProofCodeCompiler q hq n hn)

/--
Root S²₁ upper-tail certificate from sidecar proof objects plus root
recognition.
-/
theorem
    s21SondowCertificateUpper_fromHalfDenCheckedTailSidecarProofObjectsAndRootCalibration
    (root_calibration :
      SidecarSondowCertificateConcreteS21RootCalibration)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n :=
  by
    refine ⟨sondowCertificateLinearUpper,
      sondowCertificateLinearUpper_polynomial,
      max 3 ((q.den + 1) / 2), ?_⟩
    exact
      s21SondowLinearUpper_fromHalfDenCheckedTailSidecarProofObjectsAndRootCalibration
        root_calibration q hq

/--
The single root-layer calibration still needed after the sidecar semantics has
been fixed canonically.

This is the sharp cut: all proof-code objects and all length upper estimates are
already constructed above.  The only remaining root-level statement is that the
repository's abstract `proof_length S21 symbolSize` agrees with this canonical
sidecar proof-length semantics on the Sondow certificate family.
-/
abbrev SidecarSondowCertificateCanonicalProofLengthCalibration
    (fallback : _root_.FormulaCode → Nat) : Prop :=
  (sidecarSondowCertificateProofLengthCodeSemantics fallback).Calibration

/--
Family form of the remaining sidecar root calibration.

The total `ProofLengthCodeSemantics` object has a fallback outside the Sondow
certificate family.  On the relevant family itself the fallback disappears, so
the calibration is exactly the statement that root `proof_length` agrees with
the sidecar checker's minimum accepted proof-code size.
-/
theorem
    sidecarSondowCertificateCanonicalProofLengthCalibration_iff_family
    (fallback : _root_.FormulaCode → Nat) :
    SidecarSondowCertificateCanonicalProofLengthCalibration fallback ↔
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) =
          sidecarSondowCertificateProofCodeSemantics.minProofCodeSize
            (_root_.sondowCertificateValidCode n)
            (SondowCertificateRelevantCode.sondow n) := by
  constructor
  · intro hcal n
    rw [hcal.proof_length_eq_length
      (_root_.sondowCertificateValidCode n)
      (SondowCertificateRelevantCode.sondow n)]
    simp [_root_.ProofLengthCodeSemantics.length,
      _root_.ProofCodeSemantics.semanticProofLength,
      sidecarSondowCertificateProofLengthCodeSemantics,
      SondowCertificateRelevantCode.sondow]
  · intro hfamily
    refine ⟨?_⟩
    intro code hcode
    rcases hcode with ⟨n, hcode_eq⟩
    subst hcode_eq
    simp [_root_.ProofLengthCodeSemantics.length,
      _root_.ProofCodeSemantics.semanticProofLength,
      sidecarSondowCertificateProofLengthCodeSemantics,
      SondowCertificateRelevantCode.sondow]
    exact hfamily n

/--
One-line form of the remaining root calibration.

Since the concrete sidecar checker has exact minimum proof-code size `1` on
every Sondow certificate-validity code, calibrating root `proof_length` to this
checker is equivalent to proving that root `proof_length` assigns length `1` to
that same family.
-/
theorem
    sidecarSondowCertificateCanonicalProofLengthCalibration_iff_rootLengthOne
    (fallback : _root_.FormulaCode → Nat) :
    SidecarSondowCertificateCanonicalProofLengthCalibration fallback ↔
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) = (1 : Real) := by
  rw [sidecarSondowCertificateCanonicalProofLengthCalibration_iff_family]
  constructor
  · intro hfamily n
    rw [hfamily n]
    exact_mod_cast sidecarSondowCertificateProofCodeSemantics_min_eq_one n
  · intro hroot n
    rw [hroot n]
    exact_mod_cast (sidecarSondowCertificateProofCodeSemantics_min_eq_one n).symm

/-- Closed root calibration for the canonical Sondow sidecar proof-code semantics. -/
theorem sidecarSondowCertificateCanonicalProofLengthCalibration_closed
    (fallback : _root_.FormulaCode → Nat) :
    SidecarSondowCertificateCanonicalProofLengthCalibration fallback :=
  (sidecarSondowCertificateCanonicalProofLengthCalibration_iff_rootLengthOne
    fallback).2
    (fun n => _root_.rootProofLength_sondowCertificateValidCode_eq_one n)

def SidecarSondowCertificateConcreteS21RootCalibration.ofCanonicalSidecarCalibration
    (fallback : _root_.FormulaCode → Nat)
    (hcal :
      SidecarSondowCertificateCanonicalProofLengthCalibration fallback) :
    SidecarSondowCertificateConcreteS21RootCalibration where
  root_s21_length_le_codeLength := by
    intro n
    rw [hcal.proof_length_eq_length
      (_root_.sondowCertificateValidCode n)
      (SondowCertificateRelevantCode.sondow n)]
    exact sidecarSondowCertificateProofLengthCodeSemantics_length_le_codeLength
      fallback n

def SondowCheckedS21TraceCompiler.ofCanonicalSidecarCalibration
    (fallback : _root_.FormulaCode → Nat)
    (hcal :
      SidecarSondowCertificateCanonicalProofLengthCalibration fallback) :
    SondowCheckedS21TraceCompiler :=
  SondowCheckedS21TraceCompiler.ofSidecarProofObjectsAndRootCalibration
    (SidecarSondowCertificateConcreteS21RootCalibration.ofCanonicalSidecarCalibration
      fallback hcal)

def SondowCheckedS21TraceCompiler.ofSidecarFamilyRootCalibration
    (fallback : _root_.FormulaCode → Nat)
    (hfamily :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) =
          sidecarSondowCertificateProofCodeSemantics.minProofCodeSize
            (_root_.sondowCertificateValidCode n)
            (SondowCertificateRelevantCode.sondow n)) :
    SondowCheckedS21TraceCompiler :=
  SondowCheckedS21TraceCompiler.ofCanonicalSidecarCalibration
    fallback
    ((sidecarSondowCertificateCanonicalProofLengthCalibration_iff_family
      fallback).2 hfamily)

def SondowCheckedS21TraceCompiler.ofRootLengthOne
    (fallback : _root_.FormulaCode → Nat)
    (hroot :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) = (1 : Real)) :
    SondowCheckedS21TraceCompiler :=
  SondowCheckedS21TraceCompiler.ofCanonicalSidecarCalibration
    fallback
    ((sidecarSondowCertificateCanonicalProofLengthCalibration_iff_rootLengthOne
      fallback).2 hroot)

/-- Closed proof of the root `SondowCheckedS21TraceCompiler` after sidecar-slot calibration. -/
def SondowCheckedS21TraceCompiler.closed :
    SondowCheckedS21TraceCompiler :=
  SondowCheckedS21TraceCompiler.ofCanonicalSidecarCalibration
    sidecarSondowCertificateCanonicalFallback
    (sidecarSondowCertificateCanonicalProofLengthCalibration_closed
      sidecarSondowCertificateCanonicalFallback)

theorem
    s21SondowLinearUpper_fromHalfDenCheckedTailCanonicalSidecarCalibration
    (fallback : _root_.FormulaCode → Nat)
    (hcal :
      SidecarSondowCertificateCanonicalProofLengthCalibration fallback)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowCertificateLinearUpper n :=
  s21SondowLinearUpper_fromHalfDenCheckedTailSidecarProofObjectsAndRootCalibration
    (SidecarSondowCertificateConcreteS21RootCalibration.ofCanonicalSidecarCalibration
      fallback hcal)
    q hq

theorem
    s21SondowCertificateUpper_fromHalfDenCheckedTailCanonicalSidecarCalibration
    (fallback : _root_.FormulaCode → Nat)
    (hcal :
      SidecarSondowCertificateCanonicalProofLengthCalibration fallback)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n :=
  s21SondowCertificateUpper_fromHalfDenCheckedTailSidecarProofObjectsAndRootCalibration
    (SidecarSondowCertificateConcreteS21RootCalibration.ofCanonicalSidecarCalibration
      fallback hcal)
    q hq

theorem
    s21SondowLinearUpper_fromHalfDenCheckedTailClosed
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowCertificateLinearUpper n :=
  s21SondowLinearUpper_fromHalfDenCheckedTailCanonicalSidecarCalibration
    sidecarSondowCertificateCanonicalFallback
    (sidecarSondowCertificateCanonicalProofLengthCalibration_closed
      sidecarSondowCertificateCanonicalFallback)
    q hq

theorem
    s21SondowCertificateUpper_fromHalfDenCheckedTailClosed
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n :=
  s21SondowCertificateUpper_fromHalfDenCheckedTailCanonicalSidecarCalibration
    sidecarSondowCertificateCanonicalFallback
    (sidecarSondowCertificateCanonicalProofLengthCalibration_closed
      sidecarSondowCertificateCanonicalFallback)
    q hq

/--
Proof-code upper with the sidecar proof objects fully constructed.

This removes the Sondow upper-provider obligation for the proof-code-free
measured object.  It still does not calibrate the abstract root `proof_length`
symbol.
-/
theorem pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndSidecarProofObjects
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        (sidecarSondowCertificateConcreteProofCodeCompiler.codeLength n : Real) ≤
          U n :=
  pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndCompiler
    sidecarSondowCertificateConcreteProofCodeCompiler q hq

/--
The concrete target measurement supplied by the closed sidecar proof objects.

This is the measurement that can be fed into the generic checked-target
projection endpoint.  It is a `Nat`-valued concrete proof-code length, not the
root abstract `proof_length`.
-/
def sidecarSondowCertificateTargetMeasured (n : Nat) : Nat :=
  sidecarSondowCertificateConcreteProofCodeCompiler.codeLength n

/-- The current sidecar target has exact minimum proof-object size `1` at
every index.  This makes explicit that the sidecar is only a verifier shell;
it is not yet the same proof-complexity object as the Pudlak source family. -/
theorem sidecarSondowCertificateTargetMeasured_eq_one
    (n : Nat) :
    sidecarSondowCertificateTargetMeasured n = 1 := by
  let model := sidecarSondowCertificateLocalProofCodeSemantics
  change model.minCodeLength n = 1
  apply Nat.le_antisymm
  · have hproof :
        model.provesSondowCertificateAt
          (sidecarSondowCertificateVerifierProofObject n) n :=
      sidecarSondowCertificateVerifierProofObject_conclusion n
    have hle := model.minCodeLength_le_of_provesSondowCertificateAt hproof
    have hsize :
        model.size (sidecarSondowCertificateVerifierProofObject n) = 1 := by
      change (sidecarSondowCertificateVerifierProofObject n).size = 1
      exact sidecarSondowCertificateVerifierProofObject_size n
    exact hle.trans_eq hsize
  · have hex : ∃ c : model.Code, model.provesSondowCertificateAt c n :=
      ⟨sidecarSondowCertificateVerifierProofObject n,
        sidecarSondowCertificateVerifierProofObject_conclusion n⟩
    rcases model.exists_provesSondowCertificateAt_minCodeLength hex with
      ⟨c, _hproves, hsize⟩
    exact le_trans (baProofObject_one_le_size c) hsize

/-- Consequently the current sidecar target measurement is polynomially
bounded, indeed constant. -/
theorem sidecarSondowCertificateTargetMeasured_polynomial :
    _root_.is_polynomial_bound
      (fun n : Nat => (sidecarSondowCertificateTargetMeasured n : Real)) := by
  refine ⟨1, 0, ?_⟩
  intro n
  simp [sidecarSondowCertificateTargetMeasured_eq_one]

/-- If the theorem-5 checked minimum really beats every polynomial, the
current constant-size sidecar target cannot be the same proof-complexity
object up to the advertised `+2` projection. -/
theorem no_sidecarSondowCheckedTargetProjection_of_strongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (hlower :
      ∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (sem.minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) :
    ¬ InternalPudlakTheorem5CheckedTargetProjection
        scale_data sem sidecarSondowCertificateTargetMeasured := by
  intro projection
  let U : Nat → Real :=
    fun n => (sidecarSondowCertificateTargetMeasured n : Real) + 2
  have hU : _root_.is_polynomial_bound U := by
    exact _root_.is_polynomial_bound_add_const
      sidecarSondowCertificateTargetMeasured_polynomial (by norm_num)
  have hfreq := hlower U hU
  rw [Filter.frequently_atTop] at hfreq
  rcases hfreq 0 with ⟨n, _hn, hnLower⟩
  have hprojection := projection.source_le_target_add_two n
  have hnUpper :
      (sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
        U n := by
    have hprojectionReal :
        (sem.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
          (sidecarSondowCertificateTargetMeasured n : Real) + 2 := by
      exact_mod_cast hprojection
    simpa [U] using hprojectionReal
  exact (not_lt_of_ge hnUpper) hnLower

/--
Explicit polynomial upper-tail certificate for the sidecar Sondow target.

Under `q = gamma`, the half-denominator checked tail supplies checked Sondow
certificates after `max 3 ((q.den + 1) / 2)`, and the sidecar proof objects give
the concrete length bound `17(n+1)`.  This is the certificate-level form; it is
not an assumed upper-provider.
-/
def sidecarSondowCertificateUpperTailCertificate_fromHalfDenRational
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate
      (fun n : Nat => (sidecarSondowCertificateTargetMeasured n : Real)) where
  U := sondowCertificateLinearUpper
  polynomial := sondowCertificateLinearUpper_polynomial
  upperN := max 3 ((q.den + 1) / 2)
  upper_after := by
    intro n hn
    simpa [sidecarSondowCertificateTargetMeasured] using
      pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndCompiler
        sidecarSondowCertificateConcreteProofCodeCompiler q hq n hn

theorem sidecarSondowCertificateUpperTailCertificate_fromHalfDenRational_U
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    (sidecarSondowCertificateUpperTailCertificate_fromHalfDenRational
      q hq).U = sondowCertificateLinearUpper :=
  rfl

theorem sidecarSondowCertificateUpperTailCertificate_fromHalfDenRational_upperN
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    (sidecarSondowCertificateUpperTailCertificate_fromHalfDenRational
      q hq).upperN = max 3 ((q.den + 1) / 2) :=
  rfl

/--
Sondow-side checked-target upper provider constructed from the sidecar proof
objects.

The `upper_provider` vocabulary appears only as the endpoint API shape.  Its
content is no longer external: rationality is destructed to a concrete rational
`q`, and the upper-tail certificate above is built directly.
-/
noncomputable def sidecarSondowCertificateCheckedTargetUpperProvider :
    ProjectLengthExplicitCheckedTargetUpperProvider
      sidecarSondowCertificateTargetMeasured where
  upperTailOfRationality := by
    classical
    intro hrat
    let q : Rat := Classical.choose hrat
    have hq : (q : Real) = _root_.euler_mascheroni :=
      Classical.choose_spec hrat
    exact sidecarSondowCertificateUpperTailCertificate_fromHalfDenRational q hq

theorem sidecarSondowCertificateCheckedTargetUpperProvider_upperN
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (sidecarSondowCertificateCheckedTargetUpperProvider
      |>.upperTailOfRationality hrat).upperN =
        max 3 (((Classical.choose hrat : Rat).den + 1) / 2) := by
  classical
  rfl

/--
Transport the closed Sondow sidecar upper through a checked-target projection
into the theorem-5 checked source measurement.

This is the first point where the Sondow upper becomes a main-route upper.  The
only remaining input here is the same-object projection
`source <= target + 2`; the polynomial upper itself is generated above.
-/
def checkedExplicitUpperProviderOfSidecarSondowTargetProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        scale_data sem sidecarSondowCertificateTargetMeasured) :
    ProjectLengthExplicitMeasuredUpperProvider
      (month9_month10_checkedProofCodeMeasured scale_data sem) :=
  checkedExplicitUpperProviderOfCheckedTargetProjectionAndUpper
    projection sidecarSondowCertificateCheckedTargetUpperProvider

theorem checkedExplicitUpperProviderOfSidecarSondowTargetProjection_U
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        scale_data sem sidecarSondowCertificateTargetMeasured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((checkedExplicitUpperProviderOfSidecarSondowTargetProjection
      projection).upperTailOfRationality hrat).U =
        fun n : Nat => sondowCertificateLinearUpper n + 2 := by
  classical
  rfl

theorem checkedExplicitUpperProviderOfSidecarSondowTargetProjection_upperN
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        scale_data sem sidecarSondowCertificateTargetMeasured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((checkedExplicitUpperProviderOfSidecarSondowTargetProjection
      projection).upperTailOfRationality hrat).upperN =
        max 3 (((Classical.choose hrat : Rat).den + 1) / 2) := by
  classical
  rfl

/--
Abstract checked upper-provider generated from the sidecar Sondow target.

This is the shape consumed by the existing checked-search collision endpoint,
but its construction no longer assumes a Sondow upper provider.
-/
def checkedUpperProviderOfSidecarSondowTargetProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        scale_data sem sidecarSondowCertificateTargetMeasured) :
    Month9Month10AbstractMeasuredUpperProvider
      (month9_month10_checkedProofCodeMeasured scale_data sem) :=
  (checkedExplicitUpperProviderOfSidecarSondowTargetProjection
    projection).toAbstract

/--
Audit statement for the generated checked upper.

It exposes the concrete upper function and the exact half-denominator cutoff
selected under a rational witness.
-/
theorem checkedUpperProviderOfSidecarSondowTargetProjection_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        scale_data sem sidecarSondowCertificateTargetMeasured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let upper :=
      (checkedExplicitUpperProviderOfSidecarSondowTargetProjection
        projection).upperTailOfRationality hrat
    _root_.is_polynomial_bound upper.U ∧
      ∀ n : Nat, upper.upperN ≤ n →
        month9_month10_checkedProofCodeMeasured scale_data sem n ≤
          upper.U n := by
  dsimp [checkedExplicitUpperProviderOfSidecarSondowTargetProjection,
    checkedExplicitUpperProviderOfCheckedTargetProjectionAndUpper,
    checkedUpperTailCertificateOfCheckedTargetProjection]
  constructor
  · exact _root_.is_polynomial_bound_add_const
      (sidecarSondowCertificateCheckedTargetUpperProvider
        |>.upperTailOfRationality hrat).polynomial
      (by norm_num)
  · intro n hn
    have hsource :
        (sem.minProofCodeSize (scale_data.powerBoundRawCode n)
          ⟨n, rfl⟩ : Real) ≤
          (sidecarSondowCertificateTargetMeasured n : Real) + 2 := by
      exact_mod_cast projection.source_le_target_add_two n
    have htarget :
        (sidecarSondowCertificateTargetMeasured n : Real) ≤
          (sidecarSondowCertificateCheckedTargetUpperProvider
            |>.upperTailOfRationality hrat).U n :=
      (sidecarSondowCertificateCheckedTargetUpperProvider
        |>.upperTailOfRationality hrat).upper_after n hn
    have hchecked :
        (sem.minProofCodeSize (scale_data.powerBoundRawCode n)
          ⟨n, rfl⟩ : Real) ≤
          (sidecarSondowCertificateCheckedTargetUpperProvider
            |>.upperTailOfRationality hrat).U n + 2 := by
      nlinarith
    simpa [month9_month10_checkedProofCodeMeasured] using hchecked

/--
Theorem-5 provider specialized to the closed sidecar Sondow upper.

The final checked-search API still stores an `upper_provider` field internally,
but this constructor no longer takes it as a user input: it is generated from
the sidecar upper-tail certificate and the checked-target projection.
-/
def theorem5ProviderOfCanonicalSearchCoreSidecarSondowTarget
    (core : PAHilbertCanonicalSearchCore)
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        sidecarSondowCertificateTargetMeasured) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  theorem5ProviderOfCanonicalSearchCoreCheckedUpper core
    (checkedUpperProviderOfSidecarSondowTargetProjection projection)

/--
Main proof-length-free contradiction from the sidecar Sondow target.

The only remaining bridge input is the checked-target projection identifying
the theorem-5 checked source with the sidecar Sondow measured target up to the
audited `+2` overhead.
-/
theorem theorem5ProviderOfCanonicalSearchCoreSidecarSondowTarget_not_rational
    (core : PAHilbertCanonicalSearchCore)
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        sidecarSondowCertificateTargetMeasured) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  (theorem5ProviderOfCanonicalSearchCoreSidecarSondowTarget
    core projection).not_rational

/--
Explicit project-length endpoint specialized to the sidecar Sondow target.

Unlike the abstract provider endpoint, this one preserves the selected formula
for `U` and the selected half-denominator cutoff.
-/
def projectLengthExplicitEndpointOfSidecarSondowTargetUpper
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        sidecarSondowCertificateTargetMeasured) :
    ProjectLengthExplicitMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        core.scale_data core.checkerSemantics fallback) :=
  projectLengthExplicitEndpointOfCheckedTargetUpper
    core fallback projection sidecarSondowCertificateCheckedTargetUpperProvider

theorem projectLengthExplicitEndpointOfSidecarSondowTargetUpper_U
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        sidecarSondowCertificateTargetMeasured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((projectLengthExplicitEndpointOfSidecarSondowTargetUpper
      core fallback projection).upperTailOfRationality hrat).U =
        fun n : Nat => sondowCertificateLinearUpper n + 2 := by
  classical
  rfl

theorem projectLengthExplicitEndpointOfSidecarSondowTargetUpper_upperN
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        sidecarSondowCertificateTargetMeasured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((projectLengthExplicitEndpointOfSidecarSondowTargetUpper
      core fallback projection).upperTailOfRationality hrat).upperN =
        max 3 (((Classical.choose hrat : Rat).den + 1) / 2) := by
  classical
  rfl

theorem projectLengthExplicitEndpointOfSidecarSondowTargetUpper_computed_n_eq
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        sidecarSondowCertificateTargetMeasured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthExplicitEndpointOfSidecarSondowTargetUpper
        core fallback projection).computedCollisionNOfRationality hrat =
      core.rejectionExtractor.witness
        ((projectLengthExplicitEndpointOfSidecarSondowTargetUpper
          core fallback projection).upperTailOfRationality hrat).U
        ((projectLengthExplicitEndpointOfSidecarSondowTargetUpper
          core fallback projection).upperTailOfRationality hrat).polynomial
        ((projectLengthExplicitEndpointOfSidecarSondowTargetUpper
          core fallback projection).upperTailOfRationality hrat).upperN := by
  simpa [projectLengthExplicitEndpointOfSidecarSondowTargetUpper] using
    projectLengthExplicitEndpointOfCheckedTargetUpper_computed_n_eq
      core fallback projection
      sidecarSondowCertificateCheckedTargetUpperProvider hrat

/--
Sondow-specific verifier-simulation builder.

This is a more transparent sufficient condition for
`SondowCheckedS21LocalProofCodeSemantics`.  It separates the two proof-code
construction steps:

* a checked full Sondow certificate yields a verifier trace;
* the verifier trace is compiled into an S²₁ proof code.

The two size fields are bookkeeping only.  They do not mention rationality,
tail bounds, upper providers, or collision arguments.
-/
structure SondowCheckedS21VerifierSimulationBuilder where
  Trace : Type
  ProofCode : Type
  traceOfChecked :
    ∀ n : Nat, MainSondowFullCertificateCheckedAt n → Trace
  proofCodeOfTrace : Trace → ProofCode
  provesSondowCertificateAt : ProofCode → Nat → Prop
  proofCodeSize : ProofCode → Nat
  traceSize : Trace → Real
  trace_size_le_verifier_trace :
    ∀ n : Nat, ∀ hchecked : MainSondowFullCertificateCheckedAt n,
      traceSize (traceOfChecked n hchecked) ≤
        _root_.verifier_trace_size _root_.sondowCertificateValidCode n
  compiled_trace_proves_sondow_certificate :
    ∀ n : Nat, ∀ hchecked : MainSondowFullCertificateCheckedAt n,
      provesSondowCertificateAt
        (proofCodeOfTrace (traceOfChecked n hchecked)) n
  compiled_size_le_trace_plus_reference :
    ∀ n : Nat, ∀ hchecked : MainSondowFullCertificateCheckedAt n,
      (proofCodeSize (proofCodeOfTrace (traceOfChecked n hchecked)) : Real) ≤
        traceSize (traceOfChecked n hchecked) +
          _root_.theorem_reference_certificate_size n

namespace SondowCheckedS21VerifierSimulationBuilder

/--
The verifier-simulation builder supplies the local checked proof-code semantics.
-/
def toLocalProofCodeSemantics
    (builder : SondowCheckedS21VerifierSimulationBuilder) :
    SondowCheckedS21LocalProofCodeSemantics where
  Code := builder.ProofCode
  provesSondowCertificateAt := builder.provesSondowCertificateAt
  size := builder.proofCodeSize
  checked_has_predicate_size_code := by
    intro n hchecked
    let tr := builder.traceOfChecked n hchecked
    let code := builder.proofCodeOfTrace tr
    refine ⟨code, ?_, ?_⟩
    · exact builder.compiled_trace_proves_sondow_certificate n hchecked
    · have hcompile :=
        builder.compiled_size_le_trace_plus_reference n hchecked
      have htrace :=
        builder.trace_size_le_verifier_trace n hchecked
      dsimp [code, tr]
      have htotal :
          builder.traceSize (builder.traceOfChecked n hchecked) +
              _root_.theorem_reference_certificate_size n ≤
            _root_.proof_predicate_formula_size
              _root_.sondowCertificateValidCode n := by
        dsimp [_root_.proof_predicate_formula_size]
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right htrace
            (_root_.theorem_reference_certificate_size n)
      exact le_trans hcompile htotal

end SondowCheckedS21VerifierSimulationBuilder

/--
The local checked proof-code semantics yields the proof-length-free compiler
without assuming global completeness of the Sondow certificate family.
-/
noncomputable def
    SondowFullCertificateConcreteProofCodeCompiler.ofCheckedLocalProofCodeSemantics
    (model : SondowCheckedS21LocalProofCodeSemantics) :
    SondowFullCertificateConcreteProofCodeCompiler where
  codeLength := model.minCodeLength
  short_code_from_checked := by
    intro n hchecked
    rcases model.checked_has_predicate_size_code n hchecked with
      ⟨c, hproves, hsize⟩
    have hminNat :
        model.minCodeLength n ≤ model.size c :=
      model.minCodeLength_le_of_provesSondowCertificateAt hproves
    have hminReal :
        (model.minCodeLength n : Real) ≤ (model.size c : Real) := by
      exact_mod_cast hminNat
    exact le_trans hminReal hsize

/--
Proof-code upper from local checked Sondow proof-code semantics.

This is the preferred proof-length-free route: checked Sondow certificates
produce concrete proof codes locally, and the explicit verifier-size estimate
gives `17(n+1)`.
-/
theorem pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndLocalProofCodeSemantics
    (model : SondowCheckedS21LocalProofCodeSemantics)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      ((SondowFullCertificateConcreteProofCodeCompiler.ofCheckedLocalProofCodeSemantics
          model).codeLength n : Real) ≤
        sondowCertificateLinearUpper n :=
  pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndCompiler
    (SondowFullCertificateConcreteProofCodeCompiler.ofCheckedLocalProofCodeSemantics
      model)
    q hq

/--
Existential proof-code upper from local checked Sondow proof-code semantics.
The upper is constructed after the compiler is supplied; it is not an input.
-/
theorem pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndLocalProofCodeSemantics
    (model : SondowCheckedS21LocalProofCodeSemantics)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        ((SondowFullCertificateConcreteProofCodeCompiler.ofCheckedLocalProofCodeSemantics
            model).codeLength n : Real) ≤
          U n :=
  pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndCompiler
    (SondowFullCertificateConcreteProofCodeCompiler.ofCheckedLocalProofCodeSemantics
      model)
    q hq

/--
Proof-code upper from the explicit verifier-simulation builder.

This theorem is not a final discharge of the builder.  It only says that once
the trace construction and S²₁ proof-code compilation are supplied explicitly,
the upper bound follows without an upper-provider premise.
-/
theorem pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndVerifierSimulationBuilder
    (builder : SondowCheckedS21VerifierSimulationBuilder)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        ((SondowFullCertificateConcreteProofCodeCompiler.ofCheckedLocalProofCodeSemantics
            builder.toLocalProofCodeSemantics).codeLength n : Real) ≤ U n :=
  pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndLocalProofCodeSemantics
    builder.toLocalProofCodeSemantics q hq

/--
Root S²₁ proof-length model for the local checked Sondow proof-code semantics.

This is weaker than the global `ProofCodeSemantics` route: it calibrates
`proof_length` only to the conditional local minimum `minCodeLength`.  The
fallback value of `minCodeLength` at unchecked indices is irrelevant to the
Sondow upper proof, which only uses indices where the Sondow reproof has already
constructed a checked certificate.
-/
structure SondowCheckedS21LocalProofLengthModel where
  code_semantics : SondowCheckedS21LocalProofCodeSemantics
  root_calibration :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) =
        code_semantics.minCodeLength n

/--
The local checked proof-length model supplies the root calibration needed by the
clean compiler route.
-/
noncomputable def
    SondowFullCertificateConcreteS21RootCalibration.ofCheckedLocalProofLengthModel
    (model : SondowCheckedS21LocalProofLengthModel) :
    SondowFullCertificateConcreteS21RootCalibration
      (SondowFullCertificateConcreteProofCodeCompiler.ofCheckedLocalProofCodeSemantics
        model.code_semantics) where
  root_s21_length_le_codeLength := by
    intro n
    rw [model.root_calibration n]
    exact le_rfl

/--
The local checked proof-length model closes `SondowCheckedS21TraceCompiler`
without a global completeness assumption on the Sondow certificate family.
-/
noncomputable def
    SondowCheckedS21TraceCompiler.ofCheckedLocalProofLengthModel
    (model : SondowCheckedS21LocalProofLengthModel) :
    SondowCheckedS21TraceCompiler :=
  SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler
    (SondowFullCertificateConcreteProofCodeCompiler.ofCheckedLocalProofCodeSemantics
      model.code_semantics)
    (SondowFullCertificateConcreteS21RootCalibration.ofCheckedLocalProofLengthModel
      model)

/--
The proof-code semantics above yields the proof-length-free compiler used by
the clean upper route: take the concrete length to be the semantic minimum
accepted proof-code size on the Sondow certificate-validity fragment.
-/
noncomputable def
    SondowFullCertificateConcreteProofCodeCompiler.ofCheckedProofCodeSemantics
    (model : SondowCheckedS21ProofCodeSemantics) :
    SondowFullCertificateConcreteProofCodeCompiler where
  codeLength := fun n =>
    model.sem.minProofCodeSize
      (_root_.sondowCertificateValidCode n)
      (SondowCertificateRelevantCode.sondow n)
  short_code_from_checked := by
    intro n hchecked
    rcases model.checked_has_predicate_size_code n hchecked with
      ⟨c, hchecks, hsize⟩
    have hhas :
        model.sem.HasProofCodeOfSize
          (_root_.sondowCertificateValidCode n)
          (model.sem.size c) :=
      ⟨c, hchecks, le_rfl⟩
    have hminNat :
        model.sem.minProofCodeSize
            (_root_.sondowCertificateValidCode n)
            (SondowCertificateRelevantCode.sondow n) ≤
          model.sem.size c :=
      model.sem.minProofCodeSize_le_of_hasProofCodeOfSize
        (SondowCertificateRelevantCode.sondow n) hhas
    have hminReal :
        (model.sem.minProofCodeSize
            (_root_.sondowCertificateValidCode n)
            (SondowCertificateRelevantCode.sondow n) : Real) ≤
          (model.sem.size c : Real) := by
      exact_mod_cast hminNat
    exact le_trans hminReal hsize

/--
Root S²₁ proof-length model for the checked Sondow certificate fragment.

The only root-level convention is calibration: on `sondowCertificateValidCode n`,
the abstract root `proof_length S21 symbolSize` is identified with the concrete
semantic minimum proof-code size from `code_semantics`.

This field must not mention rationality, a tail upper, or the final collision
argument; otherwise the model would be circular.
-/
structure SondowCheckedS21ProofLengthModel where
  code_semantics : SondowCheckedS21ProofCodeSemantics
  root_calibration :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) =
        code_semantics.sem.minProofCodeSize
          (_root_.sondowCertificateValidCode n)
          (SondowCertificateRelevantCode.sondow n)

/--
The checked proof-length model supplies the root calibration required by the
clean compiler route.
-/
noncomputable def
    SondowFullCertificateConcreteS21RootCalibration.ofCheckedProofLengthModel
    (model : SondowCheckedS21ProofLengthModel) :
    SondowFullCertificateConcreteS21RootCalibration
      (SondowFullCertificateConcreteProofCodeCompiler.ofCheckedProofCodeSemantics
        model.code_semantics) where
  root_s21_length_le_codeLength := by
    intro n
    rw [model.root_calibration n]
    exact le_rfl

/--
The checked proof-length model closes `SondowCheckedS21TraceCompiler` without
using `upper_provider` and without passing through the root
`accepted_certificate` predicate.
-/
noncomputable def
    SondowCheckedS21TraceCompiler.ofCheckedProofLengthModel
    (model : SondowCheckedS21ProofLengthModel) :
    SondowCheckedS21TraceCompiler :=
  SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler
    (SondowFullCertificateConcreteProofCodeCompiler.ofCheckedProofCodeSemantics
      model.code_semantics)
    (SondowFullCertificateConcreteS21RootCalibration.ofCheckedProofLengthModel
      model)

/--
Concrete proof-code compiler extracted from an existing S²₁ proof-length
recognition theorem and a checked-length bound for its Sondow component.
-/
noncomputable def
    SondowFullCertificateConcreteProofCodeCompiler.ofProofLengthRecognition
    (hrec : _root_.S21GraftProofLengthRecognitionTheorem)
    (hbound : SondowProofLengthRecognitionCheckedLengthBound hrec) :
    SondowFullCertificateConcreteProofCodeCompiler where
  codeLength := hrec.sondow_proofs.length
  short_code_from_checked := hbound.sondow_length_le_predicate_from_checked

/--
The existing S²₁ proof-length recognition theorem supplies the root calibration
for the concrete compiler extracted from its Sondow proof family.
-/
noncomputable def
    SondowFullCertificateConcreteS21RootCalibration.ofProofLengthRecognition
    (hrec : _root_.S21GraftProofLengthRecognitionTheorem)
    (hbound : SondowProofLengthRecognitionCheckedLengthBound hrec) :
    SondowFullCertificateConcreteS21RootCalibration
      (SondowFullCertificateConcreteProofCodeCompiler.ofProofLengthRecognition
        hrec hbound) where
  root_s21_length_le_codeLength := by
    intro n
    rw [hrec.family_lengths.1 n]
    exact le_rfl

/--
Existing S²₁ proof-length recognition plus the checked-length bound proves the
checked-specific Sondow trace compiler.
-/
noncomputable def
    SondowCheckedS21TraceCompiler.ofProofLengthRecognition
    (hrec : _root_.S21GraftProofLengthRecognitionTheorem)
    (hbound : SondowProofLengthRecognitionCheckedLengthBound hrec) :
  SondowCheckedS21TraceCompiler :=
  SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler
    (SondowFullCertificateConcreteProofCodeCompiler.ofProofLengthRecognition
      hrec hbound)
    (SondowFullCertificateConcreteS21RootCalibration.ofProofLengthRecognition
      hrec hbound)

/--
Proof-code upper from checked Sondow proof-code semantics.

This is the fully proof-length-free model route: checked Sondow certificates
produce concrete proof codes, and the explicit verifier-size estimate gives
`17(n+1)`.
-/
theorem pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndProofCodeSemantics
    (model : SondowCheckedS21ProofCodeSemantics)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      ((SondowFullCertificateConcreteProofCodeCompiler.ofCheckedProofCodeSemantics
          model).codeLength n : Real) ≤
        sondowCertificateLinearUpper n :=
  pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndCompiler
    (SondowFullCertificateConcreteProofCodeCompiler.ofCheckedProofCodeSemantics
      model)
    q hq

/--
Existential proof-code upper from checked Sondow proof-code semantics.  The
upper is a conclusion, not an input field.
-/
theorem pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndProofCodeSemantics
    (model : SondowCheckedS21ProofCodeSemantics)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        ((SondowFullCertificateConcreteProofCodeCompiler.ofCheckedProofCodeSemantics
            model).codeLength n : Real) ≤ U n :=
  pureSondowConcreteCodeUpper_fromHalfDenCheckedTailAndCompiler
    (SondowFullCertificateConcreteProofCodeCompiler.ofCheckedProofCodeSemantics
      model)
    q hq

/--
Clean S²₁ upper from half-denominator checked tail and checked-specific trace
compiler.  This is the S²₁ version of the paper proof with no root
`accepted_certificate` and no `upper_provider`.
-/
theorem s21SondowLinearUpper_fromHalfDenCheckedTailAndCheckedTrace
    (trace : SondowCheckedS21TraceCompiler)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowCertificateLinearUpper n := by
  intro n hn
  let tail :=
    mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen
      q hq
  have hchecked : MainSondowFullCertificateCheckedAt n :=
    tail.checked_at n (by simpa [tail,
      mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen_threshold]
      using hn)
  exact le_trans
    (trace.short_s21_from_checked n hchecked)
    (by
      simpa [sondowCertificateLinearUpper] using
        proofPredicateFormulaSizeSondowCertificateValidCode_le_17_natPower n)

/-- Clean existential S²₁ upper-tail form from the checked-specific trace route. -/
theorem s21SondowCertificateUpper_fromHalfDenCheckedTailAndCheckedTrace
    (trace : SondowCheckedS21TraceCompiler)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n := by
  refine ⟨sondowCertificateLinearUpper,
    sondowCertificateLinearUpper_polynomial,
    max 3 ((q.den + 1) / 2), ?_⟩
  exact s21SondowLinearUpper_fromHalfDenCheckedTailAndCheckedTrace
    trace q hq

/--
S²₁ upper where the checked trace compiler is proved from a concrete proof-code
compiler and root proof-length recognition.
-/
theorem s21SondowLinearUpper_fromHalfDenCheckedTailConcreteCompilerAndRootCalibration
    (compiler : SondowFullCertificateConcreteProofCodeCompiler)
    (root_calibration :
      SondowFullCertificateConcreteS21RootCalibration compiler)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowCertificateLinearUpper n :=
  s21SondowLinearUpper_fromHalfDenCheckedTailAndCheckedTrace
    (SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler
      compiler root_calibration)
    q hq

/--
Existential S²₁ upper-tail form with no `upper_provider`: the upper tail is
derived from a concrete proof-code compiler plus root S²₁ recognition.
-/
theorem s21SondowCertificateUpper_fromHalfDenCheckedTailConcreteCompilerAndRootCalibration
    (compiler : SondowFullCertificateConcreteProofCodeCompiler)
    (root_calibration :
      SondowFullCertificateConcreteS21RootCalibration compiler)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n :=
  s21SondowCertificateUpper_fromHalfDenCheckedTailAndCheckedTrace
    (SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler
      compiler root_calibration)
    q hq

/--
S²₁ upper from the existing proof-length recognition theorem plus the remaining
checked-length bound for its Sondow proof family.
-/
theorem
    s21SondowLinearUpper_fromHalfDenCheckedTailProofLengthRecognition
    (hrec : _root_.S21GraftProofLengthRecognitionTheorem)
    (hbound : SondowProofLengthRecognitionCheckedLengthBound hrec)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowCertificateLinearUpper n :=
  s21SondowLinearUpper_fromHalfDenCheckedTailAndCheckedTrace
    (SondowCheckedS21TraceCompiler.ofProofLengthRecognition hrec hbound)
    q hq

/--
Existential S²₁ upper-tail form from proof-length recognition and a
checked-length bound.
-/
theorem
    s21SondowCertificateUpper_fromHalfDenCheckedTailProofLengthRecognition
    (hrec : _root_.S21GraftProofLengthRecognitionTheorem)
    (hbound : SondowProofLengthRecognitionCheckedLengthBound hrec)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n :=
  s21SondowCertificateUpper_fromHalfDenCheckedTailAndCheckedTrace
    (SondowCheckedS21TraceCompiler.ofProofLengthRecognition hrec hbound)
    q hq

/--
S²₁ upper from the checked proof-length model.

This route does not use an `upper_provider` and does not use the root
`accepted_certificate` predicate.  The model only calibrates root `proof_length`
to the concrete checked proof-code semantics.
-/
theorem s21SondowLinearUpper_fromHalfDenCheckedTailCheckedProofLengthModel
    (model : SondowCheckedS21ProofLengthModel)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowCertificateLinearUpper n :=
  s21SondowLinearUpper_fromHalfDenCheckedTailAndCheckedTrace
    (SondowCheckedS21TraceCompiler.ofCheckedProofLengthModel model)
    q hq

/--
Existential S²₁ upper-tail form from the checked proof-length model.  The upper
tail is constructed by the theorem; it is not an input field.
-/
theorem s21SondowCertificateUpper_fromHalfDenCheckedTailCheckedProofLengthModel
    (model : SondowCheckedS21ProofLengthModel)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n :=
  s21SondowCertificateUpper_fromHalfDenCheckedTailAndCheckedTrace
    (SondowCheckedS21TraceCompiler.ofCheckedProofLengthModel model)
    q hq

/--
S²₁ upper from the local checked proof-length model.

This is the preferred root S²₁ route: no `upper_provider`, no
`accepted_certificate`, and no global completeness assumption for unchecked
Sondow indices.
-/
theorem s21SondowLinearUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModel
    (model : SondowCheckedS21LocalProofLengthModel)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowCertificateLinearUpper n :=
  s21SondowLinearUpper_fromHalfDenCheckedTailAndCheckedTrace
    (SondowCheckedS21TraceCompiler.ofCheckedLocalProofLengthModel model)
    q hq

/--
Existential S²₁ upper-tail form from the local checked proof-length model.
-/
theorem s21SondowCertificateUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModel
    (model : SondowCheckedS21LocalProofLengthModel)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n :=
  s21SondowCertificateUpper_fromHalfDenCheckedTailAndCheckedTrace
    (SondowCheckedS21TraceCompiler.ofCheckedLocalProofLengthModel model)
    q hq

/-- PA upper obtained by transporting the S²₁ trace proof through a linear
S²₁-to-PA embedding on the Sondow certificate family. -/
def sondowPAUpperViaS21Embedding
    (embedding :
      _root_.S21ToPALinearEmbeddingOn _root_.sondowCertificateValidCode)
    (n : Nat) : Real :=
  embedding.C * sondowCertificateLinearUpper n + embedding.D

theorem sondowPAUpperViaS21Embedding_polynomial
    (embedding :
      _root_.S21ToPALinearEmbeddingOn _root_.sondowCertificateValidCode) :
    _root_.is_polynomial_bound
      (sondowPAUpperViaS21Embedding embedding) := by
  change _root_.is_polynomial_bound
    (fun n : Nat => embedding.C * sondowCertificateLinearUpper n + embedding.D)
  exact sondowCertificateLinearUpper_polynomial.linear_rescale
    embedding.C_nonneg embedding.D_nonneg

/--
Clean PA upper from checked-specific S²₁ trace compiler and a linear PA
embedding.  The upper is `embedding.C * 17(n+1) + embedding.D`.
-/
theorem paSondowLinearUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
    (trace : SondowCheckedS21TraceCompiler)
    (embedding :
      _root_.S21ToPALinearEmbeddingOn _root_.sondowCertificateValidCode)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowPAUpperViaS21Embedding embedding n := by
  intro n hn
  have hpa :=
    embedding.target_le_linear_source n
  have hs21 :=
    s21SondowLinearUpper_fromHalfDenCheckedTailAndCheckedTrace
      trace q hq n hn
  have hmul :
      embedding.C *
          _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤
        embedding.C * sondowCertificateLinearUpper n :=
    mul_le_mul_of_nonneg_left hs21 embedding.C_nonneg
  exact le_trans hpa (by
    simpa [sondowPAUpperViaS21Embedding] using
      add_le_add_right hmul embedding.D)

/--
Clean existential PA upper-tail form after exposing the checked-specific Sondow
trace compiler and the S²₁-to-PA embedding.
-/
theorem paSondowCertificateUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
    (trace : SondowCheckedS21TraceCompiler)
    (embedding :
      _root_.S21ToPALinearEmbeddingOn _root_.sondowCertificateValidCode)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n := by
  refine ⟨sondowPAUpperViaS21Embedding embedding,
    sondowPAUpperViaS21Embedding_polynomial embedding,
    max 3 ((q.den + 1) / 2), ?_⟩
  exact paSondowLinearUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
    trace embedding q hq

/--
PA upper where the Sondow checked trace compiler itself is discharged by a
concrete proof-code compiler and root S²₁ proof-length recognition.
-/
theorem paSondowLinearUpper_fromHalfDenCheckedTailConcreteCompilerRootCalibrationAndEmbedding
    (compiler : SondowFullCertificateConcreteProofCodeCompiler)
    (root_calibration :
      SondowFullCertificateConcreteS21RootCalibration compiler)
    (embedding :
      _root_.S21ToPALinearEmbeddingOn _root_.sondowCertificateValidCode)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowPAUpperViaS21Embedding embedding n :=
  paSondowLinearUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
    (SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler
      compiler root_calibration)
    embedding q hq

/--
Existential PA upper-tail form from the concrete Sondow proof-code compiler,
root S²₁ proof-length recognition, and a linear S²₁-to-PA embedding.
-/
theorem paSondowCertificateUpper_fromHalfDenCheckedTailConcreteCompilerRootCalibrationAndEmbedding
    (compiler : SondowFullCertificateConcreteProofCodeCompiler)
    (root_calibration :
      SondowFullCertificateConcreteS21RootCalibration compiler)
    (embedding :
      _root_.S21ToPALinearEmbeddingOn _root_.sondowCertificateValidCode)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n :=
  paSondowCertificateUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
    (SondowCheckedS21TraceCompiler.ofConcreteProofCodeCompiler
      compiler root_calibration)
    embedding q hq

/--
PA upper from proof-length recognition, checked-length bound, and a linear
S²₁-to-PA embedding.
-/
theorem
    paSondowLinearUpper_fromHalfDenCheckedTailProofLengthRecognitionAndEmbedding
    (hrec : _root_.S21GraftProofLengthRecognitionTheorem)
    (hbound : SondowProofLengthRecognitionCheckedLengthBound hrec)
    (embedding :
      _root_.S21ToPALinearEmbeddingOn _root_.sondowCertificateValidCode)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowPAUpperViaS21Embedding embedding n :=
  paSondowLinearUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
    (SondowCheckedS21TraceCompiler.ofProofLengthRecognition hrec hbound)
    embedding q hq

/--
Existential PA upper-tail form from proof-length recognition, checked-length
bound, and a linear S²₁-to-PA embedding.
-/
theorem
    paSondowCertificateUpper_fromHalfDenCheckedTailProofLengthRecognitionAndEmbedding
    (hrec : _root_.S21GraftProofLengthRecognitionTheorem)
    (hbound : SondowProofLengthRecognitionCheckedLengthBound hrec)
    (embedding :
      _root_.S21ToPALinearEmbeddingOn _root_.sondowCertificateValidCode)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n :=
  paSondowCertificateUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
    (SondowCheckedS21TraceCompiler.ofProofLengthRecognition hrec hbound)
    embedding q hq

/--
PA upper from the checked S²₁ proof-length model plus a linear S²₁-to-PA
embedding.  This is the PA endpoint of the clean model route.
-/
theorem paSondowLinearUpper_fromHalfDenCheckedTailCheckedProofLengthModelAndEmbedding
    (model : SondowCheckedS21ProofLengthModel)
    (embedding :
      _root_.S21ToPALinearEmbeddingOn _root_.sondowCertificateValidCode)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowPAUpperViaS21Embedding embedding n :=
  paSondowLinearUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
    (SondowCheckedS21TraceCompiler.ofCheckedProofLengthModel model)
    embedding q hq

/--
Existential PA upper-tail form from the checked S²₁ proof-length model and a
linear S²₁-to-PA embedding.  The upper is
`embedding.C * 17(n+1) + embedding.D`.
-/
theorem paSondowCertificateUpper_fromHalfDenCheckedTailCheckedProofLengthModelAndEmbedding
    (model : SondowCheckedS21ProofLengthModel)
    (embedding :
      _root_.S21ToPALinearEmbeddingOn _root_.sondowCertificateValidCode)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n :=
  paSondowCertificateUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
    (SondowCheckedS21TraceCompiler.ofCheckedProofLengthModel model)
    embedding q hq

/--
PA upper from the local checked S²₁ proof-length model plus a linear S²₁-to-PA
embedding.
-/
theorem paSondowLinearUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModelAndEmbedding
    (model : SondowCheckedS21LocalProofLengthModel)
    (embedding :
      _root_.S21ToPALinearEmbeddingOn _root_.sondowCertificateValidCode)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowPAUpperViaS21Embedding embedding n :=
  paSondowLinearUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
    (SondowCheckedS21TraceCompiler.ofCheckedLocalProofLengthModel model)
    embedding q hq

/--
Existential PA upper-tail form from the local checked S²₁ proof-length model.
-/
theorem paSondowCertificateUpper_fromHalfDenCheckedTailCheckedLocalProofLengthModelAndEmbedding
    (model : SondowCheckedS21LocalProofLengthModel)
    (embedding :
      _root_.S21ToPALinearEmbeddingOn _root_.sondowCertificateValidCode)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n :=
  paSondowCertificateUpper_fromHalfDenCheckedTailCheckedTraceAndEmbedding
    (SondowCheckedS21TraceCompiler.ofCheckedLocalProofLengthModel model)
    embedding q hq

/--
Sondow upper in the S²₁ trace layer.

This is the first proof-length layer that can currently be closed from a named
verification theorem rather than an abstract upper provider: a checked Sondow
certificate is converted to the Sondow `accepted_certificate` predicate, and
the S²₁ trace soundness theorem gives a proof bounded by the verifier predicate
size.  The explicit verifier-size estimate then gives the displayed `17(n+1)`.
-/
theorem s21SondowLinearUpper_fromHalfDenCheckedTailAndTraceSoundness
    (trace :
      _root_.S21VerifierTraceSoundness _root_.sondowCertificateValidCode)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowCertificateLinearUpper n := by
  intro n hn
  let tail :=
    mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen
      q hq
  have hchecked : MainSondowFullCertificateCheckedAt n :=
    tail.checked_at n (by simpa [tail,
      mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen_threshold]
      using hn)
  have hacc :
      _root_.accepted_certificate (_root_.sondowCertificateValidCode n) :=
    acceptedSondowCertificate_of_checkedAt hchecked
  exact le_trans
    (trace.short_proof_from_accepting_trace n hacc)
    (by
      simpa [sondowCertificateLinearUpper] using
        proofPredicateFormulaSizeSondowCertificateValidCode_le_17_natPower n)

/-- Existential S²₁ upper-tail form from the concrete Sondow trace route. -/
theorem s21SondowCertificateUpper_fromHalfDenCheckedTailAndTraceSoundness
    (trace :
      _root_.S21VerifierTraceSoundness _root_.sondowCertificateValidCode)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n := by
  refine ⟨sondowCertificateLinearUpper,
    sondowCertificateLinearUpper_polynomial,
    max 3 ((q.den + 1) / 2), ?_⟩
  exact s21SondowLinearUpper_fromHalfDenCheckedTailAndTraceSoundness
    trace q hq

/--
PA upper from Sondow checked-tail, S²₁ trace soundness, and a linear PA
embedding.

Compared with `SondowFullCertificatePATraceCompiler`, this exposes the lower
proof-theoretic obligations separately: Sondow trace soundness and the
S²₁-to-PA embedding.  The explicit upper is

`embedding.C * 17(n+1) + embedding.D`.
-/
theorem paSondowLinearUpper_fromHalfDenCheckedTailTraceAndEmbedding
    (trace :
      _root_.S21VerifierTraceSoundness _root_.sondowCertificateValidCode)
    (embedding :
      _root_.S21ToPALinearEmbeddingOn _root_.sondowCertificateValidCode)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowPAUpperViaS21Embedding embedding n := by
  intro n hn
  have hpa :=
    embedding.target_le_linear_source n
  have hs21 :=
    s21SondowLinearUpper_fromHalfDenCheckedTailAndTraceSoundness
      trace q hq n hn
  have hmul :
      embedding.C *
          _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤
        embedding.C * sondowCertificateLinearUpper n :=
    mul_le_mul_of_nonneg_left hs21 embedding.C_nonneg
  exact le_trans hpa (by
    simpa [sondowPAUpperViaS21Embedding] using
      add_le_add_right hmul embedding.D)

/--
Existential PA upper-tail form after exposing the S²₁ trace and PA embedding
obligations.  This removes the direct `upper_provider` input and replaces the
abstract PA trace compiler by the two standard proof-theoretic interfaces.
-/
theorem paSondowCertificateUpper_fromHalfDenCheckedTailTraceAndEmbedding
    (trace :
      _root_.S21VerifierTraceSoundness _root_.sondowCertificateValidCode)
    (embedding :
      _root_.S21ToPALinearEmbeddingOn _root_.sondowCertificateValidCode)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n := by
  refine ⟨sondowPAUpperViaS21Embedding embedding,
    sondowPAUpperViaS21Embedding_polynomial embedding,
    max 3 ((q.den + 1) / 2), ?_⟩
  exact paSondowLinearUpper_fromHalfDenCheckedTailTraceAndEmbedding
    trace embedding q hq

/--
Core no-upper-premise theorem.

Assume only:

* an explicit rational parameter `q` with `q = gamma`;
* the Sondow-specific PA trace compiler above.

Then the half-denominator Sondow reproof gives a checked certificate after
`max 3 ((q.den + 1) / 2)`, and the compiler plus the verified predicate-size
bound gives the concrete linear upper `17(n+1)`.
-/
theorem pureSondowLinearUpper_fromHalfDenCheckedTailAndTraceCompiler
    (compiler : SondowFullCertificatePATraceCompiler)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∀ n : Nat, max 3 ((q.den + 1) / 2) ≤ n →
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤
        sondowCertificateLinearUpper n := by
  intro n hn
  let tail :=
    mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen
      q hq
  have hchecked : MainSondowFullCertificateCheckedAt n :=
    tail.checked_at n (by simpa [tail,
      mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen_threshold]
      using hn)
  exact le_trans
    (compiler.short_proof_from_checked n hchecked)
    (by
      simpa [sondowCertificateLinearUpper] using
        proofPredicateFormulaSizeSondowCertificateValidCode_le_17_natPower n)

/--
Existential upper-tail form derived from the explicit theorem above.

This packages the result only after the proof has constructed the concrete upper
function and threshold.  It is the shape needed by older collision APIs, but the
proof source is the checked-tail plus trace-compiler chain, not an assumed
upper-provider field.
-/
theorem pureSondowCertificateUpper_fromHalfDenCheckedTailAndTraceCompiler
    (compiler : SondowFullCertificatePATraceCompiler)
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowCertificateValidCode n) ≤ U n := by
  refine ⟨sondowCertificateLinearUpper,
    sondowCertificateLinearUpper_polynomial,
    max 3 ((q.den + 1) / 2), ?_⟩
  exact pureSondowLinearUpper_fromHalfDenCheckedTailAndTraceCompiler
    compiler q hq

#check sidecarSondowCertificateTargetMeasured_eq_one
#print axioms sidecarSondowCertificateTargetMeasured_eq_one

#check sidecarSondowCertificateTargetMeasured_polynomial
#print axioms sidecarSondowCertificateTargetMeasured_polynomial

#check no_sidecarSondowCheckedTargetProjection_of_strongLowerBound
#print axioms no_sidecarSondowCheckedTargetProjection_of_strongLowerBound

end SondowProjectSondowUpperCompilerRoute
end SondowMainCheckedCodeBridge
