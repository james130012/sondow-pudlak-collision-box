import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
import integration.FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixPublicBounds
import integration.FoundationCompactNumericListedDirectNegationFormulaTagPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resources for formula-transform output rows

The seven checked output branches are charged from their actual child graph
certificates.  Branch selection changes only the connective skeleton; no
payload bound is accepted from the caller.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsPublicBounds

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactBinaryNumeralTerm
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABitMembershipValuationContextCompilerBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixPublicBounds
open FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate
open FoundationCompactNumericListedDirectNegationFormulaTagPublicBounds

private abbrev outputRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate.zeroValuation

def outputRowsNativeEqStructuralEnvelope
    (left right : ValuationTerm) : Nat :=
  compilePositiveRelationPayloadResource outputRowsZeroValuation
    Language.Eq.eq ![left, right]

theorem nativeEqCertificate_structuralPayloadBound_le_transparent
    (left right : ValuationTerm)
    (hequal : termValue outputRowsZeroValuation left =
      termValue outputRowsZeroValuation right) :
    hybridFormulaStructuralPayloadBound
        (nativeEqCertificate left right hequal) <=
      outputRowsNativeEqStructuralEnvelope left right := by
  simp only [nativeEqCertificate,
    outputRowsNativeEqStructuralEnvelope]
  exact le_rfl

def outputRowsNativeNeStructuralEnvelope
    (left right : ValuationTerm) : Nat :=
  compileNegativeRelationPayloadResource outputRowsZeroValuation
    Language.Eq.eq ![left, right]

theorem nativeNeCertificate_structuralPayloadBound_le_transparent
    (left right : ValuationTerm)
    (hne : ¬termValue outputRowsZeroValuation left =
      termValue outputRowsZeroValuation right) :
    hybridFormulaStructuralPayloadBound
        (nativeNeCertificate left right hne) <=
      outputRowsNativeNeStructuralEnvelope left right := by
  simp only [nativeNeCertificate,
    outputRowsNativeNeStructuralEnvelope]
  exact le_rfl

def outputRowsNativeLeStructuralEnvelope
    (left right : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![left, right]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables
    outputRowsZeroValuation
  compilePositiveRelationPayloadResource outputRowsZeroValuation
      Language.Eq.eq args +
    compilePositiveRelationPayloadResource outputRowsZeroValuation
      Language.ORing.Rel.lt args +
    weakeningFullAssemblyCost (insert equalityFormula Gamma) +
    weakeningFullAssemblyCost (insert strictFormula Gamma) +
    disjunctionFullAssemblyCost Gamma equalityFormula strictFormula

theorem nativeLeCertificate_structuralPayloadBound_le_transparent
    (left right : ValuationTerm)
    (hle : termValue outputRowsZeroValuation left <=
      termValue outputRowsZeroValuation right) :
    hybridFormulaStructuralPayloadBound
        (nativeLeCertificate left right hle) <=
      outputRowsNativeLeStructuralEnvelope left right := by
  let args : Fin 2 -> ValuationTerm := ![left, right]
  by_cases hequal : termValue outputRowsZeroValuation left =
      termValue outputRowsZeroValuation right
  · simp only [nativeLeCertificate, nativeLeCertificateCore, nativeLeFormula]
    rw [dif_pos hequal]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold outputRowsNativeLeStructuralEnvelope
    dsimp only [args, outputRowsZeroValuation]
    omega
  · simp only [nativeLeCertificate, nativeLeCertificateCore, nativeLeFormula]
    rw [dif_neg hequal]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold outputRowsNativeLeStructuralEnvelope
    dsimp only [args, outputRowsZeroValuation]
    omega

def outputRowsCountFormula
    (current next : CompactFormulaTransformStateRowCoordinates)
    (consumedCount : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm current.parserTokensCount)
    (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
      (shortBinaryNumeralTerm next.parserTokensCount))

def outputRowsZeroCaseFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (consumedCount : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm consumedCount)
      (‘0’ : ValuationTerm) ⋏
    compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
      current.outputBoundary current.outputCount next.outputBoundary
      next.outputCount

def outputRowsRawCaseFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode consumedCount : Nat) : ValuationFormula :=
  rawModeFormula (shortBinaryNumeralTerm mode) ⋏
    compactAdditiveNatListAppendSourcePrefixClosedFormula
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount

def outputRowsSameFourCaseFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm mode) (‘4’ : ValuationTerm) ⋏
    compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
      current.outputBoundary current.outputCount next.outputBoundary
      next.outputCount

def outputRowsMappedTailFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (tag consumedCount mappedHead : Nat) : ValuationFormula :=
  compactNegationFormulaTagClosedFormula tag mappedHead ⋏
    compactAdditiveNatListAppendMappedSourcePrefixClosedFormula
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputBoundary next.outputCount mappedHead

def outputRowsMappedCaseFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat) : ValuationFormula :=
  otherModeWithTailFormula (shortBinaryNumeralTerm mode)
    (outputRowsMappedTailFormula tokenTable width tokenCount current next tag
      consumedCount mappedHead)

def outputRowsPositiveBodyFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat) : ValuationFormula :=
  outputRowsRawCaseFormula tokenTable width tokenCount current next mode
      consumedCount ⋎
    (outputRowsSameFourCaseFormula tokenTable width tokenCount current next
        mode ⋎
      outputRowsMappedCaseFormula tokenTable width tokenCount current next
        mode tag consumedCount mappedHead)

def outputRowsPositiveCaseFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat) : ValuationFormula :=
  nativeLeFormula (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm consumedCount) ⋏
    outputRowsPositiveBodyFormula tokenTable width tokenCount current next
      mode tag consumedCount mappedHead

def outputRowsCasesFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat) : ValuationFormula :=
  outputRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount ⋎
    outputRowsPositiveCaseFormula tokenTable width tokenCount current next
      mode tag consumedCount mappedHead

private theorem outputRowsArithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_nativeAddTerm
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (nativeAddTerm left right) =
      termValue valuation left + termValue valuation right := by
  unfold nativeAddTerm
  rw [outputRowsArithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_outputRowsZero :
    termValue outputRowsZeroValuation (‘0’ : ValuationTerm) = 0 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

private theorem termValue_outputRowsOne :
    termValue outputRowsZeroValuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one outputRowsZeroValuation ![]

private theorem termValue_outputRowsTwo :
    termValue outputRowsZeroValuation (‘2’ : ValuationTerm) = 2 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

private theorem termValue_outputRowsFour :
    termValue outputRowsZeroValuation (‘4’ : ValuationTerm) = 4 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

private theorem termValue_outputRowsFive :
    termValue outputRowsZeroValuation (‘5’ : ValuationTerm) = 5 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

theorem consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
    (current next : CompactFormulaTransformStateRowCoordinates)
    (consumedCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount) :
    hybridFormulaStructuralPayloadBound
        (consumedCountEqualityCertificate current next consumedCount hcount) <=
      outputRowsNativeEqStructuralEnvelope
        (shortBinaryNumeralTerm current.parserTokensCount)
        (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm next.parserTokensCount)) := by
  have hequal : termValue outputRowsZeroValuation
      (shortBinaryNumeralTerm current.parserTokensCount) =
        termValue outputRowsZeroValuation
          (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm next.parserTokensCount)) := by
    simpa [termValue_shortBinaryNumeralTerm, termValue_nativeAddTerm] using
      hcount
  simpa only [consumedCountEqualityCertificate] using
    nativeEqCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm current.parserTokensCount)
      (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm next.parserTokensCount)) hequal

theorem consumedCountZeroCertificate_structuralPayloadBound_le_transparent
    (consumedCount : Nat) (hzero : consumedCount = 0) :
    hybridFormulaStructuralPayloadBound
        (consumedCountZeroCertificate consumedCount hzero) <=
      outputRowsNativeEqStructuralEnvelope
        (shortBinaryNumeralTerm consumedCount) (‘0’ : ValuationTerm) := by
  have hequal : termValue outputRowsZeroValuation
      (shortBinaryNumeralTerm consumedCount) =
        termValue outputRowsZeroValuation (‘0’ : ValuationTerm) := by
    simpa [termValue_shortBinaryNumeralTerm, termValue_outputRowsZero] using
      hzero
  simpa only [consumedCountZeroCertificate] using
    nativeEqCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm consumedCount) (‘0’ : ValuationTerm) hequal

theorem consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
    (consumedCount : Nat) (hpositive : 1 <= consumedCount) :
    hybridFormulaStructuralPayloadBound
        (consumedCountPositiveCertificate consumedCount hpositive) <=
      outputRowsNativeLeStructuralEnvelope (‘1’ : ValuationTerm)
        (shortBinaryNumeralTerm consumedCount) := by
  have hle : termValue outputRowsZeroValuation (‘1’ : ValuationTerm) <=
      termValue outputRowsZeroValuation
        (shortBinaryNumeralTerm consumedCount) := by
    simpa [termValue_outputRowsOne, termValue_shortBinaryNumeralTerm] using
      hpositive
  simpa only [consumedCountPositiveCertificate] using
    nativeLeCertificate_structuralPayloadBound_le_transparent
      (‘1’ : ValuationTerm) (shortBinaryNumeralTerm consumedCount) hle

theorem modeNativeEqualityCertificate_structuralPayloadBound_le_transparent
    (mode : Nat) (literal : ValuationTerm) (expected : Nat)
    (hliteral : termValue outputRowsZeroValuation literal = expected)
    (heq : mode = expected) :
    hybridFormulaStructuralPayloadBound
        (modeNativeEqualityCertificate mode literal expected hliteral heq) <=
      outputRowsNativeEqStructuralEnvelope
        (shortBinaryNumeralTerm mode) literal := by
  have hequal : termValue outputRowsZeroValuation
      (shortBinaryNumeralTerm mode) =
        termValue outputRowsZeroValuation literal := by
    simpa [termValue_shortBinaryNumeralTerm, hliteral] using heq
  simpa only [modeNativeEqualityCertificate] using
    nativeEqCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm mode) literal hequal

theorem modeNativeInequalityCertificate_structuralPayloadBound_le_transparent
    (mode : Nat) (literal : ValuationTerm) (expected : Nat)
    (hliteral : termValue outputRowsZeroValuation literal = expected)
    (hne : mode ≠ expected) :
    hybridFormulaStructuralPayloadBound
        (modeNativeInequalityCertificate mode literal expected hliteral hne) <=
      outputRowsNativeNeStructuralEnvelope
        (shortBinaryNumeralTerm mode) literal := by
  have hunequal : ¬termValue outputRowsZeroValuation
      (shortBinaryNumeralTerm mode) =
        termValue outputRowsZeroValuation literal := by
    simpa [termValue_shortBinaryNumeralTerm, hliteral] using hne
  simpa only [modeNativeInequalityCertificate] using
    nativeNeCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm mode) literal hunequal

def rawModeZeroPayloadEnvelope (mode : Nat) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let zeroFormula := nativeEqFormula modeTerm (‘0’ : ValuationTerm)
  let oneFormula := nativeEqFormula modeTerm (‘1’ : ValuationTerm)
  let twoFormula := nativeEqFormula modeTerm (‘2’ : ValuationTerm)
  let fiveFormula := nativeEqFormula modeTerm (‘5’ : ValuationTerm)
  transparentHybridDisjunctionLeftPayloadEnvelope outputRowsZeroValuation
    zeroFormula (oneFormula ⋎ (twoFormula ⋎ fiveFormula))
    (outputRowsNativeEqStructuralEnvelope modeTerm (‘0’ : ValuationTerm))

def rawModeOnePayloadEnvelope (mode : Nat) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let zeroFormula := nativeEqFormula modeTerm (‘0’ : ValuationTerm)
  let oneFormula := nativeEqFormula modeTerm (‘1’ : ValuationTerm)
  let twoFormula := nativeEqFormula modeTerm (‘2’ : ValuationTerm)
  let fiveFormula := nativeEqFormula modeTerm (‘5’ : ValuationTerm)
  let selected := transparentHybridDisjunctionLeftPayloadEnvelope
    outputRowsZeroValuation oneFormula (twoFormula ⋎ fiveFormula)
    (outputRowsNativeEqStructuralEnvelope modeTerm (‘1’ : ValuationTerm))
  transparentHybridDisjunctionRightPayloadEnvelope outputRowsZeroValuation
    zeroFormula (oneFormula ⋎ (twoFormula ⋎ fiveFormula)) selected

def rawModeTwoPayloadEnvelope (mode : Nat) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let zeroFormula := nativeEqFormula modeTerm (‘0’ : ValuationTerm)
  let oneFormula := nativeEqFormula modeTerm (‘1’ : ValuationTerm)
  let twoFormula := nativeEqFormula modeTerm (‘2’ : ValuationTerm)
  let fiveFormula := nativeEqFormula modeTerm (‘5’ : ValuationTerm)
  let selected := transparentHybridDisjunctionLeftPayloadEnvelope
    outputRowsZeroValuation twoFormula fiveFormula
    (outputRowsNativeEqStructuralEnvelope modeTerm (‘2’ : ValuationTerm))
  let middle := transparentHybridDisjunctionRightPayloadEnvelope
    outputRowsZeroValuation oneFormula (twoFormula ⋎ fiveFormula) selected
  transparentHybridDisjunctionRightPayloadEnvelope outputRowsZeroValuation
    zeroFormula (oneFormula ⋎ (twoFormula ⋎ fiveFormula)) middle

def rawModeFivePayloadEnvelope (mode : Nat) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let zeroFormula := nativeEqFormula modeTerm (‘0’ : ValuationTerm)
  let oneFormula := nativeEqFormula modeTerm (‘1’ : ValuationTerm)
  let twoFormula := nativeEqFormula modeTerm (‘2’ : ValuationTerm)
  let fiveFormula := nativeEqFormula modeTerm (‘5’ : ValuationTerm)
  let selected := transparentHybridDisjunctionRightPayloadEnvelope
    outputRowsZeroValuation twoFormula fiveFormula
    (outputRowsNativeEqStructuralEnvelope modeTerm (‘5’ : ValuationTerm))
  let middle := transparentHybridDisjunctionRightPayloadEnvelope
    outputRowsZeroValuation oneFormula (twoFormula ⋎ fiveFormula) selected
  transparentHybridDisjunctionRightPayloadEnvelope outputRowsZeroValuation
    zeroFormula (oneFormula ⋎ (twoFormula ⋎ fiveFormula)) middle

theorem rawModeZeroCertificate_structuralPayloadBound_le_transparent
    (mode : Nat) (hmode : mode = 0) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := nativeEqFormula (shortBinaryNumeralTerm mode)
              (‘1’ : ValuationTerm) ⋎
            (nativeEqFormula (shortBinaryNumeralTerm mode)
                (‘2’ : ValuationTerm) ⋎
              nativeEqFormula (shortBinaryNumeralTerm mode)
                (‘5’ : ValuationTerm)))
          (modeNativeEqualityCertificate mode (‘0’ : ValuationTerm) 0
            (termValue_arithmeticZero outputRowsZeroValuation) hmode)) <=
      rawModeZeroPayloadEnvelope mode := by
  let certificate := modeNativeEqualityCertificate mode
    (‘0’ : ValuationTerm) 0
      (termValue_arithmeticZero outputRowsZeroValuation) hmode
  have hcertificate :=
    modeNativeEqualityCertificate_structuralPayloadBound_le_transparent
      mode (‘0’ : ValuationTerm) 0
      (termValue_arithmeticZero outputRowsZeroValuation) hmode
  have hselected := transparentHybridDisjunctionLeftPayloadBound_le
    (right := nativeEqFormula (shortBinaryNumeralTerm mode)
        (‘1’ : ValuationTerm) ⋎
      (nativeEqFormula (shortBinaryNumeralTerm mode)
          (‘2’ : ValuationTerm) ⋎
        nativeEqFormula (shortBinaryNumeralTerm mode) (‘5’ : ValuationTerm)))
    certificate _ hcertificate
  simpa only [rawModeZeroPayloadEnvelope, certificate] using hselected

theorem rawModeOneCertificate_structuralPayloadBound_le_transparent
    (mode : Nat) (hmode : mode = 1) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := nativeEqFormula (shortBinaryNumeralTerm mode)
            (‘0’ : ValuationTerm))
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := nativeEqFormula (shortBinaryNumeralTerm mode)
                (‘2’ : ValuationTerm) ⋎
              nativeEqFormula (shortBinaryNumeralTerm mode)
                (‘5’ : ValuationTerm))
            (modeNativeEqualityCertificate mode (‘1’ : ValuationTerm) 1
              (termValue_arithmeticOne outputRowsZeroValuation) hmode))) <=
      rawModeOnePayloadEnvelope mode := by
  let certificate := modeNativeEqualityCertificate mode
    (‘1’ : ValuationTerm) 1
      (termValue_arithmeticOne outputRowsZeroValuation) hmode
  have hcertificate :=
    modeNativeEqualityCertificate_structuralPayloadBound_le_transparent
      mode (‘1’ : ValuationTerm) 1
      (termValue_arithmeticOne outputRowsZeroValuation) hmode
  let selected := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := nativeEqFormula (shortBinaryNumeralTerm mode)
        (‘2’ : ValuationTerm) ⋎
      nativeEqFormula (shortBinaryNumeralTerm mode) (‘5’ : ValuationTerm))
    certificate
  have hselected := transparentHybridDisjunctionLeftPayloadBound_le
    (right := nativeEqFormula (shortBinaryNumeralTerm mode)
        (‘2’ : ValuationTerm) ⋎
      nativeEqFormula (shortBinaryNumeralTerm mode) (‘5’ : ValuationTerm))
    certificate _ hcertificate
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := nativeEqFormula (shortBinaryNumeralTerm mode)
      (‘0’ : ValuationTerm)) selected _ hselected
  simpa only [rawModeOnePayloadEnvelope, certificate, selected] using houter

theorem rawModeTwoCertificate_structuralPayloadBound_le_transparent
    (mode : Nat) (hmode : mode = 2) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := nativeEqFormula (shortBinaryNumeralTerm mode)
            (‘0’ : ValuationTerm))
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := nativeEqFormula (shortBinaryNumeralTerm mode)
              (‘1’ : ValuationTerm))
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (right := nativeEqFormula (shortBinaryNumeralTerm mode)
                (‘5’ : ValuationTerm))
              (modeNativeEqualityCertificate mode (‘2’ : ValuationTerm) 2
                (termValue_arithmeticTwo outputRowsZeroValuation) hmode)))) <=
      rawModeTwoPayloadEnvelope mode := by
  let certificate := modeNativeEqualityCertificate mode
    (‘2’ : ValuationTerm) 2
      (termValue_arithmeticTwo outputRowsZeroValuation) hmode
  have hcertificate :=
    modeNativeEqualityCertificate_structuralPayloadBound_le_transparent
      mode (‘2’ : ValuationTerm) 2
      (termValue_arithmeticTwo outputRowsZeroValuation) hmode
  let selected := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := nativeEqFormula (shortBinaryNumeralTerm mode)
      (‘5’ : ValuationTerm)) certificate
  have hselected := transparentHybridDisjunctionLeftPayloadBound_le
    (right := nativeEqFormula (shortBinaryNumeralTerm mode)
      (‘5’ : ValuationTerm)) certificate _ hcertificate
  let middle := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := nativeEqFormula (shortBinaryNumeralTerm mode)
      (‘1’ : ValuationTerm)) selected
  have hmiddle := transparentHybridDisjunctionRightPayloadBound_le
    (left := nativeEqFormula (shortBinaryNumeralTerm mode)
      (‘1’ : ValuationTerm)) selected _ hselected
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := nativeEqFormula (shortBinaryNumeralTerm mode)
      (‘0’ : ValuationTerm)) middle _ hmiddle
  simpa only [rawModeTwoPayloadEnvelope, certificate, selected, middle] using
    houter

theorem rawModeFiveCertificate_structuralPayloadBound_le_transparent
    (mode : Nat) (hmode : mode = 5) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := nativeEqFormula (shortBinaryNumeralTerm mode)
            (‘0’ : ValuationTerm))
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := nativeEqFormula (shortBinaryNumeralTerm mode)
              (‘1’ : ValuationTerm))
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := nativeEqFormula (shortBinaryNumeralTerm mode)
                (‘2’ : ValuationTerm))
              (modeNativeEqualityCertificate mode (‘5’ : ValuationTerm) 5
                (termValue_arithmeticFive outputRowsZeroValuation) hmode)))) <=
      rawModeFivePayloadEnvelope mode := by
  let certificate := modeNativeEqualityCertificate mode
    (‘5’ : ValuationTerm) 5
      (termValue_arithmeticFive outputRowsZeroValuation) hmode
  have hcertificate :=
    modeNativeEqualityCertificate_structuralPayloadBound_le_transparent
      mode (‘5’ : ValuationTerm) 5
      (termValue_arithmeticFive outputRowsZeroValuation) hmode
  let selected := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := nativeEqFormula (shortBinaryNumeralTerm mode)
      (‘2’ : ValuationTerm)) certificate
  have hselected := transparentHybridDisjunctionRightPayloadBound_le
    (left := nativeEqFormula (shortBinaryNumeralTerm mode)
      (‘2’ : ValuationTerm)) certificate _ hcertificate
  let middle := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := nativeEqFormula (shortBinaryNumeralTerm mode)
      (‘1’ : ValuationTerm)) selected
  have hmiddle := transparentHybridDisjunctionRightPayloadBound_le
    (left := nativeEqFormula (shortBinaryNumeralTerm mode)
      (‘1’ : ValuationTerm)) selected _ hselected
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := nativeEqFormula (shortBinaryNumeralTerm mode)
      (‘0’ : ValuationTerm)) middle _ hmiddle
  simpa only [rawModeFivePayloadEnvelope, certificate, selected, middle] using
    houter

def otherModeWithTailPayloadEnvelope
    (mode : Nat) (tail : ValuationFormula) (tailResource : Nat) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let zeroFormula := nativeNeFormula modeTerm (‘0’ : ValuationTerm)
  let oneFormula := nativeNeFormula modeTerm (‘1’ : ValuationTerm)
  let twoFormula := nativeNeFormula modeTerm (‘2’ : ValuationTerm)
  let fourFormula := nativeNeFormula modeTerm (‘4’ : ValuationTerm)
  let fiveFormula := nativeNeFormula modeTerm (‘5’ : ValuationTerm)
  let fiveTail := transparentHybridConjunctionPayloadEnvelope
    outputRowsZeroValuation fiveFormula tail
    (outputRowsNativeNeStructuralEnvelope modeTerm (‘5’ : ValuationTerm))
    tailResource
  let fourTail := transparentHybridConjunctionPayloadEnvelope
    outputRowsZeroValuation fourFormula (fiveFormula ⋏ tail)
    (outputRowsNativeNeStructuralEnvelope modeTerm (‘4’ : ValuationTerm))
    fiveTail
  let twoTail := transparentHybridConjunctionPayloadEnvelope
    outputRowsZeroValuation twoFormula (fourFormula ⋏ (fiveFormula ⋏ tail))
    (outputRowsNativeNeStructuralEnvelope modeTerm (‘2’ : ValuationTerm))
    fourTail
  let oneTail := transparentHybridConjunctionPayloadEnvelope
    outputRowsZeroValuation oneFormula
    (twoFormula ⋏ (fourFormula ⋏ (fiveFormula ⋏ tail)))
    (outputRowsNativeNeStructuralEnvelope modeTerm (‘1’ : ValuationTerm))
    twoTail
  transparentHybridConjunctionPayloadEnvelope outputRowsZeroValuation
    zeroFormula
    (oneFormula ⋏ (twoFormula ⋏ (fourFormula ⋏ (fiveFormula ⋏ tail))))
    (outputRowsNativeNeStructuralEnvelope modeTerm (‘0’ : ValuationTerm))
    oneTail

theorem otherModeWithTailPayloadEnvelope_mono
    (mode : Nat) (tail : ValuationFormula)
    {small large : Nat} (hresource : small <= large) :
    otherModeWithTailPayloadEnvelope mode tail small <=
      otherModeWithTailPayloadEnvelope mode tail large := by
  unfold otherModeWithTailPayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
          (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
            hresource))))

theorem otherModeWithTailCertificate_structuralPayloadBound_le_transparent
    (mode : Nat)
    (hzero : mode ≠ 0) (hone : mode ≠ 1) (htwo : mode ≠ 2)
    (hfour : mode ≠ 4) (hfive : mode ≠ 5)
    (tail : ValuationFormula)
    (tailCertificate : CheckedHybridValuationBoundedFormulaCertificate
      outputRowsZeroValuation tail)
    (tailResource : Nat)
    (htail : hybridFormulaStructuralPayloadBound tailCertificate <=
      tailResource) :
    hybridFormulaStructuralPayloadBound
        (otherModeWithTailCertificate mode hzero hone htwo hfour hfive tail
          tailCertificate) <=
      otherModeWithTailPayloadEnvelope mode tail tailResource := by
  let zeroCertificate := modeNativeInequalityCertificate mode
    (‘0’ : ValuationTerm) 0
      (termValue_arithmeticZero outputRowsZeroValuation) hzero
  let oneCertificate := modeNativeInequalityCertificate mode
    (‘1’ : ValuationTerm) 1
      (termValue_arithmeticOne outputRowsZeroValuation) hone
  let twoCertificate := modeNativeInequalityCertificate mode
    (‘2’ : ValuationTerm) 2
      (termValue_arithmeticTwo outputRowsZeroValuation) htwo
  let fourCertificate := modeNativeInequalityCertificate mode
    (‘4’ : ValuationTerm) 4
      (termValue_arithmeticFour outputRowsZeroValuation) hfour
  let fiveCertificate := modeNativeInequalityCertificate mode
    (‘5’ : ValuationTerm) 5
      (termValue_arithmeticFive outputRowsZeroValuation) hfive
  have hzeroResource :=
    modeNativeInequalityCertificate_structuralPayloadBound_le_transparent
      mode (‘0’ : ValuationTerm) 0
      (termValue_arithmeticZero outputRowsZeroValuation) hzero
  have honeResource :=
    modeNativeInequalityCertificate_structuralPayloadBound_le_transparent
      mode (‘1’ : ValuationTerm) 1
      (termValue_arithmeticOne outputRowsZeroValuation) hone
  have htwoResource :=
    modeNativeInequalityCertificate_structuralPayloadBound_le_transparent
      mode (‘2’ : ValuationTerm) 2
      (termValue_arithmeticTwo outputRowsZeroValuation) htwo
  have hfourResource :=
    modeNativeInequalityCertificate_structuralPayloadBound_le_transparent
      mode (‘4’ : ValuationTerm) 4
      (termValue_arithmeticFour outputRowsZeroValuation) hfour
  have hfiveResource :=
    modeNativeInequalityCertificate_structuralPayloadBound_le_transparent
      mode (‘5’ : ValuationTerm) 5
      (termValue_arithmeticFive outputRowsZeroValuation) hfive
  let fiveTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    fiveCertificate tailCertificate
  have hfiveTail := transparentHybridConjunctionPayloadBound_le
    fiveCertificate tailCertificate _ _ hfiveResource htail
  let fourTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    fourCertificate fiveTail
  have hfourTail := transparentHybridConjunctionPayloadBound_le
    fourCertificate fiveTail _ _ hfourResource hfiveTail
  let twoTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    twoCertificate fourTail
  have htwoTail := transparentHybridConjunctionPayloadBound_le
    twoCertificate fourTail _ _ htwoResource hfourTail
  let oneTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    oneCertificate twoTail
  have honeTail := transparentHybridConjunctionPayloadBound_le
    oneCertificate twoTail _ _ honeResource htwoTail
  let direct := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    zeroCertificate oneTail
  have hdirect := transparentHybridConjunctionPayloadBound_le
    zeroCertificate oneTail _ _ hzeroResource honeTail
  convert hdirect using 1 <;>
    simp only [otherModeWithTailCertificate,
      otherModeWithTailPayloadEnvelope, outputRowsZeroValuation,
      modeNativeInequalityCertificate, nativeNeCertificate,
      nativeNeFormula, hybridFormulaStructuralPayloadBound,
      zeroCertificate, oneCertificate, twoCertificate, fourCertificate,
      fiveCertificate, fiveTail, fourTail, twoTail, oneTail]

def outputRowsZeroSelectedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (sameResource : Nat) : Nat :=
  let zeroResource := outputRowsNativeEqStructuralEnvelope
    (shortBinaryNumeralTerm consumedCount) (‘0’ : ValuationTerm)
  let zeroPairResource := transparentHybridConjunctionPayloadEnvelope
    outputRowsZeroValuation
    (nativeEqFormula (shortBinaryNumeralTerm consumedCount)
      (‘0’ : ValuationTerm))
    (compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
      current.outputBoundary current.outputCount next.outputBoundary
      next.outputCount) zeroResource sameResource
  let casesResource := transparentHybridDisjunctionLeftPayloadEnvelope
    outputRowsZeroValuation
    (outputRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount)
    (outputRowsPositiveCaseFormula tokenTable width tokenCount current next
      mode tag consumedCount mappedHead) zeroPairResource
  transparentHybridConjunctionPayloadEnvelope outputRowsZeroValuation
    (outputRowsCountFormula current next consumedCount)
    (outputRowsCasesFormula tokenTable width tokenCount current next mode tag
      consumedCount mappedHead)
    (outputRowsNativeEqStructuralEnvelope
      (shortBinaryNumeralTerm current.parserTokensCount)
      (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm next.parserTokensCount))) casesResource

def outputRowsRawSelectedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (modeResource sourceResource : Nat) : Nat :=
  let rawPairResource := transparentHybridConjunctionPayloadEnvelope
    outputRowsZeroValuation
    (rawModeFormula (shortBinaryNumeralTerm mode))
    (compactAdditiveNatListAppendSourcePrefixClosedFormula
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount) modeResource sourceResource
  let positiveBodyResource := transparentHybridDisjunctionLeftPayloadEnvelope
    outputRowsZeroValuation
    (outputRowsRawCaseFormula tokenTable width tokenCount current next mode
      consumedCount)
    (outputRowsSameFourCaseFormula tokenTable width tokenCount current next
        mode ⋎
      outputRowsMappedCaseFormula tokenTable width tokenCount current next
        mode tag consumedCount mappedHead) rawPairResource
  let positiveResource := transparentHybridConjunctionPayloadEnvelope
    outputRowsZeroValuation
    (nativeLeFormula (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm consumedCount))
    (outputRowsPositiveBodyFormula tokenTable width tokenCount current next
      mode tag consumedCount mappedHead)
    (outputRowsNativeLeStructuralEnvelope (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm consumedCount)) positiveBodyResource
  let casesResource := transparentHybridDisjunctionRightPayloadEnvelope
    outputRowsZeroValuation
    (outputRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount)
    (outputRowsPositiveCaseFormula tokenTable width tokenCount current next
      mode tag consumedCount mappedHead) positiveResource
  transparentHybridConjunctionPayloadEnvelope outputRowsZeroValuation
    (outputRowsCountFormula current next consumedCount)
    (outputRowsCasesFormula tokenTable width tokenCount current next mode tag
      consumedCount mappedHead)
    (outputRowsNativeEqStructuralEnvelope
      (shortBinaryNumeralTerm current.parserTokensCount)
      (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm next.parserTokensCount))) casesResource

def outputRowsSameFourSelectedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (modeResource sameResource : Nat) : Nat :=
  let samePairResource := transparentHybridConjunctionPayloadEnvelope
    outputRowsZeroValuation
    (nativeEqFormula (shortBinaryNumeralTerm mode) (‘4’ : ValuationTerm))
    (compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
      current.outputBoundary current.outputCount next.outputBoundary
      next.outputCount) modeResource sameResource
  let sameSelectedResource := transparentHybridDisjunctionLeftPayloadEnvelope
    outputRowsZeroValuation
    (outputRowsSameFourCaseFormula tokenTable width tokenCount current next mode)
    (outputRowsMappedCaseFormula tokenTable width tokenCount current next mode
      tag consumedCount mappedHead) samePairResource
  let positiveBodyResource := transparentHybridDisjunctionRightPayloadEnvelope
    outputRowsZeroValuation
    (outputRowsRawCaseFormula tokenTable width tokenCount current next mode
      consumedCount)
    (outputRowsSameFourCaseFormula tokenTable width tokenCount current next
        mode ⋎
      outputRowsMappedCaseFormula tokenTable width tokenCount current next
        mode tag consumedCount mappedHead) sameSelectedResource
  let positiveResource := transparentHybridConjunctionPayloadEnvelope
    outputRowsZeroValuation
    (nativeLeFormula (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm consumedCount))
    (outputRowsPositiveBodyFormula tokenTable width tokenCount current next
      mode tag consumedCount mappedHead)
    (outputRowsNativeLeStructuralEnvelope (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm consumedCount)) positiveBodyResource
  let casesResource := transparentHybridDisjunctionRightPayloadEnvelope
    outputRowsZeroValuation
    (outputRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount)
    (outputRowsPositiveCaseFormula tokenTable width tokenCount current next
      mode tag consumedCount mappedHead) positiveResource
  transparentHybridConjunctionPayloadEnvelope outputRowsZeroValuation
    (outputRowsCountFormula current next consumedCount)
    (outputRowsCasesFormula tokenTable width tokenCount current next mode tag
      consumedCount mappedHead)
    (outputRowsNativeEqStructuralEnvelope
      (shortBinaryNumeralTerm current.parserTokensCount)
      (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm next.parserTokensCount))) casesResource

def outputRowsMappedSelectedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (tagResource rowsResource : Nat) : Nat :=
  let mappedTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
    (compactNegationFormulaTagClosedFormula tag mappedHead)
    (compactAdditiveNatListAppendMappedSourcePrefixClosedFormula
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputBoundary next.outputCount mappedHead)
    tagResource rowsResource
  let mappedResource := otherModeWithTailPayloadEnvelope mode
    (outputRowsMappedTailFormula tokenTable width tokenCount current next tag
      consumedCount mappedHead) mappedTailResource
  let sameMappedResource := transparentHybridDisjunctionRightPayloadEnvelope
    outputRowsZeroValuation
    (outputRowsSameFourCaseFormula tokenTable width tokenCount current next mode)
    (outputRowsMappedCaseFormula tokenTable width tokenCount current next mode
      tag consumedCount mappedHead) mappedResource
  let positiveBodyResource := transparentHybridDisjunctionRightPayloadEnvelope
    outputRowsZeroValuation
    (outputRowsRawCaseFormula tokenTable width tokenCount current next mode
      consumedCount)
    (outputRowsSameFourCaseFormula tokenTable width tokenCount current next
        mode ⋎
      outputRowsMappedCaseFormula tokenTable width tokenCount current next
        mode tag consumedCount mappedHead) sameMappedResource
  let positiveResource := transparentHybridConjunctionPayloadEnvelope
    outputRowsZeroValuation
    (nativeLeFormula (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm consumedCount))
    (outputRowsPositiveBodyFormula tokenTable width tokenCount current next
      mode tag consumedCount mappedHead)
    (outputRowsNativeLeStructuralEnvelope (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm consumedCount)) positiveBodyResource
  let casesResource := transparentHybridDisjunctionRightPayloadEnvelope
    outputRowsZeroValuation
    (outputRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount)
    (outputRowsPositiveCaseFormula tokenTable width tokenCount current next
      mode tag consumedCount mappedHead) positiveResource
  transparentHybridConjunctionPayloadEnvelope outputRowsZeroValuation
    (outputRowsCountFormula current next consumedCount)
    (outputRowsCasesFormula tokenTable width tokenCount current next mode tag
      consumedCount mappedHead)
    (outputRowsNativeEqStructuralEnvelope
      (shortBinaryNumeralTerm current.parserTokensCount)
      (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm next.parserTokensCount))) casesResource

theorem outputRowsZeroSelectedPayloadEnvelope_mono
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    {small large : Nat} (hresource : small <= large) :
    outputRowsZeroSelectedPayloadEnvelope tokenTable width tokenCount current
        next mode tag consumedCount mappedHead small <=
      outputRowsZeroSelectedPayloadEnvelope tokenTable width tokenCount current
        next mode tag consumedCount mappedHead large := by
  unfold outputRowsZeroSelectedPayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
        hresource))

theorem outputRowsRawSelectedPayloadEnvelope_mono
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    {modeSmall modeLarge sourceSmall sourceLarge : Nat}
    (hmode : modeSmall <= modeLarge)
    (hsource : sourceSmall <= sourceLarge) :
    outputRowsRawSelectedPayloadEnvelope tokenTable width tokenCount current
        next mode tag consumedCount mappedHead modeSmall sourceSmall <=
      outputRowsRawSelectedPayloadEnvelope tokenTable width tokenCount current
        next mode tag consumedCount mappedHead modeLarge sourceLarge := by
  unfold outputRowsRawSelectedPayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
        (transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _
          (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ hmode
            hsource))))

theorem outputRowsSameFourSelectedPayloadEnvelope_mono
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    {modeSmall modeLarge sameSmall sameLarge : Nat}
    (hmode : modeSmall <= modeLarge)
    (hsame : sameSmall <= sameLarge) :
    outputRowsSameFourSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode tag consumedCount mappedHead modeSmall sameSmall <=
      outputRowsSameFourSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode tag consumedCount mappedHead modeLarge sameLarge := by
  unfold outputRowsSameFourSelectedPayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
        (transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
          (transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _
            (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ hmode
              hsame)))))

theorem outputRowsMappedSelectedPayloadEnvelope_mono
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    {tagSmall tagLarge rowsSmall rowsLarge : Nat}
    (htag : tagSmall <= tagLarge)
    (hrows : rowsSmall <= rowsLarge) :
    outputRowsMappedSelectedPayloadEnvelope tokenTable width tokenCount current
        next mode tag consumedCount mappedHead tagSmall rowsSmall <=
      outputRowsMappedSelectedPayloadEnvelope tokenTable width tokenCount current
        next mode tag consumedCount mappedHead tagLarge rowsLarge := by
  unfold outputRowsMappedSelectedPayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
        (transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
          (transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
            (otherModeWithTailPayloadEnvelope_mono _ _
              (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ htag
                hrows))))))

theorem outputRowsZeroSelectedCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (countCertificate : CheckedHybridValuationBoundedFormulaCertificate
      outputRowsZeroValuation
      (outputRowsCountFormula current next consumedCount))
    (zeroCertificate : CheckedHybridValuationBoundedFormulaCertificate
      outputRowsZeroValuation
      (nativeEqFormula (shortBinaryNumeralTerm consumedCount)
        (‘0’ : ValuationTerm)))
    (sameCertificate : CheckedHybridValuationBoundedFormulaCertificate
      outputRowsZeroValuation
      (compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
        current.outputBoundary current.outputCount next.outputBoundary
        next.outputCount))
    (sameResource : Nat)
    (hcount : hybridFormulaStructuralPayloadBound countCertificate <=
      outputRowsNativeEqStructuralEnvelope
        (shortBinaryNumeralTerm current.parserTokensCount)
        (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm next.parserTokensCount)))
    (hzero : hybridFormulaStructuralPayloadBound zeroCertificate <=
      outputRowsNativeEqStructuralEnvelope
        (shortBinaryNumeralTerm consumedCount) (‘0’ : ValuationTerm))
    (hsame : hybridFormulaStructuralPayloadBound sameCertificate <=
      sameResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          countCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := outputRowsPositiveCaseFormula tokenTable width tokenCount
              current next mode tag consumedCount mappedHead)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              zeroCertificate sameCertificate))) <=
      outputRowsZeroSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode tag consumedCount mappedHead sameResource := by
  let zeroPair := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    zeroCertificate sameCertificate
  have hzeroPair := transparentHybridConjunctionPayloadBound_le
    zeroCertificate sameCertificate _ _ hzero hsame
  let cases := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := outputRowsPositiveCaseFormula tokenTable width tokenCount current
      next mode tag consumedCount mappedHead) zeroPair
  have hcases := transparentHybridDisjunctionLeftPayloadBound_le
    (right := outputRowsPositiveCaseFormula tokenTable width tokenCount current
      next mode tag consumedCount mappedHead) zeroPair _ hzeroPair
  have houter := transparentHybridConjunctionPayloadBound_le
    countCertificate cases _ _ hcount hcases
  simpa only [outputRowsZeroSelectedPayloadEnvelope, outputRowsCasesFormula,
    outputRowsZeroCaseFormula, zeroPair, cases] using
    houter

theorem outputRowsRawSelectedCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (countCertificate : CheckedHybridValuationBoundedFormulaCertificate
      outputRowsZeroValuation
      (outputRowsCountFormula current next consumedCount))
    (positiveCertificate : CheckedHybridValuationBoundedFormulaCertificate
      outputRowsZeroValuation
      (nativeLeFormula (‘1’ : ValuationTerm)
        (shortBinaryNumeralTerm consumedCount)))
    (modeCertificate : CheckedHybridValuationBoundedFormulaCertificate
      outputRowsZeroValuation (rawModeFormula (shortBinaryNumeralTerm mode)))
    (sourceCertificate : CheckedHybridValuationBoundedFormulaCertificate
      outputRowsZeroValuation
      (compactAdditiveNatListAppendSourcePrefixClosedFormula tokenTable width
        tokenCount current.parserFinish current.finish current.outputCount
        current.start current.parserTokensFinish current.parserTokensCount
        consumedCount next.parserFinish next.finish next.outputCount))
    (modeResource sourceResource : Nat)
    (hcount : hybridFormulaStructuralPayloadBound countCertificate <=
      outputRowsNativeEqStructuralEnvelope
        (shortBinaryNumeralTerm current.parserTokensCount)
        (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm next.parserTokensCount)))
    (hpositive : hybridFormulaStructuralPayloadBound positiveCertificate <=
      outputRowsNativeLeStructuralEnvelope (‘1’ : ValuationTerm)
        (shortBinaryNumeralTerm consumedCount))
    (hmode : hybridFormulaStructuralPayloadBound modeCertificate <=
      modeResource)
    (hsource : hybridFormulaStructuralPayloadBound sourceCertificate <=
      sourceResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          countCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := outputRowsZeroCaseFormula tokenTable width tokenCount
              current next consumedCount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              positiveCertificate
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (right := outputRowsSameFourCaseFormula tokenTable width
                    tokenCount current next mode ⋎
                  outputRowsMappedCaseFormula tokenTable width tokenCount
                    current next mode tag consumedCount mappedHead)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  modeCertificate sourceCertificate))))) <=
      outputRowsRawSelectedPayloadEnvelope tokenTable width tokenCount current
        next mode tag consumedCount mappedHead modeResource sourceResource := by
  let rawPair := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    modeCertificate sourceCertificate
  have hrawPair := transparentHybridConjunctionPayloadBound_le
    modeCertificate sourceCertificate _ _ hmode hsource
  let positiveBody :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := outputRowsSameFourCaseFormula tokenTable width tokenCount
          current next mode ⋎
        outputRowsMappedCaseFormula tokenTable width tokenCount current next
          mode tag consumedCount mappedHead) rawPair
  have hpositiveBody := transparentHybridDisjunctionLeftPayloadBound_le
    (right := outputRowsSameFourCaseFormula tokenTable width tokenCount current
        next mode ⋎
      outputRowsMappedCaseFormula tokenTable width tokenCount current next mode
        tag consumedCount mappedHead) rawPair _ hrawPair
  let positive := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    positiveCertificate positiveBody
  have hpositiveSelected := transparentHybridConjunctionPayloadBound_le
    positiveCertificate positiveBody _ _ hpositive hpositiveBody
  let cases := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := outputRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount) positive
  have hcases := transparentHybridDisjunctionRightPayloadBound_le
    (left := outputRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount) positive _ hpositiveSelected
  have houter := transparentHybridConjunctionPayloadBound_le
    countCertificate cases _ _ hcount hcases
  simpa only [outputRowsRawSelectedPayloadEnvelope, outputRowsCasesFormula,
    outputRowsPositiveCaseFormula, outputRowsPositiveBodyFormula,
    outputRowsRawCaseFormula, rawPair, positiveBody, positive, cases] using
    houter

theorem outputRowsSameFourSelectedCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (countCertificate : CheckedHybridValuationBoundedFormulaCertificate
      outputRowsZeroValuation
      (outputRowsCountFormula current next consumedCount))
    (positiveCertificate : CheckedHybridValuationBoundedFormulaCertificate
      outputRowsZeroValuation
      (nativeLeFormula (‘1’ : ValuationTerm)
        (shortBinaryNumeralTerm consumedCount)))
    (modeCertificate : CheckedHybridValuationBoundedFormulaCertificate
      outputRowsZeroValuation
      (nativeEqFormula (shortBinaryNumeralTerm mode) (‘4’ : ValuationTerm)))
    (sameCertificate : CheckedHybridValuationBoundedFormulaCertificate
      outputRowsZeroValuation
      (compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
        current.outputBoundary current.outputCount next.outputBoundary
        next.outputCount))
    (modeResource sameResource : Nat)
    (hcount : hybridFormulaStructuralPayloadBound countCertificate <=
      outputRowsNativeEqStructuralEnvelope
        (shortBinaryNumeralTerm current.parserTokensCount)
        (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm next.parserTokensCount)))
    (hpositive : hybridFormulaStructuralPayloadBound positiveCertificate <=
      outputRowsNativeLeStructuralEnvelope (‘1’ : ValuationTerm)
        (shortBinaryNumeralTerm consumedCount))
    (hmode : hybridFormulaStructuralPayloadBound modeCertificate <=
      modeResource)
    (hsame : hybridFormulaStructuralPayloadBound sameCertificate <=
      sameResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          countCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := outputRowsZeroCaseFormula tokenTable width tokenCount
              current next consumedCount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              positiveCertificate
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left := outputRowsRawCaseFormula tokenTable width tokenCount
                  current next mode consumedCount)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                  (right := outputRowsMappedCaseFormula tokenTable width
                    tokenCount current next mode tag consumedCount mappedHead)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    modeCertificate sameCertificate)))))) <=
      outputRowsSameFourSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode tag consumedCount mappedHead modeResource
        sameResource := by
  let samePair := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    modeCertificate sameCertificate
  have hsamePair := transparentHybridConjunctionPayloadBound_le
    modeCertificate sameCertificate _ _ hmode hsame
  let sameSelected :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := outputRowsMappedCaseFormula tokenTable width tokenCount current
        next mode tag consumedCount mappedHead) samePair
  have hsameSelected := transparentHybridDisjunctionLeftPayloadBound_le
    (right := outputRowsMappedCaseFormula tokenTable width tokenCount current
      next mode tag consumedCount mappedHead) samePair _ hsamePair
  let positiveBody :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := outputRowsRawCaseFormula tokenTable width tokenCount current next
        mode consumedCount) sameSelected
  have hpositiveBody := transparentHybridDisjunctionRightPayloadBound_le
    (left := outputRowsRawCaseFormula tokenTable width tokenCount current next
      mode consumedCount) sameSelected _ hsameSelected
  let positive := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    positiveCertificate positiveBody
  have hpositiveSelected := transparentHybridConjunctionPayloadBound_le
    positiveCertificate positiveBody _ _ hpositive hpositiveBody
  let cases := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := outputRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount) positive
  have hcases := transparentHybridDisjunctionRightPayloadBound_le
    (left := outputRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount) positive _ hpositiveSelected
  have houter := transparentHybridConjunctionPayloadBound_le
    countCertificate cases _ _ hcount hcases
  simpa only [outputRowsSameFourSelectedPayloadEnvelope,
    outputRowsCasesFormula, outputRowsPositiveCaseFormula,
    outputRowsPositiveBodyFormula, outputRowsSameFourCaseFormula, samePair,
    sameSelected, positiveBody, positive, cases] using houter

theorem outputRowsMappedSelectedCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (countCertificate : CheckedHybridValuationBoundedFormulaCertificate
      outputRowsZeroValuation
      (outputRowsCountFormula current next consumedCount))
    (positiveCertificate : CheckedHybridValuationBoundedFormulaCertificate
      outputRowsZeroValuation
      (nativeLeFormula (‘1’ : ValuationTerm)
        (shortBinaryNumeralTerm consumedCount)))
    (mappedCertificate : CheckedHybridValuationBoundedFormulaCertificate
      outputRowsZeroValuation
      (outputRowsMappedCaseFormula tokenTable width tokenCount current next mode
        tag consumedCount mappedHead))
    (tagResource rowsResource : Nat)
    (hcount : hybridFormulaStructuralPayloadBound countCertificate <=
      outputRowsNativeEqStructuralEnvelope
        (shortBinaryNumeralTerm current.parserTokensCount)
        (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm next.parserTokensCount)))
    (hpositive : hybridFormulaStructuralPayloadBound positiveCertificate <=
      outputRowsNativeLeStructuralEnvelope (‘1’ : ValuationTerm)
        (shortBinaryNumeralTerm consumedCount))
    (hmapped : hybridFormulaStructuralPayloadBound mappedCertificate <=
      otherModeWithTailPayloadEnvelope mode
        (outputRowsMappedTailFormula tokenTable width tokenCount current next
          tag consumedCount mappedHead)
        (transparentHybridConjunctionPayloadEnvelope
          FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
          (compactNegationFormulaTagClosedFormula tag mappedHead)
          (compactAdditiveNatListAppendMappedSourcePrefixClosedFormula
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish
            next.finish next.outputBoundary next.outputCount mappedHead)
          tagResource rowsResource)) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          countCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := outputRowsZeroCaseFormula tokenTable width tokenCount
              current next consumedCount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              positiveCertificate
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left := outputRowsRawCaseFormula tokenTable width tokenCount
                  current next mode consumedCount)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                  (left := outputRowsSameFourCaseFormula tokenTable width
                    tokenCount current next mode) mappedCertificate))))) <=
      outputRowsMappedSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode tag consumedCount mappedHead tagResource
        rowsResource := by
  let sameMapped :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := outputRowsSameFourCaseFormula tokenTable width tokenCount current
        next mode) mappedCertificate
  have hsameMapped := transparentHybridDisjunctionRightPayloadBound_le
    (left := outputRowsSameFourCaseFormula tokenTable width tokenCount current
      next mode) mappedCertificate _ hmapped
  let positiveBody :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := outputRowsRawCaseFormula tokenTable width tokenCount current next
        mode consumedCount) sameMapped
  have hpositiveBody := transparentHybridDisjunctionRightPayloadBound_le
    (left := outputRowsRawCaseFormula tokenTable width tokenCount current next
      mode consumedCount) sameMapped _ hsameMapped
  let positive := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    positiveCertificate positiveBody
  have hpositiveSelected := transparentHybridConjunctionPayloadBound_le
    positiveCertificate positiveBody _ _ hpositive hpositiveBody
  let cases := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := outputRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount) positive
  have hcases := transparentHybridDisjunctionRightPayloadBound_le
    (left := outputRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount) positive _ hpositiveSelected
  have houter := transparentHybridConjunctionPayloadBound_le
    countCertificate cases _ _ hcount hcases
  simpa only [outputRowsMappedSelectedPayloadEnvelope,
    outputRowsCasesFormula, outputRowsPositiveCaseFormula,
    outputRowsPositiveBodyFormula, outputRowsMappedCaseFormula, sameMapped,
    positiveBody, positive, cases] using houter

noncomputable def
    compactFormulaTransformFormulaOutputRowsBranchPayloadEnvelopeFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (data : CompactFormulaTransformFormulaOutputRowsCheckedBranchData
      tokenTable width tokenCount current next mode tag consumedCount
      mappedHead) : Nat :=
  match data with
  | .zero _ _ hsame =>
      outputRowsZeroSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode tag consumedCount mappedHead
        (compactAdditiveNatListSameRowsGraphPayloadEnvelope tokenTable width
          tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount hsame)
  | .rawZero _ _ _ hsource =>
      outputRowsRawSelectedPayloadEnvelope tokenTable width tokenCount current
        next mode tag consumedCount mappedHead (rawModeZeroPayloadEnvelope mode)
        (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource)
  | .rawOne _ _ _ hsource =>
      outputRowsRawSelectedPayloadEnvelope tokenTable width tokenCount current
        next mode tag consumedCount mappedHead (rawModeOnePayloadEnvelope mode)
        (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource)
  | .rawTwo _ _ _ hsource =>
      outputRowsRawSelectedPayloadEnvelope tokenTable width tokenCount current
        next mode tag consumedCount mappedHead (rawModeTwoPayloadEnvelope mode)
        (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource)
  | .rawFive _ _ _ hsource =>
      outputRowsRawSelectedPayloadEnvelope tokenTable width tokenCount current
        next mode tag consumedCount mappedHead (rawModeFivePayloadEnvelope mode)
        (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource)
  | .sameFour _ _ _ hsame =>
      outputRowsSameFourSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode tag consumedCount mappedHead
        (outputRowsNativeEqStructuralEnvelope (shortBinaryNumeralTerm mode)
          (‘4’ : ValuationTerm))
        (compactAdditiveNatListSameRowsGraphPayloadEnvelope tokenTable width
          tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount hsame)
  | .mapped _ _ _ _ _ _ _ htag hrows =>
      outputRowsMappedSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode tag consumedCount mappedHead
        (compactNegationFormulaTagGraphPayloadEnvelope tag mappedHead htag)
        (compactAdditiveNatListAppendMappedSourcePrefixGraphPayloadEnvelope
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputBoundary next.outputCount mappedHead hrows)

def compactFormulaTransformFormulaOutputRowsPublicFinitePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat) : Nat :=
  let sameResource :=
    compactAdditiveNatListSameRowsPublicFinitePayloadEnvelope tokenTable width
      tokenCount current.outputBoundary current.outputCount next.outputBoundary
      next.outputCount
  let sourceResource :=
    compactAdditiveNatListAppendSourcePrefixPublicFinitePayloadEnvelope
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount
  let mappedTagResource :=
    compactNegationFormulaTagPublicFinitePayloadEnvelope tag mappedHead
  let mappedRowsResource :=
    compactAdditiveNatListAppendMappedSourcePrefixPublicFinitePayloadEnvelope
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputBoundary next.outputCount mappedHead
  let zeroBranch := outputRowsZeroSelectedPayloadEnvelope tokenTable width
    tokenCount current next mode tag consumedCount mappedHead sameResource
  let rawZeroBranch := outputRowsRawSelectedPayloadEnvelope tokenTable width
    tokenCount current next mode tag consumedCount mappedHead
    (rawModeZeroPayloadEnvelope mode) sourceResource
  let rawOneBranch := outputRowsRawSelectedPayloadEnvelope tokenTable width
    tokenCount current next mode tag consumedCount mappedHead
    (rawModeOnePayloadEnvelope mode) sourceResource
  let rawTwoBranch := outputRowsRawSelectedPayloadEnvelope tokenTable width
    tokenCount current next mode tag consumedCount mappedHead
    (rawModeTwoPayloadEnvelope mode) sourceResource
  let rawFiveBranch := outputRowsRawSelectedPayloadEnvelope tokenTable width
    tokenCount current next mode tag consumedCount mappedHead
    (rawModeFivePayloadEnvelope mode) sourceResource
  let sameFourBranch := outputRowsSameFourSelectedPayloadEnvelope tokenTable
    width tokenCount current next mode tag consumedCount mappedHead
    (outputRowsNativeEqStructuralEnvelope (shortBinaryNumeralTerm mode)
      (‘4’ : ValuationTerm)) sameResource
  let mappedBranch := outputRowsMappedSelectedPayloadEnvelope tokenTable width
    tokenCount current next mode tag consumedCount mappedHead mappedTagResource
    mappedRowsResource
  zeroBranch + rawZeroBranch + rawOneBranch + rawTwoBranch + rawFiveBranch +
    sameFourBranch + mappedBranch

theorem
    compactFormulaTransformFormulaOutputRowsBranchPayloadEnvelopeFromData_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (data : CompactFormulaTransformFormulaOutputRowsCheckedBranchData
      tokenTable width tokenCount current next mode tag consumedCount
      mappedHead) :
    compactFormulaTransformFormulaOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode tag consumedCount
        mappedHead data <=
      compactFormulaTransformFormulaOutputRowsPublicFinitePayloadEnvelope
        tokenTable width tokenCount current next mode tag consumedCount
        mappedHead := by
  cases data with
  | zero hcount hconsumed hsame =>
      unfold
        compactFormulaTransformFormulaOutputRowsBranchPayloadEnvelopeFromData
      have hbranch := outputRowsZeroSelectedPayloadEnvelope_mono tokenTable
        width tokenCount current next mode tag consumedCount mappedHead
        (compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_publicFinite
          tokenTable width tokenCount current.outputBoundary
          current.outputCount next.outputBoundary next.outputCount hsame)
      refine hbranch.trans ?_
      unfold
        compactFormulaTransformFormulaOutputRowsPublicFinitePayloadEnvelope
      dsimp only
      omega
  | rawZero hcount hconsumed hmode hsource =>
      unfold
        compactFormulaTransformFormulaOutputRowsBranchPayloadEnvelopeFromData
      have hbranch := outputRowsRawSelectedPayloadEnvelope_mono tokenTable
        width tokenCount current next mode tag consumedCount mappedHead
        (show rawModeZeroPayloadEnvelope mode <=
          rawModeZeroPayloadEnvelope mode from le_rfl)
        (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_publicFinite
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource)
      refine hbranch.trans ?_
      unfold
        compactFormulaTransformFormulaOutputRowsPublicFinitePayloadEnvelope
      dsimp only
      omega
  | rawOne hcount hconsumed hmode hsource =>
      unfold
        compactFormulaTransformFormulaOutputRowsBranchPayloadEnvelopeFromData
      have hbranch := outputRowsRawSelectedPayloadEnvelope_mono tokenTable
        width tokenCount current next mode tag consumedCount mappedHead
        (show rawModeOnePayloadEnvelope mode <=
          rawModeOnePayloadEnvelope mode from le_rfl)
        (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_publicFinite
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource)
      refine hbranch.trans ?_
      unfold
        compactFormulaTransformFormulaOutputRowsPublicFinitePayloadEnvelope
      dsimp only
      omega
  | rawTwo hcount hconsumed hmode hsource =>
      unfold
        compactFormulaTransformFormulaOutputRowsBranchPayloadEnvelopeFromData
      have hbranch := outputRowsRawSelectedPayloadEnvelope_mono tokenTable
        width tokenCount current next mode tag consumedCount mappedHead
        (show rawModeTwoPayloadEnvelope mode <=
          rawModeTwoPayloadEnvelope mode from le_rfl)
        (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_publicFinite
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource)
      refine hbranch.trans ?_
      unfold
        compactFormulaTransformFormulaOutputRowsPublicFinitePayloadEnvelope
      dsimp only
      omega
  | rawFive hcount hconsumed hmode hsource =>
      unfold
        compactFormulaTransformFormulaOutputRowsBranchPayloadEnvelopeFromData
      have hbranch := outputRowsRawSelectedPayloadEnvelope_mono tokenTable
        width tokenCount current next mode tag consumedCount mappedHead
        (show rawModeFivePayloadEnvelope mode <=
          rawModeFivePayloadEnvelope mode from le_rfl)
        (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_publicFinite
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource)
      refine hbranch.trans ?_
      unfold
        compactFormulaTransformFormulaOutputRowsPublicFinitePayloadEnvelope
      dsimp only
      omega
  | sameFour hcount hconsumed hmode hsame =>
      unfold
        compactFormulaTransformFormulaOutputRowsBranchPayloadEnvelopeFromData
      have hbranch := outputRowsSameFourSelectedPayloadEnvelope_mono tokenTable
        width tokenCount current next mode tag consumedCount mappedHead
        (show outputRowsNativeEqStructuralEnvelope
            (shortBinaryNumeralTerm mode) (‘4’ : ValuationTerm) <=
          outputRowsNativeEqStructuralEnvelope
            (shortBinaryNumeralTerm mode) (‘4’ : ValuationTerm) from le_rfl)
        (compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_publicFinite
          tokenTable width tokenCount current.outputBoundary
          current.outputCount next.outputBoundary next.outputCount hsame)
      refine hbranch.trans ?_
      unfold
        compactFormulaTransformFormulaOutputRowsPublicFinitePayloadEnvelope
      dsimp only
      omega
  | mapped hcount hconsumed hmodeZero hmodeOne hmodeTwo hmodeFour hmodeFive
      htag hrows =>
      unfold
        compactFormulaTransformFormulaOutputRowsBranchPayloadEnvelopeFromData
      have hbranch := outputRowsMappedSelectedPayloadEnvelope_mono tokenTable
        width tokenCount current next mode tag consumedCount mappedHead
        (compactNegationFormulaTagGraphPayloadEnvelope_le_publicFinite tag
          mappedHead htag)
        (compactAdditiveNatListAppendMappedSourcePrefixGraphPayloadEnvelope_le_publicFinite
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputBoundary next.outputCount mappedHead hrows)
      refine hbranch.trans ?_
      unfold
        compactFormulaTransformFormulaOutputRowsPublicFinitePayloadEnvelope
      dsimp only
      omega

theorem
    compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (data : CompactFormulaTransformFormulaOutputRowsCheckedBranchData
      tokenTable width tokenCount current next mode tag consumedCount
      mappedHead) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead data) <=
      compactFormulaTransformFormulaOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode tag consumedCount
        mappedHead data := by
  cases data with
  | zero hcount hconsumed hsame =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let zeroCertificate :=
        consumedCountZeroCertificate consumedCount hconsumed
      let sameCertificate :=
        compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.outputBoundary
          current.outputCount next.outputBoundary next.outputCount hsame
      have hcountResource :=
        consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
          current next consumedCount hcount
      have hzeroResource :=
        consumedCountZeroCertificate_structuralPayloadBound_le_transparent
          consumedCount hconsumed
      have hsameResource :=
        compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current.outputBoundary
          current.outputCount next.outputBoundary next.outputCount hsame
      have hselected :=
        outputRowsZeroSelectedCertificate_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead countCertificate zeroCertificate sameCertificate
          (compactAdditiveNatListSameRowsGraphPayloadEnvelope tokenTable width
            tokenCount current.outputBoundary current.outputCount
            next.outputBoundary next.outputCount hsame)
          hcountResource hzeroResource hsameResource
      change
        hybridFormulaStructuralPayloadBound
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              countCertificate
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (right := outputRowsPositiveCaseFormula tokenTable width tokenCount
                  current next mode tag consumedCount mappedHead)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  zeroCertificate sameCertificate))) <=
          outputRowsZeroSelectedPayloadEnvelope tokenTable width tokenCount
            current next mode tag consumedCount mappedHead
            (compactAdditiveNatListSameRowsGraphPayloadEnvelope tokenTable width
              tokenCount current.outputBoundary current.outputCount
              next.outputBoundary next.outputCount hsame)
      exact hselected

  | rawZero hcount hconsumed hmode hsource =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate : CheckedHybridValuationBoundedFormulaCertificate
          outputRowsZeroValuation
          (rawModeFormula (shortBinaryNumeralTerm mode)) :=
        .disjunctionLeft
          (modeNativeEqualityCertificate mode (‘0’ : ValuationTerm) 0
            (termValue_arithmeticZero outputRowsZeroValuation) hmode)
      let sourceCertificate :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource
      have hcountResource :=
        consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
          current next consumedCount hcount
      have hpositiveResource :=
        consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
          consumedCount hconsumed
      have hmodeResource :=
        rawModeZeroCertificate_structuralPayloadBound_le_transparent mode hmode
      have hsourceResource :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource
      have hselected :=
        outputRowsRawSelectedCertificate_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead countCertificate positiveCertificate modeCertificate
          sourceCertificate (rawModeZeroPayloadEnvelope mode)
          (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish next.finish
            next.outputCount hsource)
          hcountResource hpositiveResource hmodeResource hsourceResource
      exact hselected
  | rawOne hcount hconsumed hmode hsource =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate : CheckedHybridValuationBoundedFormulaCertificate
          outputRowsZeroValuation
          (rawModeFormula (shortBinaryNumeralTerm mode)) :=
        .disjunctionRight (.disjunctionLeft
          (modeNativeEqualityCertificate mode (‘1’ : ValuationTerm) 1
            (termValue_arithmeticOne outputRowsZeroValuation) hmode))
      let sourceCertificate :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource
      have hcountResource :=
        consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
          current next consumedCount hcount
      have hpositiveResource :=
        consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
          consumedCount hconsumed
      have hmodeResource :=
        rawModeOneCertificate_structuralPayloadBound_le_transparent mode hmode
      have hsourceResource :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource
      have hselected :=
        outputRowsRawSelectedCertificate_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead countCertificate positiveCertificate modeCertificate
          sourceCertificate (rawModeOnePayloadEnvelope mode)
          (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish next.finish
            next.outputCount hsource)
          hcountResource hpositiveResource hmodeResource hsourceResource
      exact hselected
  | rawTwo hcount hconsumed hmode hsource =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate : CheckedHybridValuationBoundedFormulaCertificate
          outputRowsZeroValuation
          (rawModeFormula (shortBinaryNumeralTerm mode)) :=
        .disjunctionRight (.disjunctionRight (.disjunctionLeft
          (modeNativeEqualityCertificate mode (‘2’ : ValuationTerm) 2
            (termValue_arithmeticTwo outputRowsZeroValuation) hmode)))
      let sourceCertificate :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource
      have hcountResource :=
        consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
          current next consumedCount hcount
      have hpositiveResource :=
        consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
          consumedCount hconsumed
      have hmodeResource :=
        rawModeTwoCertificate_structuralPayloadBound_le_transparent mode hmode
      have hsourceResource :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource
      have hselected :=
        outputRowsRawSelectedCertificate_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead countCertificate positiveCertificate modeCertificate
          sourceCertificate (rawModeTwoPayloadEnvelope mode)
          (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish next.finish
            next.outputCount hsource)
          hcountResource hpositiveResource hmodeResource hsourceResource
      exact hselected
  | rawFive hcount hconsumed hmode hsource =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate : CheckedHybridValuationBoundedFormulaCertificate
          outputRowsZeroValuation
          (rawModeFormula (shortBinaryNumeralTerm mode)) :=
        .disjunctionRight (.disjunctionRight (.disjunctionRight
          (modeNativeEqualityCertificate mode (‘5’ : ValuationTerm) 5
            (termValue_arithmeticFive outputRowsZeroValuation) hmode)))
      let sourceCertificate :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource
      have hcountResource :=
        consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
          current next consumedCount hcount
      have hpositiveResource :=
        consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
          consumedCount hconsumed
      have hmodeResource :=
        rawModeFiveCertificate_structuralPayloadBound_le_transparent mode hmode
      have hsourceResource :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource
      have hselected :=
        outputRowsRawSelectedCertificate_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead countCertificate positiveCertificate modeCertificate
          sourceCertificate (rawModeFivePayloadEnvelope mode)
          (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish next.finish
            next.outputCount hsource)
          hcountResource hpositiveResource hmodeResource hsourceResource
      exact hselected
  | sameFour hcount hconsumed hmode hsame =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate :=
        modeNativeEqualityCertificate mode (‘4’ : ValuationTerm) 4
          (termValue_arithmeticFour outputRowsZeroValuation) hmode
      let sameCertificate :=
        compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.outputBoundary
          current.outputCount next.outputBoundary next.outputCount hsame
      have hcountResource :=
        consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
          current next consumedCount hcount
      have hpositiveResource :=
        consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
          consumedCount hconsumed
      have hmodeResource :=
        modeNativeEqualityCertificate_structuralPayloadBound_le_transparent
          mode (‘4’ : ValuationTerm) 4
          (termValue_arithmeticFour outputRowsZeroValuation) hmode
      have hsameResource :=
        compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current.outputBoundary
          current.outputCount next.outputBoundary next.outputCount hsame
      have hselected :=
        outputRowsSameFourSelectedCertificate_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead countCertificate positiveCertificate modeCertificate
          sameCertificate
          (outputRowsNativeEqStructuralEnvelope (shortBinaryNumeralTerm mode)
            (‘4’ : ValuationTerm))
          (compactAdditiveNatListSameRowsGraphPayloadEnvelope tokenTable width
            tokenCount current.outputBoundary current.outputCount
            next.outputBoundary next.outputCount hsame)
          hcountResource hpositiveResource hmodeResource hsameResource
      exact hselected
  | mapped hcount hconsumed hmodeZero hmodeOne hmodeTwo hmodeFour hmodeFive
      htag hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let tagCertificate :=
        compactNegationFormulaTagExplicitHybridCertificateOfGraph
          tag mappedHead htag
      let rowsCertificate :=
        compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputBoundary next.outputCount mappedHead hrows
      let mappedTail :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          tagCertificate rowsCertificate
      let mappedCertificate := otherModeWithTailCertificate mode hmodeZero
        hmodeOne hmodeTwo hmodeFour hmodeFive
        (outputRowsMappedTailFormula tokenTable width tokenCount current next tag
          consumedCount mappedHead) mappedTail
      have hcountResource :=
        consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
          current next consumedCount hcount
      have hpositiveResource :=
        consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
          consumedCount hconsumed
      have htagResource :=
        compactNegationFormulaTagExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
          tag mappedHead htag
      have hrowsResource :=
        compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputBoundary next.outputCount mappedHead hrows
      have hmappedTail := transparentHybridConjunctionPayloadBound_le
        tagCertificate rowsCertificate _ _ htagResource hrowsResource
      have hmappedResource :=
        otherModeWithTailCertificate_structuralPayloadBound_le_transparent
          mode hmodeZero hmodeOne hmodeTwo hmodeFour hmodeFive
          (outputRowsMappedTailFormula tokenTable width tokenCount current next
            tag consumedCount mappedHead) mappedTail
          (transparentHybridConjunctionPayloadEnvelope
            FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
            (compactNegationFormulaTagClosedFormula tag mappedHead)
            (compactAdditiveNatListAppendMappedSourcePrefixClosedFormula
              tokenTable width tokenCount current.parserFinish current.finish
              current.outputCount current.start current.parserTokensFinish
              current.parserTokensCount consumedCount next.parserFinish
              next.finish next.outputBoundary next.outputCount mappedHead)
            (compactNegationFormulaTagGraphPayloadEnvelope tag mappedHead htag)
            (compactAdditiveNatListAppendMappedSourcePrefixGraphPayloadEnvelope
              tokenTable width tokenCount current.parserFinish current.finish
              current.outputCount current.start current.parserTokensFinish
              current.parserTokensCount consumedCount next.parserFinish
              next.finish next.outputBoundary next.outputCount mappedHead hrows))
          hmappedTail
      have hselected :=
        outputRowsMappedSelectedCertificate_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead countCertificate positiveCertificate mappedCertificate
          (compactNegationFormulaTagGraphPayloadEnvelope tag mappedHead htag)
          (compactAdditiveNatListAppendMappedSourcePrefixGraphPayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish next.finish
            next.outputBoundary next.outputCount mappedHead hrows)
          hcountResource hpositiveResource hmappedResource
      change
        hybridFormulaStructuralPayloadBound
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              countCertificate
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left := outputRowsZeroCaseFormula tokenTable width tokenCount
                  current next consumedCount)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  positiveCertificate
                  (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                    (left := outputRowsRawCaseFormula tokenTable width tokenCount
                      current next mode consumedCount)
                    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                      (left := outputRowsSameFourCaseFormula tokenTable width
                        tokenCount current next mode) mappedCertificate))))) <=
          outputRowsMappedSelectedPayloadEnvelope tokenTable width tokenCount
            current next mode tag consumedCount mappedHead
            (compactNegationFormulaTagGraphPayloadEnvelope tag mappedHead htag)
            (compactAdditiveNatListAppendMappedSourcePrefixGraphPayloadEnvelope
              tokenTable width tokenCount current.parserFinish current.finish
              current.outputCount current.start current.parserTokensFinish
              current.parserTokensCount consumedCount next.parserFinish next.finish
              next.outputBoundary next.outputCount mappedHead hrows)
      exact hselected

noncomputable def compactFormulaTransformFormulaOutputRowsGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (hgraph : CompactFormulaTransformFormulaOutputRows
      tokenTable width tokenCount current next mode tag consumedCount
      mappedHead) : Nat :=
  compactFormulaTransformFormulaOutputRowsBranchPayloadEnvelopeFromData
    tokenTable width tokenCount current next mode tag consumedCount mappedHead
    (compactFormulaTransformFormulaOutputRowsCheckedBranchDataOfGraph
      tokenTable width tokenCount current next mode tag consumedCount mappedHead
      hgraph)

theorem
    compactFormulaTransformFormulaOutputRowsGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (hgraph : CompactFormulaTransformFormulaOutputRows
      tokenTable width tokenCount current next mode tag consumedCount
      mappedHead) :
    compactFormulaTransformFormulaOutputRowsGraphPayloadEnvelope tokenTable
        width tokenCount current next mode tag consumedCount mappedHead hgraph <=
      compactFormulaTransformFormulaOutputRowsPublicFinitePayloadEnvelope
        tokenTable width tokenCount current next mode tag consumedCount
        mappedHead := by
  unfold compactFormulaTransformFormulaOutputRowsGraphPayloadEnvelope
  exact
    compactFormulaTransformFormulaOutputRowsBranchPayloadEnvelopeFromData_le_publicFinite
      tokenTable width tokenCount current next mode tag consumedCount mappedHead
      (compactFormulaTransformFormulaOutputRowsCheckedBranchDataOfGraph
        tokenTable width tokenCount current next mode tag consumedCount
        mappedHead hgraph)

theorem
    compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (hgraph : CompactFormulaTransformFormulaOutputRows
      tokenTable width tokenCount current next mode tag consumedCount
      mappedHead) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead hgraph) <=
      compactFormulaTransformFormulaOutputRowsGraphPayloadEnvelope tokenTable width
        tokenCount current next mode tag consumedCount mappedHead hgraph := by
  let data := compactFormulaTransformFormulaOutputRowsCheckedBranchDataOfGraph
    tokenTable width tokenCount current next mode tag consumedCount mappedHead
    hgraph
  have hbranch :=
    compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode tag consumedCount mappedHead
      data
  unfold compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph
  simp only [hybridFormulaStructuralPayloadBound]
  unfold compactFormulaTransformFormulaOutputRowsGraphPayloadEnvelope
  change hybridFormulaStructuralPayloadBound
      (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData
        tokenTable width tokenCount current next mode tag consumedCount mappedHead
        data) <=
    compactFormulaTransformFormulaOutputRowsBranchPayloadEnvelopeFromData
      tokenTable width tokenCount current next mode tag consumedCount mappedHead
      data
  exact hbranch

theorem
    compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (hgraph : CompactFormulaTransformFormulaOutputRows
      tokenTable width tokenCount current next mode tag consumedCount
      mappedHead) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead hgraph) <=
      compactFormulaTransformFormulaOutputRowsPublicFinitePayloadEnvelope
        tokenTable width tokenCount current next mode tag consumedCount
        mappedHead := by
  exact
    (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode tag consumedCount mappedHead
      hgraph).trans
    (compactFormulaTransformFormulaOutputRowsGraphPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount current next mode tag consumedCount mappedHead
      hgraph)

#print axioms nativeEqCertificate_structuralPayloadBound_le_transparent
#print axioms nativeNeCertificate_structuralPayloadBound_le_transparent
#print axioms nativeLeCertificate_structuralPayloadBound_le_transparent
#print axioms otherModeWithTailCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData_structuralPayloadBound_le_transparent
#print axioms
  compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
#print axioms
  compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsPublicBounds
