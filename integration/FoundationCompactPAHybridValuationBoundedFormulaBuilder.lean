import integration.FoundationCompactPAFastArithmeticLeafRecognizer
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompiler
import integration.FoundationCompactPANativeFastArithmeticSemantics

/-!
# Automatic hybrid certificates for true bounded formulas

Whole `expDef`, `lengthDef`, and positive or negative `bitDef` instances are
recognized before structural recursion.  All other constructors follow the
checked sigma-zero builder.  Thus large arithmetic leaves use their binary PA
compilers and are never unfolded merely because the surrounding formula is
bounded.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAHybridValuationBoundedFormulaBuilder

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFastArithmeticLeafRecognizer
open FoundationCompactPANativeFastArithmeticSemantics
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

abbrev HybridCertificate :=
  CheckedHybridValuationBoundedFormulaCertificate

abbrev HybridUniversalBranches :=
  CheckedHybridValuationUniversalBranches

theorem universalBranches_nonempty_of_each
    {valuation : Nat -> Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (bound : Nat)
    (hcertificate : ∀ index, index < bound ->
      Nonempty (HybridCertificate
        (extendValuation index valuation) (Rewriting.free body))) :
    Nonempty (HybridUniversalBranches valuation body bound) := by
  induction bound with
  | zero => exact
      ⟨CheckedHybridValuationUniversalBranches.nil valuation body⟩
  | succ previousBound inductionHypothesis =>
      have hprefix : ∀ index, index < previousBound ->
          Nonempty (HybridCertificate
            (extendValuation index valuation) (Rewriting.free body)) := by
        intro index hindex
        exact hcertificate index
          (Nat.lt_trans hindex (Nat.lt_succ_self previousBound))
      rcases inductionHypothesis hprefix with ⟨initial⟩
      rcases hcertificate previousBound (Nat.lt_succ_self previousBound) with
        ⟨last⟩
      exact ⟨CheckedHybridValuationUniversalBranches.snoc initial last⟩

theorem certificate_nonempty_of_sigmaZero_truth
    (formula : ValuationFormula)
    (hhierarchy : Hierarchy Polarity.sigma 0 formula)
    (valuation : Nat -> Nat)
    (htruth : formulaValue valuation formula) :
    Nonempty (HybridCertificate valuation formula) := by
  cases hrecognition : recognizeArithmeticLeaf formula with
  | some recognition =>
      cases hkind : recognition.kind with
      | «exp» =>
          have hformula : formula =
              expInstance recognition.first recognition.second := by
            simpa [ArithmeticLeafKind.instantiate, hkind] using
              recognition.sound
          have hleafTruth : formulaValue valuation
              (expInstance recognition.first recognition.second) := by
            rw [← hformula]
            exact htruth
          have hvalue := expInstance_value valuation
            recognition.first recognition.second hleafTruth
          let source : HybridCertificate valuation
              (exponentialAtValuationFormula
                recognition.first recognition.second) :=
            .exponential valuation recognition.first recognition.second hvalue
          have htarget :
              exponentialAtValuationFormula
                  recognition.first recognition.second = formula := by
            calc
              exponentialAtValuationFormula
                  recognition.first recognition.second =
                    expInstance recognition.first recognition.second := rfl
              _ = formula := hformula.symm
          exact ⟨CheckedHybridValuationBoundedFormulaCertificate.cast
            htarget source⟩
      | «length» =>
          have hformula : formula =
              lengthInstance recognition.first recognition.second := by
            simpa [ArithmeticLeafKind.instantiate, hkind] using
              recognition.sound
          have hleafTruth : formulaValue valuation
              (lengthInstance recognition.first recognition.second) := by
            rw [← hformula]
            exact htruth
          have hsize := lengthInstance_value valuation
            recognition.first recognition.second hleafTruth
          let source : HybridCertificate valuation
              (binaryLengthAtValuationFormula
                recognition.first recognition.second) :=
            .binaryLength valuation recognition.first recognition.second hsize
          have htarget :
              binaryLengthAtValuationFormula
                  recognition.first recognition.second = formula := by
            calc
              binaryLengthAtValuationFormula
                  recognition.first recognition.second =
                    lengthInstance recognition.first recognition.second := rfl
              _ = formula := hformula.symm
          exact ⟨CheckedHybridValuationBoundedFormulaCertificate.cast
            htarget source⟩
      | bit =>
          have hformula : formula =
              bitInstance recognition.first recognition.second := by
            simpa [ArithmeticLeafKind.instantiate, hkind] using
              recognition.sound
          have hleafTruth : formulaValue valuation
              (bitInstance recognition.first recognition.second) := by
            rw [← hformula]
            exact htruth
          have hbit := bitInstance_value valuation
            recognition.first recognition.second hleafTruth
          have htarget :
              binaryBitAtValuationFormula true
                  recognition.first recognition.second = formula := by
            calc
              binaryBitAtValuationFormula true
                  recognition.first recognition.second =
                    bitInstance recognition.first recognition.second := rfl
              _ = formula := hformula.symm
          have hvariables :
              recognition.first.freeVariables ∪
                  recognition.second.freeVariables ⊆
                (binaryBitAtValuationFormula true
                  recognition.first recognition.second).freeVariables := by
            intro index hindex
            have hmember :=
              recognition.freeVariables_union_subset hindex
            exact (congrArg
              (fun candidate : ValuationFormula => candidate.freeVariables)
              htarget).symm ▸ hmember
          let source : HybridCertificate valuation
              (binaryBitAtValuationFormula true
                recognition.first recognition.second) :=
            .binaryBit true valuation recognition.first recognition.second
              hbit hvariables
          exact ⟨CheckedHybridValuationBoundedFormulaCertificate.cast
            htarget source⟩
      | notBit =>
          have hformula : formula =
              ∼bitInstance recognition.first recognition.second := by
            simpa [ArithmeticLeafKind.instantiate, hkind] using
              recognition.sound
          have hleafTruth : formulaValue valuation
              (∼bitInstance recognition.first recognition.second) := by
            rw [← hformula]
            exact htruth
          have hbit := notBitInstance_value valuation
            recognition.first recognition.second hleafTruth
          have htarget :
              binaryBitAtValuationFormula false
                  recognition.first recognition.second = formula := by
            calc
              binaryBitAtValuationFormula false
                  recognition.first recognition.second =
                    ∼bitInstance recognition.first recognition.second := rfl
              _ = formula := hformula.symm
          have hvariables :
              recognition.first.freeVariables ∪
                  recognition.second.freeVariables ⊆
                (binaryBitAtValuationFormula false
                  recognition.first recognition.second).freeVariables := by
            intro index hindex
            have hmember :=
              recognition.freeVariables_union_subset hindex
            exact (congrArg
              (fun candidate : ValuationFormula => candidate.freeVariables)
              htarget).symm ▸ hmember
          let source : HybridCertificate valuation
              (binaryBitAtValuationFormula false
                recognition.first recognition.second) :=
            .binaryBit false valuation recognition.first recognition.second
              hbit hvariables
          exact ⟨CheckedHybridValuationBoundedFormulaCertificate.cast
            htarget source⟩
  | none =>
      cases formula using LO.FirstOrder.Semiformula.cases' with
      | hverum =>
          exact ⟨CheckedHybridValuationBoundedFormulaCertificate.verum
            valuation⟩
      | hfalsum =>
          have himpossible : False := by
            simpa [formulaValue] using htruth
          exact False.elim himpossible
      | hrel relationSymbol args =>
          cases relationSymbol with
          | eq => exact ⟨CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
              valuation Language.Eq.eq args htruth⟩
          | lt => exact ⟨CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
              valuation Language.ORing.Rel.lt args htruth⟩
      | hnrel relationSymbol args =>
          cases relationSymbol with
          | eq => exact ⟨CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
              valuation Language.Eq.eq args htruth⟩
          | lt => exact ⟨CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
              valuation Language.ORing.Rel.lt args htruth⟩
      | hand left right =>
          have hchildren : Hierarchy Polarity.sigma 0 left ∧
              Hierarchy Polarity.sigma 0 right := by
            simpa using hhierarchy
          have hvalues : formulaValue valuation left ∧
              formulaValue valuation right := by
            simpa [formulaValue] using htruth
          rcases certificate_nonempty_of_sigmaZero_truth
            left hchildren.1 valuation hvalues.1 with ⟨leftCertificate⟩
          rcases certificate_nonempty_of_sigmaZero_truth
            right hchildren.2 valuation hvalues.2 with ⟨rightCertificate⟩
          exact ⟨CheckedHybridValuationBoundedFormulaCertificate.conjunction
            leftCertificate rightCertificate⟩
      | hor left right =>
          have hchildren : Hierarchy Polarity.sigma 0 left ∧
              Hierarchy Polarity.sigma 0 right := by
            simpa using hhierarchy
          have hvalue : formulaValue valuation left ∨
              formulaValue valuation right := by
            simpa [formulaValue] using htruth
          rcases hvalue with hleft | hright
          · rcases certificate_nonempty_of_sigmaZero_truth
              left hchildren.1 valuation hleft with ⟨leftCertificate⟩
            exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              leftCertificate⟩
          · rcases certificate_nonempty_of_sigmaZero_truth
              right hchildren.2 valuation hright with ⟨rightCertificate⟩
            exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              rightCertificate⟩
      | hall quantifiedBody =>
          cases hhierarchy with
          | ball boundPositive bodyHierarchy =>
              rename_i boundedBody boundTerm
              let boundSource := lowerPositiveTerm boundTerm boundPositive
              have hboundTerm := bShift_lowerPositiveTerm
                boundTerm boundPositive
              have hsourceTruth : formulaValue valuation
                  (∀⁰[“x. x < !!(Rew.bShift boundSource)”]
                    boundedBody) := by
                rw [hboundTerm]
                exact htruth
              let bound := termValue valuation boundSource
              have hbranchTruth : ∀ index, index < bound ->
                  formulaValue (extendValuation index valuation)
                    (Rewriting.free boundedBody) := by
                intro index hindex
                exact ball_body_truth valuation boundSource boundedBody
                  hsourceTruth index hindex
              have hfreeHierarchy : Hierarchy Polarity.sigma 0
                  (Rewriting.free boundedBody) :=
                bodyHierarchy.rew Rew.free
              have hbranchCertificates : ∀ index, index < bound ->
                  Nonempty (HybridCertificate
                    (extendValuation index valuation)
                    (Rewriting.free boundedBody)) := by
                intro index hindex
                exact certificate_nonempty_of_sigmaZero_truth
                  (Rewriting.free boundedBody) hfreeHierarchy
                  (extendValuation index valuation)
                  (hbranchTruth index hindex)
              rcases universalBranches_nonempty_of_each bound
                hbranchCertificates with ⟨branches⟩
              let sourceCertificate :=
                CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
                  boundSource boundedBody branches
              have hformula :
                  (∀⁰ termBoundedUniversalBody
                    (Rew.bShift boundSource) boundedBody) =
                  (∀⁰[“x. x < !!boundTerm”] boundedBody) := by
                rw [termBoundedUniversal_eq_ball]
                rw [hboundTerm]
              exact ⟨CheckedHybridValuationBoundedFormulaCertificate.cast
                hformula sourceCertificate⟩
      | hexs quantifiedBody =>
          cases hhierarchy with
          | bexs boundPositive bodyHierarchy =>
              rename_i boundedBody boundTerm
              let boundedMatrix :
                  LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
                (“#0 < !!boundTerm” ⋏ boundedBody)
              have hquantifiedHierarchy : Hierarchy Polarity.sigma 0
                  boundedMatrix := by
                have hguardHierarchy : Hierarchy Polarity.sigma 0
                    (“#0 < !!boundTerm” :
                      LO.FirstOrder.ArithmeticSemiformula Nat 1) := by
                  simp
                exact Hierarchy.and hguardHierarchy bodyHierarchy
              have hexists : ∃ witness : Nat,
                  LO.FirstOrder.Semiformula.Eval ![witness] valuation
                    boundedMatrix := by
                simpa [formulaValue, boundedMatrix] using htruth
              rcases hexists with ⟨witness, hwitness⟩
              have hsubstitutionHierarchy : Hierarchy Polarity.sigma 0
                  (boundedMatrix/[shortBinaryNumeralTerm witness]) :=
                hquantifiedHierarchy.rew
                  (Rew.subst ![shortBinaryNumeralTerm witness])
              have hsubstitutionTruth : formulaValue valuation
                  (boundedMatrix/[shortBinaryNumeralTerm witness]) :=
                (formulaValue_shortBinarySubstitution
                  valuation boundedMatrix witness).mpr hwitness
              rcases certificate_nonempty_of_sigmaZero_truth
                (boundedMatrix/[shortBinaryNumeralTerm witness])
                hsubstitutionHierarchy valuation hsubstitutionTruth with
                  ⟨bodyCertificate⟩
              simpa [boundedMatrix] using
                (show Nonempty (HybridCertificate valuation
                    (∃⁰ boundedMatrix)) from
                  ⟨CheckedHybridValuationBoundedFormulaCertificate.existsWitness
                    boundedMatrix witness bodyCertificate⟩)
termination_by formula.complexity
decreasing_by
  all_goals
    subst_vars
    simp_all [LO.FirstOrder.ball, LO.FirstOrder.bexs,
      LO.FirstOrder.Semiformula.imp_eq,
      LO.FirstOrder.Semiformula.Operator.operator,
      LO.FirstOrder.Semiformula.Operator.LT.sentence_eq]

noncomputable def ofSigmaZeroTruth
    (formula : ValuationFormula)
    (hhierarchy : Hierarchy Polarity.sigma 0 formula)
    (valuation : Nat -> Nat)
    (htruth : formulaValue valuation formula) :
    HybridCertificate valuation formula :=
  Classical.choice
    (certificate_nonempty_of_sigmaZero_truth
      formula hhierarchy valuation htruth)

noncomputable def compileSigmaZeroTruth
    (formula : ValuationFormula)
    (hhierarchy : Hierarchy Polarity.sigma 0 formula)
    (valuation : Nat -> Nat)
    (htruth : formulaValue valuation formula) :=
  (ofSigmaZeroTruth formula hhierarchy valuation htruth).compile

#print axioms certificate_nonempty_of_sigmaZero_truth
#print axioms compileSigmaZeroTruth

end FoundationCompactPAHybridValuationBoundedFormulaBuilder
