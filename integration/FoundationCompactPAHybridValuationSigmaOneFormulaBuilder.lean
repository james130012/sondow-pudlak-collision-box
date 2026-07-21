import integration.FoundationCompactPAHybridValuationBoundedFormulaBuilder

/-!
# Automatic hybrid certificates for true Sigma-one formulas

Unbounded existential witnesses are extracted from standard-model truth.
Bounded universal branches use hybrid certificates, while a Sigma-zero matrix
is delegated as a whole to the hybrid bounded builder so fast arithmetic
leaves are recognized before structural recursion.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAHybridValuationSigmaOneFormulaBuilder

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaBuilder

abbrev HybridSigmaOneCertificate :=
  CheckedHybridValuationBoundedFormulaCertificate

theorem hybridSigmaOneCertificate_nonempty_of_truth
    (formula : ValuationFormula)
    (hhierarchy : Hierarchy Polarity.sigma 1 formula)
    (valuation : Nat -> Nat)
    (htruth : formulaValue valuation formula) :
    Nonempty (HybridSigmaOneCertificate valuation formula) := by
  cases formula using LO.FirstOrder.Semiformula.cases' with
  | hverum =>
      exact ⟨.verum valuation⟩
  | hfalsum =>
      have himpossible : False := by
        simpa [formulaValue] using htruth
      exact False.elim himpossible
  | hrel relationSymbol args =>
      cases relationSymbol with
      | eq => exact ⟨.positiveAtomic valuation Language.Eq.eq args htruth⟩
      | lt => exact ⟨.positiveAtomic valuation
          Language.ORing.Rel.lt args htruth⟩
  | hnrel relationSymbol args =>
      cases relationSymbol with
      | eq => exact ⟨.negativeAtomic valuation Language.Eq.eq args htruth⟩
      | lt => exact ⟨.negativeAtomic valuation
          Language.ORing.Rel.lt args htruth⟩
  | hand left right =>
      have hchildren :
          Hierarchy Polarity.sigma 1 left ∧
            Hierarchy Polarity.sigma 1 right := by
        simpa using hhierarchy
      have hvalues : formulaValue valuation left ∧
          formulaValue valuation right := by
        simpa [formulaValue] using htruth
      rcases hybridSigmaOneCertificate_nonempty_of_truth
        left hchildren.1 valuation hvalues.1 with ⟨leftCertificate⟩
      rcases hybridSigmaOneCertificate_nonempty_of_truth
        right hchildren.2 valuation hvalues.2 with ⟨rightCertificate⟩
      exact ⟨.conjunction leftCertificate rightCertificate⟩
  | hor left right =>
      have hchildren :
          Hierarchy Polarity.sigma 1 left ∧
            Hierarchy Polarity.sigma 1 right := by
        simpa using hhierarchy
      have hvalue : formulaValue valuation left ∨
          formulaValue valuation right := by
        simpa [formulaValue] using htruth
      rcases hvalue with hleft | hright
      · rcases hybridSigmaOneCertificate_nonempty_of_truth
          left hchildren.1 valuation hleft with ⟨leftCertificate⟩
        exact ⟨.disjunctionLeft leftCertificate⟩
      · rcases hybridSigmaOneCertificate_nonempty_of_truth
          right hchildren.2 valuation hright with ⟨rightCertificate⟩
        exact ⟨.disjunctionRight rightCertificate⟩
  | hall quantifiedBody =>
      cases hhierarchy with
      | ball boundPositive bodyHierarchy =>
          rename_i boundedBody boundTerm
          let boundSource := lowerPositiveTerm boundTerm boundPositive
          have hboundTerm := bShift_lowerPositiveTerm boundTerm boundPositive
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
          have hfreeHierarchy : Hierarchy Polarity.sigma 1
              (Rewriting.free boundedBody) :=
            bodyHierarchy.rew Rew.free
          have hbranchCertificates : ∀ index, index < bound ->
              Nonempty (HybridSigmaOneCertificate
                (extendValuation index valuation)
                (Rewriting.free boundedBody)) := by
            intro index hindex
            exact hybridSigmaOneCertificate_nonempty_of_truth
              (Rewriting.free boundedBody) hfreeHierarchy
              (extendValuation index valuation)
              (hbranchTruth index hindex)
          have hbranches : Nonempty
              (CheckedHybridValuationUniversalBranches valuation
                boundedBody bound) :=
            universalBranches_nonempty_of_each bound hbranchCertificates
          rcases hbranches with ⟨branches⟩
          let sourceCertificate :=
            CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
              boundSource boundedBody branches
          have hformula :
              (∀⁰ termBoundedUniversalBody
                (Rew.bShift boundSource) boundedBody) =
              (∀⁰[“x. x < !!boundTerm”] boundedBody) := by
            rw [termBoundedUniversal_eq_ball]
            rw [hboundTerm]
          exact ⟨.cast hformula sourceCertificate⟩
  | hexs quantifiedBody =>
      cases hhierarchy with
      | bexs boundPositive bodyHierarchy =>
          rename_i boundedBody boundTerm
          let boundedMatrix :
              LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
            (“#0 < !!boundTerm” ⋏ boundedBody)
          have hquantifiedHierarchy :
              Hierarchy Polarity.sigma 1 boundedMatrix := by
            have hguardHierarchy : Hierarchy Polarity.sigma 1
                (“#0 < !!boundTerm” :
                  LO.FirstOrder.ArithmeticSemiformula Nat 1) := by
              simp
            exact Hierarchy.and hguardHierarchy bodyHierarchy
          have hexists : ∃ witness : Nat,
              LO.FirstOrder.Semiformula.Eval ![witness] valuation
                boundedMatrix := by
            simpa [formulaValue, boundedMatrix] using htruth
          rcases hexists with ⟨witness, hwitness⟩
          have hsubstitutionHierarchy : Hierarchy Polarity.sigma 1
              (boundedMatrix/[shortBinaryNumeralTerm witness]) :=
            hquantifiedHierarchy.rew
              (Rew.subst ![shortBinaryNumeralTerm witness])
          have hsubstitutionTruth : formulaValue valuation
              (boundedMatrix/[shortBinaryNumeralTerm witness]) :=
            (formulaValue_shortBinarySubstitution
              valuation boundedMatrix witness).mpr hwitness
          rcases hybridSigmaOneCertificate_nonempty_of_truth
            (boundedMatrix/[shortBinaryNumeralTerm witness])
            hsubstitutionHierarchy valuation hsubstitutionTruth with
              ⟨bodyCertificate⟩
          simpa [boundedMatrix] using
            (show Nonempty (HybridSigmaOneCertificate valuation
                (∃⁰ boundedMatrix)) from
              ⟨.existsWitness boundedMatrix witness bodyCertificate⟩)
      | exs bodyHierarchy =>
          have hexists : ∃ witness : Nat,
              LO.FirstOrder.Semiformula.Eval ![witness] valuation
                quantifiedBody := by
            simpa [formulaValue] using htruth
          rcases hexists with ⟨witness, hwitness⟩
          have hsubstitutionHierarchy : Hierarchy Polarity.sigma 1
              (quantifiedBody/[shortBinaryNumeralTerm witness]) :=
            bodyHierarchy.rew
              (Rew.subst ![shortBinaryNumeralTerm witness])
          have hsubstitutionTruth : formulaValue valuation
              (quantifiedBody/[shortBinaryNumeralTerm witness]) :=
            (formulaValue_shortBinarySubstitution
              valuation quantifiedBody witness).mpr hwitness
          rcases hybridSigmaOneCertificate_nonempty_of_truth
            (quantifiedBody/[shortBinaryNumeralTerm witness])
            hsubstitutionHierarchy valuation hsubstitutionTruth with
              ⟨bodyCertificate⟩
          exact ⟨.existsWitness quantifiedBody witness bodyCertificate⟩
      | sigma bodyHierarchy =>
          have hbodySigmaZero : Hierarchy Polarity.sigma 0 quantifiedBody :=
            by simpa using Hierarchy.zero_eq_alt bodyHierarchy
          have hexists : ∃ witness : Nat,
              LO.FirstOrder.Semiformula.Eval ![witness] valuation
                quantifiedBody := by
            simpa [formulaValue] using htruth
          rcases hexists with ⟨witness, hwitness⟩
          have hsubstitutionHierarchy : Hierarchy Polarity.sigma 0
              (quantifiedBody/[shortBinaryNumeralTerm witness]) :=
            hbodySigmaZero.rew
              (Rew.subst ![shortBinaryNumeralTerm witness])
          have hsubstitutionTruth : formulaValue valuation
              (quantifiedBody/[shortBinaryNumeralTerm witness]) :=
            (formulaValue_shortBinarySubstitution
              valuation quantifiedBody witness).mpr hwitness
          rcases certificate_nonempty_of_sigmaZero_truth
            (quantifiedBody/[shortBinaryNumeralTerm witness])
            hsubstitutionHierarchy valuation hsubstitutionTruth with
              ⟨bodyCertificate⟩
          exact ⟨.existsWitness quantifiedBody witness bodyCertificate⟩
termination_by formula.complexity
decreasing_by
  all_goals
    subst_vars
    simp_all [LO.FirstOrder.ball, LO.FirstOrder.bexs,
      LO.FirstOrder.Semiformula.imp_eq,
      LO.FirstOrder.Semiformula.Operator.operator,
      LO.FirstOrder.Semiformula.Operator.LT.sentence_eq]

noncomputable def ofHybridSigmaOneTruth
    (formula : ValuationFormula)
    (hhierarchy : Hierarchy Polarity.sigma 1 formula)
    (valuation : Nat -> Nat)
    (htruth : formulaValue valuation formula) :
    HybridSigmaOneCertificate valuation formula :=
  Classical.choice
    (hybridSigmaOneCertificate_nonempty_of_truth
      formula hhierarchy valuation htruth)

noncomputable def compileHybridSigmaOneTruth
    (formula : ValuationFormula)
    (hhierarchy : Hierarchy Polarity.sigma 1 formula)
    (valuation : Nat -> Nat)
    (htruth : formulaValue valuation formula) :
    FoundationCompactCertifiedContextProof.CertifiedPAContextProof
      (valuationContext formula.freeVariables valuation) formula :=
  (ofHybridSigmaOneTruth formula hhierarchy valuation htruth).compile

#print axioms hybridSigmaOneCertificate_nonempty_of_truth
#print axioms compileHybridSigmaOneTruth

end FoundationCompactPAHybridValuationSigmaOneFormulaBuilder
