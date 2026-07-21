import integration.FoundationCompactPAHybridValuationBoundedFormulaCompiler

/-!
# Explicit finite conjunctions for hybrid certificates

The caller supplies one checked certificate for every member of a `Fin`-indexed
formula vector.  The constructor follows `List.ofFn` and `List.conj₂` directly;
it never recovers certificate data from semantic truth.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAExplicitHybridOfFnConjunction

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

/-- Assemble the exact `List.ofFn ... |>.conj₂` formula from an explicit
certificate-producing function. -/
noncomputable def buildExplicitHybridOfFnConjunctionCertificate
    {valuation : Nat -> Nat} :
    {arity : Nat} ->
    (formulas : Fin arity -> ValuationFormula) ->
    (certificates : forall coordinate,
      CheckedHybridValuationBoundedFormulaCertificate valuation
        (formulas coordinate)) ->
    CheckedHybridValuationBoundedFormulaCertificate valuation
      (List.ofFn formulas).conj₂
  | 0, formulas, certificates => by
      rw [List.ofFn_zero]
      exact .verum valuation
  | arity + 1, formulas, certificates => by
      cases arity with
      | zero =>
          simpa [List.ofFn_succ, List.ofFn_zero] using certificates 0
      | succ rest =>
          rw [List.ofFn_succ]
          rw [List.conj₂_cons_nonempty (by simp [List.ofFn_succ])]
          exact .conjunction
            (certificates 0)
            (buildExplicitHybridOfFnConjunctionCertificate
              (formulas := fun coordinate : Fin (rest + 1) =>
                formulas coordinate.succ)
              (certificates := fun coordinate => certificates coordinate.succ))

#print axioms buildExplicitHybridOfFnConjunctionCertificate

end FoundationCompactPAExplicitHybridOfFnConjunction
