import integration.FoundationCompactPAHybridValuationBoundedFormulaCompiler

/-!
# Explicit finite branch builder for hybrid bounded universals

The caller supplies a concrete certificate for every branch.  The builder
recurses on the numeric bound and constructs `nil`/`snoc` directly; it never
turns a `Nonempty` proposition into certificate data.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactPAExplicitHybridUniversalBranches

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

/-- Assemble all branches of a hybrid bounded universal from an explicit
branch-producing function. -/
def buildExplicitHybridUniversalBranches
    {valuation : Nat -> Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (bound : Nat)
    (branch : ∀ index, index < bound ->
      CheckedHybridValuationBoundedFormulaCertificate
        (extendValuation index valuation) (Rewriting.free body)) :
    CheckedHybridValuationUniversalBranches valuation body bound := by
  induction bound with
  | zero => exact .nil valuation body
  | succ previous inductionHypothesis =>
      let initial := inductionHypothesis (fun index hindex =>
        branch index
          (Nat.lt_trans hindex (Nat.lt_succ_self previous)))
      let last := branch previous (Nat.lt_succ_self previous)
      exact .snoc initial last

#print axioms buildExplicitHybridUniversalBranches

end FoundationCompactPAExplicitHybridUniversalBranches
