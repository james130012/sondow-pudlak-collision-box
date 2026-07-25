import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryGuardFullyFixedBounds

/-!
# Opaque names for the complete binary syntax-task row formula

The guard and the two-witness formula are named opaquely so downstream
resource combinators do not repeatedly normalize their full syntax trees.
The defining equalities remain explicit theorems.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryFormulaNames

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate

@[irreducible] def syntaxTaskAtRowsBinaryGuardFormula
    (count index : Nat) : ValuationFormula :=
  “!!(nativeNumeralTerm index) < !!(shortBinaryNumeralTerm count)”

theorem syntaxTaskAtRowsBinaryGuardFormula_eq
    (count index : Nat) :
    syntaxTaskAtRowsBinaryGuardFormula count index =
      “!!(nativeNumeralTerm index) < !!(shortBinaryNumeralTerm count)” := by
  unfold syntaxTaskAtRowsBinaryGuardFormula
  rfl

@[irreducible] def syntaxTaskAtRowsBinaryWitnessFormula
    (tokenTable width tokenCount boundaryTable index binderArity : Nat) :
    ValuationFormula :=
  compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula tokenTable
    width tokenCount boundaryTable (nativeNumeralTerm index)
    (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
    (nativeNumeralTerm 0)

theorem syntaxTaskAtRowsBinaryWitnessFormula_eq
    (tokenTable width tokenCount boundaryTable index binderArity : Nat) :
    syntaxTaskAtRowsBinaryWitnessFormula tokenTable width tokenCount
        boundaryTable index binderArity =
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula
        tokenTable width tokenCount boundaryTable (nativeNumeralTerm index)
        (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
        (nativeNumeralTerm 0) := by
  unfold syntaxTaskAtRowsBinaryWitnessFormula
  rfl

#print axioms syntaxTaskAtRowsBinaryGuardFormula_eq
#print axioms syntaxTaskAtRowsBinaryWitnessFormula_eq

end FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryFormulaNames
