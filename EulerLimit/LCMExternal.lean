/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.SondowForwardReproof

/-!
# External LCM bound

This module keeps the historical external-input names as compatibility shims.
The LCM estimate itself is now supplied by the internal Hanson-Sondow reproof in
`SondowForwardReproof`.
-/

open Chebyshev

/-- Historical name for the internally reproved Hanson-Sondow theorem:
`lcm(1,...,n) ≤ 3^n`. -/
theorem external_lcmUpto_le_three_pow_nat_statement :
    lcmUpto_le_three_pow_nat_statement :=
  lcmUpto_le_three_pow_nat_unconditional

theorem external_lcmUpto_le_three_pow_nat (n : ℕ) :
    Nat.lcmUpto n ≤ 3 ^ n :=
  external_lcmUpto_le_three_pow_nat_statement n

def SondowForwardInputs.of_external_lcm_bound
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound := external_lcmUpto_le_three_pow_nat_statement
  product_log := hproduct_log
  decomposition := hdecomposition

/-- Historical entry point for the fully reproved forward-input package. -/
def SondowForwardInputs.of_external_reproof : SondowForwardInputs :=
  SondowForwardInputs.of_reproof
