import Green47FC.Local
import Green47FC.Quadratic
import Green47FC.Growth

/-!
# A counterexample to the exact-containment formulation of Green 47

This file proves the negation of the right-hand side of the Formal Conjectures
statement `Green47.green_47`, preserving its quantifiers and exponent 100.
It does not refute the finite-exception conjecture of Green and Harper.
-/

namespace Green47Proof

open Filter Asymptotics

theorem witness_counterexample :
    localCondition witness ∧ ¬ sparse witness ∧ ¬ quadraticContained witness :=
  ⟨witness_localCondition, witness_not_sparse, witness_not_quadraticContained⟩

theorem not_fcStatement : ¬ fcStatement := by
  intro h
  rcases h witness witness_localCondition with hs | hq
  · exact witness_not_sparse hs
  · exact witness_not_quadraticContained hq

/-- The original FC right-hand side, written without the `answer` annotation. -/
theorem green_47_rhs_false :
    False ↔ ∀ A : Set ℕ,
      (∀ᶠ p in atTop, Nat.Prime p →
        Set.ncard (Set.image (fun a : ℕ => (a : ZMod p)) A) ≤ (p + 1) / 2) →
      ((fun X : ℕ => ((A ∩ Set.Iic X).ncard : ℝ)) =O[atTop]
        (fun X : ℕ => Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 100))
      ∨ (∃ P : Polynomial ℚ, P.degree = 2 ∧
        ∀ a ∈ A, ∃ z : ℤ, (a : ℚ) = P.eval (z : ℚ)) := by
  change False ↔ fcStatement
  exact ⟨False.elim, not_fcStatement⟩

end Green47Proof
