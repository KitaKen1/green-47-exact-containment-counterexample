import FormalConjectures.GreensOpenProblems.«47»
import Green47FC.Main

/-!
# Green 47: the exact-containment Formal Conjectures target

This file imports the registered theorem and supplies the answer `False`.
The counterexample preserves the quantifiers, the residue-class bound, and the
exponent `100` in the target.  It does not address the finite-exception variant
of Green and Harper's conjecture.
-/

open Filter

namespace Green47Proof

/-- The exact Formal Conjectures target, with its answer hole filled by
`answer(False)`. -/
theorem green_47 :
    answer(False) ↔ ∀ A : Set ℕ,
      (∀ᶠ p in atTop, Nat.Prime p → Set.ncard (Set.image (fun a : ℕ => (a : ZMod p)) A) ≤ (p + 1) / 2) →
      ((fun X : ℕ => ((A ∩ Set.Iic X).ncard : ℝ)) ≪ (fun X : ℕ => Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 100))
      ∨ (∃ P : Polynomial ℚ, P.degree = 2 ∧ ∀ a ∈ A, ∃ z : ℤ, (a : ℚ) = P.eval (z : ℚ)) := by
  change False ↔ fcStatement
  exact ⟨False.elim, not_fcStatement⟩

#print axioms green_47

end Green47Proof
