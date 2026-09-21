import FormalConjectures.GreensOpenProblems.«47»
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Rat.Lemmas
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Green 47 counterexample: definitions

This module defines the witness and the three properties used to negate the
exact-containment formulation.
-/

namespace Green47Proof

open Filter Asymptotics

def witness : Set ℕ :=
  {n | n = 2 ∨ (∃ k : ℕ, n = 4 ^ k) ∨
    ∃ p : ℕ, p.Prime ∧ p % 8 = 1 ∧ n = p ^ 2}

def localCondition (A : Set ℕ) : Prop :=
  ∀ᶠ p in atTop, Nat.Prime p →
    (Set.image (fun a : ℕ => (a : ZMod p)) A).ncard ≤ (p + 1) / 2

def sparse (A : Set ℕ) : Prop :=
  (fun X : ℕ => ((A ∩ Set.Iic X).ncard : ℝ)) =O[atTop]
    (fun X : ℕ => Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 100)

def quadraticContained (A : Set ℕ) : Prop :=
  ∃ P : Polynomial ℚ, P.degree = 2 ∧
    ∀ a ∈ A, ∃ z : ℤ, (a : ℚ) = P.eval (z : ℚ)

def fcStatement : Prop :=
  ∀ A : Set ℕ, localCondition A → sparse A ∨ quadraticContained A

theorem one_mem : 1 ∈ witness := Or.inr (Or.inl ⟨0, by norm_num⟩)
theorem two_mem : 2 ∈ witness := Or.inl rfl
theorem pow_four_mem (k : ℕ) : 4 ^ k ∈ witness := Or.inr (Or.inl ⟨k, rfl⟩)
theorem prime_square_mem (p : ℕ) (hp : p.Prime) (hmod : p % 8 = 1) :
    p ^ 2 ∈ witness := Or.inr (Or.inr ⟨p, hp, hmod, rfl⟩)

theorem prime_log_weight_not_summable :
    ¬ Summable (fun n : ℕ =>
      if n.Prime ∧ (n : ZMod 8) = 1 then Real.log (n : ℝ) / n else 0) := by
  have h := ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div
    (q := 8) (a := (1 : ZMod 8)) isUnit_one
  have heq (n : ℕ) :
      (if n.Prime then ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 8) n
       else 0) / (n : ℝ) =
      if n.Prime ∧ (n : ZMod 8) = 1 then Real.log (n : ℝ) / n else 0 := by
    by_cases hp : n.Prime
    · by_cases hn : (n : ZMod 8) = 1
      · simp [hp, hn, ArithmeticFunction.vonMangoldt.residueClass,
          ArithmeticFunction.vonMangoldt_apply_prime hp]
      · simp [hp, hn, ArithmeticFunction.vonMangoldt.residueClass]
    · simp [hp]
  simpa only [heq] using h

theorem two_not_square_rat : ¬ IsSquare (2 : ℚ) := by
  rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from rfl, Rat.isSquare_natCast_iff]
  exact Nat.prime_two.not_isSquare

end Green47Proof
