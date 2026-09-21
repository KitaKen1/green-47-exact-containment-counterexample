import Green47FC.Basic

/-!
# Green 47 counterexample: local residue bound

This module proves that the witness occupies at most half of the residue classes
modulo every sufficiently large prime.
-/

namespace Green47Proof

def unitSquares (p : ℕ) : Set (ZMod p) :=
  Units.val '' (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range

theorem ncard_unitSquares (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (unitSquares p).ncard = (p - 1) / 2 := by
  rw [unitSquares, Set.ncard_image_of_injective _ Units.val_injective]
  change Nat.card (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range = _
  rw [IsCyclic.card_powMonoidHom_range, Nat.card_units, Nat.card_eq_fintype_card,
    ZMod.card]
  have heven : 2 ∣ p - 1 := by
    obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp2
    omega
  rw [Nat.gcd_eq_right heven]

theorem square_mem_insert_unitSquares (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    x ^ 2 ∈ insert 0 (unitSquares p) := by
  by_cases hx : x = 0
  · simp [hx]
  · right
    refine ⟨(Units.mk0 x hx) ^ 2, ?_, ?_⟩
    · exact ⟨Units.mk0 x hx, rfl⟩
    · simp

theorem square_mem_unitSquares (p : ℕ) [Fact p.Prime] (x : ZMod p) (hx : x ≠ 0) :
    x ^ 2 ∈ unitSquares p := by
  refine ⟨(Units.mk0 x hx) ^ 2, ?_, ?_⟩
  · exact ⟨Units.mk0 x hx, rfl⟩
  · simp

theorem witness_square_base {n : ℕ} (hn : n ∈ witness) :
    n = 2 ∨ ∃ m : ℕ, n = m ^ 2 ∧
      ∀ q : ℕ, q.Prime → q ≠ 2 → (q % 8 ≠ 1) →
        (m : ZMod q) ≠ 0 := by
  rcases hn with h | ⟨k, rfl⟩ | ⟨p, hp, hmod, rfl⟩
  · exact Or.inl h
  · right
    refine ⟨2 ^ k, ?_, ?_⟩
    · rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
      norm_num
    · intro q hq hq2 _
      let : Fact q.Prime := ⟨hq⟩
      have h2 : (2 : ZMod q) ≠ 0 := by
        intro hz
        have h := (ZMod.natCast_eq_zero_iff 2 q).mp hz
        have := (Nat.dvd_prime Nat.prime_two).mp h
        rcases this with h | h
        · exact hq.ne_one h
        · exact hq2 h
      simpa using pow_ne_zero k h2
  · right
    refine ⟨p, rfl, ?_⟩
    intro q hq _ hq1 hz
    have hd := (ZMod.natCast_eq_zero_iff p q).mp hz
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · exact hq.ne_one h
    · exact hq1 (h ▸ hmod)

theorem local_bound (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) :
    (Set.image (fun a : ℕ => (a : ZMod q)) witness).ncard ≤ (q + 1) / 2 := by
  have hc := ncard_unitSquares q hq2
  have hqge := hq.out.two_le
  by_cases h2 : IsSquare (2 : ZMod q)
  · have hsub : Set.image (fun a : ℕ => (a : ZMod q)) witness ⊆
        insert 0 (unitSquares q) := by
      rintro _ ⟨n, hn, rfl⟩
      rcases witness_square_base hn with rfl | ⟨m, rfl, _⟩
      · obtain ⟨x, hx⟩ := h2
        change (2 : ZMod q) ∈ insert 0 (unitSquares q)
        rw [hx, ← pow_two]
        exact square_mem_insert_unitSquares q x
      · push_cast
        exact square_mem_insert_unitSquares q _
    have h := (Set.ncard_le_ncard hsub).trans (Set.ncard_insert_le 0 (unitSquares q))
    omega
  · have hq1 : q % 8 ≠ 1 := by
      intro h
      exact h2 ((ZMod.exists_sq_eq_two_iff hq2).mpr (Or.inl h))
    have hsub : Set.image (fun a : ℕ => (a : ZMod q)) witness ⊆
        insert 2 (unitSquares q) := by
      rintro _ ⟨n, hn, rfl⟩
      rcases witness_square_base hn with rfl | ⟨m, rfl, hm⟩
      · simp
      · right
        push_cast
        exact square_mem_unitSquares q _ (hm q hq.out hq2 hq1)
    have h := (Set.ncard_le_ncard hsub).trans (Set.ncard_insert_le 2 (unitSquares q))
    omega

theorem witness_localCondition : localCondition witness := by
  filter_upwards [Filter.eventually_ge_atTop 3] with q hq hp
  let : Fact q.Prime := ⟨hp⟩
  exact local_bound q (by omega)

end Green47Proof
