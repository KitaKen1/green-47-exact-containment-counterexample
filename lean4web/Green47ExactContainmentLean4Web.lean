import Mathlib

/-!
# Green 47: standalone exact-containment counterexample

This mathlib-only file reproduces the right-hand side of the current Formal
Conjectures target and proves that it is false.  It is arranged as a single file
for Lean4Web and is tested with Lean 4.35.0-rc2.
-/

#eval Lean.versionString

notation g " ≪ " f =>
  Asymptotics.IsBigO Filter.atTop (g : ℕ → ℝ) (f : ℕ → ℝ)

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

namespace Green47Proof

/-- A fixed affine function of all powers of four can be an integer square only
when its constant term vanishes (unless its leading coefficient is zero). -/
theorem constant_zero_of_four_pow_squares (C D : ℤ) (hC : C ≠ 0)
    (hs : ∀ k : ℕ, ∃ w : ℤ, w ^ 2 = C * 4 ^ k + D) : D = 0 := by
  have hCpos : 0 < C := by
    by_contra hn
    have hCneg : C ≤ -1 := by omega
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt D (show (1 : ℤ) < 4 by norm_num)
    obtain ⟨w, hw⟩ := hs k
    have hp : 0 ≤ (4 : ℤ) ^ k := by positivity
    nlinarith [sq_nonneg w, mul_le_mul_of_nonneg_right hCneg hp]
  have hC1 : 1 ≤ C := hCpos
  by_contra hD
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((3 * |D| + 1) ^ 2 + |D|)
    (show (1 : ℤ) < 4 by norm_num)
  obtain ⟨u, hu⟩ := hs k
  obtain ⟨v, hv⟩ := hs (k + 1)
  let w : ℤ := |u|
  let t : ℤ := |v|
  have hw : w ^ 2 = C * 4 ^ k + D := by simpa [w, sq_abs] using hu
  have ht : t ^ 2 = C * 4 ^ (k + 1) + D := by simpa [t, sq_abs] using hv
  have hw0 : 0 ≤ w := abs_nonneg _
  have ht0 : 0 ≤ t := abs_nonneg _
  have hwbig : 3 * |D| < w := by
    have hp : 0 ≤ (4 : ℤ) ^ k := by positivity
    have hCp := mul_le_mul_of_nonneg_right hC1 hp
    have habs := neg_abs_le D
    by_contra hn
    have hn' : w ≤ 3 * |D| := by omega
    nlinarith [abs_nonneg D]
  have hmul : (t - 2 * w) * (t + 2 * w) = -3 * D := by
    rw [pow_succ (4 : ℤ) k] at ht
    nlinarith
  have hne : t - 2 * w ≠ 0 := by
    intro he
    rw [he, zero_mul] at hmul
    omega
  have hlarge : 3 * |D| < t + 2 * w := by omega
  have hone : 1 ≤ |t - 2 * w| := Int.one_le_abs hne
  have habsmul : |t - 2 * w| * (t + 2 * w) = 3 * |D| := by
    have h := congrArg abs hmul
    simpa [abs_mul, abs_of_nonneg (by omega : 0 ≤ t + 2 * w)] using h
  nlinarith


theorem quadratic_eval (P : Polynomial ℚ) (hP : P.degree = 2) (z : ℚ) :
    P.eval z = P.coeff 2 * z ^ 2 + P.coeff 1 * z + P.coeff 0 := by
  have hd : P.natDegree = 2 := Polynomial.natDegree_eq_of_degree_eq_some hP
  rw [Polynomial.eval_eq_sum_range, hd]
  simp [Finset.sum_range_succ]
  ring

/-- Clear the three rational coefficients using their positive denominators. -/
theorem clear_quadratic_denominators (P : Polynomial ℚ) (hP : P.degree = 2) :
    ∃ a b c d : ℤ, a ≠ 0 ∧ 0 < d ∧
      ∀ z : ℤ, (d : ℚ) * P.eval (z : ℚ) = a * (z : ℚ) ^ 2 + b * z + c := by
  let A := P.coeff 2
  let B := P.coeff 1
  let C := P.coeff 0
  let a : ℤ := A.num * B.den * C.den
  let b : ℤ := B.num * A.den * C.den
  let c : ℤ := C.num * A.den * B.den
  let d : ℤ := A.den * B.den * C.den
  have hA : A ≠ 0 := by
    have hd : P.natDegree = 2 := Polynomial.natDegree_eq_of_degree_eq_some hP
    have hp0 : P ≠ 0 := by
      intro hz
      simp [hz] at hP
    simpa [A, ← hd] using Polynomial.leadingCoeff_ne_zero.mpr hp0
  have ha : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero (mul_ne_zero (by simpa using hA) (by exact_mod_cast B.den_ne_zero))
      (by exact_mod_cast C.den_ne_zero)
  have hd : 0 < d := by
    dsimp [d]
    exact mul_pos (mul_pos (by exact_mod_cast A.den_pos) (by exact_mod_cast B.den_pos))
      (by exact_mod_cast C.den_pos)
  refine ⟨a, b, c, d, ha, hd, ?_⟩
  intro z
  rw [quadratic_eval P hP]
  change (d : ℚ) * (A * (z : ℚ) ^ 2 + B * z + C) = _
  have hAn : (A.num : ℚ) = A * A.den := (div_eq_iff (by exact_mod_cast A.den_ne_zero)).mp A.num_div_den
  have hBn : (B.num : ℚ) = B * B.den := (div_eq_iff (by exact_mod_cast B.den_ne_zero)).mp B.num_div_den
  have hCn : (C.num : ℚ) = C * C.den := (div_eq_iff (by exact_mod_cast C.den_ne_zero)).mp C.num_div_den
  dsimp [a, b, c, d]
  push_cast
  rw [hAn, hBn, hCn]
  ring


theorem witness_not_quadraticContained : ¬ quadraticContained witness := by
  rintro ⟨P, hP, hcontains⟩
  obtain ⟨a, b, c, d, ha, hd, heval⟩ := clear_quadratic_denominators P hP
  have hvalues (n : ℕ) (hn : n ∈ witness) :
      ∃ z : ℤ, d * (n : ℤ) = a * z ^ 2 + b * z + c := by
    obtain ⟨z, hz⟩ := hcontains n hn
    refine ⟨z, ?_⟩
    have h := heval z
    rw [← hz] at h
    exact_mod_cast h
  let D : ℤ := b ^ 2 - 4 * a * c
  have hD : D = 0 := by
    apply constant_zero_of_four_pow_squares (4 * a * d) D
      (mul_ne_zero (mul_ne_zero (by norm_num) ha) hd.ne')
    intro k
    obtain ⟨z, hz⟩ := hvalues (4 ^ k) (pow_four_mem k)
    have hz' : d * (4 : ℤ) ^ k = a * z ^ 2 + b * z + c := by exact_mod_cast hz
    refine ⟨2 * a * z + b, ?_⟩
    dsimp [D]
    linear_combination -4 * a * hz'
  obtain ⟨z₁, hz₁⟩ := hvalues 1 one_mem
  obtain ⟨z₂, hz₂⟩ := hvalues 2 two_mem
  let u : ℤ := 2 * a * z₁ + b
  let v : ℤ := 2 * a * z₂ + b
  have hu : u ^ 2 = 4 * a * d := by
    dsimp [u, D] at *
    norm_num at hz₁
    linear_combination -4 * a * hz₁ + hD
  have hv : v ^ 2 = 8 * a * d := by
    dsimp [v, D] at *
    linear_combination -4 * a * hz₂ + hD
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hu
    have hne := mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℤ) ≠ 0) ha) hd.ne'
    exact hne hu.symm
  apply two_not_square_rat
  refine ⟨(v : ℚ) / u, ?_⟩
  have huQ : (u : ℚ) ^ 2 = 4 * a * d := by exact_mod_cast hu
  have hvQ : (v : ℚ) ^ 2 = 8 * a * d := by exact_mod_cast hv
  have huQ0 : (u : ℚ) ≠ 0 := by exact_mod_cast hu0
  field_simp
  nlinarith [huQ, hvQ]

end Green47Proof

namespace Green47Proof

open Filter Finset Asymptotics
open scoped BigOperators Topology

/-- A nonnegative series converges if its dyadic block sums converge. -/
theorem summable_of_dyadic_blocks {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hblocks : Summable (fun j : ℕ => ∑ n ∈ Ico (2 ^ j) (2 ^ (j + 1)), f n)) :
    Summable f := by
  let b : ℕ → ℝ := fun j => ∑ n ∈ Ico (2 ^ j) (2 ^ (j + 1)), f n
  have hb : ∀ j, 0 ≤ b j := fun j => sum_nonneg (fun n _ => hf n)
  have hdecomp (K : ℕ) : ∑ n ∈ range (2 ^ K), f n =
      f 0 + ∑ j ∈ range K, b j := by
    induction K with
    | zero => simp
    | succ K ih =>
      have hpow : 2 ^ K ≤ 2 ^ (K + 1) := by
        rw [pow_succ]
        omega
      rw [← sum_range_add_sum_Ico _ hpow, ih, sum_range_succ]
      dsimp [b]
      ring
  apply summable_of_sum_range_le hf (c := f 0 + ∑' j, b j)
  intro N
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt N (show (1 : ℕ) < 2 by norm_num)
  calc
    ∑ n ∈ range N, f n ≤ ∑ n ∈ range (2 ^ K), f n :=
      sum_le_sum_of_subset_of_nonneg (range_mono hK.le) (fun n _ _ => hf n)
    _ = f 0 + ∑ j ∈ range K, b j := hdecomp K
    _ ≤ f 0 + ∑' j, b j := by
      gcongr
      exact hblocks.sum_le_tsum _ (fun j _ => hb j)

def primeSet : Set ℕ := {p | p.Prime ∧ p % 8 = 1}

instance primeSetDecidable : DecidablePred (· ∈ primeSet) :=
  fun n => inferInstanceAs (Decidable (n.Prime ∧ n % 8 = 1))

noncomputable def primeCount (T : ℕ) : ℕ := (primeSet ∩ Set.Iic T).ncard

theorem mod_eight_iff (n : ℕ) : (n : ZMod 8) = 1 ↔ n % 8 = 1 := by
  constructor
  · intro h
    have h' := congrArg ZMod.val h
    simpa only [ZMod.val_natCast, show ZMod.val (1 : ZMod 8) = 1 by decide] using h'
  · intro h
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast, show ZMod.val (1 : ZMod 8) = 1 by decide] using h

theorem primeCount_le_witnessCount (T : ℕ) :
    primeCount T ≤ (witness ∩ Set.Iic (T ^ 2)).ncard := by
  have hsub : (fun p : ℕ => p ^ 2) '' (primeSet ∩ Set.Iic T) ⊆
      witness ∩ Set.Iic (T ^ 2) := by
    rintro _ ⟨p, ⟨⟨hp, hm⟩, hle⟩, rfl⟩
    exact ⟨prime_square_mem p hp hm, by exact Nat.pow_le_pow_left hle 2⟩
  have hinj : Function.Injective (fun p : ℕ => p ^ 2) := by
    intro p q h
    nlinarith
  calc
    primeCount T = ((fun p : ℕ => p ^ 2) '' (primeSet ∩ Set.Iic T)).ncard :=
      (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ (witness ∩ Set.Iic (T ^ 2)).ncard :=
      Set.ncard_le_ncard hsub ((Set.finite_Iic _).subset Set.inter_subset_right)


noncomputable def primeWeight (n : ℕ) : ℝ :=
  if n ∈ primeSet then Real.log (n : ℝ) / n else 0

theorem primeWeight_nonneg (n : ℕ) : 0 ≤ primeWeight n := by
  unfold primeWeight
  split_ifs with hn
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn.1.one_lt.le)) (Nat.cast_nonneg n)
  · rfl

theorem not_summable_primeWeight : ¬ Summable primeWeight := by
  have heq : primeWeight = (fun n : ℕ =>
      if n.Prime ∧ (n : ZMod 8) = 1 then Real.log (n : ℝ) / n else 0) := by
    funext n
    unfold primeWeight
    exact if_congr (and_congr_right (fun _ => (mod_eight_iff n).symm)) rfl rfl
  rw [heq]
  exact prime_log_weight_not_summable

theorem primeCount_eq_card (T : ℕ) :
    primeCount T = ((Iic T).filter (fun p => p ∈ primeSet)).card := by
  classical
  have heq : (((Iic T).filter (fun p => p ∈ primeSet) : Finset ℕ) : Set ℕ) =
      primeSet ∩ Set.Iic T := by ext p; simp [and_comm]
  rw [primeCount, ← heq, Set.ncard_coe_finset]

theorem block_bound (L U : ℕ) (hL : 0 < L) (hLU : L ≤ U) :
    ∑ n ∈ Ico L U, primeWeight n ≤ (primeCount U : ℝ) * (Real.log U / L) := by
  classical
  let S := (Ico L U).filter (fun p => p ∈ primeSet)
  have hcard : (S.card : ℝ) ≤ (primeCount U : ℝ) := by
    rw [primeCount_eq_card]
    exact_mod_cast card_le_card (show S ⊆ (Iic U).filter (fun p => p ∈ primeSet) from by
      intro n hn
      simp only [S, mem_filter, mem_Ico, mem_Iic] at hn ⊢
      exact ⟨hn.1.2.le, hn.2⟩)
  have hU : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast (hL.trans_le hLU)
  have hw : 0 ≤ Real.log (U : ℝ) / L := div_nonneg (Real.log_nonneg hU) (Nat.cast_nonneg L)
  calc
    ∑ n ∈ Ico L U, primeWeight n = ∑ n ∈ S, Real.log (n : ℝ) / n := by
      simp [S, sum_filter, primeWeight]
    _ ≤ ∑ _ ∈ S, Real.log (U : ℝ) / L := by
      apply sum_le_sum
      intro n hn
      have hn' := (mem_filter.mp hn).1
      have hnL : (L : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn').1
      have hnU : (n : ℝ) ≤ U := by exact_mod_cast (mem_Ico.mp hn').2.le
      have hL' : (0 : ℝ) < L := by exact_mod_cast hL
      have hnpos : (0 : ℝ) < n := hL'.trans_le hnL
      calc
        Real.log (n : ℝ) / n ≤ Real.log (U : ℝ) / n := by
          gcongr
        _ ≤ Real.log (U : ℝ) / L := by
          gcongr
    _ = S.card * (Real.log (U : ℝ) / L) := by simp
    _ ≤ (primeCount U : ℝ) * (Real.log (U : ℝ) / L) := mul_le_mul_of_nonneg_right hcard hw


/-- The proposed sparse bound would force an excessively small prime-counting function. -/
theorem count_bound_of_sparse (hs : sparse witness) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℕ in atTop,
      (primeCount T : ℝ) ≤ C * T / (Real.log T) ^ 3 := by
  obtain ⟨C, hC, hb⟩ := hs.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb.bound
  refine ⟨C, hC, ?_⟩
  have hlogevent : ∀ᶠ T : ℕ in atTop, (1 : ℝ) ≤ Real.log T :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1, hlogevent] with T hTN hT hlog
  have hlogpos : 0 < Real.log (T : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hbT := hN (T ^ 2) (by nlinarith)
  have hsqrt : Real.sqrt ((T ^ 2 : ℕ) : ℝ) = T := by
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg T)]
  have hlogsq : Real.log ((T ^ 2 : ℕ) : ℝ) = 2 * Real.log T := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hbound : ((witness ∩ Set.Iic (T ^ 2)).ncard : ℝ) ≤
      C * ((T : ℝ) / (2 * Real.log T) ^ 100) := by
    simpa only [hsqrt, hlogsq, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ ((witness ∩ Set.Iic (T ^ 2)).ncard : ℝ) from Nat.cast_nonneg _),
      abs_of_nonneg (show 0 ≤ (T : ℝ) / (2 * Real.log T) ^ 100 by positivity)] using hbT
  have hden : (Real.log (T : ℝ)) ^ 3 ≤ (2 * Real.log T) ^ 100 := by
    calc
      (Real.log (T : ℝ)) ^ 3 ≤ (Real.log (T : ℝ)) ^ 100 :=
        pow_le_pow_right₀ hlog (by norm_num)
      _ ≤ (2 * Real.log T) ^ 100 := by gcongr; linarith
  calc
    (primeCount T : ℝ) ≤ ((witness ∩ Set.Iic (T ^ 2)).ncard : ℝ) := by
      exact_mod_cast primeCount_le_witnessCount T
    _ ≤ C * ((T : ℝ) / (2 * Real.log T) ^ 100) := hbound
    _ ≤ C * ((T : ℝ) / (Real.log T) ^ 3) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (Nat.cast_nonneg T) (by positivity) hden) hC.le
    _ = C * T / (Real.log T) ^ 3 := by ring


theorem summable_primeWeight_of_count_bound (C : ℝ) (hC : 0 < C)
    (hb : ∀ᶠ T : ℕ in atTop, (primeCount T : ℝ) ≤ C * T / (Real.log T) ^ 3) :
    Summable primeWeight := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hseries : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow.mpr (show 1 < 2 by norm_num))
    have h' := (summable_nat_add_iff 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  have hmajor := hseries.mul_left (2 * C / (Real.log 2) ^ 2)
  apply summable_of_dyadic_blocks primeWeight_nonneg
  apply hmajor.of_norm_bounded_eventually_nat
  have ht : Tendsto (fun j : ℕ => 2 ^ (j + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℕ) < 2 by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually hb] with j hj
  have hjpos : 0 < (j : ℝ) + 1 := by positivity
  have hpowpos : 0 < (2 : ℝ) ^ j := by positivity
  have hL : 0 < (2 : ℕ) ^ j := by positivity
  have hLU : (2 : ℕ) ^ j ≤ 2 ^ (j + 1) := by rw [pow_succ]; omega
  have hlogU : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) = ((j : ℝ) + 1) * Real.log 2 := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_add, Nat.cast_one]
  have hw : 0 ≤ Real.log ((2 ^ (j + 1) : ℕ) : ℝ) / (2 ^ j : ℕ) := by
    rw [hlogU]
    positivity
  rw [Real.norm_of_nonneg (sum_nonneg (fun n _ => primeWeight_nonneg n))]
  calc
    ∑ n ∈ Ico (2 ^ j) (2 ^ (j + 1)), primeWeight n
        ≤ (primeCount (2 ^ (j + 1)) : ℝ) *
          (Real.log ((2 ^ (j + 1) : ℕ) : ℝ) / (2 ^ j : ℕ)) := block_bound _ _ hL hLU
    _ ≤ (C * (2 ^ (j + 1) : ℕ) / (Real.log ((2 ^ (j + 1) : ℕ) : ℝ)) ^ 3) *
          (Real.log ((2 ^ (j + 1) : ℕ) : ℝ) / (2 ^ j : ℕ)) :=
      mul_le_mul_of_nonneg_right hj hw
    _ = (2 * C / (Real.log 2) ^ 2) * (1 / ((j : ℝ) + 1) ^ 2) := by
      rw [hlogU]
      push_cast
      rw [pow_succ]
      field_simp

theorem witness_not_sparse : ¬ sparse witness := by
  intro hs
  obtain ⟨C, hC, hbound⟩ := count_bound_of_sparse hs
  exact not_summable_primeWeight (summable_primeWeight_of_count_bound C hC hbound)

end Green47Proof

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

/-- The exact FC right-hand side, with the answer hole replaced by `False`.
The standalone mathlib build omits FC's `answer` elaborator. -/
theorem green_47 :
    False ↔ ∀ A : Set ℕ,
      (∀ᶠ p in atTop, Nat.Prime p → Set.ncard (Set.image (fun a : ℕ => (a : ZMod p)) A) ≤ (p + 1) / 2) →
      ((fun X : ℕ => ((A ∩ Set.Iic X).ncard : ℝ)) ≪ (fun X : ℕ => Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 100))
      ∨ (∃ P : Polynomial ℚ, P.degree = 2 ∧ ∀ a ∈ A, ∃ z : ℤ, (a : ℚ) = P.eval (z : ℚ)) := by
  change False ↔ fcStatement
  exact ⟨False.elim, not_fcStatement⟩

end Green47Proof

#print axioms Green47Proof.green_47
