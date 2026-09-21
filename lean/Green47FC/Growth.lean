import Green47FC.Basic

/-!
# Green 47 counterexample: counting-function growth

This module proves that the witness is not bounded by
`sqrt X / (log X)^100`.
-/

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
