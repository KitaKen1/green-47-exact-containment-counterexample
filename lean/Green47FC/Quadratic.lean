import Green47FC.Basic

/-!
# Green 47 counterexample: failure of quadratic containment

This module proves that no degree-two polynomial over the rationals contains the
entire witness in its image on the integers.
-/

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
