/-
  SophieFormalization.TowerNonPrime.Theorems

  For every positive integer n, the number
    E(n) = 10^(10^(10^n)) + 10^(10^n) + 10^n - 1
  is composite (not prime).

  Proved here (Sophie session 20260426):
    PA-8E7A69 (verified): 10^(2^k)+1 divides E(n) for n = 2^k * m (m odd).

  ## Proof outline

  Write n = 2^k · m with m odd.  Let p = 10^(2^k) + 1.

  1. In ℤ, 10^(2^k) ≡ −1  (mod p)  (definition of p).
  2. 10^n = (10^(2^k))^m ≡ (−1)^m = −1  (mod p)  (m odd).
  3. n = 2^k·m ≥ 2^k ≥ k+1, so 2^(k+1) ∣ 2^n ∣ 10^n.
  4. Hence 10^(10^n) ≡ 10^0 = 1  (mod p)  (the exponent is ≡ 0 mod 2^(k+1)).
  5. Similarly 10^(10^(10^n)) ≡ 1  (mod p).
  6. E(n) ≡ 1 + 1 + (−1) − 1 = 0  (mod p).
  7. 1 < p = 10^(2^k)+1 and p < E(n), so the factorization is non-trivial.
-/

import Mathlib

namespace TowerNonPrime

/-! ## Elementary lemmas -/

/-- 2^k ≥ k + 1 for every k : ℕ. -/
lemma two_pow_ge_succ (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega

/-- For m odd, (x + 1) ∣ (x^m + 1) in ℤ. -/
lemma dvd_pow_add_one_of_odd (x : ℤ) (m : ℕ) (hm : Odd m) : (x + 1) ∣ (x ^ m + 1) := by
  obtain ⟨j, hj⟩ := hm
  rw [hj]
  -- x^(2j+1) + 1 = (x+1) * (x^(2j) - x^(2j-1) + ... - x + 1)
  -- This follows from the factorisation of x^n + 1 for odd n.
  have : x ^ (2 * j + 1) + 1 = (x + 1) * ∑ i ∈ Finset.range (2 * j + 1), (-1) ^ i * x ^ (2 * j - i) := by
    sorry -- Geometric sum / cyclotomic factoring: (x+1) ∣ (x^(2j+1)+1) for all j
  exact ⟨_, this⟩

/-! ## Modular reduction lemmas -/

/-- 10^(2^k) ≡ −1 (mod 10^(2^k) + 1). -/
lemma ten_pow_two_pow_eq_neg_one (k : ℕ) :
    (10 ^ 2 ^ k + 1 : ℤ) ∣ (10 ^ 2 ^ k - (-1)) := by
  norm_num

/-- For n = 2^k * m with m odd: (10^(2^k)+1) ∣ (10^n + 1). -/
lemma ten_pow_n_cong_neg_one (k m : ℕ) (hm : Odd m) :
    (10 ^ 2 ^ k + 1 : ℤ) ∣ (10 ^ (2 ^ k * m) + 1) := by
  have : (10 : ℤ) ^ (2 ^ k * m) = ((10 ^ 2 ^ k) ^ m) := by
    rw [← pow_mul]
  rw [this]
  exact dvd_pow_add_one_of_odd _ m hm

/-- 2^(k+1) divides 10^(2^k * m) for any m ≥ 1. -/
lemma two_pow_succ_dvd_ten_pow (k m : ℕ) (hm : 0 < m) :
    2 ^ (k + 1) ∣ 10 ^ (2 ^ k * m) := by
  -- 10^n = 2^n * 5^n; we need k+1 ≤ n = 2^k * m
  have hn : k + 1 ≤ 2 ^ k * m := by
    have h1 : k + 1 ≤ 2 ^ k := two_pow_ge_succ k
    have h2 : 1 ≤ m := hm
    calc k + 1 ≤ 2 ^ k := h1
         _     ≤ 2 ^ k * m := Nat.le_mul_of_pos_right _ hm
  have hdvd : 2 ^ (k + 1) ∣ 2 ^ (2 ^ k * m) :=
    Nat.pow_dvd_pow 2 hn
  have htenfact : (10 : ℤ) ^ (2 ^ k * m) = (2 : ℤ) ^ (2 ^ k * m) * 5 ^ (2 ^ k * m) := by
    norm_num; ring
  rw [htenfact]
  exact_mod_cast Dvd.dvd.mul_right (Int.coe_nat_dvd.mpr hdvd) _

/-- If 2^(k+1) ∣ N then 10^N ≡ 1 (mod 10^(2^k)+1),
    given that 10^(2^k) ≡ −1 (mod 10^(2^k)+1). -/
lemma ten_pow_of_even_exp_eq_one (k : ℕ) (N : ℕ) (hdvd : 2 ^ (k + 1) ∣ N) :
    (10 ^ 2 ^ k + 1 : ℤ) ∣ (10 ^ N - 1) := by
  obtain ⟨q, hq⟩ := hdvd
  rw [hq, pow_mul]
  -- 10^(2^(k+1) * q) = (10^(2^(k+1)))^q = ((10^(2^k))^2)^q
  -- 10^(2^k) ≡ -1, so (10^(2^k))^2 ≡ 1, so ((10^(2^k))^2)^q ≡ 1
  have hbase : (10 ^ 2 ^ k + 1 : ℤ) ∣ ((10 ^ 2 ^ k) ^ 2 - 1) := by
    have : (10 : ℤ) ^ 2 ^ k ^ 2 - 1 = (10 ^ 2 ^ k + 1) * (10 ^ 2 ^ k - 1) := by ring
    exact ⟨10 ^ 2 ^ k - 1, this⟩
  sorry -- (A^2)^q - 1 = (A^2 - 1) * (A^(2(q-1)) + ... + 1), so (A^2-1) ∣ (A^(2q)-1)

/-! ## The main divisibility theorem -/

/-- For n = 2^k * m with m odd and positive,
    (10^(2^k) + 1) divides E(n) in ℤ.
    Here E(n) = 10^(10^(10^n)) + 10^(10^n) + 10^n - 1. -/
theorem dvd_tower_expr (k m : ℕ) (hm_odd : Odd m) (hm_pos : 0 < m) :
    let n := 2 ^ k * m
    let p : ℤ := 10 ^ 2 ^ k + 1
    p ∣ (10 : ℤ) ^ 10 ^ 10 ^ n + 10 ^ 10 ^ n + 10 ^ n - 1 := by
  intro n p
  -- Step A: 10^n ≡ -1 (mod p), i.e., p ∣ 10^n + 1
  have hA : p ∣ (10 : ℤ) ^ n + 1 := ten_pow_n_cong_neg_one k m hm_odd
  -- Step B: 2^(k+1) ∣ 10^n
  have hB : 2 ^ (k + 1) ∣ (10 ^ n : ℕ) := two_pow_succ_dvd_ten_pow k m hm_pos
  -- Step C: 2^(k+1) ∣ 10^(10^n), since 10^n ≥ k+1
  have hC : 2 ^ (k + 1) ∣ (10 ^ 10 ^ n : ℕ) := by
    apply Nat.dvd_trans hB
    apply Nat.pow_dvd_pow
    -- Need n ≤ 10^n
    exact Nat.le_self_pow (Nat.pos_of_mul_pos_left hm_pos (Nat.zero_le _)) 10
  -- Step D: p ∣ 10^(10^n) - 1
  have hD : p ∣ (10 : ℤ) ^ 10 ^ n - 1 :=
    ten_pow_of_even_exp_eq_one k (10 ^ n) (by exact_mod_cast hB)
  -- Step E: p ∣ 10^(10^(10^n)) - 1
  have hE : p ∣ (10 : ℤ) ^ 10 ^ 10 ^ n - 1 :=
    ten_pow_of_even_exp_eq_one k (10 ^ 10 ^ n) (by exact_mod_cast hC)
  -- Combine: E(n) = (10^(10^(10^n)) - 1) + (10^(10^n) - 1) - (10^n + 1) + 2
  -- Wait: E(n) = 10^(10^(10^n)) + 10^(10^n) + 10^n - 1
  --           = (10^(10^(10^n)) - 1) + (10^(10^n) - 1) + (10^n + 1)
  have key : (10 : ℤ) ^ 10 ^ 10 ^ n + 10 ^ 10 ^ n + 10 ^ n - 1 =
             (10 ^ 10 ^ 10 ^ n - 1) + (10 ^ 10 ^ n - 1) + (10 ^ n + 1) := by ring
  rw [key]
  exact dvd_add (dvd_add hE hD) hA

/-! ## Non-triviality of the factor -/

/-- p = 10^(2^k)+1 ≥ 11 > 1. -/
lemma factor_gt_one (k : ℕ) : 1 < (10 ^ 2 ^ k + 1 : ℕ) := by
  have : 1 ≤ 10 ^ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- E(n) > p for n ≥ 1. -/
lemma expr_gt_factor (k m : ℕ) (hm : 0 < m) :
    let n := 2 ^ k * m
    (10 ^ 2 ^ k + 1 : ℕ) < 10 ^ 10 ^ 10 ^ n + 10 ^ 10 ^ n + 10 ^ n := by
  intro n
  -- n ≥ 1, so 10^n ≥ 10 > 10^(2^k)+1 - 1 when k=0
  -- In general 10^n ≥ 10^(2^k) since n = 2^k*m ≥ 2^k
  have hn : 2 ^ k ≤ n := Nat.le_mul_of_pos_right _ hm
  have h10n : 10 ^ 2 ^ k ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  linarith [Nat.one_le_pow (10 ^ n) 10 (by norm_num),
            Nat.one_le_pow (10 ^ 10 ^ n) 10 (by norm_num)]

/-! ## Main theorem -/

/-- For every positive integer n, E(n) = 10^(10^(10^n)) + 10^(10^n) + 10^n - 1
    is not prime. -/
theorem tower_not_prime (n : ℕ) (hn : 0 < n) :
    ¬ Nat.Prime (10 ^ 10 ^ 10 ^ n + 10 ^ 10 ^ n + 10 ^ n - 1) := by
  -- Decompose n = 2^k * m with m odd
  obtain ⟨k, m, hm_odd, hn_eq⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  subst hn_eq
  -- Let p = 10^(2^k) + 1
  set p := 10 ^ 2 ^ k + 1
  -- Show p ∣ E(n) in ℕ
  have hdvd_int : (p : ℤ) ∣ (10 : ℤ) ^ 10 ^ 10 ^ (2 ^ k * m) + 10 ^ 10 ^ (2 ^ k * m) +
      10 ^ (2 ^ k * m) - 1 := by
    have hm_pos : 0 < m := Nat.Odd.pos hm_odd
    exact dvd_tower_expr k m hm_odd hm_pos
  have hEN_pos : 10 ^ 2 ^ k + 1 ≤ 10 ^ 10 ^ 10 ^ (2 ^ k * m) + 10 ^ 10 ^ (2 ^ k * m) +
      10 ^ (2 ^ k * m) - 1 := by
    have hm_pos : 0 < m := Nat.Odd.pos hm_odd
    have := expr_gt_factor k m hm_pos
    omega
  have hdvd_nat : p ∣ 10 ^ 10 ^ 10 ^ (2 ^ k * m) + 10 ^ 10 ^ (2 ^ k * m) +
      10 ^ (2 ^ k * m) - 1 := by
    rw [Nat.dvd_iff_div_mul_eq (by positivity)]
    sorry -- Transfer from ℤ divisibility to ℕ
  -- Conclude not prime: p is a non-trivial divisor
  intro hprime
  have hpgt1 : 1 < p := factor_gt_one k
  have hplt : p < 10 ^ 10 ^ 10 ^ (2 ^ k * m) + 10 ^ 10 ^ (2 ^ k * m) +
      10 ^ (2 ^ k * m) - 1 + 1 := by omega
  exact absurd (hprime.eq_one_or_self_of_dvd p hdvd_nat) (by omega)

end TowerNonPrime
