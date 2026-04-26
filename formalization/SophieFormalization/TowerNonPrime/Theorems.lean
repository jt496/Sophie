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
  have : x ^ m + 1 = x ^ m - (-1) ^ m := by
    rw [hm.neg_one_pow, sub_neg_eq_add]
  rw [this]
  exact sub_dvd_pow_sub_pow x (-1) m

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
    have h10 : (10 :ℤ) = 2 * 5 := by norm_num
    rw [h10, mul_pow]
  rw_mod_cast [htenfact]
  grind

/-- If 2^(k+1) ∣ N then 10^N ≡ 1 (mod 10^(2^k)+1),
    given that 10^(2^k) ≡ −1 (mod 10^(2^k)+1). -/
lemma ten_pow_of_even_exp_eq_one (k : ℕ) (N : ℕ) (hdvd : 2 ^ (k + 1) ∣ N) :
    (10 ^ 2 ^ k + 1 : ℤ) ∣ (10 ^ N - 1) := by
  obtain ⟨q, hq⟩ := hdvd
  have hbase : (10 ^ 2 ^ k + 1 : ℤ) ∣ (10 ^ 2 ^ (k + 1) - 1) := by
    rw [pow_succ, pow_mul, pow_two]
    exact ⟨10 ^ 2 ^ k - 1, by ring⟩
  rw [hq, pow_mul]
  have hsub : (10 ^ 2 ^ (k + 1) - 1 : ℤ) ∣ ((10 ^ 2 ^ (k + 1)) ^ q - 1) := by
    have h := sub_dvd_pow_sub_pow ((10 : ℤ) ^ 2 ^ (k + 1)) 1 q
    rw [one_pow] at h
    exact h
  exact dvd_trans hbase hsub

/-! ## The main divisibility theorem -/

-- /-- For n = 2^k * m with m odd and positive,
--     (10^(2^k) + 1) divides E(n) in ℤ.
--     Here E(n) = 10^(10^(10^n)) + 10^(10^n) + 10^n - 1. -/
-- theorem dvd_tower_expr (k m : ℕ) (hm_odd : Odd m) (hm_pos : 0 < m) :
--     let n := 2 ^ k * m
--     let p : ℤ := 10 ^ 2 ^ k + 1
--     p ∣ (10 : ℤ) ^ 10 ^ 10 ^ n + 10 ^ 10 ^ n + 10 ^ n - 1 := by
--   intro n p
--   -- Step A: 10^n ≡ -1 (mod p), i.e., p ∣ 10^n + 1
--   have hA : p ∣ (10 : ℤ) ^ n + 1 := ten_pow_n_cong_neg_one k m hm_odd
--   -- Step B: 2^(k+1) ∣ 10^n
--   have hB : 2 ^ (k + 1) ∣ (10 ^ n : ℕ) := two_pow_succ_dvd_ten_pow k m hm_pos
--   -- Step C: 2^(k+1) ∣ 10^(10^n), since 10^

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
    induction n with
    | zero => norm_num
    | succ n ih =>
    simp only [Order.add_one_le_iff]
    rw [pow_succ]
    grind
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
  have hm_pos : 0 < m := by exact Nat.pos_of_mul_pos_left hn--Nat.Odd.pos hm_odd
  have hdvd_int : (p : ℤ) ∣ (10 : ℤ) ^ 10 ^ 10 ^ (2 ^ k * m) + 10 ^ 10 ^ (2 ^ k * m) +
      10 ^ (2 ^ k * m) - 1 := by
    exact dvd_tower_expr k m hm_odd hm_pos
  have hEN_pos : 10 ^ 2 ^ k + 1 ≤ 10 ^ 10 ^ 10 ^ (2 ^ k * m) + 10 ^ 10 ^ (2 ^ k * m) +
      10 ^ (2 ^ k * m) - 1 := by
    have := expr_gt_factor k m hm_pos
    omega
  have hdvd_nat : p ∣ 10 ^ 10 ^ 10 ^ (2 ^ k * m) + 10 ^ 10 ^ (2 ^ k * m) +
      10 ^ (2 ^ k * m) - 1 := by
    rw [← Int.natCast_dvd_natCast]
    have hpos : 1 ≤ 10 ^ 10 ^ 10 ^ (2 ^ k * m) + 10 ^ 10 ^ (2 ^ k * m) + 10 ^ (2 ^ k * m) := by
      have := expr_gt_factor k m hm_pos
      have := factor_gt_one k
      omega
    rw [Int.natCast_sub hpos]
    exact hdvd_int
  -- Conclude not prime: p is a non-trivial divisor
  intro hprime
  have hpgt1 : 1 < p := factor_gt_one k
  have hplt : p < 10 ^ 10 ^ 10 ^ (2 ^ k * m) + 10 ^ 10 ^ (2 ^ k * m) +
      10 ^ (2 ^ k * m) - 1 + 1 := by omega
  exact absurd (hprime.eq_one_or_self_of_dvd p hdvd_nat) (by grind)

end TowerNonPrime
