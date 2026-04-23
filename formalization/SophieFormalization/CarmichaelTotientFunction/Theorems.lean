/-
  Carmichael's Totient Function Conjecture — Partial Formalization
  Sophie session: 20260423_151851_carmichael-s-totient-function-conjecture
  Source: PA-1865AE (checker-validated Cases 1–3) + PA-6713E5 (Case 4a)

  Conjecture: For every n : ℕ with n > 0, there exists m : ℕ with m ≠ n, m > 0
  and φ(m) = φ(n).  Equivalently, no totient value is achieved exactly once.

  Proved here (sorry-free):
    Case 1 — n odd            : partner m = 2 * n
    Case 2 — n ≡ 2 (mod 4)   : partner m = n / 2
    Case 3 — n = 2^a, a ≥ 2  : partner m = 3 * 2^(a-1)
    Case 4a— n = 2^a * q, a ≥ 2, q odd, 3 ∤ q : partner m = 3 * 2^(a-1) * q
-/

import Mathlib

open Nat

namespace CarmichaelTotient

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

private lemma two_pow_succ_eq (a : ℕ) : 2 ^ (a + 1) = 2 * 2 ^ a := by ring

private lemma totient_two_pow (a : ℕ) (ha : 1 ≤ a) : φ (2 ^ a) = 2 ^ (a - 1) := by
  have h := Nat.totient_prime_pow_succ (p := 2) Nat.prime_two (a - 1)
  rw [Nat.sub_add_cancel ha] at h
  simp [h]

private lemma totient_two_pow_eq_two_mul (a : ℕ) (ha : 2 ≤ a) :
    φ (2 ^ a) = 2 * φ (2 ^ (a - 1)) := by
  rw [totient_two_pow a (by omega), totient_two_pow (a-1) (by omega)]
  cases a with
  | zero => omega
  | succ n =>
    simp only [Nat.succ_sub_one]
    have hn : n = (n - 1) + 1 := by omega
    grind

private lemma totient_three_mul_two_pow (a : ℕ) (ha : 1 ≤ a) : φ (3 * 2 ^ a) = 2 ^ a := by
  have hcop : Nat.Coprime 3 (2 ^ a) := Nat.Coprime.pow_right a (by decide)
  rw [Nat.totient_mul hcop, Nat.totient_prime (by decide : Nat.Prime 3),
      show (3 : ℕ) - 1 = 2 from rfl, totient_two_pow a (by omega)]
  cases a with
  | zero => omega
  | succ n => simp [two_pow_succ_eq]

private lemma not_dvd_two_pow_of_prime_odd {p : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1)
    (a : ℕ) : ¬ p ∣ 2 ^ a := by
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.pow_right a
    (Nat.coprime_comm.mpr (Nat.coprime_two_left.mpr ⟨p / 2, by omega⟩)))

-- ────────────────────────────────────────────────────────────────────────────
-- Case 1: n odd  →  partner 2n
-- ────────────────────────────────────────────────────────────────────────────

/-- For n odd and positive, 2n is a distinct partner with the same totient. -/
theorem totient_partner_odd (n : ℕ) (hn : Odd n) (hn0 : 0 < n) :
    φ (2 * n) = φ n ∧ 2 * n ≠ n :=
  ⟨Nat.totient_two_mul_of_odd hn, by omega⟩

-- ────────────────────────────────────────────────────────────────────────────
-- Case 2: n ≡ 2 (mod 4)  →  partner n/2
-- ────────────────────────────────────────────────────────────────────────────

/-- For n ≡ 2 (mod 4), the integer n/2 is a distinct partner with the same totient. -/
theorem totient_partner_two_mod_four (n : ℕ) (h : n % 4 = 2) :
    ∃ m : ℕ, m ≠ n ∧ φ m = φ n ∧ 0 < m := by
  refine ⟨n / 2, by omega, ?_, by omega⟩
  have hk_odd : Odd (n / 2) := by rw [Nat.odd_iff]; omega
  conv_rhs => rw [show n = 2 * (n / 2) from by omega]
  exact (Nat.totient_two_mul_of_odd hk_odd).symm

-- ────────────────────────────────────────────────────────────────────────────
-- Case 3: n = 2^a, a ≥ 2  →  partner 3 * 2^(a-1)
-- ────────────────────────────────────────────────────────────────────────────

/-- For n = 2^a with a ≥ 2, the number 3·2^(a-1) is a distinct partner. -/
theorem totient_partner_pow_two (a : ℕ) (ha : 2 ≤ a) :
    φ (3 * 2 ^ (a - 1)) = φ (2 ^ a) ∧ 3 * 2 ^ (a - 1) ≠ 2 ^ a := by
  constructor
  · rw [totient_three_mul_two_pow (a - 1) (by omega), totient_two_pow a (by omega)]
  · intro heq
    have h3 : 3 ∣ 3 * 2 ^ (a - 1) := dvd_mul_right 3 _
    rw [heq] at h3
    exact absurd h3 (not_dvd_two_pow_of_prime_odd (by decide) (by decide) a)

-- ────────────────────────────────────────────────────────────────────────────
-- Case 4a: n = 2^a * q, a ≥ 2, q odd, 3 ∤ q  →  partner 3 * 2^(a-1) * q
-- ────────────────────────────────────────────────────────────────────────────

/-- For n = 2^a·q with a ≥ 2, q odd, 3 ∤ q, the number 3·2^(a-1)·q is a distinct partner. -/
theorem totient_partner_pow_two_mul_odd (a q : ℕ) (ha : 2 ≤ a) (hq0 : 0 < q)
    (hq_odd : Odd q) (hq3 : ¬ 3 ∣ q) :
    φ (3 * 2 ^ (a - 1) * q) = φ (2 ^ a * q) ∧ 3 * 2 ^ (a - 1) * q ≠ 2 ^ a * q := by
  have hcop_2_q    : Nat.Coprime 2 q               := Nat.coprime_two_left.mpr hq_odd
  have hcop_2a_q   : Nat.Coprime (2 ^ a) q         := hcop_2_q.pow_left a
  have hcop_2b_q   : Nat.Coprime (2 ^ (a - 1)) q   := hcop_2_q.pow_left (a - 1)
  have hcop_3_2b   : Nat.Coprime 3 (2 ^ (a - 1))   := Nat.Coprime.pow_right _ (by decide)
  have hcop_3_q    : Nat.Coprime 3 q               :=
    (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr hq3
  have hcop_32b_q  : Nat.Coprime (3 * 2 ^ (a - 1)) q := hcop_3_q.mul_left hcop_2b_q
  constructor
  · -- φ(3·2^(a-1)·q) = φ(3·2^(a-1)) · φ(q) = φ(2^a) · φ(q) = φ(2^a·q)
    rw [show 3 * 2 ^ (a - 1) * q = 3 * 2 ^ (a - 1) * q from rfl]
    rw [Nat.totient_mul hcop_32b_q, Nat.totient_mul hcop_2a_q,
        totient_three_mul_two_pow (a - 1) (by omega), totient_two_pow a (by omega)]
  · intro heq
    have h3 : 3 ∣ 3 * 2 ^ (a - 1) * q := ⟨2 ^ (a - 1) * q, by ring⟩
    rw [heq] at h3
    rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 3)).mp h3 with h | h
    · exact absurd h (not_dvd_two_pow_of_prime_odd (by decide) (by decide) a)
    · exact absurd h hq3

end CarmichaelTotient
