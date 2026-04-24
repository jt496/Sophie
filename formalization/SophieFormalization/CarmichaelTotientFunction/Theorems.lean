/-
  Carmichael's Totient Function Conjecture — Partial Formalization
  Sophie session: 20260423_151851_carmichael-s-totient-function-conjecture
  Source: PA-1865AE (checker-validated Cases 1–3) + PA-6713E5 (Case 4a)

  Conjecture: For every n : ℕ with n > 0, there exists m : ℕ with m ≠ n, m > 0
  and φ(m) = φ(n).  Equivalently, no totient value is achieved exactly once.

  Proved here (sorry-free):
    Case 1 — n odd                            : partner m = 2 * n
    Case 2 — n ≡ 2 (mod 4)                   : partner m = n / 2
    Case 3 — n = 2^a, a ≥ 2                  : partner m = 3 * 2^(a-1)
    Case 4a— n = 2^a * q, a ≥ 2, q odd, 3 ∤ q : partner m = 3 * 2^(a-1) * q
    Case 4b— n = 2^a * 3 * r, a ≥ 1, gcd(r,6)=1 : partner m = 2^(a+1) * r
    Case 5 — n = 2^a * 3^b * s, a,b ≥ 2, 7 ∤ s : partner m = 7 * 2^(a-1) * 3^(b-1) * s
    Case 6 — n = 2^a * 3^b * 7 * s            : partner m = 2^(a+1) * 3^(b+1) * s
    Case 7 — n = 2^a * 3^b * 7^2 * s, 43 ∤ s  : partner m = 43 * 2^a * 3^b * s
    Case Gen— n = 2^a * 3^b * 7^c * s, 43 ∤ s : partner m = 43 * 2^(a-1) * 3^(b-1) * 7^(c-1) * s
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
  rw [h, show 2 - 1 = 1 from rfl, mul_one]

private lemma totient_two_pow_eq_two_mul (a : ℕ) (ha : 2 ≤ a) :
    φ (2 ^ a) = 2 * φ (2 ^ (a - 1)) := by
  rw [totient_two_pow a (by omega), totient_two_pow (a-1) (by omega)]
  have ha1 : a - 1 = a - 1 - 1 + 1 := by omega
  conv_lhs => rw [ha1, pow_add, pow_one]
  ring

private lemma totient_three_pow (b : ℕ) (hb : 1 ≤ b) : φ (3 ^ b) = 2 * 3 ^ (b - 1) := by
  have h := Nat.totient_prime_pow_succ (p := 3) (by decide) (b - 1)
  rw [Nat.sub_add_cancel hb] at h
  rw [h]
  omega

private lemma totient_three_pow_eq_three_mul (b : ℕ) (hb : 2 ≤ b) :
    φ (3 ^ b) = 3 * φ (3 ^ (b - 1)) := by
  rw [totient_three_pow b (by omega), totient_three_pow (b-1) (by omega)]
  have hb1 : b - 1 = b - 1 - 1 + 1 := by omega
  conv_lhs => rw [hb1, pow_add, pow_one]
  ring

private lemma totient_seven_pow (c : ℕ) (hc : 1 ≤ c) : φ (7 ^ c) = 6 * 7 ^ (c - 1) := by
  have h := Nat.totient_prime_pow_succ (p := 7) (by decide) (c - 1)
  rw [Nat.sub_add_cancel hc] at h
  rw [h]
  omega

private lemma totient_seven_pow_eq_seven_mul (c : ℕ) (hc : 2 ≤ c) :
    φ (7 ^ c) = 7 * φ (7 ^ (c - 1)) := by
  rw [totient_seven_pow c (by omega), totient_seven_pow (c-1) (by omega)]
  have hc1 : c - 1 = c - 1 - 1 + 1 := by omega
  conv_lhs => rw [hc1, pow_add, pow_one]
  ring

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
theorem totient_partner_pow_two_mul_odd (a q : ℕ) (ha : 2 ≤ a)
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


theorem carmichael_case_4b (a r : ℕ) (ha : 1 ≤ a) (hr_coprime : Nat.gcd r 6 = 1) :
  let n := 2^a * 3 * r
  let m := 2^(a+1) * r
  totient m = totient n ∧ m ≠ n := by
  intro n m
  have hpos : r > 0 := by
    by_contra hc
    have hrc : r = 0 := by omega
    subst hrc
    simp at hr_coprime
  have hcop6 : Nat.Coprime r 6 := hr_coprime
  have hcop2 : Nat.Coprime r 2 := Nat.Coprime.coprime_dvd_right (by decide : 2 ∣ 6) hcop6
  have hcop3 : Nat.Coprime r 3 := Nat.Coprime.coprime_dvd_right (by decide : 3 ∣ 6) hcop6
  have hcop2_symm : Nat.Coprime 2 r := hcop2.symm
  have hcop3_symm : Nat.Coprime 3 r := hcop3.symm
  have hcop_2a1_r : Nat.Coprime (2^(a+1)) r := Nat.Coprime.pow_left (a+1) hcop2_symm
  have hcop_2a3_r : Nat.Coprime (2^a * 3) r := Nat.Coprime.mul_left (Nat.Coprime.pow_left a hcop2_symm) hcop3_symm
  have hcop_2a_3 : Nat.Coprime (2^a) 3 := Nat.Coprime.pow_left a (by decide : Nat.Coprime 2 3)

  constructor
  · have h1 : totient m = 2^a * totient r := by
      dsimp [m]
      rw [Nat.totient_mul hcop_2a1_r, totient_two_pow (a+1) (by omega)]
      congr 1
    have h2 : totient n = 2^a * totient r := by
      dsimp [n]
      rw [Nat.totient_mul hcop_2a3_r, Nat.totient_mul hcop_2a_3]
      rw [totient_two_pow a ha, show totient 3 = 2 by rfl]
      have ha_eq : a = a - 1 + 1 := by omega
      conv_rhs => rw [ha_eq, pow_add, pow_one]
    rw [h1, h2]
  · intro h_eq
    have h_eq2 : 2 * (2^a * r) = 3 * (2^a * r) := by
      calc 2 * (2^a * r) = 2^(a+1) * r := by ring
        _ = 2^a * 3 * r := h_eq
        _ = 3 * (2^a * r) := by ring
    have h_cancel : 2 = 3 := Nat.eq_of_mul_eq_mul_right (by positivity) h_eq2
    contradiction

theorem carmichael_case_5 (a b s : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hs_coprime : Nat.gcd s 42 = 1) :
  let n := 2^a * 3^b * s
  let m := 7 * 2^(a-1) * 3^(b-1) * s
  totient m = totient n ∧ m ≠ n := by
  intro n m
  have h_pos_s : s > 0 := by
    by_contra h; have h0 : s = 0 := by omega;
    subst h0; simp at hs_coprime
  have hcop42 : Nat.Coprime s 42 := hs_coprime
  have hcop2 : Nat.Coprime s 2 := hcop42.coprime_dvd_right (by decide)
  have hcop3 : Nat.Coprime s 3 := hcop42.coprime_dvd_right (by decide)
  have hcop7 : Nat.Coprime s 7 := hcop42.coprime_dvd_right (by decide)

  have h_phi_n : φ n = 2^a * 3^(b-1) * φ s := by
    dsimp [n]
    have h1 : Nat.Coprime (2^a * 3^b) s := by
      apply Nat.Coprime.mul_left
      · exact (hcop2.pow_right a).symm
      · exact (hcop3.pow_right b).symm
    have h2 : Nat.Coprime (2^a) (3^b) := (Nat.Coprime.pow_left a (Nat.Coprime.pow_right b (by decide)))
    simp only [Nat.totient_mul h1, Nat.totient_mul h2, totient_two_pow a (by omega), totient_three_pow b (by omega)]
    simp_rw [← mul_assoc]
    congr
    rw [← pow_succ]; congr; omega

  have h_phi_m : φ m = 2^a * 3^(b-1) * φ s := by
    dsimp [m]
    have h1 : Nat.Coprime (7 * 2^(a-1) * 3^(b-1)) s := by
      apply Nat.Coprime.mul_left
      · apply Nat.Coprime.mul_left
        · exact hcop7.symm
        · exact (hcop2.pow_right _).symm
      · exact (hcop3.pow_right _).symm
    have h2 : Nat.Coprime 7 (2^(a-1) * 3^(b-1)) := by
      apply Nat.Coprime.mul_right
      · apply Nat.Coprime.pow_right; decide
      · apply Nat.Coprime.pow_right; decide
    have h3 : Nat.Coprime (2^(a-1)) (3^(b-1)) := by
      apply Nat.Coprime.pow_left; apply Nat.Coprime.pow_right; decide
    rw [Nat.totient_mul h1]
    rw [show 7 * 2^(a-1) * 3^(b-1) = 7 * (2^(a-1) * 3^(b-1)) by ring]
    rw [Nat.totient_mul h2, Nat.totient_mul h3]
    rw [Nat.totient_prime (by decide : Nat.Prime 7), show (7 - 1) = 6 by rfl]
    rw [totient_two_pow (a-1) (by omega), totient_three_pow (b-1) (by omega)]
    have ha11 : a - 1 - 1 = a - 2 := by omega
    have hb11 : b - 1 - 1 = b - 2 := by omega
    rw [ha11, hb11]
    have ha_val : 2^a = 2^(a-2) * 4 := by
      calc 2^a = 2^((a-2)+2) := by congr; omega
        _ = 2^(a-2) * 2^2 := by rw [pow_add]
        _ = 2^(a-2) * 4 := rfl
    have hb_val : 3^(b-1) = 3^(b-2) * 3 := by
      calc 3^(b-1) = 3^((b-2)+1) := by congr; omega
        _ = 3^(b-2) * 3^1 := by rw [pow_add]
        _ = 3^(b-2) * 3 := rfl
    rw [ha_val, hb_val]
    ring

  constructor
  · rw [h_phi_n, h_phi_m]
  · intro heq
    have h_prod_pos : 2^(a-1) * 3^(b-1) * s > 0 := by positivity
    have h67 : 6 = 7 := Nat.eq_of_mul_eq_mul_right h_prod_pos (by
      calc 6 * (2^(a-1) * 3^(b-1) * s) = 2 * 3 * 2^(a-1) * 3^(b-1) * s := by ring
        _ = (2 * 2^(a-1)) * (3 * 3^(b-1)) * s := by ring
        _ = 2^(a-1+1) * 3^(b-1+1) * s := by ring
        _ = n := by dsimp [n]; congr <;> omega
        _ = m := heq.symm
        _ = 7 * (2^(a-1) * 3^(b-1) * s) := by ring
    )
    contradiction

theorem carmichael_case_6 (a b s : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hs_coprime : Nat.gcd s 42 = 1) :
  let n := 2^a * 3^b * 7 * s
  let m := 2^(a+1) * 3^(b+1) * s
  totient m = totient n ∧ m ≠ n := by
  intro n m
  have hs_pos : s > 0 := by
    by_contra hc
    have hs0 : s = 0 := by omega
    subst hs0
    simp at hs_coprime
  have hcop42 : Nat.Coprime s 42 := hs_coprime
  have hcop2 : Nat.Coprime s 2 := Nat.Coprime.coprime_dvd_right (by decide : 2 ∣ 42) hcop42
  have hcop3 : Nat.Coprime s 3 := Nat.Coprime.coprime_dvd_right (by decide : 3 ∣ 42) hcop42
  have hcop7 : Nat.Coprime s 7 := Nat.Coprime.coprime_dvd_right (by decide : 7 ∣ 42) hcop42
  have hcop2_symm : Nat.Coprime 2 s := hcop2.symm
  have hcop3_symm : Nat.Coprime 3 s := hcop3.symm
  have hcop7_symm : Nat.Coprime 7 s := hcop7.symm

  have hcop2_3 : Nat.Coprime 2 3 := by decide
  have hcop2_7 : Nat.Coprime 2 7 := by decide
  have hcop3_7 : Nat.Coprime 3 7 := by decide
  have hcop2a1_3b1 : Nat.Coprime (2^(a+1)) (3^(b+1)) := Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ hcop2_3)
  have hcop2a_3b : Nat.Coprime (2^a) (3^b) := Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ hcop2_3)
  have hcop2a3b_7 : Nat.Coprime (2^a * 3^b) 7 := Nat.Coprime.mul_left (Nat.Coprime.pow_left a hcop2_7) (Nat.Coprime.pow_left b hcop3_7)
  have hcop2a13b1_s : Nat.Coprime (2^(a+1) * 3^(b+1)) s := Nat.Coprime.mul_left (Nat.Coprime.pow_left _ hcop2_symm) (Nat.Coprime.pow_left _ hcop3_symm)
  have hcop2a3b7_s : Nat.Coprime (2^a * 3^b * 7) s := Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.pow_left _ hcop2_symm) (Nat.Coprime.pow_left _ hcop3_symm)) hcop7_symm

  constructor
  · have h1 : totient m = 2^a * (2 * 3^b) * totient s := by
      dsimp [m]
      rw [Nat.totient_mul hcop2a13b1_s, Nat.totient_mul hcop2a1_3b1]
      rw [totient_two_pow (a+1) (by omega), totient_three_pow (b+1) (by omega)]
      have ha_eq : a + 1 - 1 = a := by omega
      have hb_eq : b + 1 - 1 = b := by omega
      rw [ha_eq, hb_eq]
    have h2 : totient n = 2^(a-1) * (2 * 3^(b-1)) * 6 * totient s := by
      dsimp [n]
      rw [Nat.totient_mul hcop2a3b7_s, Nat.totient_mul hcop2a3b_7, Nat.totient_mul hcop2a_3b]
      rw [totient_two_pow a ha, totient_three_pow b hb, show totient 7 = 6 by rfl]
    rw [h1, h2]
    have ha_eq2 : a = a - 1 + 1 := by omega
    have hb_eq2 : b = b - 1 + 1 := by omega
    conv_lhs => rw [ha_eq2, hb_eq2, pow_add, pow_one, pow_add, pow_one]
    ring
  · intro h_eq
    have h_eq2 : 6 * (2^a * 3^b * s) = 7 * (2^a * 3^b * s) := by
      calc 6 * (2^a * 3^b * s) = 2^(a+1) * 3^(b+1) * s := by ring
        _ = 2^a * 3^b * 7 * s := h_eq
        _ = 7 * (2^a * 3^b * s) := by ring
    have h_cancel : 6 = 7 := Nat.eq_of_mul_eq_mul_right (by positivity) h_eq2
    contradiction

theorem carmichael_case_7 (a b s : ℕ) (hs_coprime : Nat.gcd s 42 = 1) (hs43 : ¬ 43 ∣ s) :
  let n := 2^a * 3^b * 7^2 * s
  let m := 43 * 2^a * 3^b * s
  totient m = totient n ∧ m ≠ n := by
  intro n m
  have hs_pos : s > 0 := by
    by_contra hc
    have hs0 : s = 0 := by omega
    subst hs0
    simp at hs_coprime
  have hcop42 : Nat.Coprime s 42 := hs_coprime
  have hcop2 : Nat.Coprime s 2 := Nat.Coprime.coprime_dvd_right (by decide : 2 ∣ 42) hcop42
  have hcop3 : Nat.Coprime s 3 := Nat.Coprime.coprime_dvd_right (by decide : 3 ∣ 42) hcop42
  have hcop7 : Nat.Coprime s 7 := Nat.Coprime.coprime_dvd_right (by decide : 7 ∣ 42) hcop42
  have hcop2_symm : Nat.Coprime 2 s := hcop2.symm
  have hcop3_symm : Nat.Coprime 3 s := hcop3.symm
  have hcop7_symm : Nat.Coprime 7 s := hcop7.symm

  have hcop2_3 : Nat.Coprime 2 3 := by decide
  have hcop43_2 : Nat.Coprime 43 2 := by decide
  have hcop43_3 : Nat.Coprime 43 3 := by decide
  have hcop43_2a : Nat.Coprime 43 (2^a) := Nat.Coprime.pow_right a hcop43_2
  have hcop43_3b : Nat.Coprime 43 (3^b) := Nat.Coprime.pow_right b hcop43_3
  have hcop43_2a3b : Nat.Coprime 43 (2^a * 3^b) := Nat.Coprime.mul_right hcop43_2a hcop43_3b
  have hcop43_s : Nat.Coprime 43 s := (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr hs43
  have hcops_43 : Nat.Coprime s 43 := hcop43_s.symm
  have hcop2a_3b : Nat.Coprime (2^a) (3^b) := Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ hcop2_3)

  have hcop432a_3b : Nat.Coprime (43 * 2^a) (3^b) := Nat.Coprime.mul_left hcop43_3b hcop2a_3b
  have hcop432a3b_s : Nat.Coprime (43 * 2^a * 3^b) s := Nat.Coprime.mul_left (Nat.Coprime.mul_left hcop43_s (Nat.Coprime.pow_left _ hcop2_symm)) (Nat.Coprime.pow_left _ hcop3_symm)

  have hcop2a3b_72 : Nat.Coprime (2^a * 3^b) (7^2) := by
    have h1 : Nat.Coprime 2 7 := by decide
    have h2 : Nat.Coprime 3 7 := by decide
    exact Nat.Coprime.mul_left (Nat.Coprime.pow_left a (Nat.Coprime.pow_right 2 h1)) (Nat.Coprime.pow_left b (Nat.Coprime.pow_right 2 h2))

  have hcop2a3b72_s : Nat.Coprime (2^a * 3^b * 7^2) s := by
    have h1 : Nat.Coprime (2^a) s := Nat.Coprime.pow_left a hcop2_symm
    have h2 : Nat.Coprime (3^b) s := Nat.Coprime.pow_left b hcop3_symm
    have h3 : Nat.Coprime (7^2) s := Nat.Coprime.pow_left 2 hcop7_symm
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_left h1 h2) h3

  constructor
  · have h1 : totient m = 42 * totient (2^a) * totient (3^b) * totient s := by
      calc totient m = totient (43 * 2^a * 3^b * s) := rfl
        _ = totient (43 * 2^a * 3^b) * totient s := Nat.totient_mul hcop432a3b_s
        _ = totient (43 * 2^a) * totient (3^b) * totient s := by rw [Nat.totient_mul hcop432a_3b]
        _ = totient 43 * totient (2^a) * totient (3^b) * totient s := by rw [Nat.totient_mul hcop43_2a]
        _ = 42 * totient (2^a) * totient (3^b) * totient s := rfl
    have h2 : totient n = 42 * totient (2^a) * totient (3^b) * totient s := by
      calc totient n = totient (2^a * 3^b * 7^2 * s) := rfl
        _ = totient (2^a * 3^b * 7^2) * totient s := Nat.totient_mul hcop2a3b72_s
        _ = totient (2^a * 3^b) * totient (7^2) * totient s := by rw [Nat.totient_mul hcop2a3b_72]
        _ = totient (2^a) * totient (3^b) * totient (7^2) * totient s := by rw [Nat.totient_mul hcop2a_3b]
        _ = totient (2^a) * totient (3^b) * 42 * totient s := by
          have ht7 : totient (7^2) = 42 := by
            have hx := totient_seven_pow 2 (by omega)
            have hexp : 2 - 1 = 1 := rfl
            rw [hexp, pow_one] at hx
            exact hx
          rw [ht7]
        _ = 42 * totient (2^a) * totient (3^b) * totient s := by ring
    rw [h1, h2]
  · intro h_eq
    have h_eq2 : 49 * (2^a * 3^b * s) = 43 * (2^a * 3^b * s) := by
      calc 49 * (2^a * 3^b * s) = 2^a * 3^b * 7^2 * s := by ring
        _ = 2^a * 3^b * (7^2) * s := by ring
        _ = n := rfl
        _ = m  := h_eq.symm
        _ = 43 * 2^a * 3^b * s := rfl
        _ = 43 * (2^a * 3^b * s) := by ring
    have h_cancel : 49 = 43 := Nat.eq_of_mul_eq_mul_right (by positivity) h_eq2
    contradiction

theorem carmichael_case_general (a b c s : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hs_coprime : Nat.gcd s 42 = 1) (hs43 : ¬ 43 ∣ s) :
  let n := 2^a * 3^b * 7^c * s
  let m := 43 * 2^(a-1) * 3^(b-1) * 7^(c-1) * s
  totient m = totient n ∧ m ≠ n := by
  intro n m
  have hs_pos : s > 0 := by
    by_contra hcx
    have hs0 : s = 0 := by omega
    subst hs0
    simp at hs_coprime
  have hcop42 : Nat.Coprime s 42 := hs_coprime
  have hcop2 : Nat.Coprime s 2 := Nat.Coprime.coprime_dvd_right (by decide : 2 ∣ 42) hcop42
  have hcop3 : Nat.Coprime s 3 := Nat.Coprime.coprime_dvd_right (by decide : 3 ∣ 42) hcop42
  have hcop7 : Nat.Coprime s 7 := Nat.Coprime.coprime_dvd_right (by decide : 7 ∣ 42) hcop42
  have hcop2_symm : Nat.Coprime 2 s := hcop2.symm
  have hcop3_symm : Nat.Coprime 3 s := hcop3.symm
  have hcop7_symm : Nat.Coprime 7 s := hcop7.symm

  have hcop2_3 : Nat.Coprime 2 3 := by decide
  have hcop43_2 : Nat.Coprime 43 2 := by decide
  have hcop43_3 : Nat.Coprime 43 3 := by decide
  have hcop43_7 : Nat.Coprime 43 7 := by decide
  have hcop43_2a1 : Nat.Coprime 43 (2^(a-1)) := Nat.Coprime.pow_right _ hcop43_2
  have hcop43_3b1 : Nat.Coprime 43 (3^(b-1)) := Nat.Coprime.pow_right _ hcop43_3
  have hcop43_7c1 : Nat.Coprime 43 (7^(c-1)) := Nat.Coprime.pow_right _ hcop43_7
  have hcop43_s : Nat.Coprime 43 s := (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr hs43

  have hcop_m_parts_1 : Nat.Coprime (43 * 2^(a-1)) (3^(b-1)) := Nat.Coprime.mul_left hcop43_3b1 (Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ hcop2_3))
  have hcop_m_parts_2 : Nat.Coprime (43 * 2^(a-1) * 3^(b-1)) (7^(c-1)) := by
    have h1 : Nat.Coprime 43 (7^(c-1)) := hcop43_7c1
    have h2 : Nat.Coprime (2^(a-1)) (7^(c-1)) := Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ (by decide : Nat.Coprime 2 7))
    have h3 : Nat.Coprime (3^(b-1)) (7^(c-1)) := Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 7))
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_left h1 h2) h3

  have hcop_m_s : Nat.Coprime (43 * 2^(a-1) * 3^(b-1) * 7^(c-1)) s := by
    have h1 : Nat.Coprime 43 s := hcop43_s
    have h2 : Nat.Coprime (2^(a-1)) s := Nat.Coprime.pow_left _ hcop2_symm
    have h3 : Nat.Coprime (3^(b-1)) s := Nat.Coprime.pow_left _ hcop3_symm
    have h4 : Nat.Coprime (7^(c-1)) s := Nat.Coprime.pow_left _ hcop7_symm
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left h1 h2) h3) h4

  have hcop_n_1 : Nat.Coprime (2^a) (3^b) := Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ hcop2_3)
  have hcop_n_2 : Nat.Coprime (2^a * 3^b) (7^c) := by
    have h2 : Nat.Coprime (2^a) (7^c) := Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ (by decide : Nat.Coprime 2 7))
    have h3 : Nat.Coprime (3^b) (7^c) := Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 7))
    exact Nat.Coprime.mul_left h2 h3

  have hcop_n_s : Nat.Coprime (2^a * 3^b * 7^c) s := by
    have h2 : Nat.Coprime (2^a) s := Nat.Coprime.pow_left _ hcop2_symm
    have h3 : Nat.Coprime (3^b) s := Nat.Coprime.pow_left _ hcop3_symm
    have h7 : Nat.Coprime (7^c) s := Nat.Coprime.pow_left _ hcop7_symm
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_left h2 h3) h7

  constructor
  · have h1 : totient m = 42 * totient (2^(a-1)) * totient (3^(b-1)) * totient (7^(c-1)) * totient s := by
      calc totient m = totient (43 * 2^(a-1) * 3^(b-1) * 7^(c-1) * s) := rfl
        _ = totient (43 * 2^(a-1) * 3^(b-1) * 7^(c-1)) * totient s := Nat.totient_mul hcop_m_s
        _ = totient (43 * 2^(a-1) * 3^(b-1)) * totient (7^(c-1)) * totient s := by rw [Nat.totient_mul hcop_m_parts_2]
        _ = totient (43 * 2^(a-1)) * totient (3^(b-1)) * totient (7^(c-1)) * totient s := by rw [Nat.totient_mul hcop_m_parts_1]
        _ = totient 43 * totient (2^(a-1)) * totient (3^(b-1)) * totient (7^(c-1)) * totient s := by rw [Nat.totient_mul hcop43_2a1]
        _ = 42 * totient (2^(a-1)) * totient (3^(b-1)) * totient (7^(c-1)) * totient s := rfl
    have h2 : totient n = 42 * totient (2^(a-1)) * totient (3^(b-1)) * totient (7^(c-1)) * totient s := by
      calc totient n = totient (2^a * 3^b * 7^c * s) := rfl
        _ = totient (2^a * 3^b * 7^c) * totient s := Nat.totient_mul hcop_n_s
        _ = totient (2^a * 3^b) * totient (7^c) * totient s := by rw [Nat.totient_mul hcop_n_2]
        _ = totient (2^a) * totient (3^b) * totient (7^c) * totient s := by rw [Nat.totient_mul hcop_n_1]
        _ = (2 * totient (2^(a-1))) * totient (3^b) * totient (7^c) * totient s := by
          rw [totient_two_pow_eq_two_mul a ha]
        _ = (2 * totient (2^(a-1))) * (3 * totient (3^(b-1))) * totient (7^c) * totient s := by
          have hbx := totient_three_pow_eq_three_mul b hb
          rw [hbx]
        _ = (2 * totient (2^(a-1))) * (3 * totient (3^(b-1))) * (7 * totient (7^(c-1))) * totient s := by
          have hcx := totient_seven_pow_eq_seven_mul c hc
          rw [hcx]
        _ = 42 * totient (2^(a-1)) * totient (3^(b-1)) * totient (7^(c-1)) * totient s := by ring
    rw [h1, h2]
  · intro h_eq
    have h_cancel2 : 42 * (2^(a-1) * 3^(b-1) * 7^(c-1) * s) = 43 * (2^(a-1) * 3^(b-1) * 7^(c-1) * s) := by
      calc 42 * (2^(a-1) * 3^(b-1) * 7^(c-1) * s) = (2 * 2^(a-1)) * (3 * 3^(b-1)) * (7 * 7^(c-1)) * s := by ring
        _ = 2^(a-1+1) * 3^(b-1+1) * 7^(c-1+1) * s := by
           rw [pow_add 2 (a-1) 1, pow_one, mul_comm (2^(a-1))]
           rw [pow_add 3 (b-1) 1, pow_one, mul_comm (3^(b-1))]
           rw [pow_add 7 (c-1) 1, pow_one, mul_comm (7^(c-1))]
        _ = 2^a * 3^b * 7^c * s := by
           have ha1 : a - 1 + 1 = a := by omega
           have hb1 : b - 1 + 1 = b := by omega
           have hc1 : c - 1 + 1 = c := by omega
           rw [ha1, hb1, hc1]
        _ = n := rfl
        _ = m  := h_eq.symm
        _ = 43 * 2^(a-1) * 3^(b-1) * 7^(c-1) * s := rfl
        _ = 43 * (2^(a-1) * 3^(b-1) * 7^(c-1) * s) := by ring
    have h_cancel : 42 = 43 := Nat.eq_of_mul_eq_mul_right (by positivity) h_cancel2
    contradiction

end CarmichaelTotient
