/-
  SophieFormalization.ErdosStraus.Theorems
  Verified cases of the Erdős–Straus conjecture: 4/n = 1/x + 1/y + 1/z
  has a positive integer solution for every n ≥ 2.

  Proved here (Sophie session 20260421, rounds 1–10):
    • Even n          (FA-6AA92B / PA-C5E101)
    • n ≡ 3 mod 4     (FA-6AA92B / PA-C5E101)
    • n ≡ 5 mod 12    (FA-6AA92B / SP-34E0FD)
    • n ≡ 9 mod 12    (FA-A4DCFE / PA-EF2F96)

  Still open: n ≡ 1 mod 12.
-/

import Mathlib

/-! ## Even n -/

/-- For even n = 2m (m ≥ 1): 4/(2m) = 1/m + 1/(2m) + 1/(2m). -/
theorem erdos_straus_even (m : ℕ) (hm : 0 < m) :
    (4 : ℚ) / (2 * m) = 1 / m + 1 / (2 * m) + 1 / (2 * m) := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
  field_simp
  ring

/-! ## n ≡ 3 mod 4 -/

/-- For n ≡ 3 mod 4: write n = 4k + 3, a = k + 1. Then
    4/n = 1/(a+1) + 1/(a·(a+1)) + 1/(n·a).
    Key identity: 1/(a+1) + 1/(a(a+1)) = 1/a, then 1/a + 1/(na) = 4/n. -/
theorem erdos_straus_three_mod4 (k : ℕ) :
    (4 : ℚ) / (4 * k + 3) =
      1 / ((k : ℚ) + 2) +
      1 / (((k : ℚ) + 1) * ((k : ℚ) + 2)) +
      1 / ((4 * (k : ℚ) + 3) * ((k : ℚ) + 1)) := by
  have h1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (k : ℚ) + 2 ≠ 0 := by positivity
  have h3 : 4 * (k : ℚ) + 3 ≠ 0 := by positivity
  field_simp
  ring

/-! ## n ≡ 5 mod 12 -/

/-- For n ≡ 5 mod 12: write n = 12k + 5. Then
    4/n = 1/n + 1/(4k+2) + 1/((4k+2)·n).
    Key identity: 1/(4k+2) + 1/((4k+2)(12k+5)) = 3/(12k+5), so total = 4/n. -/
theorem erdos_straus_five_mod12 (k : ℕ) :
    (4 : ℚ) / (12 * k + 5) =
      1 / (12 * (k : ℚ) + 5) +
      1 / (4 * (k : ℚ) + 2) +
      1 / ((4 * (k : ℚ) + 2) * (12 * (k : ℚ) + 5)) := by
  have h1 : (4 : ℚ) * k + 2 ≠ 0 := by positivity
  have h2 : (12 : ℚ) * k + 5 ≠ 0 := by positivity
  field_simp
  ring

/-! ## n ≡ 9 mod 12 -/

/-- For n ≡ 9 mod 12: write n = 12k + 9, j = 4k + 3, b = 3k + 3. Then
    4/n = 1/(b+1) + 1/(b·(b+1)) + 1/(j·b).
    Key identity: 1/(b+1) + 1/(b(b+1)) = 1/b, then 1/b + 1/(jb) = 4/n. -/
theorem erdos_straus_nine_mod12 (k : ℕ) :
    (4 : ℚ) / (12 * k + 9) =
      1 / (3 * (k : ℚ) + 4) +
      1 / ((3 * (k : ℚ) + 3) * (3 * (k : ℚ) + 4)) +
      1 / ((4 * (k : ℚ) + 3) * (3 * (k : ℚ) + 3)) := by
  have h1 : (3 : ℚ) * k + 3 ≠ 0 := by positivity
  have h2 : (3 : ℚ) * k + 4 ≠ 0 := by positivity
  have h3 : (4 : ℚ) * k + 3 ≠ 0 := by positivity
  have h4 : (12 : ℚ) * k + 9 ≠ 0 := by positivity
  field_simp
  ring

/-- Existential form: for every n ≡ 9 mod 12, there exist positive integers
    x, y, z with 4/n = 1/x + 1/y + 1/z. -/
theorem erdos_straus_of_nine_mod12 (n : ℕ) (hn : n % 12 = 9) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  obtain ⟨k, hk⟩ : ∃ k, n = 12 * k + 9 := ⟨n / 12, by omega⟩
  subst hk
  exact ⟨3 * k + 4, (3 * k + 3) * (3 * k + 4), (4 * k + 3) * (3 * k + 3),
         by omega, by positivity, by positivity, by push_cast; exact erdos_straus_nine_mod12 k⟩

namespace ErdosStraus

private lemma four_dvd_of_mod12 (n : ℕ) (h : n % 12 = 1) : 4 ∣ n + 3 := by
  grind

private lemma anchor_mul4 (n : ℕ) (h : n % 12 = 1) :
    4 * ((n + 3) / 4) = n + 3 :=
  Nat.mul_div_cancel' (four_dvd_of_mod12 n h)

private lemma anchor_mod3 (n : ℕ) (h : n % 12 = 1) :
    ((n + 3) / 4) % 3 = 1 := by
  have h4b := anchor_mul4 n h
  grind

/-- Anchor k=0 criterion: for n ≡ 1 mod 12, if n·⌈(n+3)/4⌉ has a prime
    factor p ≡ 2 mod 3, then 4/n decomposes via the anchor x = (n+3)/4. -/
theorem erdos_straus_anchor_k0 (n : ℕ) (hn12 : n % 12 = 1) (hn2 : 2 ≤ n)
    (p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 2)
    (hpdvd : p ∣ n * ((n + 3) / 4)) :
    ∃ x Y Z : ℕ, 0 < x ∧ 0 < Y ∧ 0 < Z ∧
      (4 : ℚ) / n = 1 / x + 1 / Y + 1 / Z := by
  set b := (n + 3) / 4 with hb_def
  set m := n * b with hm_def
  -- Exact division fact
  have h4b : 4 * b = n + 3 := anchor_mul4 n hn12
  -- Positivity
  have hn_pos : 0 < n := by linarith
  have hb_pos : 0 < b := by
    have : 0 < 4 * b := by linarith [h4b]
    grind
  have hm_pos : 0 < m := Nat.mul_pos hn_pos hb_pos
  -- Get the quotient q so that p * q = m
  obtain ⟨q, hq⟩ := hpdvd
  have hp_pos : 0 < p := hp.pos
  have hq_pos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq_pos
    · simp at hq; linarith
    · exact hq_pos
  -- Mod 3 facts
  have hn3 : n % 3 = 1 := by grind
  have hb3 : b % 3 = 1 := anchor_mod3 n hn12
  have hm3 : m % 3 = 1 := by
    have : (n * b) % 3 = (n % 3) * (b % 3) % 3 := Nat.mul_mod n b 3
    grind
  have hq3 : q % 3 = 2 := by
    have : (p * q) % 3 = 1 := by rw [← hq, hm3]
    rw [Nat.mul_mod, hp3] at this
    have : q % 3 < 3 := Nat.mod_lt _ (by norm_num)
    omega
  -- Divisibility for witnesses
  have h3pm : 3 ∣ p + m := by
    have : (p + m) % 3 = 0 := by grind
    exact Nat.dvd_of_mod_eq_zero this
  have h3qp1 : 3 ∣ q + 1 := by
    have : (q + 1) % 3 = 0 := by grind
    exact Nat.dvd_of_mod_eq_zero this
  -- Define witnesses
  refine ⟨b, (p + m) / 3, m * ((q + 1) / 3), hb_pos, ?_, ?_, ?_⟩
  · -- 0 < Y = (p + m) / 3
    have hpm_pos : 0 < p + m := Nat.add_pos_left hp_pos m
    exact Nat.div_pos (by grind) (by norm_num)
  · -- 0 < Z = m * ((q+1)/3)
    apply Nat.mul_pos hm_pos
    exact Nat.div_pos (by grind) (by norm_num)
  · -- Rational identity: 4/n = 1/b + 1/Y + 1/Z
    -- Lift all ℕ facts to ℚ
    have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast hn_pos.ne'
    have hb_ne : (b : ℚ) ≠ 0 := by exact_mod_cast hb_pos.ne'
    have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp_pos.ne'
    have hm_ne : (m : ℚ) ≠ 0 := by exact_mod_cast hm_pos.ne'
    have hq_ne : (q : ℚ) ≠ 0 := by exact_mod_cast hq_pos.ne'
    -- Cast the key ℕ equalities to ℚ
    have h4bQ : 4 * (b : ℚ) = (n : ℚ) + 3 := by exact_mod_cast h4b
    have hpqQ : (p : ℚ) * q = m := by exact_mod_cast hq.symm
    have h3pmQ : 3 * ((p + m) / 3 : ℕ) = p + m := by
      exact_mod_cast Nat.mul_div_cancel' h3pm
    have h3qp1Q : 3 * ((q + 1) / 3 : ℕ) = q + 1 := by
      exact_mod_cast Nat.mul_div_cancel' h3qp1
    -- Y and Z nonzero
    have hY_ne : ((p + m) / 3 : ℕ) ≠ 0 := by
      have : 0 < (p + m) / 3 := Nat.div_pos (by grind) (by norm_num)
      exact this.ne'
    have hqp1_div_ne : ((q + 1) / 3 : ℕ) ≠ 0 := by
      have : 0 < (q + 1) / 3 := Nat.div_pos (by grind) (by norm_num)
      exact this.ne'
    have hZ_ne : m * ((q + 1) / 3 : ℕ) ≠ 0 := Nat.mul_ne_zero (by exact_mod_cast hm_pos.ne') hqp1_div_ne
    -- Cast Y and Z equations
    have hYQ : 3 * ((p + m) / 3 : ℚ) = (p : ℚ) + m := by exact_mod_cast h3pmQ
    have hZdivQ : 3 * (((q + 1) / 3 : ℕ) : ℚ) = (q : ℚ) + 1 := by exact_mod_cast h3qp1Q
    -- Prove the identity by field_simp then linear_combination
    have hY_cast : ((p + m) / 3 : ℚ) = ((p + m) / 3 : ℕ) := by norm_cast
    have hZ_cast : (m * ((q + 1) / 3) : ℚ) = (m : ℚ) * ((q + 1) / 3 : ℕ) := by norm_cast;
    rw [Nat.cast_mul]
    field_simp
    have hYQ' : ((↑((p + m) / 3) : ℚ)) = ((p : ℚ) + (m : ℚ)) / 3 := by linarith [hYQ]
    have hZdivQ' : ((↑((q + 1) / 3) : ℚ)) = ((q : ℚ) + 1) / 3 := by linarith [hZdivQ]
    rw [hYQ', hZdivQ']
    field_simp; grind

end ErdosStraus
