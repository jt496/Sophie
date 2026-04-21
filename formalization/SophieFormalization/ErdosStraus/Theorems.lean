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
