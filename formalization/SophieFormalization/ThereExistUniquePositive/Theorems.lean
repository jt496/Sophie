import Mathlib

/-!
# Putnam 2001 A5 : a^(n+1) - (a+1)^n = 2001 has a unique positive solution

We prove that there are unique positive integers `a` and `n` with
`a^(n+1) - (a+1)^n = 2001`, the solution being `(a, n) = (13, 2)`
(since `13^3 - 14^2 = 2197 - 196 = 2001`).

To avoid truncated natural subtraction we phrase the equation additively as
`a^(n+1) = (a+1)^n + 2001`.

## Strategy
* `dvd_2002`      : reducing mod `a` forces `a ∣ 2002`.
* `mod3`          : reducing mod 3 forces `a ≡ 1 [MOD 3]` and `n` even.
* `dvd_2002_succ` : reducing mod `a+1` (using `n` even) forces `(a+1) ∣ 2002`.
* Two consecutive divisors of `2002 = 2·7·11·13` can only be `(1,2)` or
  `(13,14)`, so `a ∈ {1, 13}`.  `a = 1` is impossible, and for `a = 13` the
  single inequality `13^36 < 14^35` bounds `n ≤ 34`, leaving a finite check.
-/

namespace ThereExistUniquePositive

/-- The defining property of a positive-integer solution `(a, n)`. -/
def IsSol (p : ℕ × ℕ) : Prop :=
  0 < p.1 ∧ 0 < p.2 ∧ p.1 ^ (p.2 + 1) = (p.1 + 1) ^ p.2 + 2001

/-- `(13, 2)` is a solution. -/
lemma isSol_13_2 : IsSol (13, 2) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num

/-- **Mod `a` reduction.** Any solution forces `a ∣ 2002`.
    Reducing the equation modulo `a`: `a^(n+1) ≡ 0` and `(a+1)^n ≡ 1`, hence
    `0 ≡ 1 + 2001 = 2002 [MOD a]`. -/
lemma dvd_2002 {a n : ℕ} (h : a ^ (n + 1) = (a + 1) ^ n + 2001) : a ∣ 2002 := by
  have h0 : a ^ (n + 1) ≡ 0 [MOD a] :=
    (Nat.modEq_zero_iff_dvd).mpr (dvd_pow_self a (Nat.succ_ne_zero n))
  have hbase : (a + 1) ≡ 1 [MOD a] := by
    show (a + 1) % a = 1 % a
    exact Nat.add_mod_left a 1
  have h1 : (a + 1) ^ n ≡ 1 [MOD a] := by
    calc (a + 1) ^ n ≡ 1 ^ n [MOD a] := hbase.pow n
      _ = 1 := one_pow n
  have hkey : (0 : ℕ) ≡ 2002 [MOD a] := by
    calc (0 : ℕ) ≡ a ^ (n + 1) [MOD a] := h0.symm
      _ = (a + 1) ^ n + 2001 := h
      _ ≡ 1 + 2001 [MOD a] := h1.add_right 2001
      _ = 2002 := by norm_num
  exact (Nat.modEq_zero_iff_dvd).mp hkey.symm

/-- **Mod 3 reduction.** Any solution forces `a ≡ 1 [MOD 3]` and `n` even.
    Since `2001 ≡ 0 [MOD 3]`, working in `ZMod 3` the equation becomes
    `x^(n+1) = (x+1)^n`; the residues `x = 0, 2` are impossible, and `x = 1`
    gives `(-1)^n = 1`, i.e. `n` even. -/
lemma mod3 {a n : ℕ} (hn : 0 < n) (h : a ^ (n + 1) = (a + 1) ^ n + 2001) :
    a % 3 = 1 ∧ Even n := by
  have hz : (a : ZMod 3) ^ (n + 1) = ((a : ZMod 3) + 1) ^ n := by
    have hc := congrArg (Nat.cast : ℕ → ZMod 3) h
    push_cast at hc
    rw [show (2001 : ZMod 3) = 0 from by native_decide] at hc
    simpa using hc
  have hcast : (a : ZMod 3) = ((a % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod a 3).symm
  have h3 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases h3 with h0 | h1 | h2
  · exfalso
    rw [hcast, h0] at hz
    rw [show (((0 : ℕ)) : ZMod 3) = 0 from by norm_num, zero_pow (by omega : n + 1 ≠ 0),
        zero_add, one_pow] at hz
    revert hz; native_decide
  · refine ⟨h1, ?_⟩
    rw [hcast, h1] at hz
    rw [show (((1 : ℕ)) : ZMod 3) = 1 from by norm_num, one_pow,
        show (1 + 1 : ZMod 3) = -1 from by native_decide] at hz
    rcases Nat.even_or_odd n with he | ho
    · exact he
    · exfalso; rw [ho.neg_one_pow] at hz; revert hz; native_decide
  · exfalso
    rw [hcast, h2] at hz
    rw [show (((2 : ℕ)) : ZMod 3) = -1 from by native_decide,
        show (-1 + 1 : ZMod 3) = 0 from by native_decide, zero_pow (by omega : n ≠ 0)] at hz
    rcases Nat.even_or_odd (n + 1) with he | ho
    · rw [he.neg_one_pow] at hz; revert hz; native_decide
    · rw [ho.neg_one_pow] at hz; revert hz; native_decide

/-- **Mod 4 reduction.** With `n` even, any solution forces `a` odd.
    Since `2001 ≡ 1 [MOD 4]`, if `a` were even then `a^(n+1) ≡ 0` and the odd
    `(a+1)^n ≡ 1 [MOD 4]` (as `n` is even), giving `0 ≡ 1 + 1 = 2 [MOD 4]`.
    (Not needed for the final proof, but kept as an independent verified fact.) -/
lemma mod4 {a n : ℕ} (hn : 0 < n) (hne : Even n)
    (h : a ^ (n + 1) = (a + 1) ^ n + 2001) : ¬ Even a := by
  intro hae
  have hz : (a : ZMod 4) ^ (n + 1) = ((a : ZMod 4) + 1) ^ n + 1 := by
    have hc := congrArg (Nat.cast : ℕ → ZMod 4) h
    push_cast at hc
    rw [show (2001 : ZMod 4) = 1 from by native_decide] at hc
    exact hc
  have hcast : (a : ZMod 4) = ((a % 4 : ℕ) : ZMod 4) := (ZMod.natCast_mod a 4).symm
  have h4 : a % 4 = 0 ∨ a % 4 = 2 := by
    have := Nat.even_iff.mp hae; omega
  have hpow2 : (2 : ZMod 4) ^ (n + 1) = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, n + 1 = k + 2 := ⟨n - 1, by omega⟩
    rw [hk, pow_add, show (2 : ZMod 4) ^ 2 = 0 from by native_decide, mul_zero]
  rcases h4 with h0 | h2
  · rw [hcast, h0, show (((0 : ℕ)) : ZMod 4) = 0 from by norm_num,
        zero_pow (by omega : n + 1 ≠ 0), zero_add, one_pow] at hz
    revert hz; native_decide
  · rw [hcast, h2, show (((2 : ℕ)) : ZMod 4) = 2 from by norm_num,
        show (2 + 1 : ZMod 4) = -1 from by native_decide, hne.neg_one_pow, hpow2] at hz
    revert hz; native_decide

/-- **Mod `a+1` reduction.** With `n` even, any solution forces `(a+1) ∣ 2002`.
    Modulo `a+1`: `a ≡ -1`, `(a+1)^n ≡ 0`, so `(-1)^(n+1) ≡ 2001`; as `n+1` is
    odd this is `-1 ≡ 2001`, i.e. `2002 ≡ 0 [MOD a+1]`. -/
lemma dvd_2002_succ {a n : ℕ} (hn : 0 < n) (hne : Even n)
    (h : a ^ (n + 1) = (a + 1) ^ n + 2001) : (a + 1) ∣ 2002 := by
  haveI : NeZero (a + 1) := ⟨Nat.succ_ne_zero a⟩
  have hz : (a : ZMod (a + 1)) ^ (n + 1) = ((a : ZMod (a + 1)) + 1) ^ n + 2001 := by
    have hc := congrArg (Nat.cast : ℕ → ZMod (a + 1)) h
    push_cast at hc
    exact hc
  have ha1 : (a : ZMod (a + 1)) + 1 = 0 := by
    have h0 := ZMod.natCast_self (a + 1)
    push_cast at h0
    exact h0
  have haneg : (a : ZMod (a + 1)) = -1 := eq_neg_of_add_eq_zero_left ha1
  rw [ha1, zero_pow (by omega : n ≠ 0), haneg, (hne.add_one).neg_one_pow, zero_add] at hz
  -- hz : (-1 : ZMod (a+1)) = 2001
  have hkey : ((2002 : ℕ) : ZMod (a + 1)) = 0 := by
    have e : ((2002 : ℕ) : ZMod (a + 1)) = (2001 : ZMod (a + 1)) + 1 := by push_cast; ring
    rw [e, ← hz]; ring
  exact (ZMod.natCast_eq_zero_iff 2002 (a + 1)).mp hkey

/-- **Main theorem (Putnam 2001 A5).**
    There is a unique pair of positive integers `(a, n)` with
    `a^(n+1) = (a+1)^n + 2001`, namely `(13, 2)`. -/
theorem unique_solution : ∃! p : ℕ × ℕ, IsSol p := by
  refine ⟨(13, 2), isSol_13_2, ?_⟩
  rintro ⟨a, n⟩ ⟨ha, hn, heq⟩
  -- Structural reductions.
  have hdvd : a ∣ 2002 := dvd_2002 heq
  obtain ⟨_, hneven⟩ := mod3 hn heq
  have hdvd1 : (a + 1) ∣ 2002 := dvd_2002_succ hn hneven heq
  -- `a` and `a+1` are coprime, so `a*(a+1) ∣ 2002`, bounding `a ≤ 44`.
  have hcop : Nat.Coprime a (a + 1) := by simp
  have hmul : a * (a + 1) ∣ 2002 := hcop.mul_dvd_of_dvd_of_dvd hdvd hdvd1
  have hle : a * (a + 1) ≤ 2002 := Nat.le_of_dvd (by norm_num) hmul
  have ha44 : a ≤ 44 := by
    by_contra hc
    have : 45 * 46 ≤ a * (a + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  -- The only consecutive divisors of 2002 are (1,2) and (13,14): `a ∈ {1, 13}`.
  have ha113 : a = 1 ∨ a = 13 := by
    interval_cases a <;>
      first
        | (left; rfl)
        | (right; rfl)
        | (exfalso; revert hdvd hdvd1; native_decide)
  rcases ha113 with rfl | rfl
  · -- a = 1 : `1 = 2^n + 2001` is impossible.
    exfalso
    simp only [one_pow] at heq
    have : 1 ≤ (1 + 1) ^ n := Nat.one_le_pow _ _ (by norm_num)
    omega
  · -- a = 13 : bound `n ≤ 34`, then a finite check pins `n = 2`.
    have heq' : (13 : ℕ) ^ (n + 1) = 14 ^ n + 2001 := by
      have e : (13 + 1 : ℕ) = 14 := by norm_num
      rw [e] at heq; exact heq
    have hbound : n ≤ 34 := by
      by_contra hc                         -- hc : ¬ n ≤ 34, i.e. 35 ≤ n
      have h35 : (13 : ℕ) ^ 36 < 14 ^ 35 := by native_decide
      have hpos : 0 < (14 : ℕ) ^ (n - 35) := pow_pos (by norm_num) _
      have key : (13 : ℕ) ^ (n + 1) < 14 ^ n := by
        calc (13 : ℕ) ^ (n + 1) = 13 ^ 36 * 13 ^ (n - 35) := by
              rw [← pow_add]; congr 1; omega
          _ ≤ 13 ^ 36 * 14 ^ (n - 35) := by gcongr; norm_num
          _ < 14 ^ 35 * 14 ^ (n - 35) := by
              exact (Nat.mul_lt_mul_right hpos).mpr h35
          _ = 14 ^ n := by rw [← pow_add]; congr 1; omega
      omega
    interval_cases n <;>
      first
        | rfl
        | (exfalso; revert heq'; native_decide)

end ThereExistUniquePositive

