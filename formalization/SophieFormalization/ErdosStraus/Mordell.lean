/-
  SophieFormalization.ErdosStraus.Mordell
  Mordell's (1967) covering system for the Erdős–Straus conjecture.

  Main result: 4/n = 1/x + 1/y + 1/z is solvable in positive integers for
  all n ≥ 2 with n % 840 ∉ {1, 121, 169, 289, 361, 529}.

  Source: L.J. Mordell, "Diophantine Equations" (1969), Chapter 14.
-/

import Mathlib
import SophieFormalization.ErdosStraus.Theorems

namespace ErdosStraus

/-! ## Parametric Identity Families

Two families of explicit solutions parametrised by arbitrary positive integers a, b, c, d. -/

/-- **Family A** (Mordell eq. 2): if a + b·n + c·n = 4·a·b·c·d then
    4/n = 1/(b·c·d·n) + 1/(a·c·d) + 1/(a·b·d).
    Witness: (x, y, z) = (b·c·d·n, a·c·d, a·b·d). -/
theorem mordell_family_a (n a b c d : ℕ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b * n + c * n = 4 * a * b * c * d) :
    (4 : ℚ) / n = 1 / (↑b * ↑c * ↑d * ↑n) + 1 / (↑a * ↑c * ↑d) + 1 / (↑a * ↑b * ↑d) := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hb' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hc' : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have h' : (a : ℚ) + ↑b * ↑n + ↑c * ↑n = 4 * ↑a * ↑b * ↑c * ↑d := by exact_mod_cast h
  -- Both sides equal (a + b·n + c·n) / (a·b·c·d·n)
  have step : (1 : ℚ) / (↑b * ↑c * ↑d * ↑n) + 1 / (↑a * ↑c * ↑d) + 1 / (↑a * ↑b * ↑d)
            = (↑a + ↑b * ↑n + ↑c * ↑n) / (↑a * ↑b * ↑c * ↑d * ↑n) := by
    field_simp;
  rw [step, h']
  field_simp;

/-- **Family B** (Mordell eq. 3): if n·a + b + c = 4·a·b·c·d then
    4/n = 1/(b·c·d) + 1/(n·a·b·d) + 1/(n·a·c·d).
    Witness: (x, y, z) = (b·c·d, n·a·b·d, n·a·c·d). -/
theorem mordell_family_b (n a b c d : ℕ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : n * a + b + c = 4 * a * b * c * d) :
    (4 : ℚ) / n = 1 / (↑b * ↑c * ↑d) + 1 / (↑n * ↑a * ↑b * ↑d) + 1 / (↑n * ↑a * ↑c * ↑d) := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hb' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hc' : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have h' : (n : ℚ) * ↑a + ↑b + ↑c = 4 * ↑a * ↑b * ↑c * ↑d := by exact_mod_cast h
  -- Both sides equal (n·a + b + c) / (n·a·b·c·d)
  have step : (1 : ℚ) / (↑b * ↑c * ↑d) + 1 / (↑n * ↑a * ↑b * ↑d) + 1 / (↑n * ↑a * ↑c * ↑d)
            = (↑n * ↑a + ↑b + ↑c) / (↑n * ↑a * ↑b * ↑c * ↑d) := by
    field_simp; ring
  rw [step, h']
  field_simp;

/-! ## Covering Congruence Classes

Explicit solutions for each congruence class covered by Mordell's argument.
All proofs are direct rational identities, closed by `field_simp; ring`. -/

/-- n ≡ 0 mod 4: take x = y = z = 3n/4.
    Subsumes the even-n case for multiples of 4. -/
theorem erdos_straus_zero_mod4 (k : ℕ) (hk : 0 < k) :
    (4 : ℚ) / (4 * k) = 1 / (3 * k) + 1 / (3 * k) + 1 / (3 * k) := by
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  field_simp; ring

/-- n ≡ 2 mod 4, n = 4k+2: Family B with (a,b,c,d) = (1,1,1,k+1).
    Condition: (4k+2)·1 + 1 + 1 = 4k+4 = 4(k+1). ✓
    Witness: (x,y,z) = (k+1, (4k+2)(k+1), (4k+2)(k+1)). -/
theorem erdos_straus_two_mod4 (k : ℕ) :
    (4 : ℚ) / (4 * k + 2) =
      1 / ((k : ℚ) + 1) +
      1 / ((4 * k + 2) * (k + 1)) +
      1 / ((4 * k + 2) * (k + 1)) := by
  have h1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have h2 : 4 * (k : ℚ) + 2 ≠ 0 := by positivity
  field_simp; ring

/-- n ≡ 5 mod 8, n = 8k+5: Family B with (a,b,c,d) = (1,1,2,k+1).
    Condition: (8k+5)·1 + 1 + 2 = 8k+8 = 8(k+1). ✓
    Witness: (x,y,z) = (2(k+1), (8k+5)(k+1), 2(8k+5)(k+1)). -/
theorem erdos_straus_five_mod8 (k : ℕ) :
    (4 : ℚ) / (8 * k + 5) =
      1 / (2 * ((k : ℚ) + 1)) +
      1 / ((8 * k + 5) * (k + 1)) +
      1 / (2 * (8 * k + 5) * (k + 1)) := by
  have h1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have h2 : 8 * (k : ℚ) + 5 ≠ 0 := by positivity
  field_simp; ring

/-- n ≡ 2 mod 3, n = 3m+2: Family B with (a,b,c,d) = (1,1,m+1,1).
    Condition: (3m+2)·1 + 1 + (m+1) = 4m+4 = 4(m+1). ✓
    Witness: (x,y,z) = (m+1, (3m+2), (3m+2)(m+1)).
    (Corresponds to Mordell's q=3 case.) -/
theorem erdos_straus_two_mod3 (m : ℕ) :
    (4 : ℚ) / (3 * m + 2) =
      1 / ((m : ℚ) + 1) +
      1 / (3 * m + 2) +
      1 / ((3 * m + 2) * (m + 1)) := by
  have h1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have h2 : 3 * (m : ℚ) + 2 ≠ 0 := by positivity
  field_simp; ring

/-- n ≡ 0 mod 3, n = 3m: 4/(3m) = 1/m + 1/(4m) + 1/(12m). -/
theorem erdos_straus_zero_mod3 (m : ℕ) (hm : 0 < m) :
    (4 : ℚ) / (3 * m) = 1 / m + 1 / (4 * m) + 1 / (12 * m) := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp; ring

/-- n ≡ 0 mod 7, n = 7m: 4/(7m) = 1/(3m) + 1/(6m) + 1/(14m). -/
theorem erdos_straus_zero_mod7 (m : ℕ) (hm : 0 < m) :
    (4 : ℚ) / (7 * m) = 1 / (3 * m) + 1 / (6 * m) + 1 / (14 * m) := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp; ring

/-- n ≡ 0 mod 5, n = 5m: 4/(5m) = 1/(2m) + 1/(5m) + 1/(10m). -/
theorem erdos_straus_zero_mod5 (m : ℕ) (hm : 0 < m) :
    (4 : ℚ) / (5 * m) = 1 / (2 * m) + 1 / (5 * m) + 1 / (10 * m) := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp; ring

/-! ## Helper Lemmas for Hard Residues

Algebraic identity families used for residues 193, 337, 457, 673, 697, 793 mod 840.
Each family is parameterised by integer divisibility conditions on y and z. -/

/-- Restate Nat.mul_mod for local use. -/
private theorem nat_mul_mod_eq (a b m : ℕ) : (a * b) % m = (a % m) * (b % m) % m :=
  Nat.mul_mod a b m

/-- **C3 family**: if 4x = n+3, 3y = nx+5, 5z = nxy, and n,x,y,z > 0, then 4/n=1/x+1/y+1/z. -/
private theorem c3_family (n x y z : ℕ)
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h4x : 4 * x = n + 3) (h3y : 3 * y = n * x + 5) (h5z : 5 * z = n * x * y) :
    (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have h4xQ : 4 * (x : ℚ) = n + 3 := by exact_mod_cast h4x
  have h3yQ : 3 * (y : ℚ) = n * x + 5 := by exact_mod_cast h3y
  have h5zQ : 5 * (z : ℚ) = n * x * y := by exact_mod_cast h5z
  have hn_q : (0:ℚ) < n := by exact_mod_cast hn
  have hx_q : (0:ℚ) < x := by exact_mod_cast hx
  have hy_q : (0:ℚ) < y := by exact_mod_cast hy
  field_simp
  linear_combination (y : ℚ) * z * h4xQ + z * h3yQ + h5zQ

/-- **C7-10 family**: if 4x = n+7, 7y = nx+10, 10z = nxy, and n,x,y,z > 0,
    then 4/n = 1/x + 1/y + 1/z. Used for r=193. -/
private theorem c7_10_family (n x y z : ℕ)
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h4x : 4 * x = n + 7) (h7y : 7 * y = n * x + 10) (h10z : 10 * z = n * x * y) :
    (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have h4xQ : 4 * (x : ℚ) = n + 7 := by exact_mod_cast h4x
  have h7yQ : 7 * (y : ℚ) = n * x + 10 := by exact_mod_cast h7y
  have h10zQ : 10 * (z : ℚ) = n * x * y := by exact_mod_cast h10z
  have hn_q : (0:ℚ) < n := by exact_mod_cast hn
  have hx_q : (0:ℚ) < x := by exact_mod_cast hx
  have hy_q : (0:ℚ) < y := by exact_mod_cast hy
  field_simp
  linear_combination (y : ℚ) * z * h4xQ + z * h7yQ + h10zQ

/-- **C7-5 family**: if 4x = n+7, 7y = nx+5, 5z = nxy, and n,x,y,z > 0,
    then 4/n = 1/x + 1/y + 1/z. Used for r=673. -/
private theorem c7_5_family (n x y z : ℕ)
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h4x : 4 * x = n + 7) (h7y : 7 * y = n * x + 5) (h5z : 5 * z = n * x * y) :
    (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have h4xQ : 4 * (x : ℚ) = n + 7 := by exact_mod_cast h4x
  have h7yQ : 7 * (y : ℚ) = n * x + 5 := by exact_mod_cast h7y
  have h5zQ : 5 * (z : ℚ) = n * x * y := by exact_mod_cast h5z
  have hn_q : (0:ℚ) < n := by exact_mod_cast hn
  have hx_q : (0:ℚ) < x := by exact_mod_cast hx
  have hy_q : (0:ℚ) < y := by exact_mod_cast hy
  field_simp
  linear_combination (y : ℚ) * z * h4xQ + z * h7yQ + h5zQ

/-- **C7-20 family**: if 4x = n+7, 7y = nx+20, 20z = nxy, and n,x,y,z > 0,
    then 4/n = 1/x + 1/y + 1/z. Used for r=793. -/
private theorem c7_20_family (n x y z : ℕ)
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h4x : 4 * x = n + 7) (h7y : 7 * y = n * x + 20) (h20z : 20 * z = n * x * y) :
    (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have h4xQ : 4 * (x : ℚ) = n + 7 := by exact_mod_cast h4x
  have h7yQ : 7 * (y : ℚ) = n * x + 20 := by exact_mod_cast h7y
  have h20zQ : 20 * (z : ℚ) = n * x * y := by exact_mod_cast h20z
  have hn_q : (0:ℚ) < n := by exact_mod_cast hn
  have hx_q : (0:ℚ) < x := by exact_mod_cast hx
  have hy_q : (0:ℚ) < y := by exact_mod_cast hy
  field_simp
  linear_combination (y : ℚ) * z * h4xQ + z * h7yQ + h20zQ

/-! ## Hard Residue Lemmas (mod 840)

These six residues are not covered by any single modular congruence from the families above.
Each is handled by a specific parametric family derived from the c3 or c7 helper lemmas. -/

/-- Shared proof tactic for c3-family hard residues.
    Given n = 840*k+r and x = 210*k+x0 with the right r,x0, proves ∃ x y z with 4/n=1/x+1/y+1/z. -/
private theorem c3_residue_proof (n x : ℕ)
    (hn3 : n % 3 = 1) (hx3 : x % 3 = 1)
    (hx5 : x % 5 = 0) (h4x : 4 * x = n + 3)
    (hn_pos : 0 < n) (hx_pos : 0 < x) :
    ∃ X Y Z : ℕ, 0 < X ∧ 0 < Y ∧ 0 < Z ∧ (4 : ℚ) / n = 1 / X + 1 / Y + 1 / Z := by
  have hP3 : (n * x) % 3 = 1 := by rw [nat_mul_mod_eq, hn3, hx3]
  have hP5 : (n * x) % 5 = 0 := by rw [nat_mul_mod_eq, hx5]; simp
  set P := n * x
  set y := P / 3 + 2
  set z := P * y / 5
  have h3y : 3 * y = P + 5 := by
    simp only [y]; have := Nat.div_add_mod P 3; grind
  have h5z : 5 * z = P * y := by
    simp only [z]; have := Nat.div_add_mod (P * y) 5
    have hPy5 : (P * y) % 5 = 0 := by rw [nat_mul_mod_eq, hP5]; simp
    grind
  have hy_pos : 0 < y := by simp only [y]; grind
  have hP_pos : 0 < P := Nat.mul_pos hn_pos hx_pos
  have hPy_pos : 0 < P * y := Nat.mul_pos hP_pos hy_pos
  have hz_pos : 0 < z := by
    simp only [z]
    have := Nat.div_add_mod (P * y) 5
    have hPy5 : (P * y) % 5 = 0 := by rw [nat_mul_mod_eq, hP5]; simp
    grind
  exact ⟨x, y, z, hx_pos, hy_pos, hz_pos,
         c3_family n x y z hn_pos hx_pos hy_pos hz_pos h4x h3y h5z⟩

/-- n ≡ 337 mod 840: c3 family with x = 210k+85. -/
theorem erdos_straus_337_mod840 (k : ℕ) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (840 * k + 337) = 1 / x + 1 / y + 1 / z := by
  have := c3_residue_proof (840*k+337) (210*k+85)
    (by grind) (by grind) (by grind) (by ring) (by grind) (by grind)
  push_cast at this ⊢; exact this

/-- n ≡ 457 mod 840: c3 family with x = 210k+115. -/
theorem erdos_straus_457_mod840 (k : ℕ) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (840 * k + 457) = 1 / x + 1 / y + 1 / z := by
  have := c3_residue_proof (840*k+457) (210*k+115)
    (by grind) (by grind) (by grind) (by ring) (by grind) (by grind)
  push_cast at this ⊢; exact this

/-- n ≡ 697 mod 840: c3 family with x = 210k+175. -/
theorem erdos_straus_697_mod840 (k : ℕ) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (840 * k + 697) = 1 / x + 1 / y + 1 / z := by
  have := c3_residue_proof (840*k+697) (210*k+175)
    (by grind) (by grind) (by grind) (by ring) (by grind) (by grind)
  push_cast at this ⊢; exact this

/-- Shared proof for c7-10 family residues (n%7=4, x%7=1, x%10=0, 4x=n+7). -/
private theorem c7_10_residue_proof (n x : ℕ)
    (hn7 : n % 7 = 4) (hx7 : x % 7 = 1)
    (hx10 : x % 10 = 0) (h4x : 4 * x = n + 7)
    (hn_pos : 0 < n) (hx_pos : 0 < x) :
    ∃ X Y Z : ℕ, 0 < X ∧ 0 < Y ∧ 0 < Z ∧ (4 : ℚ) / n = 1 / X + 1 / Y + 1 / Z := by
  have hP7 : (n * x) % 7 = 4 := by rw [nat_mul_mod_eq, hn7, hx7]
  have hP10 : (n * x) % 10 = 0 := by rw [nat_mul_mod_eq, hx10]; simp
  set P := n * x
  set y := P / 7 + 2
  set z := P * y / 10
  have h7y : 7 * y = P + 10 := by
    simp only [y]; have := Nat.div_add_mod P 7; grind
  have h10z : 10 * z = P * y := by
    simp only [z]; have := Nat.div_add_mod (P * y) 10
    have hPy10 : (P * y) % 10 = 0 := by rw [nat_mul_mod_eq, hP10]; simp
    grind
  have hy_pos : 0 < y := by simp only [y]; grind
  have hP_pos : 0 < P := Nat.mul_pos hn_pos hx_pos
  have hPy_pos : 0 < P * y := Nat.mul_pos hP_pos hy_pos
  have hz_pos : 0 < z := by
    simp only [z]
    have := Nat.div_add_mod (P * y) 10
    have hPy10 : (P * y) % 10 = 0 := by rw [nat_mul_mod_eq, hP10]; simp
    grind
  exact ⟨x, y, z, hx_pos, hy_pos, hz_pos,
         c7_10_family n x y z hn_pos hx_pos hy_pos hz_pos h4x h7y h10z⟩

/-- n ≡ 193 mod 840: c7-10 family with x = 210k+50.
    4x = n+7; n%7=4, x%7=1 so (nx)%7=4 (7y = nx+10); x%10=0 so 10|nx (10z = nx*y). -/
theorem erdos_straus_193_mod840 (k : ℕ) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (840 * k + 193) = 1 / x + 1 / y + 1 / z := by
  have := c7_10_residue_proof (840*k+193) (210*k+50)
    (by grind) (by grind) (by grind) (by ring) (by grind) (by grind)
  push_cast at this ⊢; exact this

/-- Shared proof for c7-5 family residues (n%7=1, x%7=2, x%5=0, 4x=n+7). -/
private theorem c7_5_residue_proof (n x : ℕ)
    (hn7 : n % 7 = 1) (hx7 : x % 7 = 2)
    (hx5 : x % 5 = 0) (h4x : 4 * x = n + 7)
    (hn_pos : 0 < n) (hx_pos : 0 < x) :
    ∃ X Y Z : ℕ, 0 < X ∧ 0 < Y ∧ 0 < Z ∧ (4 : ℚ) / n = 1 / X + 1 / Y + 1 / Z := by
  have hP7 : (n * x) % 7 = 2 := by rw [nat_mul_mod_eq, hn7, hx7]
  have hP5 : (n * x) % 5 = 0 := by rw [nat_mul_mod_eq, hx5]; simp
  set P := n * x
  set y := P / 7 + 1
  set z := P * y / 5
  have h7y : 7 * y = P + 5 := by
    simp only [y]; have := Nat.div_add_mod P 7; grind
  have h5z : 5 * z = P * y := by
    simp only [z]; have := Nat.div_add_mod (P * y) 5
    have hPy5 : (P * y) % 5 = 0 := by rw [nat_mul_mod_eq, hP5]; simp
    grind
  have hy_pos : 0 < y := by simp only [y]; grind
  have hP_pos : 0 < P := Nat.mul_pos hn_pos hx_pos
  have hPy_pos : 0 < P * y := Nat.mul_pos hP_pos hy_pos
  have hz_pos : 0 < z := by
    simp only [z]
    have := Nat.div_add_mod (P * y) 5
    have hPy5 : (P * y) % 5 = 0 := by rw [nat_mul_mod_eq, hP5]; simp
    grind
  exact ⟨x, y, z, hx_pos, hy_pos, hz_pos,
         c7_5_family n x y z hn_pos hx_pos hy_pos hz_pos h4x h7y h5z⟩

/-- n ≡ 673 mod 840: c7-5 family with x = 210k+170.
    4x = n+7; n%7=1, x%7=2 so (nx)%7=2 (7y = nx+5); x%5=0 so 5|nx (5z = nx*y). -/
theorem erdos_straus_673_mod840 (k : ℕ) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (840 * k + 673) = 1 / x + 1 / y + 1 / z := by
  have := c7_5_residue_proof (840*k+673) (210*k+170)
    (by grind) (by grind) (by grind) (by ring) (by grind) (by grind)
  push_cast at this ⊢; exact this

/-- Shared proof for c7-20 family residues (n%7=2, x%7=4, x%10=0, 4x=n+7). -/
private theorem c7_20_residue_proof (n x : ℕ)
    (hn7 : n % 7 = 2) (hx7 : x % 7 = 4)
    (hx10 : x % 10 = 0) (h4x : 4 * x = n + 7)
    (hn_pos : 0 < n) (hx_pos : 0 < x) :
    ∃ X Y Z : ℕ, 0 < X ∧ 0 < Y ∧ 0 < Z ∧ (4 : ℚ) / n = 1 / X + 1 / Y + 1 / Z := by
  have hP7 : (n * x) % 7 = 1 := by rw [nat_mul_mod_eq, hn7, hx7]
  have hP10 : (n * x) % 10 = 0 := by rw [nat_mul_mod_eq, hx10]; simp
  set P := n * x
  set y := (P + 20) / 7
  set z := P * y / 20
  have hP20_mod7 : (P + 20) % 7 = 0 := by have : P % 7 = 1 := hP7; grind
  have h7y : 7 * y = P + 20 := by
    simp only [y]; have := Nat.div_add_mod (P + 20) 7; grind
  have h7xy_eq : 7 * (P * y) = P * (P + 20) := by nlinarith [h7y]
  have hP10_dvd : 10 ∣ P := Nat.dvd_of_mod_eq_zero hP10
  have h20_Psum : 20 ∣ P * (P + 20) := by
    obtain ⟨m, hm⟩ := hP10_dvd
    exact ⟨5 * m * (m + 2), by rw [hm]; ring⟩
  have hgcd : Nat.Coprime 7 20 := by norm_num
  have h20_Py : 20 ∣ P * y := by
    have hdvd : 20 ∣ 7 * (P * y) := h7xy_eq ▸ h20_Psum
    exact hgcd.symm.dvd_of_dvd_mul_left hdvd
  have h20z : 20 * z = P * y := by
    simp only [z]
    obtain ⟨q, hq⟩ := h20_Py
    rw [hq, Nat.mul_div_cancel_left _ (by norm_num)]
  have hy_pos : 0 < y := by simp only [y]; grind
  have hP_pos : 0 < P := Nat.mul_pos hn_pos hx_pos
  have hPy_pos : 0 < P * y := Nat.mul_pos hP_pos hy_pos
  have hz_pos : 0 < z := by
    have : 20 * z = P * y := h20z
    grind
  exact ⟨x, y, z, hx_pos, hy_pos, hz_pos,
         c7_20_family n x y z hn_pos hx_pos hy_pos hz_pos h4x h7y h20z⟩

/-- n ≡ 793 mod 840: c7-20 family with x = 210k+200.
    4x = n+7; n%7=2, x%7=4 so (nx)%7=1 (7y = nx+20); x%10=0 so 10|nx,
    and 4|nx (x%4=0 for even k, else 2|x and 2|y), giving 20|nx*y. -/
theorem erdos_straus_793_mod840 (k : ℕ) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (840 * k + 793) = 1 / x + 1 / y + 1 / z := by
  have := c7_20_residue_proof (840*k+793) (210*k+200)
    (by grind) (by grind) (by grind) (by ring) (by grind) (by grind)
  push_cast at this ⊢; exact this

/-- n ≡ 6 mod 7, n = 7j+6: Family B with (a,b,c,d) = (1,1,j+1,j+1) — wait:
    Condition: (7j+6)·1 + 1 + (j+1) = 8j+8 = 8(j+1). And 4·1·1·(j+1)·d = 4(j+1)d.
    We need 8(j+1) = 4(j+1)d, so d=2.
    So (a,b,c,d) = (1,1,j+1,2): Condition (7j+6) + 1 + (j+1) = 8(j+1) = 4·1·1·(j+1)·2. ✓
    Witness: (x,y,z) = (2(j+1), (7j+6)·2, (7j+6)·2(j+1)).
    (Corresponds to Mordell's q=7, b=1, n≡-1 mod 7 case.) -/
theorem erdos_straus_six_mod7 (j : ℕ) :
    (4 : ℚ) / (7 * j + 6) =
      1 / (2 * ((j : ℚ) + 1)) +
      1 / (2 * (7 * j + 6)) +
      1 / (2 * (7 * j + 6) * (j + 1)) := by
  have h1 : (j : ℚ) + 1 ≠ 0 := by positivity
  have h2 : 7 * (j : ℚ) + 6 ≠ 0 := by positivity
  field_simp; ring

/-- n ≡ 5 mod 7, n = 7j+5: Family B with (a,b,c,d) = (1,2,j+1,?) ...
    Condition: (7j+5)·1 + 2 + (j+1) = 8j+8 = 8(j+1) = 4·1·2·(j+1)·1. ✓
    So (a,b,c,d) = (1,2,j+1,1).
    Witness: (x,y,z) = (2(j+1), (7j+5)·2, (7j+5)·2(j+1))... let me recheck:
    (x,y,z) = (b·c·d, n·a·b·d, n·a·c·d) = (2·(j+1)·1, n·1·2·1, n·1·(j+1)·1)
             = (2(j+1), 2n, n(j+1)).
    Verify: 1/(2(j+1)) + 1/(2n) + 1/(n(j+1)) = (n + (j+1) + 2)/...
    (Corresponds to Mordell's q=7, ab|2, n≡-2 mod 7 case.) -/
theorem erdos_straus_five_mod7 (j : ℕ) :
    (4 : ℚ) / (7 * j + 5) =
      1 / (2 * ((j : ℚ) + 1)) +
      1 / (2 * (7 * j + 5)) +
      1 / ((7 * j + 5) * (j + 1)) := by
  have h1 : (j : ℚ) + 1 ≠ 0 := by positivity
  have h2 : 7 * (j : ℚ) + 5 ≠ 0 := by positivity
  field_simp; ring

/-- n ≡ 3 mod 7, n = 7j+3: covered by Mordell's q=7 argument (n ≡ −4 mod 7).
    The covering uses Family B, but the witness depends on j mod 4 since 7j+3 cycles
    through all residues mod 4 as j varies.  The case is handled in mordell_covering
    via the combined mod-840 case split; no single parametric formula covers all j.
    For concrete small cases: j=0 (n=3): from erdos_straus_three_mod4;
    j=1 (n=10): even, from erdos_straus_even; j=2 (n=17): erdos_straus_five_mod8, etc. -/
theorem erdos_straus_three_mod7 (j : ℕ) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (7 * j + 3) = 1 / x + 1 / y + 1 / z := by
  -- Direct witness via Mordell Family B (n = 7j+3, a=2, b=1, c=2j+1, d=1):
  -- Condition: (7j+3)·2 + 1 + (2j+1) = 16j+8 = 4·2·1·(2j+1)·1 ✓
  -- Witnesses: x = 2j+1, y = 2(7j+3), z = 2(7j+3)(2j+1)
  -- Verify: 1/(2j+1) + 1/(2(7j+3)) + 1/(2(7j+3)(2j+1))
  --       = (2(7j+3) + (2j+1) + 1) / (2(7j+3)(2j+1))
  --       = (16j+8) / (2(7j+3)(2j+1)) = 8(2j+1) / (2(7j+3)(2j+1)) = 4/(7j+3) ✓
  refine ⟨2*j+1, 2*(7*j+3), 2*(7*j+3)*(2*j+1),
          by grind, by grind, by positivity, ?_⟩
  have h1 : (2*(j:ℚ)+1) ≠ 0 := by positivity
  have h2 : 7*(j:ℚ)+3 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Helper: given modular conditions, n%840 must be one of the 6 hard residues. -/
private lemma hard_residue_cases (n : ℕ)
    (h8_1 : n % 8 = 1) (h3_1 : n % 3 = 1)
    (h7 : n % 7 ≠ 0) (h7_3 : n % 7 ≠ 3) (h7_5 : n % 7 ≠ 5) (h7_6 : n % 7 ≠ 6)
    (h5 : n % 5 ≠ 0)
    (h1 : n % 840 ≠ 1) (h121 : n % 840 ≠ 121) (h169 : n % 840 ≠ 169)
    (h289 : n % 840 ≠ 289) (h361 : n % 840 ≠ 361) (h529 : n % 840 ≠ 529) :
    n % 840 = 193 ∨ n % 840 = 337 ∨ n % 840 = 457 ∨
    n % 840 = 673 ∨ n % 840 = 697 ∨ n % 840 = 793 := by
  have h7r : n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 4 := by grind
  have h5r : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    grind
  have hr : n % 840 < 840 := Nat.mod_lt _ (by norm_num)
  -- For each combo of (n%7, n%5), establish exact modular constraints and let grind finish.
  -- grind can handle a single sub-case once n%840%7 and n%840%5 are concrete values.
  rcases h7r with h7v | h7v | h7v <;> rcases h5r with h5v | h5v | h5v | h5v <;>
    (have h840_8 : n % 840 % 8 = 1 := by grind
     have h840_3 : n % 840 % 3 = 1 := by grind
     have h840_7 : n % 840 % 7 = n % 7 := by grind
     have h840_5 : n % 840 % 5 = n % 5 := by grind
     grind)

/-! ## Main Theorem -/

/-- **Mordell's Covering Theorem** (1967): the Erdős–Straus conjecture holds for all n ≥ 2
    with n % 840 ∉ {1, 121, 169, 289, 361, 529}.

    The modulus 840 = 8 · 3 · 5 · 7 = lcm(8, 3, 5, 7) arises from combining:
    - mod 8:  n ≡ 0,2,4,6 (even); n ≡ 3,7 (≡3 mod 4); n ≡ 5 (≡5 mod 8) all covered.
    - mod 3:  n ≡ 0 (multiple of 3) or n ≡ 2 mod 3 covered; leaves n ≡ 1 mod 3.
    - mod 5:  further reductions via q=15 covering n ≡ 3,2 mod 5 (along with q=7 for multiples).
    - mod 7:  reductions via q=7 covering n ≡ 3,5,6 mod 7 and multiples of 7.
    By CRT, only n ≡ 1,121,169,289,361,529 mod 840 may remain uncovered. -/
theorem mordell_covering (n : ℕ) (hn : 2 ≤ n)
    (h : n % 840 ∉ ({1, 121, 169, 289, 361, 529} : Finset ℕ)) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  push Not at h
  obtain ⟨h1, h121, h169, h289, h361, h529⟩ := h
  -- The key: n%840 is not in {1,121,169,289,361,529}, so it falls into covered classes.
  -- We reduce: n%2=0 (even), or n%4=3, or n%3=0, or n%3=2, etc.
  -- Use the fact that n%840 ∉ {1,121,...} together with the modular structure.
  -- Step 1: if n is even
  by_cases heven : n % 2 = 0
  · obtain ⟨m, hm⟩ : ∃ m, n = 2 * m := ⟨n / 2, by grind⟩
    have hm_pos : 0 < m := by grind
    rw [hm]
    exact ⟨m, 2 * m, 2 * m, by grind, by grind, by grind, by
      push_cast; exact erdos_straus_even m hm_pos⟩
  -- n is odd
  -- Step 2: n ≡ 3 mod 4
  by_cases h4 : n % 4 = 3
  · obtain ⟨k, hk⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by grind⟩
    rw [hk]
    exact ⟨k + 2, (k + 1) * (k + 2), (4 * k + 3) * (k + 1), by grind, by positivity,
           by positivity, by push_cast; exact erdos_straus_three_mod4 k⟩
  -- Step 2b: n ≡ 5 mod 8 (odd, not ≡3 mod 4, so ≡1 mod 4; then ≡5 mod 8 stays)
  by_cases h8 : n % 8 = 5
  · obtain ⟨k, hk⟩ : ∃ k, n = 8 * k + 5 := ⟨n / 8, by grind⟩
    rw [hk]
    exact ⟨2 * (k + 1), (8 * k + 5) * (k + 1), 2 * (8 * k + 5) * (k + 1), by grind,
           by positivity, by positivity, by push_cast; exact erdos_straus_five_mod8 k⟩
  -- n ≡ 1 mod 4 (since n is odd and n % 4 ≠ 3)
  have h4_1 : n % 4 = 1 := by grind
  -- and n % 8 ≠ 5, so n % 8 = 1 (since n ≡ 1 mod 4)
  have h8_1 : n % 8 = 1 := by grind
  -- Step 3: n ≡ 0 mod 3
  by_cases h3 : n % 3 = 0
  · obtain ⟨m, hm⟩ : ∃ m, n = 3 * m := ⟨n / 3, by grind⟩
    have hm_pos : 0 < m := by grind
    rw [hm]
    exact ⟨m, 4 * m, 12 * m, by grind, by grind, by grind, by
      push_cast; exact erdos_straus_zero_mod3 m hm_pos⟩
  -- n ≡ 2 mod 3
  by_cases h3_2 : n % 3 = 2
  · -- n ≡ 1 mod 4 and n ≡ 2 mod 3. So n ≡ 5 mod 12.
    obtain ⟨k, hk⟩ : ∃ k, n = 12 * k + 5 := ⟨n / 12, by grind⟩
    rw [hk]
    exact ⟨12 * k + 5, 4 * k + 2, (4 * k + 2) * (12 * k + 5),
           by grind, by grind, by positivity, by push_cast; exact erdos_straus_five_mod12 k⟩
  -- n ≡ 1 mod 3 (since we ruled out 0 and 2)
  have h3_1 : n % 3 = 1 := by grind
  -- n ≡ 1 mod 4, n ≡ 1 mod 3 ⟹ n ≡ 1 mod 12
  -- Step 4: n ≡ 0 mod 7
  by_cases h7 : n % 7 = 0
  · obtain ⟨m, hm⟩ : ∃ m, n = 7 * m := ⟨n / 7, by grind⟩
    have hm_pos : 0 < m := by grind
    rw [hm]
    exact ⟨3 * m, 6 * m, 14 * m, by grind, by grind, by grind, by
      push_cast; exact erdos_straus_zero_mod7 m hm_pos⟩
  -- Step 5: n ≡ 6 mod 7
  by_cases h7_6 : n % 7 = 6
  · obtain ⟨j, hj⟩ : ∃ j, n = 7 * j + 6 := ⟨n / 7, by grind⟩
    rw [hj]
    exact ⟨2 * (j + 1), 2 * (7 * j + 6), 2 * (7 * j + 6) * (j + 1), by grind,
           by grind, by positivity, by push_cast; exact erdos_straus_six_mod7 j⟩
  -- Step 6: n ≡ 5 mod 7
  by_cases h7_5 : n % 7 = 5
  · obtain ⟨j, hj⟩ : ∃ j, n = 7 * j + 5 := ⟨n / 7, by grind⟩
    rw [hj]
    exact ⟨2 * (j + 1), 2 * (7 * j + 5), (7 * j + 5) * (j + 1), by grind,
           by grind, by positivity, by push_cast; exact erdos_straus_five_mod7 j⟩
  -- Step 7: n ≡ 3 mod 7
  by_cases h7_3 : n % 7 = 3
  · obtain ⟨j, hj⟩ : ∃ j, n = 7 * j + 3 := ⟨n / 7, by grind⟩
    subst hj
    exact_mod_cast erdos_straus_three_mod7 j
  -- Step 8: n ≡ 0 mod 5
  by_cases h5 : n % 5 = 0
  · obtain ⟨m, hm⟩ : ∃ m, n = 5 * m := ⟨n / 5, by grind⟩
    have hm_pos : 0 < m := by grind
    rw [hm]
    exact ⟨2 * m, 5 * m, 10 * m, by grind, by grind, by grind, by
      push_cast; exact erdos_straus_zero_mod5 m hm_pos⟩
  -- Now: n ≡ 1 mod 4, n ≡ 1 mod 3, n % 7 ∈ {1,2,4}, n % 5 ∈ {1,2,3,4}
  -- n % 840 ∈ {193, 337, 457, 673, 697, 793} (the 6 hard residues)
  have hr := hard_residue_cases n h8_1 h3_1 h7 h7_3 h7_5 h7_6 h5
               h1 h121 h169 h289 h361 h529
  obtain ⟨k, hk⟩ : ∃ k, n = 840 * k + n % 840 := ⟨n / 840, by grind⟩
  rcases hr with h193 | h337 | h457 | h673 | h697 | h793
  · rw [h193] at hk; subst hk; exact_mod_cast erdos_straus_193_mod840 k
  · rw [h337] at hk; subst hk; exact_mod_cast erdos_straus_337_mod840 k
  · rw [h457] at hk; subst hk; exact_mod_cast erdos_straus_457_mod840 k
  · rw [h673] at hk; subst hk; exact_mod_cast erdos_straus_673_mod840 k
  · rw [h697] at hk; subst hk; exact_mod_cast erdos_straus_697_mod840 k
  · rw [h793] at hk; subst hk; exact_mod_cast erdos_straus_793_mod840 k

end ErdosStraus
