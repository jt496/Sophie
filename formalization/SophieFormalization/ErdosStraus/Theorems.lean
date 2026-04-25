/-
  SophieFormalization.ErdosStraus.Theorems
  Verified cases of the Erdős–Straus conjecture: 4/n = 1/x + 1/y + 1/z
  has a positive integer solution for every n ≥ 2.

  Proved here (Sophie session 20260421, rounds 1–33):
    • Even n          (FA-6AA92B / PA-C5E101)
    • n ≡ 3 mod 4     (FA-6AA92B / PA-C5E101)
    • n ≡ 5 mod 12    (FA-6AA92B / SP-34E0FD, PA-25D02A)
    • n ≡ 9 mod 12    (FA-A4DCFE / PA-EF2F96)
    • n ≡ 1 mod 12, k=0 anchor (PA-A1849C)
    • n ≡ 1 mod 12, k=1 anchor (PA-8F3E37)

  Still open: unconditional proof for n ≡ 1 mod 12.
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

/-- Existential form (PA-25D02A): for every n ≡ 5 mod 12, there exist positive integers
    x, y, z with 4/n = 1/x + 1/y + 1/z.
    Witness: x = n, y = (n+1)/3, z = n·(n+1)/3 (valid since 3 ∣ n+1 when n ≡ 2 mod 3). -/
theorem erdos_straus_of_five_mod12 (n : ℕ) (hn : 5 ≤ n) (hmod : n % 12 = 5) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  obtain ⟨k, hk⟩ : ∃ k, n = 12 * k + 5 := ⟨n / 12, by omega⟩
  subst hk
  -- x = 12k+5 = n,  y = 4k+2 = (n+1)/3,  z = (4k+2)·(12k+5) = n·(n+1)/3
  exact ⟨12 * k + 5, 4 * k + 2, (4 * k + 2) * (12 * k + 5),
         by omega, by omega, by positivity,
         by push_cast; exact erdos_straus_five_mod12 k⟩

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

/-! ## n ≡ 1 mod 12, k=1 anchor (PA-8F3E37) -/

private lemma four_dvd_k1 (n : ℕ) (h : n % 12 = 1) : 4 ∣ n + 7 := by
  grind

private lemma anchor_k1_mul4 (n : ℕ) (h : n % 12 = 1) :
    4 * ((n + 7) / 4) = n + 7 :=
  Nat.mul_div_cancel' (four_dvd_k1 n h)

/-- k=1 anchor criterion (PA-8F3E37): for n ≡ 1 mod 12, define b₁ = (n+7)/4.
    Then 4/n = 1/b₁ + 7/(n·b₁).  If p is a prime dividing m = n·b₁ with cofactor
    q = m/p satisfying q ≡ 6 mod 7, witnesses Y = (p+m)/7 and Z = m·(q+1)/7
    give 7/m = 1/Y + 1/Z, yielding a full 3-term decomposition of 4/n. -/
theorem erdos_straus_anchor_k1 (n : ℕ) (hn12 : n % 12 = 1) (hn2 : 2 ≤ n)
    (p : ℕ) (hp : p.Prime)
    (q : ℕ) (hpq : p * q = n * ((n + 7) / 4)) (hq7 : q % 7 = 6) :
    ∃ x Y Z : ℕ, 0 < x ∧ 0 < Y ∧ 0 < Z ∧
      (4 : ℚ) / n = 1 / x + 1 / Y + 1 / Z := by
  set b := (n + 7) / 4 with hb_def
  set m := n * b with hm_def
  have h4b : 4 * b = n + 7 := anchor_k1_mul4 n hn12
  have hn_pos : 0 < n := by linarith
  have hb_pos : 0 < b := by
    have : 0 < 4 * b := by linarith [h4b]
    grind
  have hm_pos : 0 < m := Nat.mul_pos hn_pos hb_pos
  have hp_pos : 0 < p := hp.pos
  have hpq' : p * q = m := hpq
  have hq_pos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq_pos
    · simp at hpq'; linarith
    · exact hq_pos
  -- Key divisibility: 7 ∣ q + 1 (from q ≡ 6 mod 7)
  have h7qp1 : 7 ∣ q + 1 := by
    have : (q + 1) % 7 = 0 := by omega
    exact Nat.dvd_of_mod_eq_zero this
  -- p + m = p · (q + 1), so 7 ∣ p + m
  have hpm_eq : p + m = p * (q + 1) := by
    have h : p * (q + 1) = p * q + p := by ring
    linarith [hpq', h]
  have h7pm : 7 ∣ p + m := by
    rw [hpm_eq]; exact dvd_mul_of_dvd_right h7qp1 p
  -- Witnesses: x = b, Y = (p + m) / 7, Z = m * ((q + 1) / 7)
  refine ⟨b, (p + m) / 7, m * ((q + 1) / 7), hb_pos, ?_, ?_, ?_⟩
  · -- 0 < Y: p + m is a positive multiple of 7, so ≥ 7
    exact Nat.div_pos (Nat.le_of_dvd (Nat.add_pos_left hp_pos m) h7pm) (by norm_num)
  · -- 0 < Z: m · ((q+1)/7) with q+1 ≥ 7
    exact Nat.mul_pos hm_pos
      (Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos q) h7qp1) (by norm_num))
  · -- Rational identity: 4/n = 1/b + 1/Y + 1/Z
    have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast hn_pos.ne'
    have hb_ne : (b : ℚ) ≠ 0 := by exact_mod_cast hb_pos.ne'
    have hm_ne : (m : ℚ) ≠ 0 := by exact_mod_cast hm_pos.ne'
    have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp_pos.ne'
    have hq_ne : (q : ℚ) ≠ 0 := by exact_mod_cast hq_pos.ne'
    have h4bQ : 4 * (b : ℚ) = (n : ℚ) + 7 := by exact_mod_cast h4b
    have hpqQ : (p : ℚ) * q = m := by exact_mod_cast hpq'
    have h7pmQ : 7 * ((p + m) / 7 : ℕ) = p + m :=
      by exact_mod_cast Nat.mul_div_cancel' h7pm
    have h7qp1Q : 7 * ((q + 1) / 7 : ℕ) = q + 1 :=
      by exact_mod_cast Nat.mul_div_cancel' h7qp1
    have hY_pos : 0 < (p + m) / 7 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.add_pos_left hp_pos m) h7pm) (by norm_num)
    have hQdiv_pos : 0 < (q + 1) / 7 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos q) h7qp1) (by norm_num)
    have hY_ne : ((p + m) / 7 : ℕ) ≠ 0 := hY_pos.ne'
    have hQdiv_ne : ((q + 1) / 7 : ℕ) ≠ 0 := hQdiv_pos.ne'
    have hZ_ne : m * ((q + 1) / 7 : ℕ) ≠ 0 :=
      Nat.mul_ne_zero (by exact_mod_cast hm_pos.ne') hQdiv_ne
    have hYQ : 7 * ((p + m) / 7 : ℚ) = (p : ℚ) + m := by exact_mod_cast h7pmQ
    have hZdivQ : 7 * (((q + 1) / 7 : ℕ) : ℚ) = (q : ℚ) + 1 := by exact_mod_cast h7qp1Q
    rw [Nat.cast_mul]
    field_simp
    have hYQ' : ((↑((p + m) / 7) : ℚ)) = ((p : ℚ) + m) / 7 := by norm_cast
    have hZdivQ' : ((↑((q + 1) / 7) : ℚ)) = ((q : ℚ) + 1) / 7 := by linarith [hZdivQ]
    rw [hYQ', hZdivQ']
    field_simp; grind

end ErdosStraus


-- Appended by Formalizer round 35 (PA-C38ABE)

namespace ErdosStraus

/-! ## n ≡ 1 mod 12, unified anchor mechanism (PA-C38ABE) -/

/-- Unified anchor identity: for n ≡ 1 mod 12 and any k ≥ 0,
    with b_k = (n+3)/4 + k and p_k = 3 + 4·k,
    4/n = 1/b_k + p_k/(n·b_k). -/
theorem erdos_straus_anchor_identity (n k : ℕ) (hn12 : n % 12 = 1) (hn2 : 2 ≤ n) :
    (4 : ℚ) / n = 1 / ((n + 3) / 4 + k : ℕ) + (3 + 4 * k : ℕ) / (↑n * ((n + 3) / 4 + k : ℕ)) := by
  set b : ℕ := (n + 3) / 4 + k
  set pk : ℕ := 3 + 4 * k
  have hn_pos : 0 < n := by linarith
  have hb_base : 4 * ((n + 3) / 4) = n + 3 := anchor_mul4 n hn12
  have h4b : 4 * b = n + pk := by
    simp only [b, pk]
    have : 4 * ((n + 3) / 4 + k) = 4 * ((n + 3) / 4) + 4 * k := by ring
    linarith
  have hb_pos : 0 < b := by simp only [b]; linarith [hb_base]
  have hn_ne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
  have hb_ne : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb_pos.ne'
  have h4bQ : 4 * (b : ℚ) = (n : ℚ) + (pk : ℚ) := by exact_mod_cast h4b
  field_simp
  nlinarith [mul_pos (show (0 : ℚ) < n from by exact_mod_cast hn_pos)
                     (show (0 : ℚ) < b from by exact_mod_cast hb_pos)]

/-- Anchor Mechanism Lemma (PA-C38ABE): for n ≡ 1 mod 12 and k ≥ 0,
    if d > 0 divides D_k = n·b_k and p_k = 3+4k divides d + D_k,
    then Y = (d+D_k)/p_k and Z = (D_k/d)·Y give 4/n = 1/b_k + 1/Y + 1/Z. -/
theorem erdos_straus_anchor_mechanism (n k : ℕ) (hn12 : n % 12 = 1) (hn2 : 2 ≤ n)
    (d : ℕ) (hd_pos : 0 < d)
    (hd_dvd : d ∣ n * ((n + 3) / 4 + k))
    (hp_dvd : (3 + 4 * k) ∣ d + n * ((n + 3) / 4 + k)) :
    ∃ x Y Z : ℕ, 0 < x ∧ 0 < Y ∧ 0 < Z ∧
      (4 : ℚ) / n = 1 / x + 1 / Y + 1 / Z := by
  set b : ℕ := (n + 3) / 4 + k
  set pk : ℕ := 3 + 4 * k
  set D : ℕ := n * b
  have hb_base : 4 * ((n + 3) / 4) = n + 3 := anchor_mul4 n hn12
  have h4b : 4 * b = n + pk := by
    simp only [b, pk]
    have : 4 * ((n + 3) / 4 + k) = 4 * ((n + 3) / 4) + 4 * k := by ring
    linarith
  have hn_pos : 0 < n := by linarith
  have hb_pos : 0 < b := by simp only [b]; linarith [hb_base]
  have hD_pos : 0 < D := Nat.mul_pos hn_pos hb_pos
  have hpk_pos : 0 < pk := by simp [pk];
  have hpk_dvd : pk ∣ d + D := hp_dvd
  obtain ⟨q, hq⟩ := hd_dvd
  have hDq : d * q = D := hq.symm
  have hq_pos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | hqp
    · simp at hq; linarith [hD_pos]
    · exact hqp
  have hY_pos : 0 < (d + D) / pk :=
    Nat.div_pos (Nat.le_of_dvd (Nat.add_pos_left hd_pos D) hpk_dvd) (by simp [pk])
  have hpk_Y : pk * ((d + D) / pk) = d + D := Nat.mul_div_cancel' hpk_dvd
  refine ⟨b, (d + D) / pk, q * ((d + D) / pk), hb_pos, hY_pos, Nat.mul_pos hq_pos hY_pos, ?_⟩
  have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  have hb_ne : (b : ℚ) ≠ 0 := by exact_mod_cast hb_pos.ne'
  have hpk_ne : (pk : ℚ) ≠ 0 := by exact_mod_cast hpk_pos.ne'
  have hq_ne : (q : ℚ) ≠ 0 := by exact_mod_cast hq_pos.ne'
  have h4bQ : 4 * (b : ℚ) = (n : ℚ) + pk := by exact_mod_cast h4b
  have hDqQ : (d : ℚ) * q = D := by exact_mod_cast hDq
  have hpkYQ : (pk : ℚ) * ((d + D) / pk : ℕ) = d + D := by exact_mod_cast hpk_Y
  have hY_ne : ((d + D) / pk : ℕ) ≠ 0 := hY_pos.ne'
  have hYQ' : ((↑((d + D) / pk) : ℚ)) = ((d : ℚ) + D) / pk := by
    have := hpkYQ; field_simp at this ⊢; linarith
  rw [Nat.cast_mul, hYQ']
  field_simp
  grind

end ErdosStraus


-- Appended by Formalizer round 37 (PA-3F943E)

namespace ErdosStraus

/-! ## n ≡ 1 mod 12: closed-form identity via p | n+4 (PA-3F943E / SP-DAEE25) -/

private lemma four_dvd_np_of_mod' (n p : ℕ) (hn : n % 4 = 1) (hp : p % 4 = 3) :
    4 ∣ n + p := by omega

private lemma four_dvd_qp1_of_mod' (q : ℕ) (hq : q % 4 = 3) : 4 ∣ q + 1 := by
  omega

/-- Closed-form EF identity (PA-3F943E / SP-DAEE25): for n ≡ 1 mod 12, n ≥ 13,
    p prime with p ≡ 3 mod 4 and p ∣ n+4, q = (n+4)/p ≡ 3 mod 4:
      4/n = 1/b + 1/(n·m) + 1/(n·m·b)
    where b = (n+p)/4 and m = (q+1)/4. -/
theorem erdos_straus_pn4_identity (n p : ℕ)
    (hn12 : n % 12 = 1) (hn13 : 13 ≤ n)
    (hp : p.Prime) (hp4 : p % 4 = 3)
    (hpdvd : p ∣ n + 4)
    (hq4 : ((n + 4) / p) % 4 = 3) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  set q  := (n + 4) / p with hq_def
  set b  := (n + p) / 4 with hb_def
  set m  := (q + 1) / 4 with hm_def
  have hn4    : n % 4 = 1     := by omega
  have hn_pos : 0 < n         := by omega
  have hp_pos : 0 < p         := hp.pos
  have hpq    : p * q = n + 4 := Nat.mul_div_cancel' hpdvd
  have hq_pos : 0 < q         := by
    rcases Nat.eq_zero_or_pos q with hpos
    · simp at hpq; omega
  have h4np   : 4 ∣ n + p     := four_dvd_np_of_mod' n p hn4 hp4
  have h4b    : 4 * b = n + p := Nat.mul_div_cancel' h4np
  have hb_pos : 0 < b         := by
    have h : 0 < 4 * b := by linarith [h4b, hp_pos, hn13]
    omega
  have h4qp1  : 4 ∣ q + 1     := four_dvd_qp1_of_mod' q hq4
  have h4m    : 4 * m = q + 1 := Nat.mul_div_cancel' h4qp1
  have hm_pos : 0 < m         := by
    have h : 0 < 4 * m := by linarith [h4m, hq_pos]
    omega
  -- b + 1 = p * m  (key algebraic step)
  have hbp1  : b + 1 = p * m := by
    have hpm4  : 4 * (p * m) = n + p + 4 := by nlinarith [h4m, hpq]
    have h4bp4 : 4 * (b + 1)  = n + p + 4 := by linarith [h4b]
    omega
  refine ⟨b, n * m, n * m * b, hb_pos, Nat.mul_pos hn_pos hm_pos,
          Nat.mul_pos (Nat.mul_pos hn_pos hm_pos) hb_pos, ?_⟩
  have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  have hb_ne : (b : ℚ) ≠ 0 := by exact_mod_cast hb_pos.ne'
  have hm_ne : (m : ℚ) ≠ 0 := by exact_mod_cast hm_pos.ne'
  have h4bQ  : 4 * (b : ℚ) = (n : ℚ) + (p : ℚ) := by exact_mod_cast h4b
  have hbp1Q : (b : ℚ) + 1 = (p : ℚ) * (m : ℚ) := by exact_mod_cast hbp1
  have hpqQ  : (p : ℚ) * (q : ℚ) = (n : ℚ) + 4  := by exact_mod_cast hpq
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
  field_simp
  nlinarith [mul_pos (show (0:ℚ) < n from by exact_mod_cast hn_pos)
                     (show (0:ℚ) < b from by exact_mod_cast hb_pos),
             mul_pos (show (0:ℚ) < n from by exact_mod_cast hn_pos)
                     (show (0:ℚ) < m from by exact_mod_cast hm_pos),
             mul_comm (p : ℚ) (m : ℚ)]

#check erdos_straus_anchor_mechanism
#check  erdos_straus_pn4_identity

end ErdosStraus

-- Appended by Formalizer round 41 (PA-C85CD9)

namespace ErdosStraus

/-! ## n ≡ 1 mod 12: n+4 Criterion (PA-C85CD9) -/

/-- Helper: if q · s = n + 4 with q ≡ 3 (mod 4) and n ≡ 1 (mod 4), then s ≡ 3 (mod 4). -/
private lemma s_mod4_of_mul_eq (q s n : ℕ) (hq : q % 4 = 3) (hn : n % 4 = 1)
    (hqs : q * s = n + 4) : s % 4 = 3 := by
  have h1 : (q * s) % 4 = 1 := by rw [hqs]; omega
  have h2 : q % 4 * (s % 4) % 4 = 1 := by
    have hmm := Nat.mul_mod q s 4
    omega
  rw [hq] at h2
  -- h2 : 3 * (s % 4) % 4 = 1
  have h3 : s % 4 < 4 := Nat.mod_lt s (by norm_num)
  omega

/-- **n+4 Criterion** (PA-C85CD9): for n ≡ 1 (mod 12) with n ≥ 13, if q is a
    prime factor of n+4 with q ≡ 3 (mod 4), let s = (n+4)/q, xn = (n+q)/4,
    t = (s+1)/4. Then xn, n·t, xn·(n·t) are positive integers satisfying
      4/n = 1/xn + 1/(n·t) + 1/(xn·n·t).

    Equivalently, the witnesses x = (n+q)/4, y = n·(s+1)/4, z = n·(n+q)·(s+1)/16
    give 4/n = 1/x + 1/y + 1/z. -/
theorem erdos_straus_n4_criterion (n q : ℕ)
    (hn12 : n % 12 = 1) (hn13 : 13 ≤ n)
    (hq4 : q % 4 = 3)
    (hqdvd : q ∣ n + 4) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  have hn4 : n % 4 = 1 := by omega
  -- Natural number building blocks
  set s  : ℕ := (n + 4) / q  with hs_def
  set xn : ℕ := (n + q) / 4  with hxn_def
  set t  : ℕ := (s + 1) / 4  with ht_def
  -- Key division identities
  have hqs   : q  * s  = n + 4 := Nat.mul_div_cancel' hqdvd
  have h4nq  : 4 ∣ n + q       := by omega
  have h4xn  : 4  * xn = n + q := Nat.mul_div_cancel' h4nq
  have hs4   : s % 4 = 3        := s_mod4_of_mul_eq q s n hq4 hn4 hqs
  have h4sp1 : 4 ∣ s + 1       := by omega
  have h4t   : 4  * t  = s + 1 := Nat.mul_div_cancel' h4sp1
  -- Positivity
  have hn_pos  : 0 < n  := by omega
  have hs_pos  : 0 < s  := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · exfalso; rw [hs, mul_zero] at hqs; omega
    · exact hs
  have hxn_pos : 0 < xn := by
    have : 0 < 4 * xn := by linarith [h4xn,  hn13]
    omega
  have ht_pos  : 0 < t  := by
    have : 0 < 4 * t  := by linarith [h4t, hs_pos]
    omega
  -- Witnesses: x = xn, y = n * t, z = xn * (n * t)
  refine ⟨xn, n * t, xn * (n * t),
          hxn_pos,
          Nat.mul_pos hn_pos ht_pos,
          Nat.mul_pos hxn_pos (Nat.mul_pos hn_pos ht_pos),
          ?_⟩
  -- Rational identity: 4/n = 1/xn + 1/(n·t) + 1/(xn·n·t)
  -- After clearing denominators (multiplying by xn·n·t), this reduces to:
  --   4 · xn · t = n · t + xn + 1
  -- which is a linear combination of the three ℚ equations below.
  have hn_ne  : (n  : ℚ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  have hxn_ne : (xn : ℚ) ≠ 0 := by exact_mod_cast hxn_pos.ne'
  have ht_ne  : (t  : ℚ) ≠ 0 := by exact_mod_cast ht_pos.ne'
  -- Key ℚ equations (cast from ℕ)
  have h4xnQ : 4 * (xn : ℚ) = ↑n + ↑q := by exact_mod_cast h4xn
  have h4tQ  : 4 * (t  : ℚ) = ↑s + 1  := by exact_mod_cast h4t
  have hqsQ  : (q  : ℚ) * ↑s = ↑n + 4  := by exact_mod_cast hqs
  -- Clear casts and denominators, then close by linear combination
  push_cast
  field_simp [hn_ne, hxn_ne, ht_ne,
              mul_ne_zero hn_ne ht_ne,
              mul_ne_zero hxn_ne (mul_ne_zero hn_ne ht_ne)]
  -- After field_simp the goal is: 4 * xn * t = n * t + xn + 1
  -- Proof: (t - 1/4)·(4xn - n - q) + (q/4)·(4t - s - 1) + (1/4)·(qs - n - 4) = 4xt - nt - xn - 1
  linear_combination ((t : ℚ) - 1 / 4) * h4xnQ + (q : ℚ) / 4 * h4tQ +
                     (1 : ℚ) / 4 * hqsQ

#check erdos_straus_n4_criterion

end ErdosStraus
