import Mathlib

def triangular (n : Nat) : Nat := n * (n + 1) / 2

lemma eight_mul_triangular_add_one (n : Nat) : 8 * triangular n + 1 = (2 * n + 1) ^ 2 := by
  unfold triangular;
  have h : 2 * (n * (n + 1) / 2) = n * (n + 1) := sorry
  sorry

theorem sum_two_triangular_iff_four_mul_add_one_sum_sq (m : Nat) :
  (exists a b : Nat, m = triangular a + triangular b) ↔ (exists X Y : Int, 4 * m + 1 = X ^ 2 + Y ^ 2) := by
  constructor
  · rintro ⟨a, b, rfl⟩; use (a + b + 1), (a - b : Int)
    unfold triangular; zify; ring; sorry
  · rintro ⟨X, Y, h⟩; have h1 : (X^2 + Y^2) % 4 = 1 := by rw [← h]; norm_num
    have h2 : (X % 2 = 1 ∧ Y % 2 = 0) ∨ (X % 2 = 0 ∧ Y % 2 = 1) := by
      revert h1; generalize X^2 % 4 = x2; generalize Y^2 % 4 = y2; intro h;
      have qX := Int.sq_mod_four X;
      have qY := Int.sq_mod_four Y;
      revert h qX qY; generalize X % 2 = x; generalize Y % 2 = y; intro h qX qY;
      interval_cases x2 <;> interval_cases y2 <;> simp at h qX qY
      · apply Int.odd_iff_not_even.mp; rw [Int.even_iff_mod_two_eq_zero, ← Int.sq_mod_four, qX]; norm_num
      · apply Int.even_iff_mod_two_eq_zero.mp; rw [← Int.sq_mod_four, qX]; norm_num
    wlog h_p : X % 2 = 1 ∧ Y % 2 = 0
    · cases h2 with | h1 => exact this m X Y h h1 (by assumption) | h2 => rw [add_comm] at h; exact this m Y X h h2 (by assumption)
    let S := X + Y; let D := X - Y;
    have hS : S % 2 = 1 := by dsimp [S]; rw [Int.add_mod, h_p.1, h_p.2]; norm_num
    have hD : D % 2 = 1 := by dsimp [D]; rw [Int.sub_mod, h_p.1, h_p.2]; norm_num
    use (S.natAbs - 1) / 2, (D.natAbs - 1) / 2
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 8); rw [Nat.left_distrib]
    repeat rw [eight_mul_triangular_add_one]; zify
    have hA (K : Int) (hk : K % 2 = 1) : (2 * ((K.natAbs - 1) / 2) + 1 : Int) ^ 2 = K ^ 2 := by
      have : K.natAbs % 2 = 1 := by rw [← Int.natAbs_mod_two, hk]; norm_num
      have : 2 * ((K.natAbs - 1) / 2) + 1 = K.natAbs := by rw [Nat.div_mul_cancel (Nat.dvd_sub_mod this)]; simp
      zify [this]; exact Int.natAbs_sq K
    rw [hA S hS, hA D hD, ← h]; ring
