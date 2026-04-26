import Mathlib

def triangular (n : Nat) : Nat := n * (n + 1) / 2

lemma eight_mul_triangular_add_one (n : Nat) : 8 * triangular n + 1 = (2 * n + 1) ^ 2 := by
  unfold triangular;
  have h : 2 * (n * (n + 1) / 2) = n * (n + 1) := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  nlinarith [h]

theorem sum_two_triangular_iff_four_mul_add_one_sum_sq (m : Nat) :
  (exists a b : Nat, m = triangular a + triangular b) ↔ (exists X Y : Int, 4 * m + 1 = X ^ 2 + Y ^ 2) := by
  constructor
  · rintro ⟨a, b, rfl⟩; use (a + b + 1), (a - b : Int)
    have ha := eight_mul_triangular_add_one a; have hb := eight_mul_triangular_add_one b; zify at ha hb ⊢; nlinarith [ha, hb]
  · rintro ⟨X, Y, h⟩; have h1 : (X^2 + Y^2) % 4 = 1 := by rw [← h]; norm_num
    have h2 : (X % 2 = 1 ∧ Y % 2 = 0) ∨ (X % 2 = 0 ∧ Y % 2 = 1) := by
      rcases Int.even_or_odd X with ⟨a, ha⟩ | ⟨a, ha⟩ <;> rcases Int.even_or_odd Y with ⟨b, hb⟩ | ⟨b, hb⟩ <;>
        simp only [ha, hb] at h1 ⊢ <;> ring_nf at h1 ⊢ <;> omega
    wlog h_p : X % 2 = 1 ∧ Y % 2 = 0
    · cases h2 with
      | inl h_inl => exact absurd h_inl h_p
      | inr h_inr => exact this m Y X (by linarith) (by rwa [add_comm]) (Or.inl ⟨h_inr.2, h_inr.1⟩) ⟨h_inr.2, h_inr.1⟩
    let S := X + Y; let D := X - Y;
    have hS : S % 2 = 1 := by dsimp [S]; rw [Int.add_emod, h_p.1, h_p.2]; norm_num
    have hD : D % 2 = 1 := by dsimp [D]; rw [Int.sub_emod, h_p.1, h_p.2]; norm_num
    use (S.natAbs - 1) / 2, (D.natAbs - 1) / 2
    have hA (K : Int) (hk : K % 2 = 1) : (2 * ((K.natAbs - 1) / 2) + 1 : Int) ^ 2 = K ^ 2 := by
      have h1 : K.natAbs % 2 = 1 := by omega
      have h2 : 2 * ((K.natAbs - 1) / 2) + 1 = K.natAbs := by omega
      have h2' : (2 * ((K.natAbs - 1) / 2) + 1 : Int) = ↑K.natAbs := by grind
      rw [h2']; exact Int.natAbs_sq K
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 8)
    have ha8 := eight_mul_triangular_add_one ((S.natAbs - 1) / 2)
    have hb8 := eight_mul_triangular_add_one ((D.natAbs - 1) / 2)
    have hAS := hA S hS; have hAD := hA D hD
    dsimp only [S, D] at hAS hAD
    zify at ha8 hb8 ⊢
    apply (add_left_inj 2).1
    have hsa : ((S).natAbs : ℤ) - 1 = (((S).natAbs - 1:ℕ) : ℤ) := by
      refine Eq.symm (Nat.cast_pred (by refine Int.natAbs_pos.mpr (by grind)))
    have hda : ((D).natAbs : ℤ) - 1 = (((D).natAbs - 1:ℕ) : ℤ) := by
      refine Eq.symm (Nat.cast_pred (by refine Int.natAbs_pos.mpr (by grind)))
    calc
      _ = 4 * (m : ℤ)  + 1 + 4 *m + 1 := by ring
      _ = _ := by
        rw  [← @one_add_one_eq_two ℤ, mul_comm _ 8, mul_add, add_assoc, add_assoc, add_assoc, add_comm _ (1 + 1),
        ←add_assoc, add_assoc 1, add_comm 1, ← add_assoc,← add_assoc, ←add_assoc, ha8,add_assoc, add_assoc, add_assoc, hb8,
        ←add_assoc,h]
        dsimp [S, D]
        rw [← hsa, ←  hda, hAS, hAD]
        ring
