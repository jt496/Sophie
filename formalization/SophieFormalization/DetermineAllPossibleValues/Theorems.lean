import Mathlib

/-!
# Values of `A³ + B³ + C³ − 3ABC` over the nonnegative integers

This file characterises exactly which nonnegative integers arise as
`A^3 + B^3 + C^3 - 3*A*B*C` with `A, B, C` nonnegative integers.

The answer is: every natural number `n` with `n % 9 ∉ {3, 6}`, and no others.

Key tool: the symmetric factorisation
`A^3 + B^3 + C^3 - 3ABC = (A+B+C)·((A-B)² + (A-B)(B-C) + (B-C)²)`,
from which the modular obstruction `3 ∣ f → 9 ∣ f` follows.
-/

namespace DetermineAllPossibleValues

/-- For all residues `a, b, c` modulo `9`, the expression
`a³ + b³ + c³ − 3abc` is never `3` or `6` in `ZMod 9`.
This is the finite computation underlying the obstruction. -/
lemma mod9_obstruction : ∀ a b c : ZMod 9,
    a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≠ 3 ∧
    a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≠ 6 := by
  decide

/-- The cast `(n : ZMod 9)` only depends on `n % 9`. -/
lemma natCast_zmod9 (n : ℕ) : (n : ZMod 9) = ((n % 9 : ℕ) : ZMod 9) := by
  conv_lhs => rw [← Nat.div_add_mod n 9]
  push_cast
  rw [show (9 : ZMod 9) = 0 from by decide]
  ring

/-- **Characterisation of the attainable values.**
A natural number `n` is of the form `A³ + B³ + C³ − 3ABC` for nonnegative
integers `A, B, C` if and only if `n` is not congruent to `3` or `6` modulo `9`. -/
theorem cube_expr_values (n : ℕ) :
    (∃ A B C : ℕ, (A : ℤ) ^ 3 + (B : ℤ) ^ 3 + (C : ℤ) ^ 3 - 3 * A * B * C = n) ↔
      n % 9 ≠ 3 ∧ n % 9 ≠ 6 := by
  constructor
  · -- Forward: representability forces the modular obstruction.
    rintro ⟨A, B, C, h⟩
    have hkey : (A : ZMod 9) ^ 3 + (B : ZMod 9) ^ 3 + (C : ZMod 9) ^ 3
        - 3 * (A : ZMod 9) * (B : ZMod 9) * (C : ZMod 9) = (n : ZMod 9) := by
      have h2 := congrArg (fun z : ℤ => (z : ZMod 9)) h
      push_cast at h2
      linear_combination h2
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · refine (mod9_obstruction A B C).1 ?_
      rw [hkey, natCast_zmod9, hc]; decide
    · refine (mod9_obstruction A B C).2 ?_
      rw [hkey, natCast_zmod9, hc]; decide
  · -- Reverse: explicit constructions for each allowed residue class.
    rintro ⟨h3, h6⟩
    have hcase : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcase with h | h | h
    · -- n ≡ 0 (mod 3); together with the obstruction, n ≡ 0 (mod 9).
      have h9 : n % 9 = 0 := by omega
      rcases Nat.eq_zero_or_pos n with hz | hpos
      · exact ⟨0, 0, 0, by subst hz; norm_num⟩
      · obtain ⟨m, hm⟩ : ∃ m, n = 9 * (m + 1) := ⟨n / 9 - 1, by omega⟩
        exact ⟨m + 2, m + 1, m, by subst hm; push_cast; ring⟩
    · -- n ≡ 1 (mod 3): use (k+1, k, k).
      obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
      exact ⟨k + 1, k, k, by subst hk; push_cast; ring⟩
    · -- n ≡ 2 (mod 3): use (k+1, k+1, k).
      obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
      exact ⟨k + 1, k + 1, k, by subst hk; push_cast; ring⟩

end DetermineAllPossibleValues

