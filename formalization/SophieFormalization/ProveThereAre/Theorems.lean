import Mathlib

/-!
# Infinitely many integer solutions to 4m² + m = 5n² + n

We prove that the Diophantine equation `4m² + m = 5n² + n` has infinitely many
integer solutions, by constructing an explicit infinite parametric family.

## Strategy

The substitution `p = 8m + 1`, `q = 10n + 1` transforms the equation into
`5p² - 4q² = 1`, equivalently the negative Pell equation `X² - 5Y² = -1`
via `X = 2q`, `Y = p`.

The Pell recurrence `(X_{k+1}, Y_{k+1}) = (9X_k + 20Y_k, 4X_k + 9Y_k)`
starting from `(X_0, Y_0) = (2, 1)` generates all solutions.  The even-indexed
terms satisfy `X_k ≡ 2 (mod 20)` and `Y_k ≡ 1 (mod 8)` (period-2 behaviour),
yielding the integer solution `m = (Y_k - 1)/8`, `n = (X_k/2 - 1)/10`.
Since `Y_k` is strictly increasing, the map `k ↦ (m_k, n_k)` is injective,
giving infinitely many distinct solutions.
-/

namespace PellQuadratic

/-- The Pell sequence satisfying `X² - 5Y² = -1`, with recurrence from `(9,4)`. -/
def pell : ℕ → ℤ × ℤ
  | 0 => (2, 1)
  | n + 1 => let (x, y) := pell n; (9 * x + 20 * y, 4 * x + 9 * y)

lemma pell_eq (n : ℕ) : (pell n).1 ^ 2 - 5 * (pell n).2 ^ 2 = -1 := by
  induction n with
  | zero => simp [pell]
  | succ n ih => simp only [pell]; ring_nf; linarith [ih]

lemma pell_pos (n : ℕ) : 0 < (pell n).1 ∧ 0 < (pell n).2 := by
  induction n with
  | zero => simp [pell]
  | succ n ih => simp only [pell]; constructor <;> linarith [ih.1, ih.2]

lemma pell_snd_strictMono : StrictMono (fun n => (pell n).2) :=
  strictMono_nat_of_lt_succ fun n => by
    simp only [pell]; linarith [(pell_pos n).1, (pell_pos n).2]

/-- Even-indexed Pell terms satisfy `X ≡ 2 (mod 20)` and `Y ≡ 1 (mod 8)`. -/
lemma pell_even_mod (n : ℕ) :
    (pell (2 * n)).1 % 20 = 2 ∧ (pell (2 * n)).2 % 8 = 1 := by
  induction n with
  | zero => simp [pell]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring]
    simp only [pell]; obtain ⟨hx, hy⟩ := ih; constructor <;> omega

private lemma div8_strictMono {x y : ℤ} (hx : x % 8 = 1) (hy : y % 8 = 1) (hlt : x < y) :
    (x - 1) / 8 < (y - 1) / 8 := by
  obtain ⟨a, ha⟩ : (8 : ℤ) ∣ x - 1 := Int.dvd_of_emod_eq_zero (by omega)
  obtain ⟨b, hb⟩ : (8 : ℤ) ∣ y - 1 := Int.dvd_of_emod_eq_zero (by omega)
  have hxa : x = 8 * a + 1 := by linarith
  have hyb : y = 8 * b + 1 := by linarith
  rw [show (x - 1) / 8 = a from by rw [hxa]; omega,
      show (y - 1) / 8 = b from by rw [hyb]; omega]
  linarith

/-- The parametric solution family: m-component. -/
def solM (k : ℕ) : ℤ := ((pell (2 * k)).2 - 1) / 8

/-- The parametric solution family: n-component. -/
def solN (k : ℕ) : ℤ := ((pell (2 * k)).1 / 2 - 1) / 10

lemma sol_is_solution (k : ℕ) : 4 * solM k ^ 2 + solM k = 5 * solN k ^ 2 + solN k := by
  unfold solM solN
  obtain ⟨hx, hy⟩ := pell_even_mod k
  obtain ⟨a, ha⟩ : (8 : ℤ) ∣ (pell (2 * k)).2 - 1 := Int.dvd_of_emod_eq_zero (by omega)
  obtain ⟨b, hb⟩ : (20 : ℤ) ∣ (pell (2 * k)).1 - 2 := Int.dvd_of_emod_eq_zero (by omega)
  have hY : (pell (2 * k)).2 = 8 * a + 1 := by linarith
  have hX : (pell (2 * k)).1 = 20 * b + 2 := by linarith
  have hX2 : (pell (2 * k)).1 / 2 = 10 * b + 1 := by rw [hX]; omega
  rw [show ((pell (2 * k)).2 - 1) / 8 = a from by rw [hY]; omega,
      show ((pell (2 * k)).1 / 2 - 1) / 10 = b from by rw [hX2]; omega]
  have hpell := pell_eq (2 * k)
  rw [hX, hY] at hpell
  nlinarith [hpell]

lemma solM_strictMono : StrictMono solM := fun a b hab =>
  div8_strictMono (pell_even_mod a).2 (pell_even_mod b).2 (pell_snd_strictMono (by omega))

/-- The equation `4m² + m = 5n² + n` has infinitely many integer solutions. -/
theorem infinite_solutions :
    Set.Infinite {p : ℤ × ℤ | 4 * p.1 ^ 2 + p.1 = 5 * p.2 ^ 2 + p.2} := by
  apply Set.infinite_of_injective_forall_mem (f := fun k => (solM k, solN k))
  · intro a b hab
    simp only [Prod.mk.injEq] at hab
    exact solM_strictMono.injective hab.1
  · intro k
    simp only [Set.mem_setOf_eq]
    exact sol_is_solution k

end PellQuadratic

