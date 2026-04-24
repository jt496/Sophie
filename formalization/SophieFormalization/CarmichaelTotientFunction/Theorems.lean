import Mathlib

/-!
## Carmichael's Totient Conjecture — Partial Formalization

Carmichael's conjecture: for every positive integer n, there exists m ≠ n
with φ(m) = φ(n) (no value of Euler's totient function is achieved exactly once).

This file formalizes the partial results from the Sophie exploration sessions:
- Case 1: the conjecture holds for all odd n (PA-D3C692, Round 1)
- Case 2: the conjecture holds for all n ≡ 2 (mod 4) (PA-D3C692, Round 1)
- Case 3: the conjecture holds for all pure powers of 2 (PA-D3C692, Round 1)
- Key Lemma: φ(3k) = φ(4k) for odd k with 3 ∤ k (PA-2793CB, Round 2)
- SP-5BC5F6: the conjecture holds for all n = 4p, p prime (Round 2)
-/

namespace Carmichael

open Nat

/-- The full Carmichael totient conjecture (open problem). -/
def CarmichaelConjecture : Prop :=
  ∀ n : ℕ, 0 < n → ∃ m : ℕ, m ≠ n ∧ m.totient = n.totient

/-! ### Case 1: n is odd (PA-D3C692) -/

/-- For odd n > 0, φ(2n) = φ(n) and 2n ≠ n, witnessing the conjecture. -/
theorem carmichael_of_odd (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) :
    ∃ m : ℕ, m ≠ n ∧ m.totient = n.totient :=
  ⟨2 * n, by omega, Nat.totient_two_mul_of_odd hn⟩

/-! ### Case 2: n ≡ 2 (mod 4) (PA-D3C692) -/

/-- For n = 2m with m odd, φ(2m) = φ(m) and m ≠ 2m, witnessing the conjecture. -/
theorem carmichael_of_two_mul_odd (m : ℕ) (hm : Odd m) (hm_pos : 0 < m) :
    ∃ k : ℕ, k ≠ 2 * m ∧ k.totient = (2 * m).totient :=
  ⟨m, by omega, (Nat.totient_two_mul_of_odd hm).symm⟩

/-! ### Key Lemma (PA-2793CB, Round 2) -/

private lemma totient_four_mul_of_odd {k : ℕ} (hk : Odd k) :
    (4 * k).totient = 2 * k.totient := by
  have heq : 4 * k = 2 * (2 * k) := by ring
  rw [heq, Nat.totient_two_mul_of_even ⟨k, by ring⟩, Nat.totient_two_mul_of_odd hk]

private lemma totient_three_mul_of_not_dvd {k : ℕ} (hk : ¬ 3 ∣ k) :
    (3 * k).totient = 2 * k.totient := by
  have h3 : Nat.Prime 3 := by norm_num
  rw [Nat.totient_mul_of_prime_of_not_dvd h3 hk]

/-- Key Lemma: for odd k with 3 ∤ k, φ(3k) = φ(4k) = 2·φ(k). -/
theorem key_lemma (k : ℕ) (hk_odd : Odd k) (hk_3 : ¬ 3 ∣ k) :
    (3 * k).totient = (4 * k).totient :=
  (totient_three_mul_of_not_dvd hk_3).trans (totient_four_mul_of_odd hk_odd).symm

/-- Corollary: if n = 4k with k odd and 3 ∤ k, the conjecture holds for n. -/
theorem carmichael_of_four_mul_coprime3 (k : ℕ) (hk_odd : Odd k) (hk_3 : ¬ 3 ∣ k)
    (hk_pos : 0 < k) :
    ∃ m : ℕ, m ≠ 4 * k ∧ m.totient = (4 * k).totient :=
  ⟨3 * k, by omega, key_lemma k hk_odd hk_3⟩

/-! ### Case 3: n is a power of 2, n ≥ 4 (PA-D3C692) -/

/-- For n = 2^(a+2), the pair n' = 3·2^(a+1) satisfies φ(n') = φ(n). -/
theorem carmichael_of_pow_two (a : ℕ) :
    ∃ m : ℕ, m ≠ 2 ^ (a + 2) ∧ m.totient = (2 ^ (a + 2)).totient := by
  refine ⟨3 * 2 ^ (a + 1), ?_, ?_⟩
  · -- 3 · 2^(a+1) ≠ 2^(a+2) = 2 · 2^(a+1)
    have hpos : 0 < 2 ^ (a + 1) := by positivity
    have h : (2 : ℕ) ^ (a + 2) = 2 * 2 ^ (a + 1) := by ring
    omega
  · -- φ(3 · 2^(a+1)) = φ(3) · φ(2^(a+1)) = 2 · 2^a = 2^(a+1) = φ(2^(a+2))
    have hcop : Nat.Coprime 3 (2 ^ (a + 1)) :=
      (show Nat.Coprime 3 2 from by decide).pow_right _
    have h2 : Nat.Prime 2 := by norm_num
    rw [Nat.totient_mul hcop,
        show (3 : ℕ).totient = 2 from by decide,
        Nat.totient_prime_pow_succ h2 a,
        Nat.totient_prime_pow_succ h2 (a + 1),
        show (2 : ℕ) - 1 = 1 from by norm_num, mul_one]
    ring

/-! ### SP-5BC5F6 (Round 2): conjecture holds for n = 4p, p prime -/

/-- For any prime p, φ(4p) has a second preimage:
    - p = 2: φ(8) = 4 = φ(5)
    - p = 3: φ(12) = 4 = φ(5)
    - p odd prime ≠ 3: φ(3p) = φ(4p) by the Key Lemma -/
theorem carmichael_of_four_prime (p : ℕ) (hp : Nat.Prime p) :
    ∃ m : ℕ, m ≠ 4 * p ∧ m.totient = (4 * p).totient := by
  by_cases h2 : p = 2
  · subst h2; exact ⟨5, by norm_num, by decide⟩
  · by_cases h3 : p = 3
    · subst h3; exact ⟨5, by norm_num, by decide⟩
    · -- p is an odd prime with 3 ∤ p; apply Key Lemma with k = p
      have hp_odd : Odd p := (Nat.even_or_odd p).resolve_left (by
        rintro ⟨k, hk⟩
        have hdvd : 2 ∣ p := ⟨k, by omega⟩
        exact h2 ((hp.eq_one_or_self_of_dvd 2 hdvd).resolve_left (by norm_num)).symm)
      have hp3 : ¬ 3 ∣ p := by
        intro hdvd
        rcases hp.eq_one_or_self_of_dvd 3 hdvd with h | h
        · norm_num at h
        · exact h3 h.symm
      exact ⟨3 * p, by omega, key_lemma p hp_odd hp3⟩

/-! ### Hard residual case (open) -/

/-- The remaining open case: n = 2^a · m with a ≥ 2 and m > 1 odd.
    No uniform construction is known; this is the core of the open conjecture. -/
theorem carmichael_hard_case (n : ℕ) (hn_pos : 0 < n)
    (ha : ∃ a k : ℕ, 2 ≤ a ∧ 1 < k ∧ Odd k ∧ n = 2 ^ a * k) :
    ∃ m : ℕ, m ≠ n ∧ m.totient = n.totient := by
  sorry -- Open: the genuinely hard residual case of Carmichael's conjecture

end Carmichael
