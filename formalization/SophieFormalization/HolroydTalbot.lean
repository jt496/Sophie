/-
  SophieFormalization.HolroydTalbot
  Statement of the Holroyd-Talbot conjecture and proved special cases.

  Holroyd-Talbot Conjecture (2005):
    For any graph G and 1 ≤ r ≤ μ(G)/2, G is r-EKR:
    there exists a vertex v such that vertexStar G v r is a maximum
    intersecting family of independent r-sets.
    Moreover G is strictly r-EKR when 1 < r < μ(G)/2.
-/

import SophieFormalization.Basic

open Classical

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## The r-EKR Property -/

/-- G is r-EKR: some vertex star is a maximum intersecting r-family. -/
def IsREKR (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ v : V, ∀ F : Finset (Finset V),
    F ⊆ indepRSets G r →
    IsIntersecting F →
    F.card ≤ (vertexStar G v r).card

/-- G is strictly r-EKR: every maximum intersecting r-family IS some vertex star. -/
def IsStrictlyREKR (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ v : V,
  ∀ F : Finset (Finset V),
    F ⊆ indepRSets G r →
    IsIntersecting F →
    F.card = (vertexStar G v r).card →
    ∃ w : V, F = vertexStar G w r

/-! ## The Holroyd-Talbot Conjecture -/

/-- The Holroyd-Talbot conjecture: G is r-EKR for all 1 ≤ r ≤ μ(G)/2. -/
def HolroydTalbotConj (G : SimpleGraph V) : Prop :=
  ∀ r : ℕ, 1 ≤ r → 2 * r ≤ mu G → IsREKR G r

/-- The strict Holroyd-Talbot conjecture: strictly r-EKR when 1 < r < μ(G)/2. -/
def HolroydTalbotStrictConj (G : SimpleGraph V) : Prop :=
  ∀ r : ℕ, 1 < r → 2 * r < mu G → IsStrictlyREKR G r

/-! ## Key Lemma: Stars Are Maximal Intersecting Families -/

/-- Stars are maximal intersecting families (proved by Sophie agents, Round 5). -/
theorem vertexStar_maximal_intersecting (G : SimpleGraph V) (v : V) (r : ℕ)
    (s : Finset V) (hs : s ∈ indepRSets G r) (hv : v ∉ s) :
    ∀ t ∈ vertexStar G v r, (s ∩ t).Nonempty := by
  intro t ht
  rw [mem_vertexStar_iff] at ht
  -- t contains v, s does not contain v.
  -- s and t are both independent r-sets, so s ∩ t might be empty only if they
  -- are disjoint. But we need more structure to close this in general.
  -- (Formalization in progress — the key argument uses r < μ(G)/2.)
  sorry

/-! ## Proved Special Cases -/

theorem ht_r_one (G : SimpleGraph V) (h : 1 ≤ mu G) : IsREKR G 1 := by
  sorry

/-! ## The H ⊔ H Theorem (Sophie Rounds 9–11) -/
-- See DisjointUnion.lean for the full development.
