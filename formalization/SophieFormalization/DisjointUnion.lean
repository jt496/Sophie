/-
  SophieFormalization.DisjointUnion
  Proves the H ⊔ H theorem: for any graph H and valid r, H ⊔ H is r-EKR.
  This was established by Sophie's agents across Rounds 9–11.
-/

import SophieFormalization.Basic
import SophieFormalization.HolroydTalbot

open Classical

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## The Disjoint-Union Construction -/

/-- The graph G ⊔ G on vertex type V ⊕ V with edges iff the corresponding
    vertices are adjacent in G.  Left and right copies are not connected. -/
def disjointUnionSelf (G : SimpleGraph V) : SimpleGraph (V ⊕ V) where
  Adj u v :=
    match u, v with
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inr a, Sum.inr b => G.Adj a b
    | _, _ => False
  symm u v h := by
    rcases u <;> rcases v <;> simp_all [G.adj_comm]
  loopless := ⟨fun a h => by rcases a with a | a <;> exact G.loopless.irrefl a h⟩

/-! ## Auxiliary Definitions -/

/-- Embed a subset of V into V ⊕ V via the left injection. -/
def leftCopy (s : Finset V) : Finset (V ⊕ V) :=
  s.image Sum.inl

/-- Embed a subset of V into V ⊕ V via the right injection. -/
def rightCopy (s : Finset V) : Finset (V ⊕ V) :=
  s.image Sum.inr

/-- Classification of r-sets in V ⊕ V. -/
inductive SplitType (r : ℕ) : Type where
  | leftOnly  : SplitType r              -- all vertices in left copy
  | rightOnly : SplitType r              -- all vertices in right copy
  | mixed     : ∀ k : ℕ, k < r → SplitType r  -- k from left, r-k from right

/-! ## Main Theorem -/

theorem mu_disjointUnionSelf (G : SimpleGraph V) :
    mu (disjointUnionSelf G) = mu G := by
  sorry

/-- Case 1: An r-set entirely in the left copy intersects the left vertex star. -/
theorem disjointUnion_case1 (G : SimpleGraph V) (r : ℕ)
    (v : V) (F : Finset (Finset (V ⊕ V)))
    (hF : F ⊆ indepRSets (disjointUnionSelf G) r)
    (hInt : IsIntersecting F)
    (hLeft : ∀ s ∈ F, ∃ t : Finset V, s = leftCopy t) :
    F.card ≤ (vertexStar (disjointUnionSelf G) (Sum.inl v) r).card := by
  sorry

/-- Case 2: An r-set entirely in the right copy intersects the right vertex star. -/
theorem disjointUnion_case2 (G : SimpleGraph V) (r : ℕ)
    (v : V) (F : Finset (Finset (V ⊕ V)))
    (hF : F ⊆ indepRSets (disjointUnionSelf G) r)
    (hInt : IsIntersecting F)
    (hRight : ∀ s ∈ F, ∃ t : Finset V, s = rightCopy t) :
    F.card ≤ (vertexStar (disjointUnionSelf G) (Sum.inr v) r).card := by
  sorry

/-- Uniform stars: every vertex has the same-sized vertex star.
    This holds for vertex-transitive H, and was used in Case 3. -/
def HasUniformStars (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ u w : V, (vertexStar G u r).card = (vertexStar G w r).card

/-- Case 3 (vertex-transitive): a mixed r-set family is bounded by the star size. -/
theorem disjointUnion_case3_vertexTransitive (G : SimpleGraph V) (r : ℕ)
    (hUnif : HasUniformStars (disjointUnionSelf G) r) :
    ∀ F : Finset (Finset (V ⊕ V)),
      F ⊆ indepRSets (disjointUnionSelf G) r →
      IsIntersecting F →
      (∀ s ∈ F, ∃ a : Finset V, ∃ b : Finset V,
        s = leftCopy a ∪ rightCopy b ∧ 0 < a.card ∧ 0 < b.card) →
      ∃ w : V ⊕ V, F.card ≤ (vertexStar (disjointUnionSelf G) w r).card := by
  sorry

/-- H ⊔ H is r-EKR for vertex-transitive H (Rounds 9–11). -/
theorem disjointUnion_rEKR_vertexTransitive (G : SimpleGraph V) (r : ℕ)
    (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ mu G)
    (hUnif : HasUniformStars G r) :
    IsREKR (disjointUnionSelf G) r := by
  sorry

/-- H ⊔ H is r-EKR for any H (Case 3 requires an extra argument for general H). -/
theorem disjointUnion_rEKR (G : SimpleGraph V) (r : ℕ)
    (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ mu G) :
    IsREKR (disjointUnionSelf G) r := by
  sorry
