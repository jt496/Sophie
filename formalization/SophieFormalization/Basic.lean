/-
  SophieFormalization.Basic
  Basic definitions for the Holroyd-Talbot conjecture formalization.
-/

import Mathlib

open Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [DecidableEq V] [Fintype V]

section GraphIndependence

variable (G : SimpleGraph V)

/-- A set s is independent in G if no two of its elements are adjacent. -/
def IsIndepSet (s : Finset V) : Prop :=
  ∀ v ∈ s, ∀ w ∈ s, ¬G.Adj v w

/-- A set s is a maximal independent set. -/
def IsMaximalIndep (s : Finset V) : Prop :=
  IsIndepSet G s ∧ ∀ v ∉ s, ∃ w ∈ s, G.Adj v w

/-- mu G is the minimum size of a maximal independent set of G (μ(G)). -/
noncomputable def mu : ℕ :=
  sInf {k | ∃ s : Finset V, IsMaximalIndep G s ∧ s.card = k}

/-- The collection of all independent r-sets of G. -/
noncomputable def indepRSets (r : ℕ) : Finset (Finset V) :=
  (Finset.powersetCard r Finset.univ).filter (fun s => IsIndepSet G s)

/-- The star at vertex v with parameter r: all independent r-sets containing v. -/
noncomputable def vertexStar (v : V) (r : ℕ) : Finset (Finset V) :=
  (indepRSets G r).filter (fun s => v ∈ s)

/-- A family F of sets is intersecting if every two members share a common element. -/
def IsIntersecting (F : Finset (Finset V)) : Prop :=
  ∀ s ∈ F, ∀ t ∈ F, (s ∩ t).Nonempty

end GraphIndependence

section BasicLemmas

variable (G : SimpleGraph V)

/-- The vertex star at v is a subset of all independent r-sets. -/
lemma vertexStar_subset_indepRSets (v : V) (r : ℕ) :
    vertexStar G v r ⊆ indepRSets G r :=
  Finset.filter_subset _ _

/-- A set belongs to the star at v iff it is an independent r-set containing v. -/
lemma mem_vertexStar_iff (v : V) (r : ℕ) (s : Finset V) :
    s ∈ vertexStar G v r ↔ s ∈ indepRSets G r ∧ v ∈ s := by
  simp [vertexStar, Finset.mem_filter]

/-- A set belongs to indepRSets G r iff it has cardinality r and is independent. -/
lemma mem_indepRSets_iff (r : ℕ) (s : Finset V) :
    s ∈ indepRSets G r ↔ s.card = r ∧ IsIndepSet G s := by
  simp [indepRSets, Finset.mem_filter, Finset.mem_powersetCard]

/-- The vertex star at v is an intersecting family. -/
lemma vertexStar_isIntersecting (v : V) (r : ℕ) :
    IsIntersecting (vertexStar G v r) := by
  intro s hs t ht
  rw [mem_vertexStar_iff] at hs ht
  exact ⟨v, Finset.mem_inter.mpr ⟨hs.2, ht.2⟩⟩

end BasicLemmas
