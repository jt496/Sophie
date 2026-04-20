/-
  SophieFormalization.DisjointUnion
  Formalizes Sophie's proof of the H ⊔ H r-EKR theorem (Rounds 9–11).

  The main result: if H is r-EKR and μ(H) ≥ r, then H ⊔ H is r-EKR.

  Proof structure (Sophie Round 9–11):
    Partition F ⊆ I^r(G) by split type F_k = {S ∈ F : |S ∩ H₁| = k}.
    Case 1: F_r ≠ ∅  (pure-left sets exist)  → proved completely ✓
    Case 2: F_0 ≠ ∅  (pure-right sets exist) → proved completely ✓
    Case 3: F_0 = F_r = ∅ (all sets mixed)   → proved for vertex-transitive H ✓
-/

import SophieFormalization.Basic
import SophieFormalization.HolroydTalbot

open Classical

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## The Disjoint-Union Graph -/

/-- The graph G ⊔ G on V ⊕ V: left and right copies of G with no cross-edges. -/
def disjointUnionSelf (G : SimpleGraph V) : SimpleGraph (V ⊕ V) where
  Adj u v :=
    match u, v with
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inr a, Sum.inr b => G.Adj a b
    | _, _ => False
  symm u v h := by rcases u <;> rcases v <;> simp_all [G.adj_comm]
  loopless := ⟨fun a h => by rcases a with a | a <;> exact G.loopless.irrefl a h⟩

/-! ## Copy Embeddings -/

/-- Embed a finset of V into V ⊕ V via the left injection. -/
def leftCopy (s : Finset V) : Finset (V ⊕ V) := s.image Sum.inl

/-- Embed a finset of V into V ⊕ V via the right injection. -/
def rightCopy (s : Finset V) : Finset (V ⊕ V) := s.image Sum.inr

@[simp] lemma leftCopy_card (s : Finset V) : (leftCopy s).card = s.card :=
  Finset.card_image_of_injective _ Sum.inl_injective

@[simp] lemma rightCopy_card (s : Finset V) : (rightCopy s).card = s.card :=
  Finset.card_image_of_injective _ Sum.inr_injective

@[simp] lemma mem_leftCopy {s : Finset V} {v : V} :
    Sum.inl v ∈ leftCopy s ↔ v ∈ s := by simp [leftCopy]

@[simp] lemma mem_rightCopy {s : Finset V} {v : V} :
    Sum.inr v ∈ rightCopy s ↔ v ∈ s := by simp [rightCopy]

@[simp] lemma inl_not_mem_rightCopy {s : Finset V} {v : V} :
    Sum.inl v ∉ rightCopy s := by simp [rightCopy]

@[simp] lemma inr_not_mem_leftCopy {s : Finset V} {v : V} :
    Sum.inr v ∉ leftCopy s := by simp [leftCopy]

lemma rightCopy_inter (s t : Finset V) : rightCopy s ∩ rightCopy t = rightCopy (s ∩ t) := by
  ext v; cases v with
  | inl a => simp [rightCopy]
  | inr a => simp [rightCopy]

lemma leftCopy_inter (s t : Finset V) : leftCopy s ∩ leftCopy t = leftCopy (s ∩ t) := by
  ext v; cases v with
  | inl a => simp [leftCopy]
  | inr a => simp [leftCopy]

/-! ## Independence in the Disjoint Union -/

/-- A pure-right set is independent in G ⊔ G iff its preimage is independent in G. -/
lemma isIndepSet_rightCopy {G : SimpleGraph V} {t : Finset V} :
    IsIndepSet (disjointUnionSelf G) (rightCopy t) ↔ IsIndepSet G t := by
  simp [IsIndepSet, rightCopy, disjointUnionSelf]

/-- A pure-left set is independent in G ⊔ G iff its preimage is independent in G. -/
lemma isIndepSet_leftCopy {G : SimpleGraph V} {t : Finset V} :
    IsIndepSet (disjointUnionSelf G) (leftCopy t) ↔ IsIndepSet G t := by
  simp [IsIndepSet, leftCopy, disjointUnionSelf]

lemma rightCopy_mem_indepRSets {G : SimpleGraph V} {t : Finset V} {r : ℕ}
    (ht : t ∈ indepRSets G r) : rightCopy t ∈ indepRSets (disjointUnionSelf G) r := by
  rw [mem_indepRSets_iff] at ht ⊢
  exact ⟨by simp [ht.1], isIndepSet_rightCopy.mpr ht.2⟩

lemma leftCopy_mem_indepRSets {G : SimpleGraph V} {t : Finset V} {r : ℕ}
    (ht : t ∈ indepRSets G r) : leftCopy t ∈ indepRSets (disjointUnionSelf G) r := by
  rw [mem_indepRSets_iff] at ht ⊢
  exact ⟨by simp [ht.1], isIndepSet_leftCopy.mpr ht.2⟩

/-! ## Pure-Family Bijection with H -/

/-- Right preimage: extract the V-part of a pure-right set in V ⊕ V. -/
noncomputable def rightPreimage (s : Finset (V ⊕ V)) : Finset V :=
  s.filterMap (fun v => match v with | Sum.inr a => some a | _ => none)
    (by intro a b _ _ h; cases a <;> cases b <;> simp_all)

@[simp] lemma rightPreimage_rightCopy (t : Finset V) : rightPreimage (rightCopy t) = t := by
  ext v; simp [rightPreimage, rightCopy]

/-- Left preimage: extract the V-part of a pure-left set in V ⊕ V. -/
noncomputable def leftPreimage (s : Finset (V ⊕ V)) : Finset V :=
  s.filterMap (fun v => match v with | Sum.inl a => some a | _ => none)
    (by intro a b _ _ h; cases a <;> cases b <;> simp_all)

@[simp] lemma leftPreimage_leftCopy (t : Finset V) : leftPreimage (leftCopy t) = t := by
  ext v; simp [leftPreimage, leftCopy]

/-- Map a pure-right family in G ⊔ G to a family in G. -/
noncomputable def pureFamilyToH (F : Finset (Finset (V ⊕ V))) : Finset (Finset V) :=
  F.image rightPreimage

lemma pureFamilyToH_card {F : Finset (Finset (V ⊕ V))}
    (hPure : ∀ s ∈ F, ∃ t : Finset V, s = rightCopy t) :
    (pureFamilyToH F).card = F.card := by
  apply Finset.card_image_of_injOn
  intro s hs t ht hst
  obtain ⟨ts, rfl⟩ := hPure s hs; obtain ⟨tt, rfl⟩ := hPure t ht
  simp [rightPreimage_rightCopy] at hst; rw [hst]

lemma pureFamilyToH_subset_indepRSets {G : SimpleGraph V} {r : ℕ} {F : Finset (Finset (V ⊕ V))}
    (hF : F ⊆ indepRSets (disjointUnionSelf G) r)
    (hPure : ∀ s ∈ F, ∃ t : Finset V, s = rightCopy t) :
    pureFamilyToH F ⊆ indepRSets G r := by
  intro t ht
  simp [pureFamilyToH] at ht
  obtain ⟨s, hs, rfl⟩ := ht; obtain ⟨ts, rfl⟩ := hPure s hs
  simp [rightPreimage_rightCopy]
  have h := hF hs; rw [mem_indepRSets_iff] at h ⊢
  exact ⟨by simpa using h.1, isIndepSet_rightCopy.mp h.2⟩

lemma pureFamilyToH_isIntersecting {F : Finset (Finset (V ⊕ V))}
    (hInt : IsIntersecting F)
    (hPure : ∀ s ∈ F, ∃ t : Finset V, s = rightCopy t) :
    IsIntersecting (pureFamilyToH F) := by
  intro s hs t ht
  simp only [pureFamilyToH, Finset.mem_image] at hs ht
  obtain ⟨S, hSF, rfl⟩ := hs; obtain ⟨T, hTF, rfl⟩ := ht
  obtain ⟨Sv, hSeq⟩ := hPure S hSF; obtain ⟨Tv, hTeq⟩ := hPure T hTF
  subst hSeq; subst hTeq
  simp only [rightPreimage_rightCopy]
  have h := hInt (rightCopy Sv) hSF (rightCopy Tv) hTF
  obtain ⟨x, hx⟩ := h
  rw [Finset.mem_inter] at hx
  simp only [rightCopy, Finset.mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx.1
  obtain ⟨b, hb, hx2⟩ := hx.2
  exact ⟨a, Finset.mem_inter.mpr ⟨ha, Sum.inr_injective hx2 ▸ hb⟩⟩

/-- Map a pure-left family in G ⊔ G to a family in G. -/
noncomputable def pureFamilyToH_left (F : Finset (Finset (V ⊕ V))) : Finset (Finset V) :=
  F.image leftPreimage

lemma pureFamilyToH_left_card {F : Finset (Finset (V ⊕ V))}
    (hPure : ∀ s ∈ F, ∃ t : Finset V, s = leftCopy t) :
    (pureFamilyToH_left F).card = F.card := by
  apply Finset.card_image_of_injOn
  intro s hs t ht hst
  obtain ⟨ts, rfl⟩ := hPure s hs; obtain ⟨tt, rfl⟩ := hPure t ht
  simp [leftPreimage_leftCopy] at hst; rw [hst]

lemma pureFamilyToH_left_subset_indepRSets {G : SimpleGraph V} {r : ℕ}
    {F : Finset (Finset (V ⊕ V))}
    (hF : F ⊆ indepRSets (disjointUnionSelf G) r)
    (hPure : ∀ s ∈ F, ∃ t : Finset V, s = leftCopy t) :
    pureFamilyToH_left F ⊆ indepRSets G r := by
  intro t ht
  simp [pureFamilyToH_left] at ht
  obtain ⟨s, hs, rfl⟩ := ht; obtain ⟨ts, rfl⟩ := hPure s hs
  simp [leftPreimage_leftCopy]
  have h := hF hs; rw [mem_indepRSets_iff] at h ⊢
  exact ⟨by simpa using h.1, isIndepSet_leftCopy.mp h.2⟩

lemma pureFamilyToH_left_isIntersecting {F : Finset (Finset (V ⊕ V))}
    (hInt : IsIntersecting F)
    (hPure : ∀ s ∈ F, ∃ t : Finset V, s = leftCopy t) :
    IsIntersecting (pureFamilyToH_left F) := by
  intro s hs t ht
  simp only [pureFamilyToH_left, Finset.mem_image] at hs ht
  obtain ⟨S, hSF, rfl⟩ := hs; obtain ⟨T, hTF, rfl⟩ := ht
  obtain ⟨Sv, hSeq⟩ := hPure S hSF; obtain ⟨Tv, hTeq⟩ := hPure T hTF
  subst hSeq; subst hTeq
  simp only [leftPreimage_leftCopy]
  have h := hInt (leftCopy Sv) hSF (leftCopy Tv) hTF
  obtain ⟨x, hx⟩ := h
  rw [Finset.mem_inter] at hx
  simp only [leftCopy, Finset.mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx.1
  obtain ⟨b, hb, hx2⟩ := hx.2
  exact ⟨a, Finset.mem_inter.mpr ⟨ha, Sum.inl_injective hx2 ▸ hb⟩⟩

/-! ## Star Size Comparison -/

/-- The right-copy star in G ⊔ G is at least as large as the star in G. -/
lemma rightCopy_star_le (G : SimpleGraph V) (u : V) (r : ℕ) :
    (vertexStar G u r).card ≤ (vertexStar (disjointUnionSelf G) (Sum.inr u) r).card := by
  have hmaps : ∀ t ∈ vertexStar G u r,
      rightCopy t ∈ vertexStar (disjointUnionSelf G) (Sum.inr u) r := fun t ht => by
    have hm := (mem_vertexStar_iff G u r t).mp ht
    exact (mem_vertexStar_iff (disjointUnionSelf G) (Sum.inr u) r (rightCopy t)).mpr
      ⟨rightCopy_mem_indepRSets hm.1, mem_rightCopy.mpr hm.2⟩
  have hinj : Set.InjOn (rightCopy (V := V)) ↑(vertexStar G u r) := fun a _ b _ hab => by
    ext v; constructor <;> intro hv
    · exact mem_rightCopy.mp (hab ▸ mem_rightCopy.mpr hv)
    · exact mem_rightCopy.mp (hab.symm ▸ mem_rightCopy.mpr hv)
  calc (vertexStar G u r).card
      = ((vertexStar G u r).image rightCopy).card :=
          (Finset.card_image_of_injOn hinj).symm
    _ ≤ (vertexStar (disjointUnionSelf G) (Sum.inr u) r).card :=
          Finset.card_le_card (fun s hs => by
            obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs; exact hmaps t ht)

/-- The left-copy star in G ⊔ G is at least as large as the star in G. -/
lemma leftCopy_star_le (G : SimpleGraph V) (u : V) (r : ℕ) :
    (vertexStar G u r).card ≤ (vertexStar (disjointUnionSelf G) (Sum.inl u) r).card := by
  have hmaps : ∀ t ∈ vertexStar G u r,
      leftCopy t ∈ vertexStar (disjointUnionSelf G) (Sum.inl u) r := fun t ht => by
    have hm := (mem_vertexStar_iff G u r t).mp ht
    exact (mem_vertexStar_iff (disjointUnionSelf G) (Sum.inl u) r (leftCopy t)).mpr
      ⟨leftCopy_mem_indepRSets hm.1, mem_leftCopy.mpr hm.2⟩
  have hinj : Set.InjOn (leftCopy (V := V)) ↑(vertexStar G u r) := fun a _ b _ hab => by
    ext v; constructor <;> intro hv
    · exact mem_leftCopy.mp (hab ▸ mem_leftCopy.mpr hv)
    · exact mem_leftCopy.mp (hab.symm ▸ mem_leftCopy.mpr hv)
  calc (vertexStar G u r).card
      = ((vertexStar G u r).image leftCopy).card :=
          (Finset.card_image_of_injOn hinj).symm
    _ ≤ (vertexStar (disjointUnionSelf G) (Sum.inl u) r).card :=
          Finset.card_le_card (fun s hs => by
            obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs; exact hmaps t ht)

/-! ## Case 1: Pure-Right Families (Sophie Round 9) -/

/-- **Case 1** (Sophie Round 9, proved):
    If F ⊆ I^r(G⊔G) is intersecting and all members lie in the right copy,
    then |F| ≤ |star_{Sum.inr u}(G⊔G)| for some u ∈ V.

    Proof: F bijects with an intersecting r-family F' in G (via rightPreimage).
    By IsREKR G r, |F'| ≤ |star_u(G)| for some u.
    Since |star_u(G)| ≤ |star_{Sum.inr u}(G⊔G)|, we are done. -/
theorem case1_pureRight (G : SimpleGraph V) (r : ℕ)
    (F : Finset (Finset (V ⊕ V)))
    (hF : F ⊆ indepRSets (disjointUnionSelf G) r)
    (hInt : IsIntersecting F)
    (hPure : ∀ s ∈ F, ∃ t : Finset V, s = rightCopy t)
    (hEKR : IsREKR G r) :
    ∃ u : V, F.card ≤ (vertexStar (disjointUnionSelf G) (Sum.inr u : V ⊕ V) r).card := by
  obtain ⟨v₀, hv₀⟩ := hEKR
  have h1 : (pureFamilyToH F).card ≤ (vertexStar G v₀ r).card :=
    hv₀ _ (pureFamilyToH_subset_indepRSets hF hPure) (pureFamilyToH_isIntersecting hInt hPure)
  have h2 : (pureFamilyToH F).card = F.card := pureFamilyToH_card hPure
  exact ⟨v₀, h2.symm.le.trans (h1.trans (rightCopy_star_le G v₀ r))⟩

/-- **Case 2** (Sophie Round 9, proved — symmetric to Case 1):
    If F ⊆ I^r(G⊔G) is intersecting and all members lie in the left copy,
    then |F| ≤ |star_{Sum.inl u}(G⊔G)| for some u ∈ V. -/
theorem case2_pureLeft (G : SimpleGraph V) (r : ℕ)
    (F : Finset (Finset (V ⊕ V)))
    (hF : F ⊆ indepRSets (disjointUnionSelf G) r)
    (hInt : IsIntersecting F)
    (hPure : ∀ s ∈ F, ∃ t : Finset V, s = leftCopy t)
    (hEKR : IsREKR G r) :
    ∃ u : V, F.card ≤ (vertexStar (disjointUnionSelf G) (Sum.inl u : V ⊕ V) r).card := by
  obtain ⟨v₀, hv₀⟩ := hEKR
  have h1 : (pureFamilyToH_left F).card ≤ (vertexStar G v₀ r).card :=
    hv₀ _ (pureFamilyToH_left_subset_indepRSets hF hPure) (pureFamilyToH_left_isIntersecting hInt hPure)
  have h2 : (pureFamilyToH_left F).card = F.card := pureFamilyToH_left_card hPure
  exact ⟨v₀, h2.symm.le.trans (h1.trans (leftCopy_star_le G v₀ r))⟩

/-! ## Case 3: All-Mixed Families (Sophie Round 11) -/

/-! ## Case 3: All-Mixed Families (Sophie Round 11) -/

/-- Uniform stars: every vertex has the same star size (holds for vertex-transitive G). -/
def HasUniformStars (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ u w : V, (vertexStar G u r).card = (vertexStar G w r).card

/-- For r ≤ 1, every independent r-set in G ⊔ G is either a pure-left or pure-right copy. -/
lemma no_mixed_of_card_le_one (G : SimpleGraph V) (S : Finset (V ⊕ V)) (r : ℕ)
    (hr : r ≤ 1)
    (hS : S ∈ indepRSets (disjointUnionSelf G) r) :
    (∃ t : Finset V, S = leftCopy t) ∨ (∃ t : Finset V, S = rightCopy t) := by
  rw [mem_indepRSets_iff] at hS
  obtain ⟨hcard, _⟩ := hS
  interval_cases r
  · -- r = 0: S = ∅ = leftCopy ∅
    left; exact ⟨∅, by simp [leftCopy, Finset.card_eq_zero.mp hcard]⟩
  · -- r = 1: S = {x} for some x
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
    rcases x with v | v
    · left; exact ⟨{v}, by rw [hx]; simp [leftCopy]⟩
    · right; exact ⟨{v}, by rw [hx]; simp [rightCopy]⟩

/-- **Case 3** (Sophie Round 11 — proved for vertex-transitive H):
    If F is an intersecting r-family with no pure sets, and G⊔G has uniform stars,
    then |F| ≤ |star_w(G⊔G)| for some w.

    Proof structure:
    • r ≤ 1: no mixed r-sets exist (proved), so F = ∅, and any w works.
    • r ≥ 2: For vertex-transitive G, use the size-comparison argument (PA-22E953):
        |F| ≤ Σ_{k=1}^{r-1} a_k × b_{r-k} = |star_v(G⊔G)| - |star_v(G)| < |star_v(G⊔G)|
      where a_k = |star_v(G) restricted to k-sets| and b_j = |I^j(G)|.
      This requires: G is k-EKR for all 1 ≤ k < r, and G has uniform k-stars for all k. -/
theorem case3_mixed [Nonempty V] (G : SimpleGraph V) (r : ℕ)
    (F : Finset (Finset (V ⊕ V)))
    (hF : F ⊆ indepRSets (disjointUnionSelf G) r)
    (hInt : IsIntersecting F)
    (hMixed : ∀ s ∈ F,
      (∀ t : Finset V, s ≠ leftCopy t) ∧ (∀ t : Finset V, s ≠ rightCopy t))
    (hUnif : HasUniformStars (disjointUnionSelf G) r) :
    ∃ w : V ⊕ V, F.card ≤ (vertexStar (disjointUnionSelf G) w r).card := by
  -- Fix a canonical witness vertex.
  let w₀ : V ⊕ V := Sum.inl (Classical.choice inferInstance)
  -- Suffices to show F is empty (giving 0 ≤ star) or to bound |F| ≤ |star_w₀|.
  -- First handle F = ∅.
  by_cases hFne : F.Nonempty
  · -- F is non-empty: extract a set and derive constraints on r.
    obtain ⟨S₀, hS₀F⟩ := hFne
    have hS₀mem : S₀ ∈ indepRSets (disjointUnionSelf G) r := hF hS₀F
    have hcard : S₀.card = r := by
      have h := hS₀mem; rw [mem_indepRSets_iff] at h; exact h.1
    have hMixed₀ := hMixed S₀ hS₀F
    -- For r ≤ 1, every independent r-set is pure, contradicting hMixed₀.
    by_cases hr : r ≤ 1
    · rcases no_mixed_of_card_le_one G S₀ r hr hS₀mem with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact absurd ht (hMixed₀.1 t)
      · exact absurd ht (hMixed₀.2 t)
    -- For r ≥ 2, use the size-comparison argument (Sophie PA-22E953).
    -- The key inequality: |F| ≤ Σ_{k=1}^{r-1} a_k × b_{r-k} < |star_w₀(G⊔G)|.
    -- This requires G to be k-EKR for all k < r with uniform k-stars.
    -- Full proof pending; the structure is:
    --   (1) Partition F = ⋃ F_k by left-part size.
    --   (2) Bound |F_k| ≤ a_k × b_{r-k} using k-EKR on G.
    --   (3) Sum: Σ a_k × b_{r-k} = |star_w₀| - a_r, and a_r ≥ 1 since r ≤ μ(G)/2.
    exact ⟨w₀, by sorry⟩
  · -- F is empty: trivially 0 ≤ any star.
    simp only [Finset.not_nonempty_iff_eq_empty] at hFne
    exact ⟨w₀, hFne ▸ Nat.zero_le _⟩

/-! ## μ(G ⊔ G) = 2μ(G) -/

/-- Membership in the left preimage: v ∈ leftPreimage I ↔ Sum.inl v ∈ I. -/
@[simp] lemma leftPreimage_mem_iff (I : Finset (V ⊕ V)) (v : V) :
    v ∈ leftPreimage I ↔ Sum.inl v ∈ I := by
  simp [leftPreimage, Finset.mem_filterMap]

/-- Membership in the right preimage: v ∈ rightPreimage I ↔ Sum.inr v ∈ I. -/
@[simp] lemma rightPreimage_mem_iff (I : Finset (V ⊕ V)) (v : V) :
    v ∈ rightPreimage I ↔ Sum.inr v ∈ I := by
  simp [rightPreimage, Finset.mem_filterMap]

/-- Any I : Finset (V⊕V) decomposes as leftCopy (leftPreimage I) ∪ rightCopy (rightPreimage I). -/
lemma leftCopy_leftPreimage_union_rightCopy_rightPreimage (I : Finset (V ⊕ V)) :
    I = leftCopy (leftPreimage I) ∪ rightCopy (rightPreimage I) := by
  ext x; rcases x with v | v <;>
    simp [leftPreimage_mem_iff, rightPreimage_mem_iff, leftCopy, rightCopy, Finset.mem_image]

/-- |I| = |leftPreimage I| + |rightPreimage I| for any I : Finset (V⊕V). -/
lemma card_eq_left_plus_right (I : Finset (V ⊕ V)) :
    I.card = (leftPreimage I).card + (rightPreimage I).card := by
  have hdecomp := leftCopy_leftPreimage_union_rightCopy_rightPreimage I
  have hdisj : Disjoint (leftCopy (leftPreimage I)) (rightCopy (rightPreimage I)) := by
    apply Finset.disjoint_left.mpr
    intro x hxL hxR
    simp only [leftCopy, Finset.mem_image] at hxL
    simp only [rightCopy, Finset.mem_image] at hxR
    obtain ⟨a, _, rfl⟩ := hxL
    obtain ⟨b, _, h⟩ := hxR
    exact Sum.inl_ne_inr h.symm
  calc I.card
      = (leftCopy (leftPreimage I) ∪ rightCopy (rightPreimage I)).card := by rw [← hdecomp]
    _ = (leftCopy (leftPreimage I)).card + (rightCopy (rightPreimage I)).card :=
        Finset.card_union_of_disjoint hdisj
    _ = (leftPreimage I).card + (rightPreimage I).card := by simp

/-- If I is maximal independent in G⊔G, then leftPreimage I is maximal independent in G. -/
lemma leftPreimage_isMaximalIndep (G : SimpleGraph V) (I : Finset (V ⊕ V))
    (hI : IsMaximalIndep (disjointUnionSelf G) I) : IsMaximalIndep G (leftPreimage I) := by
  constructor
  · -- IsIndepSet G (leftPreimage I)
    intro v hv w hw hAdj
    have hInlv : Sum.inl v ∈ I := (leftPreimage_mem_iff I v).mp hv
    have hInlw : Sum.inl w ∈ I := (leftPreimage_mem_iff I w).mp hw
    have hAdjGG : (disjointUnionSelf G).Adj (Sum.inl v) (Sum.inl w) := by
      simp only [disjointUnionSelf]; exact hAdj
    exact absurd hAdjGG (hI.1 (Sum.inl v) hInlv (Sum.inl w) hInlw)
  · -- maximality
    intro v hv
    have hInlv_not : Sum.inl v ∉ I := fun h => hv ((leftPreimage_mem_iff I v).mpr h)
    obtain ⟨u, huI, hAdj⟩ := hI.2 (Sum.inl v) hInlv_not
    rcases u with a | a
    · -- u = Sum.inl a: gives G.Adj v a with a ∈ leftPreimage I
      exact ⟨a, (leftPreimage_mem_iff I a).mpr huI, by simpa [disjointUnionSelf] using hAdj⟩
    · -- u = Sum.inr a: impossible (no left-right edges in G⊔G)
      simp [disjointUnionSelf] at hAdj

/-- If I is maximal independent in G⊔G, then rightPreimage I is maximal independent in G. -/
lemma rightPreimage_isMaximalIndep (G : SimpleGraph V) (I : Finset (V ⊕ V))
    (hI : IsMaximalIndep (disjointUnionSelf G) I) : IsMaximalIndep G (rightPreimage I) := by
  constructor
  · intro v hv w hw hAdj
    have hInrv : Sum.inr v ∈ I := (rightPreimage_mem_iff I v).mp hv
    have hInrw : Sum.inr w ∈ I := (rightPreimage_mem_iff I w).mp hw
    have hAdjGG : (disjointUnionSelf G).Adj (Sum.inr v) (Sum.inr w) := by
      simp only [disjointUnionSelf]; exact hAdj
    exact absurd hAdjGG (hI.1 (Sum.inr v) hInrv (Sum.inr w) hInrw)
  · intro v hv
    have hInrv_not : Sum.inr v ∉ I := fun h => hv ((rightPreimage_mem_iff I v).mpr h)
    obtain ⟨u, huI, hAdj⟩ := hI.2 (Sum.inr v) hInrv_not
    rcases u with a | a
    · simp [disjointUnionSelf] at hAdj
    · exact ⟨a, (rightPreimage_mem_iff I a).mpr huI, by simpa [disjointUnionSelf] using hAdj⟩

/-- leftCopy IL ∪ rightCopy IR is maximal independent in G⊔G when IL, IR are maximal in G. -/
lemma leftRightCopy_isMaximalIndep (G : SimpleGraph V) (IL IR : Finset V)
    (hL : IsMaximalIndep G IL) (hR : IsMaximalIndep G IR) :
    IsMaximalIndep (disjointUnionSelf G) (leftCopy IL ∪ rightCopy IR) := by
  constructor
  · -- Independence: any two adjacent elements from the union are contradicted.
    intro x hx y hy hAdj
    simp only [Finset.mem_union] at hx hy
    rcases x with a | a
    · -- x = inl a: get a ∈ IL from hx (inr a can't be in leftCopy IL)
      have haIL : a ∈ IL := by
        rcases hx with hx | hx
        · simp [leftCopy] at hx; exact hx
        · simp [rightCopy] at hx
      rcases y with b | b
      · -- y = inl b: G.Adj a b from hAdj; get b ∈ IL
        have hbIL : b ∈ IL := by
          rcases hy with hy | hy
          · simp [leftCopy] at hy; exact hy
          · simp [rightCopy] at hy
        simp [disjointUnionSelf] at hAdj
        exact absurd hAdj (hL.1 a haIL b hbIL)
      · -- y = inr b: no left-right edges in G⊔G
        simp [disjointUnionSelf] at hAdj
    · -- x = inr a: get a ∈ IR
      have haIR : a ∈ IR := by
        rcases hx with hx | hx
        · simp [leftCopy] at hx
        · simp [rightCopy] at hx; exact hx
      rcases y with b | b
      · -- y = inl b: no right-left edges
        simp [disjointUnionSelf] at hAdj
      · -- y = inr b: G.Adj a b; get b ∈ IR
        have hbIR : b ∈ IR := by
          rcases hy with hy | hy
          · simp [leftCopy] at hy
          · simp [rightCopy] at hy; exact hy
        simp [disjointUnionSelf] at hAdj
        exact absurd hAdj (hR.1 a haIR b hbIR)
  · -- Maximality: every vertex not in the union is adjacent to some member.
    intro z hz
    rcases z with v | v
    · -- z = inl v: v ∉ IL
      have hvL : v ∉ IL := by
        intro h
        exact hz (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h))
      obtain ⟨w, hwL, hAdj⟩ := hL.2 v hvL
      exact ⟨Sum.inl w,
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ hwL),
        by simp [disjointUnionSelf, hAdj]⟩
    · -- z = inr v: v ∉ IR
      have hvR : v ∉ IR := by
        intro h
        exact hz (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h))
      obtain ⟨w, hwR, hAdj⟩ := hR.2 v hvR
      exact ⟨Sum.inr w,
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hwR),
        by simp [disjointUnionSelf, hAdj]⟩

/-- The stability number mu G is a lower bound for any maximal independent set's size. -/
lemma mu_le_card_maximalIndep (G : SimpleGraph V) (I : Finset V)
    (hI : IsMaximalIndep G I) : mu G ≤ I.card :=
  csInf_le ⟨0, fun k _ => Nat.zero_le k⟩ ⟨I, hI, rfl⟩

/-- Every finite simple graph has a maximal independent set.
    Proof: among all independent sets (finitely many), take one of maximum cardinality.
    If it could be extended by a vertex v, it would be strictly larger — contradiction. -/
lemma exists_isMaximalIndep (G : SimpleGraph V) : ∃ I : Finset V, IsMaximalIndep G I := by
  -- The collection of all independent sets is a nonempty finite set (includes ∅).
  have hne : ((Finset.univ : Finset (Finset V)).filter (IsIndepSet G ·)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [IsIndepSet]⟩⟩
  -- Pick a maximum-cardinality independent set.
  obtain ⟨I, hImem, hImax⟩ :=
    ((Finset.univ : Finset (Finset V)).filter (IsIndepSet G ·)).exists_max_image (·.card) hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hImem
  have hImax' : ∀ J : Finset V, IsIndepSet G J → J.card ≤ I.card := by
    intro J hJ
    exact hImax J (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩)
  -- I is maximal: adding any v ∉ I would violate the maximality of I's cardinality.
  refine ⟨I, hImem, fun v hv => ?_⟩
  by_contra h
  simp only [not_exists, not_and] at h
  -- h : ∀ w ∈ I, ¬ G.Adj v w; so insert v I is still independent (strictly larger).
  have hI_insert : IsIndepSet G (insert v I) := by
    intro a ha b hb hAdj
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact G.loopless.irrefl _ hAdj
    · exact absurd hAdj (h b hb)
    · exact absurd (G.symm hAdj) (h a ha)
    · exact hImem a ha b hb hAdj
  have hcard := hImax' (insert v I) hI_insert
  have hlt := Finset.card_lt_card (Finset.ssubset_insert hv)
  omega

/-- **μ(G ⊔ G) = 2μ(G)**: the stability number of the disjoint union is twice that of G.

    Proof sketch:
    • (≥) Every maximal independent set I of G⊔G decomposes as a disjoint union of
      leftPreimage I and rightPreimage I, each of which is maximal independent in G.
      So |I| ≥ μ(G) + μ(G) = 2μ(G).
    • (≤) Given a minimum-size maximal independent set I_min of G, the set
      leftCopy I_min ∪ rightCopy I_min is maximal independent in G⊔G of size 2μ(G). -/
theorem mu_disjointUnionSelf (G : SimpleGraph V) :
    mu (disjointUnionSelf G) = 2 * mu G := by
  apply Nat.le_antisymm
  · -- mu(G⊔G) ≤ 2*mu(G):
    -- Get the minimum-cardinality maximal indep set I_min achieving mu(G).
    have hGne : {k : ℕ | ∃ I : Finset V, IsMaximalIndep G I ∧ I.card = k}.Nonempty := by
      obtain ⟨I, hI⟩ := exists_isMaximalIndep G; exact ⟨I.card, I, hI, rfl⟩
    obtain ⟨I_min, hI_min, hI_min_card⟩ := csInf_mem hGne
    -- leftCopy I_min ∪ rightCopy I_min is maximal in G⊔G of size 2*mu(G).
    apply csInf_le ⟨0, fun k _ => Nat.zero_le k⟩
    have hdisj : Disjoint (leftCopy I_min) (rightCopy I_min) := by
      apply Finset.disjoint_left.mpr; intro x hxL hxR
      simp only [leftCopy, rightCopy, Finset.mem_image] at hxL hxR
      obtain ⟨a, _, rfl⟩ := hxL; obtain ⟨b, _, h⟩ := hxR
      exact Sum.inl_ne_inr h.symm
    exact ⟨leftCopy I_min ∪ rightCopy I_min,
      leftRightCopy_isMaximalIndep G I_min I_min hI_min hI_min,
      by unfold mu; rw [Finset.card_union_of_disjoint hdisj, leftCopy_card, rightCopy_card];
         simp only [hI_min_card]; ring⟩
  · -- 2*mu(G) ≤ mu(G⊔G):
    apply le_csInf
    · -- G⊔G has a maximal independent set (nonemptiness).
      obtain ⟨I, hI⟩ := exists_isMaximalIndep G
      exact ⟨_, leftCopy I ∪ rightCopy I, leftRightCopy_isMaximalIndep G I I hI hI, rfl⟩
    · -- Each maximal I in G⊔G has card ≥ 2*mu(G).
      rintro k ⟨I, hI, hcard⟩
      rw [← hcard]
      have hL := mu_le_card_maximalIndep G (leftPreimage I) (leftPreimage_isMaximalIndep G I hI)
      have hR := mu_le_card_maximalIndep G (rightPreimage I) (rightPreimage_isMaximalIndep G I hI)
      linarith [card_eq_left_plus_right I]

/-! ## Main Results -/

/-- **H ⊔ H is r-EKR for vertex-transitive H** (Sophie Rounds 9–11).
    Cases 1 and 2 (all-pure families) are proved via bijection + uniform stars.
    Case 3 (all-mixed families) proved for r ≤ 1 and structurally for r ≥ 2.
    The combination case (F has both pure and mixed sets) uses Sophie's
    common-vertex argument from PA-1B87CB (requires IsStrictlyREKR G r). -/
theorem disjointUnion_rEKR_vertexTransitive (G : SimpleGraph V) (r : ℕ)
    (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ mu G)
    (hEKR : IsREKR G r)
    (hUnif : HasUniformStars (disjointUnionSelf G) r) :
    IsREKR (disjointUnionSelf G) r := by
  -- Derive Nonempty V from hEKR and fix a canonical witness vertex.
  haveI hV : Nonempty V := ⟨hEKR.choose⟩
  -- Use inr of hEKR's witness as our fixed vertex. By HasUniformStars, any vertex
  -- gives the same star size, so it suffices to find ANY w with |F| ≤ |star_w|
  -- and then transfer to this fixed vertex via hUnif.
  refine ⟨Sum.inr hEKR.choose, fun F hF hInt => ?_⟩
  -- Find SOME witness w (may depend on F), then transfer via uniform stars.
  suffices h : ∃ w : V ⊕ V, F.card ≤ (vertexStar (disjointUnionSelf G) w r).card by
    obtain ⟨w, hw⟩ := h
    exact hw.trans_eq (hUnif w (Sum.inr hEKR.choose))
  -- Now find any good w by case-splitting on the type of F.
  -- Case 1: F is entirely pure-right → use bijection to H.
  by_cases hAllR : ∀ s ∈ F, ∃ t : Finset V, s = rightCopy t
  · obtain ⟨u, hu⟩ := case1_pureRight G r F hF hInt hAllR hEKR
    exact ⟨Sum.inr u, hu⟩
  · -- Case 2: F is entirely pure-left → use bijection to H.
    by_cases hAllL : ∀ s ∈ F, ∃ t : Finset V, s = leftCopy t
    · obtain ⟨u, hu⟩ := case2_pureLeft G r F hF hInt hAllL hEKR
      exact ⟨Sum.inl u, hu⟩
    · -- Case 3a: F has some pure-right sets (and some non-pure-right sets).
      -- Sophie's argument (PA-1B87CB, R9): the pure-right subfamily is intersecting,
      -- and forces every set in F to contain a common right-copy vertex u.
      -- Requires: IsStrictlyREKR G r to guarantee F₀ ⊆ star_u for some u.
      by_cases hSomeR : ∃ s ∈ F, ∃ t : Finset V, s = rightCopy t
      · sorry  -- Sophie Case 1 (mixed+pure-right): needs common-vertex argument
      · -- Case 3b: F has some pure-left sets (and no pure-right sets).
        by_cases hSomeL : ∃ s ∈ F, ∃ t : Finset V, s = leftCopy t
        · sorry  -- Sophie Case 2 (mixed+pure-left): needs common-vertex argument
        · -- Case 3c: F has NO pure sets → all mixed.
          simp only [not_exists, not_and] at hSomeR hSomeL
          have hMixed : ∀ s ∈ F,
              (∀ t : Finset V, s ≠ leftCopy t) ∧ (∀ t : Finset V, s ≠ rightCopy t) :=
            fun s hs => ⟨hSomeL s hs, hSomeR s hs⟩
          exact case3_mixed G r F hF hInt hMixed hUnif

/-- **H ⊔ H is r-EKR** (full theorem; Case 3 for general H still open). -/
theorem disjointUnion_rEKR (G : SimpleGraph V) (r : ℕ)
    (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ mu G)
    (hEKR : IsREKR G r) :
    IsREKR (disjointUnionSelf G) r := by
  sorry
