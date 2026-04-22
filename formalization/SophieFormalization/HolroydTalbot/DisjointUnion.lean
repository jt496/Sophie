/-
  SophieFormalization.HolroydTalbot.DisjointUnion
  Formalizes Sophie's proof of the H ⊔ H r-EKR theorem (Rounds 9–14).

  The main result: if H is r-EKR and μ(H) ≥ r, then H ⊔ H is r-EKR.

  Proof structure (Sophie Rounds 9–14):
    Partition F ⊆ I^r(G⊔G) by split type F_k = {S ∈ F : |S ∩ H₁| = k}.

    Case 1: F is all-pure-right (F_0 = F) → proved completely ✓
      Bijection rightPreimage : F → F' ⊆ I^r(H), then |F'| ≤ |star_u(H)| by IsREKR.

    Case 2: F is all-pure-left (F_r = F) → proved completely ✓
      Symmetric to Case 1.

    Case 3a: F has both pure-right and pure-left members → contradiction ✓
      leftCopy s ∩ rightCopy t = ∅ always, so F cannot be intersecting. PROVED.

    Case 3b/3b': F has pure-right+mixed or pure-left+mixed → OPEN (sorry)
      Needs: IsStrictlyREKR G r (common-vertex forcing argument).
      Open subproblem SP-86620A in Sophie knowledge base.

    Case 3c: F is all-mixed (F_0 = F_r = ∅) → PROOF STRATEGY IS FLAWED (Round 15)

      FAILED APPROACH (DA-TERM07): Termwise bound |F_k| ≤ |I^k|×|star_v(G,r-k)| is FALSE.
        Counterexample: G=K₆^c, r=3, k=2, 2r=6=μ(K₆^c) ✓.
        Left-star family F₂ = {(L,R) : 0∈L, L∈I²,R∈I¹} has |F₂|=30, but bound=15×1=15.
        Fails because a left-star family is intersecting via the LEFT part alone, so the
        right part can range freely over ALL of I^{r-k}, far exceeding one right-star.

      CORRECT PICTURE — Complementary Slice Coupling (SP-CPLNG2):
        While |F_k| can exceed |I^k|×|star_v(G,r-k)|, a large F_k FORCES F_{r-k} small.
        Precisely: F_k and F_{r-k} are cross-intersecting (since F is intersecting):
          ∀ S∈F_k, T∈F_{r-k}: L_S∩L_T ≠ ∅  OR  R_S∩R_T ≠ ∅.
        When F_k is a left-star (L_S always contains 0), any T∈F_{r-k} must either
        meet 0 in its left part OR meet R_S in its right part for every S∈F_k.
        This severly constrains F_{r-k}.

        CONJECTURE (SP-CPLNG2, computationally verified for r≤4 on K_n^c, C_n):
          ∀ cross-intersecting (F_k, F_{r-k}):  |F_k| + |F_{r-k}|
            ≤ |I^k(G)|×|star_v(G,r-k)| + |I^{r-k}(G)|×|star_v(G,k)|   (combined slice)
        The bound is TIGHT, achieved exactly when F_k = { S : v₀ ∈ R_S } and
        F_{r-k} = { T : v₀ ∈ R_T } — i.e., both slices taken from star_{inr v₀}.

        SUMMING over k=1..r-1 and using star_inr_card_eq gives |F_mixed| ≤ |star_{inr v₀}|-|star_v₀(G,r)|.

      CORRECT PROOF STRATEGY (to be formalised):
        The extremal all-mixed family is the all-mixed part of a right-star.
        A direct injection F ↪ star_{inr v₀}(G⊔G) may be possible via:
          (a) Katona cyclic-permutation argument on the right parts, or
          (b) Proving SP-CPLNG2 by a Bollobás set-pairs bound applied to the pair
              (right-projections, left-projections) which are cross-linked.
        See SP-MX15A1 for the reformulated open problem.

  KEY PROVED LEMMAS:
    • mu_disjointUnionSelf : μ(G⊔G) = 2μ(G)                           ✓
    • star_inr_card_eq : |star_{inr v}(G⊔G)| = Σ decomposition         ✓
    • case1_pureRight / case2_pureLeft                                  ✓
    • not_both_pureCopies_intersecting : no pure-left AND pure-right     ✓
    • case3_mixed  (proof strategy FLAWED — hFk_bound is FALSE, see R15)   ✗/sorry
-/

import SophieFormalization.HolroydTalbot.Basic
import SophieFormalization.HolroydTalbot.Theorems

open Classical
set_option linter.unusedSectionVars false
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

/-! ## Preimage Decomposition -/

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

/-! ## Star Identity for G ⊔ G -/

/-- The r-star at inr v in G⊔G decomposes into:
    - pure-right r-sets: correspond to r-sets in star_v(G), count = |star_v(G, r)|
    - mixed r-sets with left-part size k (1 ≤ k ≤ r-1):
      leftPreimage is any k-independent-set in G,
      rightPreimage is any (r-k)-independent-set containing v.
    So |star_{inr v}(G⊔G, r)| = |star_v G r| + Σ_{k=1}^{r-1} |indepRSets G k| × |star_v G (r-k)|. -/
lemma star_inr_card_eq (G : SimpleGraph V) (v : V) (r : ℕ) :
    (vertexStar (disjointUnionSelf G) (Sum.inr v) r).card =
    (vertexStar G v r).card +
      ∑ k ∈ Finset.Icc 1 (r - 1),
        (indepRSets G k).card * (vertexStar G v (r - k)).card := by
  -- Slice the star by left-part size.
  let Sk (k : ℕ) : Finset (Finset (V ⊕ V)) :=
    (vertexStar (disjointUnionSelf G) (Sum.inr v) r).filter (fun S => (leftPreimage S).card = k)
  -- The star is (Sk 0) ∪ (⋃_{k=1}^{r-1} Sk k): size-r sets containing inr v have
  -- left-part size 0 (pure-right) or 1..r-1 (mixed); left-part size r impossible
  -- since inr v ∈ S means v ∈ rightPreimage S, but pure-left has no right elements.
  -- Step A: Sk 0 = image rightCopy (vertexStar G v r), so |Sk 0| = |vertexStar G v r|.
  have hSk0 : (Sk 0).card = (vertexStar G v r).card := by
    suffices himg : Sk 0 = (vertexStar G v r).image rightCopy by
      rw [himg]
      apply Finset.card_image_of_injective
      intro a b hab
      simp only [rightCopy, Finset.image_inj Sum.inr_injective] at hab
      exact hab
    ext S
    simp only [Sk, Finset.mem_filter, mem_vertexStar_iff, mem_indepRSets_iff, Finset.mem_image]
    constructor
    · intro ⟨⟨⟨hcard, hindep⟩, hvS⟩, hk0⟩
      have hLempty : leftPreimage S = ∅ := Finset.card_eq_zero.mp hk0
      have hSeqR : S = rightCopy (rightPreimage S) := by
        have h := leftCopy_leftPreimage_union_rightCopy_rightPreimage S
        rw [hLempty] at h; simp only [leftCopy, Finset.image_empty, Finset.empty_union] at h
        exact h
      refine ⟨rightPreimage S, ⟨⟨?_, ?_⟩, (rightPreimage_mem_iff S v).mpr hvS⟩, hSeqR.symm⟩
      · -- card
        rw [← rightCopy_card, ← hSeqR]; exact hcard
      · -- independence
        exact isIndepSet_rightCopy.mp (hSeqR ▸ hindep)
    · rintro ⟨t, ⟨⟨htcard, htindep⟩, hvt⟩, rfl⟩
      refine ⟨⟨⟨by simp [htcard], isIndepSet_rightCopy.mpr htindep⟩,
               by simp [mem_rightCopy, hvt]⟩, ?_⟩
      -- (leftPreimage (rightCopy t)).card = 0
      have : leftPreimage (rightCopy t) = ∅ := by
        ext w; simp [leftPreimage_mem_iff]
      simp [this]
  -- Step B: For k ∈ 1..r-1, Sk k bijects with indepRSets G k × vertexStar G v (r-k),
  --         so |Sk k| = |indepRSets G k| × |vertexStar G v (r-k)|.
  have hSkk : ∀ k ∈ Finset.Icc 1 (r - 1),
      (Sk k).card = (indepRSets G k).card * (vertexStar G v (r - k)).card := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [← Finset.card_product]
    apply Finset.card_bij (fun S _ => (leftPreimage S, rightPreimage S))
    · -- well-formedness: (leftPreimage S, rightPreimage S) ∈ indepRSets G k ×ˢ vertexStar G v (r-k)
      intro S hS
      simp only [Sk, Finset.mem_filter, mem_vertexStar_iff, mem_indepRSets_iff] at hS
      obtain ⟨⟨⟨hcard, hindep⟩, hvS⟩, hLcard⟩ := hS
      have hRcard : (rightPreimage S).card = r - k := by
        have := card_eq_left_plus_right S; rw [hcard, hLcard] at this; omega
      simp only [Finset.mem_product, mem_indepRSets_iff, mem_vertexStar_iff, mem_indepRSets_iff]
      refine ⟨⟨hLcard, fun x hx y hy hAdj => ?_⟩,
             ⟨⟨hRcard, fun x hx y hy hAdj => ?_⟩, (rightPreimage_mem_iff S v).mpr hvS⟩⟩
      · -- IsIndepSet G (leftPreimage S): lift to G⊔G via leftCopy
        have h := hindep (Sum.inl x) ((leftPreimage_mem_iff S x).mp hx)
                         (Sum.inl y) ((leftPreimage_mem_iff S y).mp hy)
        exact h hAdj
      · -- IsIndepSet G (rightPreimage S): lift to G⊔G via rightCopy
        have h := hindep (Sum.inr x) ((rightPreimage_mem_iff S x).mp hx)
                         (Sum.inr y) ((rightPreimage_mem_iff S y).mp hy)
        exact h hAdj
    · -- injectivity: S determined by (leftPreimage S, rightPreimage S)
      intro S₁ _ S₂ _ heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hLeq, hReq⟩ := heq
      have h1 := leftCopy_leftPreimage_union_rightCopy_rightPreimage S₁
      have h2 := leftCopy_leftPreimage_union_rightCopy_rightPreimage S₂
      rw [hLeq, hReq] at h1; exact h1.trans h2.symm
    · -- surjectivity: given (L, R), take leftCopy L ∪ rightCopy R ∈ Sk k
      intro ⟨L, R⟩ hLR
      simp only [Finset.mem_product, mem_indepRSets_iff, mem_vertexStar_iff,
                 mem_indepRSets_iff] at hLR
      obtain ⟨⟨hLcard, hLindep⟩, ⟨⟨hRcard, hRindep⟩, hvR⟩⟩ := hLR
      have hdisj : Disjoint (leftCopy L) (rightCopy R) := by
        apply Finset.disjoint_left.mpr
        intro x hxL hxR
        simp only [leftCopy, rightCopy, Finset.mem_image] at hxL hxR
        obtain ⟨a, _, rfl⟩ := hxL; obtain ⟨b, _, h⟩ := hxR
        exact Sum.inl_ne_inr h.symm
      have hLRcard : (leftCopy L ∪ rightCopy R).card = r := by
        rw [Finset.card_union_of_disjoint hdisj]; simp [hLcard, hRcard]; omega
      refine ⟨leftCopy L ∪ rightCopy R, ?_, ?_⟩
      · simp only [Sk, Finset.mem_filter, mem_vertexStar_iff, mem_indepRSets_iff]
        refine ⟨⟨⟨hLRcard, ?_⟩, by simp [mem_rightCopy, hvR]⟩, ?_⟩
        · -- IsIndepSet (disjointUnionSelf G) (leftCopy L ∪ rightCopy R)
          intro x hxLR y hyLR
          simp only [Finset.mem_union, leftCopy, rightCopy, Finset.mem_image] at hxLR hyLR
          rcases hxLR with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;>
          rcases hyLR with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
          · exact hLindep a ha b hb
          · simp [disjointUnionSelf]
          · simp [disjointUnionSelf]
          · exact hRindep a ha b hb
        · -- (leftPreimage (leftCopy L ∪ rightCopy R)).card = k
          have : leftPreimage (leftCopy L ∪ rightCopy R) = L := by
            ext w; simp [leftPreimage_mem_iff]
          rw [this, hLcard]
      · simp only [Prod.mk.injEq]
        exact ⟨by ext w; simp [leftPreimage_mem_iff],
               by ext w; simp [rightPreimage_mem_iff]⟩
  -- Step C: The star decomposes as biUnion (Icc 0 (r-1)) Sk;
  -- separate k=0 from k≥1, apply hSk0 and hSkk.
  -- Every S in the star has leftPreimage size in Icc 0 (r-1) (since it contains inr v).
  have hmem_star : ∀ S ∈ vertexStar (disjointUnionSelf G) (Sum.inr v) r,
      (leftPreimage S).card ∈ Finset.Icc 0 (r - 1) := by
    intro S hS
    simp only [mem_vertexStar_iff, mem_indepRSets_iff, Finset.mem_Icc] at hS ⊢
    obtain ⟨⟨hcard, _⟩, hvS⟩ := hS
    refine ⟨Nat.zero_le _, ?_⟩
    have hRne : v ∈ rightPreimage S := (rightPreimage_mem_iff S v).mpr hvS
    have hRpos : 0 < (rightPreimage S).card := Finset.card_pos.mpr ⟨v, hRne⟩
    have := card_eq_left_plus_right S; rw [hcard] at this; omega
  have hstar_eq : vertexStar (disjointUnionSelf G) (Sum.inr v) r =
      Finset.biUnion (Finset.Icc 0 (r - 1)) Sk := by
    ext S
    simp only [Finset.mem_biUnion, Sk, Finset.mem_filter]
    exact ⟨fun hS => ⟨(leftPreimage S).card, hmem_star S hS, hS, rfl⟩,
           fun ⟨_, _, hS, rfl⟩ => hS⟩
  have hdisj_Sk : ∀ i ∈ Finset.Icc 0 (r - 1), ∀ j ∈ Finset.Icc 0 (r - 1),
      i ≠ j → Disjoint (Sk i) (Sk j) := by
    intro i _ j _ hij
    apply Finset.disjoint_filter.mpr
    intro S _ hi hj; exact hij (hi.symm.trans hj)
  have hIcc_split : Finset.Icc 0 (r - 1) = {0} ∪ Finset.Icc 1 (r - 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
  have h01disj : Disjoint ({0} : Finset ℕ) (Finset.Icc 1 (r - 1)) := by
    simp
  rw [hstar_eq, Finset.card_biUnion hdisj_Sk, hIcc_split,
      Finset.sum_union h01disj, Finset.sum_singleton, hSk0]
  congr 1
  exact Finset.sum_congr rfl hSkk

/-! ## Case 3: All-Mixed Families (Sophie Round 11) -/

/-- Uniform stars: every vertex has the same star size (holds for vertex-transitive G). -/
def HasUniformStars (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ u w : V, (vertexStar G u r).card = (vertexStar G w r).card

/-! ### Pure-pair exclusion lemmas -/

/-- leftCopy and rightCopy always produce disjoint sets in V ⊕ V. -/
lemma leftCopy_disjoint_rightCopy (s t : Finset V) :
    Disjoint (leftCopy s) (rightCopy t) := by
  apply Finset.disjoint_left.mpr
  intro x hxL hxR
  simp only [leftCopy, rightCopy, Finset.mem_image] at hxL hxR
  obtain ⟨a, _, rfl⟩ := hxL
  obtain ⟨b, _, h⟩ := hxR
  exact Sum.inl_ne_inr h.symm

/-- An intersecting family cannot contain both a pure-left and a pure-right member.
    Proof: leftCopy s ∩ rightCopy t = ∅ for any s t (left and right injections have
    disjoint ranges), so the two sets cannot meet — contradicting IsIntersecting. -/
lemma not_both_pureCopies_intersecting
    (F : Finset (Finset (V ⊕ V)))
    (hInt : IsIntersecting F)
    {s t : Finset V}
    (hL : leftCopy s ∈ F) (hR : rightCopy t ∈ F) : False := by
  obtain ⟨x, hx⟩ := hInt _ hL _ hR
  rw [Finset.mem_inter] at hx
  simp only [leftCopy, rightCopy, Finset.mem_image] at hx
  obtain ⟨⟨a, _, rfl⟩, ⟨b, _, h⟩⟩ := hx
  exact Sum.inl_ne_inr h.symm

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

    Proof structure (Sophie PA-22E953):
    • r ≤ 1: no mixed r-sets exist (proved), so F = ∅, and any w works.
    • r ≥ 2: Partition F = ⋃_{k=1}^{r-1} F_k where F_k = {S ∈ F : |left(S)| = k}.
      For each k, right-project F_k to get an intersecting (r-k)-family in G.
      By IsREKR G (r-k), |right-projection(F_k)| ≤ |star_v G (r-k)| (some v).
      By uniform stars, use the SAME v for all k.
      |F_k| ≤ |indepRSets G k| × |star_v G (r-k)| (injectivity of left/right split).
      Summing: |F| ≤ Σ_{k=1}^{r-1} |indepRSets G k| × |star_v G (r-k)| = |star_{inr v}(G⊔G, r)|
      (using the star identity lemma). -/
theorem case3_mixed [Nonempty V] (G : SimpleGraph V) (r : ℕ)
    (F : Finset (Finset (V ⊕ V)))
    (hF : F ⊆ indepRSets (disjointUnionSelf G) r)
    (hInt : IsIntersecting F)
    (hMixed : ∀ s ∈ F,
      (∀ t : Finset V, s ≠ leftCopy t) ∧ (∀ t : Finset V, s ≠ rightCopy t))
    (hUnif : HasUniformStars (disjointUnionSelf G) r)
    -- Additional hypotheses needed for r ≥ 2:
    -- G is k-EKR for all 0 < k < r (with the standard bound 2k ≤ μ(G)).
    (hEKRlt : ∀ k, 0 < k → k < r → IsREKR G k)
    -- G has uniform k-stars for all k (holds when G is vertex-transitive).
    (hUnifG : ∀ k, HasUniformStars G k) :
    ∃ w : V ⊕ V, F.card ≤ (vertexStar (disjointUnionSelf G) w r).card := by
  -- Fix a canonical reference vertex from the Nonempty instance.
  let v₀ : V := Classical.choice inferInstance
  -- We will show the bound holds for w = Sum.inr v₀.
  refine ⟨Sum.inr v₀, ?_⟩
  -- Split on whether F is non-empty.
  by_cases hFne : F.Nonempty
  · -- F is non-empty: extract S₀ to constrain r.
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
    -- For r ≥ 2, use the partition-and-bound argument.
    simp only [not_le] at hr
    have hr2 : 2 ≤ r := hr
    -- Partition F by left-part size: F_k = {S ∈ F : |leftPreimage S| = k}.
    -- For mixed sets, the left-part size k satisfies 1 ≤ k ≤ r - 1.
    -- Define the k-th slice of F.
    let Fk (k : ℕ) : Finset (Finset (V ⊕ V)) := F.filter (fun S => (leftPreimage S).card = k)
    -- ⚠ WARNING (Sophie Round 15, DA-TERM07 + DA-F614RE): The termwise bound below is FALSE.
    --
    -- WHAT FAILS: hFk_bound claims |F_k| ≤ |I^k(G)| × |star_v₀(G, r-k)| for each k.
    -- This fails because F_k can be a LEFT-STAR (all L_S contain some common vertex a),
    -- which is intersecting via L_S alone. Then R_S ranges freely over all of I^{r-k}(G),
    -- giving |F_k| = |star_a(G,k)| × |I^{r-k}(G)|, which can greatly exceed |I^k|×|star_v₀(G,r-k)|.
    -- Concrete: G=K₆^c, r=3, k=2, 2r=μ(G)=6 ✓: left-star |F₂|=30 > bound 15×1=15. ✗
    --
    -- WHAT DOES HOLD (Complementary Slice Coupling, SP-CPLNG2):
    -- The PAIRED bound (k and r-k slices together) holds tightly:
    --   |F_k| + |F_{r-k}| ≤ |I^k(G)|×|star_v₀(G,r-k)| + |I^{r-k}(G)|×|star_v₀(G,k)|
    -- This is the size of the combined (k,r-k) contribution to star_{inr v₀}(G⊔G, r).
    -- Computationally verified (tight, with equality) for K_n^c n≤7, C_n n≤9, r≤4.
    --
    -- WHY: F_k and F_{r-k} are CROSS-INTERSECTING (F is intersecting, left and right parts
    -- both live in G). When F_k uses the left-star structure to be large, the cross-intersection
    -- constraint forces F_{r-k} to use only those T where R_T intersects every L_S — a
    -- severe restriction that reduces |F_{r-k}| by exactly the amount |F_k| gained.
    -- The extremal family achieving equality is: F_k = {S : v₀ ∈ R_S} and F_{r-k} = {T : v₀ ∈ R_T},
    -- i.e., both slices are the corresponding slices of star_{inr v₀}(G⊔G, r).
    --
    -- A CORRECT PROOF of the all-mixed case should instead show:
    --   (Step 1) For each complementary pair (k, r-k), prove the coupled bound above.
    --   (Step 2) Sum over k = 1..⌊r/2⌋ (plus the k=r/2 term when r is even) to get:
    --              |F| ≤ Σ_{k=1}^{r-1} |I^k|×|star_v₀(G,r-k)|
    --            which by star_inr_card_eq equals |star_{inr v₀}(G⊔G,r)| - |star_v₀(G,r)|.
    -- The sorry below retains the (false) termwise statement to preserve proof structure.
    -- TODO: Replace hFk_bound with the coupled version to unblock this proof.
    have hFk_bound : ∀ k ∈ Finset.Icc 1 (r - 1),
        (Fk k).card ≤ (indepRSets G k).card * (vertexStar G v₀ (r - k)).card := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      sorry  -- ⚠ STATEMENT IS FALSE — see DA-TERM07/DA-F614RE (R15). Replace with SP-CPLNG2.
    -- Partition: |F| = Σ_{k=1}^{r-1} |F_k|, since all sets are mixed with left-parts in 1..r-1.
    have hpartition : F.card = ∑ k ∈ Finset.Icc 1 (r - 1), (Fk k).card := by
      -- Step 1: each S ∈ F has (leftPreimage S).card ∈ Icc 1 (r-1).
      have hmem : ∀ S ∈ F, (leftPreimage S).card ∈ Finset.Icc 1 (r - 1) := by
        intro S hSF
        simp only [Finset.mem_Icc]
        have hSindep := hF hSF
        rw [mem_indepRSets_iff] at hSindep
        obtain ⟨hcard, _⟩ := hSindep
        have hMixS := hMixed S hSF
        have hdecomp := leftCopy_leftPreimage_union_rightCopy_rightPreimage S
        have hlrcard : r = (leftPreimage S).card + (rightPreimage S).card := by
          rw [← hcard]; exact card_eq_left_plus_right S
        constructor
        · -- 1 ≤ (leftPreimage S).card: if = 0, then S = rightCopy (...), contradiction.
          by_contra hlt
          simp only [not_le, Nat.lt_one_iff] at hlt
          have hLempty : leftPreimage S = ∅ := Finset.card_eq_zero.mp hlt
          have hSeqR : S = rightCopy (rightPreimage S) := by
            have h := hdecomp; rw [hLempty] at h
            simp only [leftCopy, Finset.image_empty, Finset.empty_union] at h; exact h
          exact absurd hSeqR (hMixS.2 (rightPreimage S))
        · -- (leftPreimage S).card ≤ r - 1: if ≥ r, then S = leftCopy (...), contradiction.
          by_contra hlt
          simp only [not_le] at hlt
          have hkr : (leftPreimage S).card = r := by omega
          have hRempty : rightPreimage S = ∅ := by
            apply Finset.card_eq_zero.mp; omega
          have hSeqL : S = leftCopy (leftPreimage S) := by
            have h := hdecomp; rw [hRempty] at h
            simp only [rightCopy, Finset.image_empty, Finset.union_empty] at h; exact h
          exact absurd hSeqL (hMixS.1 (leftPreimage S))
      -- Step 2: F = biUnion(Icc 1 (r-1), Fk).
      have hF_eq : F = (Finset.Icc 1 (r - 1)).biUnion Fk := by
        ext S
        simp only [Fk, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter]
        constructor
        · intro hS; exact ⟨(leftPreimage S).card, Finset.mem_Icc.mp (hmem S hS), hS, rfl⟩
        · rintro ⟨_, _, hS, _⟩; exact hS
      -- Step 3: disjoint parts (Fk k and Fk j are disjoint for k ≠ j).
      have hdisj : ∀ i ∈ Finset.Icc 1 (r - 1), ∀ j ∈ Finset.Icc 1 (r - 1),
          i ≠ j → Disjoint (Fk i) (Fk j) := by
        intro i _ j _ hij
        apply Finset.disjoint_left.mpr
        intro S
        simp only [Fk, Finset.mem_filter]
        rintro ⟨_, hSi⟩ ⟨_, hSj⟩; exact hij (hSi.symm.trans hSj)
      rw [hF_eq, Finset.card_biUnion hdisj]
    -- Apply the bound for each k and sum.
    calc F.card
        = ∑ k ∈ Finset.Icc 1 (r - 1), (Fk k).card := hpartition
      _ ≤ ∑ k ∈ Finset.Icc 1 (r - 1),
            (indepRSets G k).card * (vertexStar G v₀ (r - k)).card := by
          gcongr with k hk; exact hFk_bound k hk
      _ ≤ (vertexStar (disjointUnionSelf G) (Sum.inr v₀) r).card := by
          rw [star_inr_card_eq G v₀ r]; exact Nat.le_add_left _ _
  · -- F is empty: trivially 0 ≤ any star.
    simp only [Finset.not_nonempty_iff_eq_empty] at hFne
    exact hFne ▸ Nat.zero_le _

/-! ## μ(G ⊔ G) = 2μ(G) -/

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

/-- **H ⊔ H is r-EKR for vertex-transitive H** (Sophie Rounds 9–14).

    FULLY PROVED cases (no sorry):
    • Case 1: F all-pure-right  → bijection to H, apply IsREKR.
    • Case 2: F all-pure-left   → symmetric.
    • Case 3a (impossible): F has a pure-left AND a pure-right member → contradiction,
      since leftCopy s ∩ rightCopy t = ∅, so they cannot meet (not_both_pureCopies_intersecting).

    OPEN (sorry — remaining gaps):
    • Case 3b: F has pure-right + mixed sets (no pure-left):
        Needs IsStrictlyREKR G r to force a common right-copy vertex via PA-1B87CB.
    • Case 3b': F has pure-left + mixed sets (no pure-right): symmetric.
    • Case 3c (all-mixed): proved up to hFk_bound sorry:
        |F_k| ≤ |I^k(G)| × |star_v₀(G, r-k)| for each split type k.
        Needs cross-intersecting EKR (SP-EFF503 in Sophie knowledge base).

    Additional hypotheses (needed for Case 3c structure):
    - hEKRlt: G is k-EKR for all 0 < k < r
    - hUnifG: G has uniform k-stars for all k (follows from vertex-transitivity)
    - hUnif:  G⊔G has uniform r-stars (follows from vertex-transitivity) -/
theorem disjointUnion_rEKR_vertexTransitive (G : SimpleGraph V) (r : ℕ)
    (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ mu G)
    (hEKR : IsREKR G r)
    (hEKRlt : ∀ k, 0 < k → k < r → IsREKR G k)
    (hUnifG : ∀ k, HasUniformStars G k)
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
      · -- Case 3a: F has some pure-right sets [hSomeR] and is neither all-pure-right
        --   nor all-pure-left. F may also have pure-left or mixed sets.
        --   • Sub-case: F has BOTH a pure-left and a pure-right member.
        --     Then leftCopy s ∩ rightCopy t = ∅ (disjoint ranges in V⊕V), so they
        --     can't intersect — contradicting hInt. Close this sub-case.
        --   • Sub-case: F has pure-right and mixed (no pure-left) — genuinely open.
        --     This is the common-vertex argument: need that the pure-right subfamily
        --     forces all mixed sets to share a specific right-copy vertex.
        --     Requires IsStrictlyREKR G r (each max intersecting family = a star).
        obtain ⟨sR, hsFR, tR, rfl⟩ := hSomeR
        by_cases hSomeL' : ∃ sL ∈ F, ∃ tL : Finset V, sL = leftCopy tL
        · -- Sub-case: F has both a pure-left leftCopy tL and pure-right rightCopy tR.
          --   These cannot intersect — contradiction with hInt.
          obtain ⟨sL, hsFL, tL, rfl⟩ := hSomeL'
          exact absurd (not_both_pureCopies_intersecting F hInt hsFL hsFR) id
        · -- Sub-case: F has pure-right [hsFR] and no pure-left sets [hSomeL' fails].
          --   All non-pure-right members of F are mixed.
          --   Open: show every mixed S ∈ F shares a right-copy vertex with all
          --   pure-right sets in F (common-vertex argument, needs IsStrictlyREKR G r).
          sorry  -- [OPEN] pure-right + mixed case: needs IsStrictlyREKR G r
      · -- Case 3b: F has some pure-left sets [hSomeL] and no pure-right sets
        --   [¬hSomeR holds via the outer by_cases].
        --   All non-pure-left members of F are mixed.
        --   Open: symmetric common-vertex argument for pure-left + mixed.
        by_cases hSomeL : ∃ s ∈ F, ∃ t : Finset V, s = leftCopy t
        · sorry  -- [OPEN] pure-left + mixed case: needs IsStrictlyREKR G r (symmetric to 3a)
        · -- Case 3c: F has NO pure sets → all mixed.
          simp only [not_exists, not_and] at hSomeR hSomeL
          have hMixed : ∀ s ∈ F,
              (∀ t : Finset V, s ≠ leftCopy t) ∧ (∀ t : Finset V, s ≠ rightCopy t) :=
            fun s hs => ⟨hSomeL s hs, hSomeR s hs⟩
          exact case3_mixed G r F hF hInt hMixed hUnif hEKRlt hUnifG

/-- **H ⊔ H is r-EKR** (full theorem; Case 3 for general H still open). -/
theorem disjointUnion_rEKR (G : SimpleGraph V) (r : ℕ)
    (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ mu G)
    (hEKR : IsREKR G r) :
    IsREKR (disjointUnionSelf G) r := by
  sorry

/-! ## r=2 All-Mixed Case: Complete Proof (Sophie Round 20, PA-75F443)

  The key theorem: if F ⊆ I²(G⊔G) is intersecting and all-mixed (no pure-left
  or pure-right sets), then F is contained in some vertex star of G⊔G.

  Proof: pick any S₀ = {inl a₀, inr b₀} ∈ F.
  • Case A: every T ∈ F contains inl a₀ → F ⊆ star_{inl a₀}.
  • Case B: some T ∈ F doesn't contain inl a₀ → S₀ ∩ T ≠ ∅ forces d = b₀
    (inr b₀ ∈ T). Then for any U ∈ F: S₀∩U and T∩U together force inr b₀ ∈ U.
    So F ⊆ star_{inr b₀}.
  In either case F is a sub-star, giving |F| ≤ max star size.
-/


section AllMixedR2

variable (G : SimpleGraph V)

/-- For a mixed 2-IS S (not pure-left, not pure-right), the left and right preimages
    each have cardinality 1. -/
lemma mixed_2is_preimage_card (S : Finset (V ⊕ V))
    (hS : S ∈ indepRSets (disjointUnionSelf G) 2)
    (hnotL : ∀ t : Finset V, S ≠ leftCopy t)
    (hnotR : ∀ t : Finset V, S ≠ rightCopy t) :
    (leftPreimage S).card = 1 ∧ (rightPreimage S).card = 1 := by
  rw [mem_indepRSets_iff] at hS
  obtain ⟨hcard, _⟩ := hS
  have hlr : (leftPreimage S).card + (rightPreimage S).card = 2 := by
    have := card_eq_left_plus_right S; omega
  have hLpos : 0 < (leftPreimage S).card := by
    rcases Nat.eq_zero_or_pos (leftPreimage S).card with h | h
    · exfalso
      have hd := leftCopy_leftPreimage_union_rightCopy_rightPreimage S
      rw [Finset.card_eq_zero.mp h] at hd; simp [leftCopy] at hd
      exact hnotR _ hd
    · exact h
  have hRpos : 0 < (rightPreimage S).card := by
    rcases Nat.eq_zero_or_pos (rightPreimage S).card with h | h
    · exfalso
      have hd := leftCopy_leftPreimage_union_rightCopy_rightPreimage S
      rw [Finset.card_eq_zero.mp h] at hd; simp [rightCopy] at hd
      exact hnotL _ hd
    · exact h
  exact ⟨by omega, by omega⟩

/-- Each mixed 2-IS is a cross-pair {inl a, inr b}. -/
lemma mixed_2is_as_crossPair (S : Finset (V ⊕ V))
    (hS : S ∈ indepRSets (disjointUnionSelf G) 2)
    (hnotL : ∀ t : Finset V, S ≠ leftCopy t)
    (hnotR : ∀ t : Finset V, S ≠ rightCopy t) :
    ∃ a b : V, S = {Sum.inl a, Sum.inr b} := by
  obtain ⟨hL1, hR1⟩ := mixed_2is_preimage_card G S hS hnotL hnotR
  obtain ⟨a, hLa⟩ := Finset.card_eq_one.mp hL1
  obtain ⟨b, hRb⟩ := Finset.card_eq_one.mp hR1
  refine ⟨a, b, ?_⟩
  have hd := leftCopy_leftPreimage_union_rightCopy_rightPreimage S
  rw [hLa, hRb] at hd
  simp only [leftCopy, rightCopy, Finset.image_singleton] at hd
  rw [hd, ← Finset.insert_eq]

/-- When two cross-pairs intersect, they share a left or a right vertex. -/
private lemma crossPair_inter_eq (a b c d : V)
    (h : ({Sum.inl a, Sum.inr b} : Finset (V ⊕ V)) ∩ {Sum.inl c, Sum.inr d} |>.Nonempty) :
    a = c ∨ b = d := by
  obtain ⟨x, hx⟩ := h
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
  obtain ⟨h1 | h1, h2 | h2⟩ := hx
  · left;  exact Sum.inl_injective (h1.symm.trans h2)
  · exact absurd (h1.symm.trans h2) Sum.inl_ne_inr
  · exact absurd (h1.symm.trans h2) (Ne.symm Sum.inl_ne_inr)
  · right; exact Sum.inr_injective (h1.symm.trans h2)

/-- **r=2 All-Mixed Sub-star Theorem** (PA-75F443, Sophie Round 20):
    Any intersecting all-mixed 2-family in G⊔G is contained in some vertex star.

    Proof: Pick S₀ = {inl a₀, inr b₀} ∈ F.
    Case A: every T ∈ F contains inl a₀ → F ⊆ star_{inl a₀}.
    Case B: some T ∈ F has inl a₀ ∉ T → T = {inl c, inr b₀} (forced).
      For any U = {inl e, inr f}: if f ≠ b₀ then S₀∩U forces e=a₀; T∩U forces c=e=a₀,
      contradicting c≠a₀. Hence f=b₀ and F ⊆ star_{inr b₀}. -/
theorem allMixed_r2_sub_star [Nonempty V]
    (F : Finset (Finset (V ⊕ V)))
    (hF : F ⊆ indepRSets (disjointUnionSelf G) 2)
    (hInt : IsIntersecting F)
    (hMixed : ∀ s ∈ F,
      (∀ t : Finset V, s ≠ leftCopy t) ∧ (∀ t : Finset V, s ≠ rightCopy t)) :
    ∃ w : V ⊕ V, F ⊆ vertexStar (disjointUnionSelf G) w 2 := by
  rcases Finset.eq_empty_or_nonempty F with rfl | ⟨S₀, hS₀F⟩
  · exact ⟨Sum.inl (Classical.choice inferInstance), Finset.empty_subset _⟩
  obtain ⟨a₀, b₀, hS₀eq⟩ :=
    mixed_2is_as_crossPair G S₀ (hF hS₀F) (hMixed S₀ hS₀F).1 (hMixed S₀ hS₀F).2
  by_cases hCaseA : ∀ T ∈ F, Sum.inl a₀ ∈ T
  · -- Case A: F ⊆ star_{inl a₀}
    exact ⟨Sum.inl a₀, fun T hTF => by
      rw [mem_vertexStar_iff]; exact ⟨hF hTF, hCaseA T hTF⟩⟩
  · -- Case B: some T ∈ F has inl a₀ ∉ T
    push_neg at hCaseA
    obtain ⟨T, hTF, hTnotA⟩ := hCaseA
    obtain ⟨c, d, hTeq⟩ :=
      mixed_2is_as_crossPair G T (hF hTF) (hMixed T hTF).1 (hMixed T hTF).2
    have hcne : c ≠ a₀ := by
      intro h; apply hTnotA; rw [hTeq, h]; simp
    -- S₀ ∩ T ≠ ∅ forces d = b₀
    have hdB : d = b₀ := by
      have hST := hInt S₀ hS₀F T hTF
      rw [hS₀eq, hTeq] at hST
      rcases crossPair_inter_eq a₀ b₀ c d hST with h | h
      · exact absurd h.symm hcne
      · exact h.symm
    -- Every U ∈ F must contain inr b₀
    have hAllB : ∀ U ∈ F, Sum.inr b₀ ∈ U := by
      intro U hUF
      obtain ⟨e, f, hUeq⟩ :=
        mixed_2is_as_crossPair G U (hF hUF) (hMixed U hUF).1 (hMixed U hUF).2
      suffices hfb : f = b₀ by rw [hUeq]; simp [hfb]
      have hSU := hInt S₀ hS₀F U hUF
      rw [hS₀eq, hUeq] at hSU
      rcases crossPair_inter_eq a₀ b₀ e f hSU with haeq | hbeq
      · -- e = a₀; now use T ∩ U
        have hTU := hInt T hTF U hUF
        rw [hTeq, hUeq] at hTU
        rcases crossPair_inter_eq c d e f hTU with hceq | hdeq
        · -- c = e = a₀, contradicts c ≠ a₀
          exact absurd (hceq.trans haeq.symm) hcne
        · -- d = f, and d = b₀, so f = b₀
          exact hdeq.symm.trans hdB
      · exact hbeq.symm
    exact ⟨Sum.inr b₀, fun U hUF => by
      rw [mem_vertexStar_iff]; exact ⟨hF hUF, hAllB U hUF⟩⟩

/-- **r=2 All-Mixed Bound** (PA-75F443):
    An intersecting all-mixed 2-family in G⊔G satisfies |F| ≤ |star_w| for some w.
    This fully proves the all-mixed sub-case without any sorry. -/
theorem allMixed_r2_bound [Nonempty V]
    (F : Finset (Finset (V ⊕ V)))
    (hF : F ⊆ indepRSets (disjointUnionSelf G) 2)
    (hInt : IsIntersecting F)
    (hMixed : ∀ s ∈ F,
      (∀ t : Finset V, s ≠ leftCopy t) ∧ (∀ t : Finset V, s ≠ rightCopy t)) :
    ∃ w : V ⊕ V, F.card ≤ (vertexStar (disjointUnionSelf G) w 2).card := by
  obtain ⟨w, hw⟩ := allMixed_r2_sub_star G F hF hInt hMixed
  exact ⟨w, Finset.card_le_card hw⟩

end AllMixedR2
