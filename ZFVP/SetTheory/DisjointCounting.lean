import ZFVP.SetTheory.NullSets

/-! Counting pairwise disjoint large subsets of a finite set: if `N` pairwise disjoint subsets of
`Y` each satisfy `X_j × 2^m ≰# Y` (each has more than `|Y| / 2^m` elements), then `N ≤# 2^m`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem not_insert_fresh_cardLE {A p : V} (hA : IsInternallyFinite A) (hp : p ∉ A) : ¬ insert p A ≤# A := by
  obtain ⟨n, hn, hAn⟩ := hA
  intro h
  have h2 : insert n n ≤# insert p A := cardLE_insert_fresh hAn.ge (mem_irrefl n) hp
  have : succ n ≤# n := by
    have := (h2.trans h).trans hAn.le
    simpa only [succ] using this
  exact not_succ_cardLE_self hn this

/-- If `A` does not fit into `B` (both finite), then `B` with a fresh point fits into `A`. -/
theorem insert_self_cardLE_of_not_cardLE {A B : V} (hA : IsInternallyFinite A) (hB : IsInternallyFinite B)
    (h : ¬ A ≤# B) : insert B B ≤# A := by
  obtain ⟨a, ha, hAa⟩ := hA
  obtain ⟨b, hb, hBb⟩ := hB
  have : IsOrdinal a := IsOrdinal.nat ha
  have : IsOrdinal b := IsOrdinal.nat hb
  have hab : ¬ a ⊆ b := fun hab ↦ h (hAa.le.trans ((cardLE_of_subset hab).trans hBb.ge))
  have hba : b ∈ a := by
    rcases IsOrdinal.subset_or_supset (α := a) (β := b) with h' | h'
    · exact (hab h').elim
    · rcases (IsOrdinal.subset_iff (α := b) (β := a)).mp h' with rfl | h''
      · exact (hab (fun x hx ↦ hx)).elim
      · exact h''
  have hsucc : succ b ⊆ a := by
    intro x hx
    rcases mem_succ_iff.mp hx with rfl | hx
    · exact hba
    · exact IsOrdinal.toIsTransitive.mem_trans hx hba
  have h1 : insert B B ≤# insert b b := cardLE_insert_fresh hBb.le (mem_irrefl B) (mem_irrefl b)
  have h2 : insert b b ≤# a := by
    have := cardLE_of_subset hsucc
    simpa only [succ] using this
  exact h1.trans (h2.trans hAa.ge)

/-- The pairs `(j, x)` with `x ∈ X j`. -/
def SigmaRel (X p : V) : Prop := kpair.π₂ p ∈ X ‘ (kpair.π₁ p)

instance sigmaRel_definable (X : V) : ℒₛₑₜ-predicate[V] (SigmaRel X) := by
  unfold SigmaRel
  definability

/-- The injections from `Y'` into `X j × 2^m`. -/
noncomputable def injectionSet (X m Y' j : V) : V :=
  {g ∈ ((X ‘ j) ×ˢ (((2 : ℕ) : V) ^ m)) ^ Y' ; Injective g}

instance injectionSet_definable (X m Y' : V) : ℒₛₑₜ-function₁[V] (injectionSet X m Y') := by
  have h : ℒₛₑₜ-relation (fun C j : V ↦ ∀ g, g ∈ C ↔
      g ∈ ((X ‘ j) ×ˢ (((2 : ℕ) : V) ^ m)) ^ Y' ∧ Injective g) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = injectionSet X m Y' (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [injectionSet, mem_sep_iff]

theorem mem_injectionSet_iff (X m Y' j g : V) :
    g ∈ injectionSet X m Y' j ↔ g ∈ ((X ‘ j) ×ˢ (((2 : ℕ) : V) ^ m)) ^ Y' ∧ Injective g :=
  mem_sep_iff

/-- The graph of the combined injection `(j, w) ↦ (j, g_j w)`. -/
def CombinedInjRel (c X m Y' q : V) : Prop :=
  ∃ j w, kpair.π₁ q = ⟨j, w⟩ₖ ∧
    kpair.π₂ q = ⟨⟨j, kpair.π₁ ((c ‘ (injectionSet X m Y' j)) ‘ w)⟩ₖ, kpair.π₂ ((c ‘ (injectionSet X m Y' j)) ‘ w)⟩ₖ

instance combinedInjRel_definable (c X m Y' : V) : ℒₛₑₜ-predicate[V] (CombinedInjRel c X m Y') := by
  unfold CombinedInjRel
  definability

/-- Pairwise disjoint subsets of `Y` of relative size more than `2^{-m}` number at most `2^m`. -/
theorem disjoint_family_cardLE (hAC : InternalChoice V) {N Y m X : V} (hN : N ∈ (ω : V))
    (hY : IsInternallyFinite Y) (hm : m ∈ (ω : V)) (hX : X ∈ (℘ Y) ^ N)
    (hdisj : ∀ j ∈ N, ∀ j' ∈ N, j ≠ j' → ∀ x, x ∈ X ‘ j → x ∈ X ‘ j' → False)
    (hbig : ∀ j ∈ N, ¬ (X ‘ j) ×ˢ (((2 : ℕ) : V) ^ m) ≤# Y) : N ≤# ((2 : ℕ) : V) ^ m := by
  have hXf : IsFunction X := IsFunction.of_mem hX
  have hXj : ∀ j ∈ N, X ‘ j ⊆ Y := fun j hj ↦ mem_power_iff.mp (function_value_mem hX hj)
  have h2m : IsInternallyFinite (((2 : ℕ) : V) ^ m) := internallyFinite_two_pow hm
  -- the sum set
  obtain ⟨S₀, hSdef⟩ : ∃ S : V, S = sep (N ×ˢ Y) (SigmaRel X) (sigmaRel_definable X) := ⟨_, rfl⟩
  have hSmem : ∀ j x, ⟨j, x⟩ₖ ∈ S₀ ↔ j ∈ N ∧ x ∈ X ‘ j := by
    intro j x
    rw [hSdef, mem_sep_iff, kpair_mem_iff]
    unfold SigmaRel
    rw [kpair.π₁_kpair, kpair.π₂_kpair]
    constructor
    · rintro ⟨⟨hj, -⟩, hx⟩
      exact ⟨hj, hx⟩
    · rintro ⟨hj, hx⟩
      exact ⟨⟨hj, hXj j hj x hx⟩, hx⟩
  have hSpairs : ∀ p ∈ S₀, ∃ j x, p = ⟨j, x⟩ₖ := by
    intro p hp
    rw [hSdef] at hp
    obtain ⟨j, -, x, -, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hp).1
    exact ⟨j, x, rfl⟩
  have hSY : S₀ ≤# Y := by
    refine cardLE_of_injective_map kpair.π₂ pi2_definable ?_ ?_
    · intro p hp
      obtain ⟨j, x, rfl⟩ := hSpairs p hp
      rw [kpair.π₂_kpair]
      obtain ⟨hj, hx⟩ := (hSmem j x).mp hp
      exact hXj j hj x hx
    · intro p hp p' hp' h
      obtain ⟨j, x, rfl⟩ := hSpairs p hp
      obtain ⟨j', x', rfl⟩ := hSpairs p' hp'
      simp only [kpair.π₂_kpair] at h
      subst h
      obtain ⟨hj, hx⟩ := (hSmem j x).mp hp
      obtain ⟨hj', hx'⟩ := (hSmem j' x).mp hp'
      by_contra hne
      exact hdisj j hj j' hj' (fun h ↦ hne (by rw [h])) x hx hx'
  -- the fresh point and the injections
  obtain ⟨Y', hY'def⟩ : ∃ Y' : V, Y' = insert Y Y := ⟨_, rfl⟩
  have hinjne : ∀ j ∈ N, IsNonempty (injectionSet X m Y' j) := by
    intro j hj
    have hfin : IsInternallyFinite ((X ‘ j) ×ˢ (((2 : ℕ) : V) ^ m)) :=
      internallyFinite_prod (internallyFinite_subset hY (hXj j hj)) h2m
    obtain ⟨g, hg, hgi⟩ := insert_self_cardLE_of_not_cardLE hfin hY (hbig j hj)
    rw [← hY'def] at hg
    exact ⟨g, (mem_injectionSet_iff _ _ _ _ _).mpr ⟨hg, hgi⟩⟩
  obtain ⟨ℐ, hℐdef⟩ : ∃ I : V, I = repl (injectionSet X m Y') (injectionSet_definable X m Y') N := ⟨_, rfl⟩
  obtain ⟨c, -, hcval⟩ := hAC ℐ (fun I hI ↦ by
    rw [hℐdef] at hI
    obtain ⟨j, hj, rfl⟩ := (repl_spec (injectionSet_definable X m Y')).mp hI
    exact hinjne j hj)
  have hg : ∀ j ∈ N, c ‘ (injectionSet X m Y' j) ∈ injectionSet X m Y' j := fun j hj ↦
    hcval _ (by rw [hℐdef]; exact (repl_spec (injectionSet_definable X m Y')).mpr ⟨j, hj, rfl⟩)
  have hgfun : ∀ j ∈ N, c ‘ (injectionSet X m Y' j) ∈ ((X ‘ j) ×ˢ (((2 : ℕ) : V) ^ m)) ^ Y' :=
    fun j hj ↦ ((mem_injectionSet_iff _ _ _ _ _).mp (hg j hj)).1
  have hginj : ∀ j ∈ N, Injective (c ‘ (injectionSet X m Y' j)) :=
    fun j hj ↦ ((mem_injectionSet_iff _ _ _ _ _).mp (hg j hj)).2
  -- the combined injection `N × Y' → Σ × 2^m`
  obtain ⟨G, hGdef⟩ : ∃ G : V, G = sep ((N ×ˢ Y') ×ˢ (S₀ ×ˢ (((2 : ℕ) : V) ^ m))) (CombinedInjRel c X m Y')
    (combinedInjRel_definable c X m Y') := ⟨_, rfl⟩
  have hval : ∀ j ∈ N, ∀ w ∈ Y', (c ‘ (injectionSet X m Y' j)) ‘ w ∈ (X ‘ j) ×ˢ (((2 : ℕ) : V) ^ m) :=
    fun j hj w hw ↦ function_value_mem (hgfun j hj) hw
  have hGmem : ∀ j w q, ⟨⟨j, w⟩ₖ, q⟩ₖ ∈ G ↔ j ∈ N ∧ w ∈ Y' ∧
      q = ⟨⟨j, kpair.π₁ ((c ‘ (injectionSet X m Y' j)) ‘ w)⟩ₖ, kpair.π₂ ((c ‘ (injectionSet X m Y' j)) ‘ w)⟩ₖ := by
    intro j w q
    rw [hGdef, mem_sep_iff, kpair_mem_iff, kpair_mem_iff]
    unfold CombinedInjRel
    rw [kpair.π₁_kpair, kpair.π₂_kpair]
    constructor
    · rintro ⟨⟨⟨hj, hw⟩, -⟩, j', w', hjw, hq⟩
      obtain ⟨rfl, rfl⟩ := kpair_inj hjw
      exact ⟨hj, hw, hq⟩
    · rintro ⟨hj, hw, rfl⟩
      obtain ⟨a, ha, b, hb, hab⟩ := mem_prod_iff.mp (hval j hj w hw)
      refine ⟨⟨⟨hj, hw⟩, kpair_mem_iff.mpr ⟨?_, ?_⟩⟩, j, w, rfl, rfl⟩
      · rw [hab, kpair.π₁_kpair]
        exact (hSmem j a).mpr ⟨hj, ha⟩
      · rw [hab, kpair.π₂_kpair]
        exact hb
  have hGpairs : ∀ p ∈ G, ∃ j w q, p = ⟨⟨j, w⟩ₖ, q⟩ₖ := by
    intro p hp
    rw [hGdef] at hp
    obtain ⟨r, hr, q, -, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hp).1
    obtain ⟨j, -, w, -, rfl⟩ := mem_prod_iff.mp hr
    exact ⟨j, w, q, rfl⟩
  have hG : N ×ˢ Y' ≤# S₀ ×ˢ (((2 : ℕ) : V) ^ m) := by
    refine ⟨G, ?_, ?_⟩
    · rw [mem_function_iff]
      refine ⟨fun p hp ↦ by rw [hGdef] at hp; exact (mem_sep_iff.mp hp).1, fun r hr ↦ ?_⟩
      obtain ⟨j, hj, w, hw, rfl⟩ := mem_prod_iff.mp hr
      refine ⟨_, (hGmem j w _).mpr ⟨hj, hw, rfl⟩, fun q hq ↦ ((hGmem j w q).mp hq).2.2⟩
    · intro r r' q h h'
      obtain ⟨j, w, q₁, he⟩ := hGpairs _ h
      obtain ⟨hr, hq⟩ := kpair_inj he
      obtain ⟨j', w', q₂, he'⟩ := hGpairs _ h'
      obtain ⟨hr', hq'⟩ := kpair_inj he'
      rw [hr] at h ⊢
      rw [hr'] at h' ⊢
      obtain ⟨hj, hw, hqeq⟩ := (hGmem j w _).mp h
      obtain ⟨hj', hw', heq⟩ := (hGmem j' w' _).mp h'
      rw [hqeq] at heq
      obtain ⟨h1, h2⟩ := kpair_inj heq
      obtain ⟨hjj', h3⟩ := kpair_inj h1
      subst hjj'
      have hvv : (c ‘ (injectionSet X m Y' j)) ‘ w' = (c ‘ (injectionSet X m Y' j)) ‘ w := by
        obtain ⟨a, -, b, -, hab⟩ := mem_prod_iff.mp (hval j hj w hw)
        obtain ⟨a', -, b', -, hab'⟩ := mem_prod_iff.mp (hval j hj w' hw')
        rw [hab, hab'] at h3 h2 ⊢
        simp only [kpair.π₁_kpair, kpair.π₂_kpair] at h3 h2
        rw [h3, h2]
      have := injective_value_eq (hgfun j hj) (hginj j hj) hw' hw hvv
      rw [this]
  have hYfin' : IsInternallyFinite Y' := by rw [hY'def]; exact internallyFinite_insert hY Y
  by_contra hcon
  have hNfin : IsInternallyFinite N := ⟨N, hN, CardEQ.refl N⟩
  have h1 : insert (((2 : ℕ) : V) ^ m) (((2 : ℕ) : V) ^ m) ≤# N := insert_self_cardLE_of_not_cardLE hNfin h2m hcon
  have h2 : insert (((2 : ℕ) : V) ^ m) (((2 : ℕ) : V) ^ m) ×ˢ Y' ≤# (((2 : ℕ) : V) ^ m) ×ˢ Y :=
    (prod_cardLE_prod h1 (CardLE.refl _)).trans (hG.trans ((prod_cardLE_prod hSY (CardLE.refl _)).trans
      (prod_comm_cardLE _ _)))
  have h3 : insert ⟨((2 : ℕ) : V) ^ m, Y⟩ₖ ((((2 : ℕ) : V) ^ m) ×ˢ Y) ⊆
      insert (((2 : ℕ) : V) ^ m) (((2 : ℕ) : V) ^ m) ×ˢ Y' := by
    intro z hz
    rw [hY'def]
    rcases mem_insert.mp hz with rfl | hz
    · exact kpair_mem_iff.mpr ⟨mem_insert.mpr (Or.inl rfl), mem_insert.mpr (Or.inl rfl)⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
      exact kpair_mem_iff.mpr ⟨mem_insert.mpr (Or.inr ha), mem_insert.mpr (Or.inr hb)⟩
  have hfresh : ⟨((2 : ℕ) : V) ^ m, Y⟩ₖ ∉ (((2 : ℕ) : V) ^ m) ×ˢ Y := by
    intro h
    exact mem_irrefl _ (kpair_mem_iff.mp h).1
  exact not_insert_fresh_cardLE (internallyFinite_prod h2m hY) hfresh ((cardLE_of_subset h3).trans h2)

end ZFVP
