import ZFVP.SetTheory.NaturalPigeonhole
import ZFVP.SetTheory.FiniteSets
import ZFVP.SetTheory.FiniteSequencesCardinality
import ZFVP.SetTheory.UltrafilterOrdinals
import ZFVP.SetTheory.SplittingScheme
import ZFVP.SetTheory.FunctionValue

/-! Finite cardinal arithmetic at the level of sets: tagged disjoint unions, commutativity and
associativity of products up to `≤#`, `2^(n+1) ≋ 2^n × 2`, finiteness of products and of `2^n`,
comparability of finite sets, and the halving lemma `A × 2 ≤# C → B × 2 ≤# C → A ∪ B ≤# C` for
finite `A`, `B`, which underlies subadditivity of the coded Lebesgue measure. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An injective definable map gives a cardinality comparison. -/
theorem cardLE_of_injective_map {A B : V} (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hmaps : ∀ x ∈ A, F x ∈ B) (hinj : ∀ x ∈ A, ∀ y ∈ A, F x = F y → x = y) : A ≤# B := by
  refine ⟨definableGraph A F hF, definableGraph_mem_function_of_mapsTo A B F hF hmaps, ?_⟩
  intro x₁ x₂ y h₁ h₂
  obtain ⟨hx₁, he₁⟩ := (pair_mem_definableGraph_iff A F hF x₁ y).mp h₁
  obtain ⟨hx₂, he₂⟩ := (pair_mem_definableGraph_iff A F hF x₂ y).mp h₂
  exact hinj x₁ hx₁ x₂ hx₂ (he₁.symm.trans he₂)

/-- The tagged disjoint union `A × {0} ∪ B × {1}`. -/
noncomputable def disjointUnion (A B : V) : V := (A ×ˢ ({∅} : V)) ∪ (B ×ˢ ({succ (∅ : V)} : V))

theorem mem_disjointUnion_iff (A B z : V) :
    z ∈ disjointUnion A B ↔ (∃ a ∈ A, z = ⟨a, ∅⟩ₖ) ∨ ∃ b ∈ B, z = ⟨b, succ ∅⟩ₖ := by
  unfold disjointUnion
  rw [mem_union_iff, mem_prod_iff, mem_prod_iff]
  constructor
  · rintro (⟨a, ha, t, ht, rfl⟩ | ⟨b, hb, t, ht, rfl⟩)
    · rw [mem_singleton_iff] at ht
      exact Or.inl ⟨a, ha, by rw [ht]⟩
    · rw [mem_singleton_iff] at ht
      exact Or.inr ⟨b, hb, by rw [ht]⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact Or.inl ⟨a, ha, ∅, mem_singleton_iff.mpr rfl, rfl⟩
    · exact Or.inr ⟨b, hb, succ ∅, mem_singleton_iff.mpr rfl, rfl⟩

theorem succ_empty_ne_empty : (succ ∅ : V) ≠ ∅ := by
  intro h
  have : (∅ : V) ∈ succ ∅ := mem_succ_iff.mpr (Or.inl rfl)
  rw [h] at this
  exact not_mem_empty this

/-- Injections with disjoint domains and disjoint ranges combine. -/
theorem cardLE_union_of_disjoint {A B A' B' : V} (hAB : ∀ x, x ∈ A → x ∈ B → False)
    (hA'B' : ∀ y, y ∈ A' → y ∈ B' → False) (h1 : A ≤# A') (h2 : B ≤# B') : A ∪ B ≤# A' ∪ B' := by
  obtain ⟨f, hf, hfi⟩ := h1
  obtain ⟨g, hg, hgi⟩ := h2
  have hff : IsFunction f := IsFunction.of_mem hf
  have hgf : IsFunction g := IsFunction.of_mem hg
  have hfd : domain f = A := domain_eq_of_mem_function hf
  have hgd : domain g = B := domain_eq_of_mem_function hg
  have hfsub : f ⊆ A ×ˢ A' := (mem_function_iff.mp hf).1
  have hgsub : g ⊆ B ×ˢ B' := (mem_function_iff.mp hg).1
  refine ⟨f ∪ g, ?_, ?_⟩
  · rw [mem_function_iff]
    refine ⟨fun p hp ↦ ?_, fun x hx ↦ ?_⟩
    · rcases mem_union_iff.mp hp with hp | hp
      · exact prod_subset_prod_of_subset (fun z hz ↦ mem_union_iff.mpr (Or.inl hz))
          (fun z hz ↦ mem_union_iff.mpr (Or.inl hz)) p (hfsub p hp)
      · exact prod_subset_prod_of_subset (fun z hz ↦ mem_union_iff.mpr (Or.inr hz))
          (fun z hz ↦ mem_union_iff.mpr (Or.inr hz)) p (hgsub p hp)
    · rcases mem_union_iff.mp hx with hx | hx
      · refine ⟨f ‘ x, mem_union_iff.mpr (Or.inl (kpair_value_mem (by rw [hfd]; exact hx))), fun y hy ↦ ?_⟩
        rcases mem_union_iff.mp hy with hy | hy
        · exact (value_eq_of_kpair_mem hy).symm
        · exact (hAB x hx (kpair_mem_iff.mp (hgsub _ hy)).1).elim
      · refine ⟨g ‘ x, mem_union_iff.mpr (Or.inr (kpair_value_mem (by rw [hgd]; exact hx))), fun y hy ↦ ?_⟩
        rcases mem_union_iff.mp hy with hy | hy
        · exact (hAB x (kpair_mem_iff.mp (hfsub _ hy)).1 hx).elim
        · exact (value_eq_of_kpair_mem hy).symm
  · intro x₁ x₂ y h₁ h₂
    rcases mem_union_iff.mp h₁ with h₁ | h₁ <;> rcases mem_union_iff.mp h₂ with h₂ | h₂
    · exact hfi x₁ x₂ y h₁ h₂
    · exact (hA'B' y (kpair_mem_iff.mp (hfsub _ h₁)).2 (kpair_mem_iff.mp (hgsub _ h₂)).2).elim
    · exact (hA'B' y (kpair_mem_iff.mp (hfsub _ h₂)).2 (kpair_mem_iff.mp (hgsub _ h₁)).2).elim
    · exact hgi x₁ x₂ y h₁ h₂

/-- `A ∪ B ≤# A ⊔ B`. -/
theorem union_cardLE_disjointUnion (A B : V) : A ∪ B ≤# disjointUnion A B := by
  have he : A ∪ B = A ∪ (B \ A) := by
    apply mem_ext
    intro x
    rw [mem_union_iff, mem_union_iff, mem_sdiff_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · by_cases hA : x ∈ A
        · exact Or.inl hA
        · exact Or.inr ⟨h, hA⟩
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr h.1
  rw [he]
  unfold disjointUnion
  have h1 : A ≤# A ×ˢ ({∅} : V) := by
    refine cardLE_of_injective_map (fun x ↦ ⟨x, ∅⟩ₖ) (by definability) ?_ ?_
    · intro x hx
      exact kpair_mem_iff.mpr ⟨hx, mem_singleton_iff.mpr rfl⟩
    · intro x _ y _ h
      exact (kpair_inj h).1
  have h2 : B \ A ≤# B ×ˢ ({succ (∅ : V)} : V) := by
    refine cardLE_of_injective_map (fun x ↦ ⟨x, succ ∅⟩ₖ) (by definability) ?_ ?_
    · intro x hx
      exact kpair_mem_iff.mpr ⟨(mem_sdiff_iff.mp hx).1, mem_singleton_iff.mpr rfl⟩
    · intro x _ y _ h
      exact (kpair_inj h).1
  refine cardLE_union_of_disjoint (fun x hx hx' ↦ (mem_sdiff_iff.mp hx').2 hx) ?_ h1 h2
  intro z hz hz'
  obtain ⟨a, _, t, ht, rfl⟩ := mem_prod_iff.mp hz
  obtain ⟨b, _, t', ht', he'⟩ := mem_prod_iff.mp hz'
  rw [mem_singleton_iff] at ht ht'
  obtain ⟨-, hte⟩ := kpair_inj he'
  exact succ_empty_ne_empty (by rw [← ht', ← hte, ht])

theorem disjointUnion_cardLE {A B A' B' : V} (h1 : A ≤# A') (h2 : B ≤# B') :
    disjointUnion A B ≤# disjointUnion A' B' := by
  have h1' : A ×ˢ ({∅} : V) ≤# A' ×ˢ ({∅} : V) := prod_cardLE_prod h1 (CardLE.refl _)
  have h2' : B ×ˢ ({succ (∅ : V)} : V) ≤# B' ×ˢ ({succ (∅ : V)} : V) := prod_cardLE_prod h2 (CardLE.refl _)
  have hd : ∀ X Y : V, ∀ z, z ∈ X ×ˢ ({∅} : V) → z ∈ Y ×ˢ ({succ (∅ : V)} : V) → False := by
    intro X Y z hz hz'
    obtain ⟨a, _, t, ht, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨b, _, t', ht', he⟩ := mem_prod_iff.mp hz'
    rw [mem_singleton_iff] at ht ht'
    obtain ⟨-, hte⟩ := kpair_inj he
    exact succ_empty_ne_empty (by rw [← ht', ← hte, ht])
  exact cardLE_union_of_disjoint (hd A B) (hd A' B') h1' h2'

theorem disjointUnion_self_eq (A : V) : disjointUnion A A = A ×ˢ ((2 : ℕ) : V) := by
  apply mem_ext
  intro z
  rw [mem_disjointUnion_iff, mem_prod_iff]
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨a, ha, ∅, (mem_two_iff _).mpr (Or.inl rfl), rfl⟩
    · exact ⟨a, ha, succ ∅, (mem_two_iff _).mpr (Or.inr rfl), rfl⟩
  · rintro ⟨a, ha, i, hi, rfl⟩
    rcases (mem_two_iff i).mp hi with rfl | rfl
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩

theorem prod_comm_cardLE (A B : V) : A ×ˢ B ≤# B ×ˢ A := by
  refine cardLE_of_injective_map (fun z ↦ ⟨kpair.π₂ z, kpair.π₁ z⟩ₖ) (by definability) ?_ ?_
  · intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
    rw [kpair.π₁_kpair, kpair.π₂_kpair]
    exact kpair_mem_iff.mpr ⟨hb, ha⟩
  · intro z hz z' hz' h
    obtain ⟨a, _, b, _, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨a', _, b', _, rfl⟩ := mem_prod_iff.mp hz'
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at h
    obtain ⟨rfl, rfl⟩ := kpair_inj h
    rfl

theorem prod_assoc_cardLE (A B C : V) : (A ×ˢ B) ×ˢ C ≤# A ×ˢ (B ×ˢ C) := by
  refine cardLE_of_injective_map (fun z ↦ ⟨kpair.π₁ (kpair.π₁ z), ⟨kpair.π₂ (kpair.π₁ z), kpair.π₂ z⟩ₖ⟩ₖ)
    (by definability) ?_ ?_
  · intro z hz
    obtain ⟨p, hp, c, hc, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hp
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact kpair_mem_iff.mpr ⟨ha, kpair_mem_iff.mpr ⟨hb, hc⟩⟩
  · intro z hz z' hz' h
    obtain ⟨p, hp, c, _, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨a, _, b, _, rfl⟩ := mem_prod_iff.mp hp
    obtain ⟨p', hp', c', _, rfl⟩ := mem_prod_iff.mp hz'
    obtain ⟨a', _, b', _, rfl⟩ := mem_prod_iff.mp hp'
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at h
    obtain ⟨rfl, h2⟩ := kpair_inj h
    obtain ⟨rfl, rfl⟩ := kpair_inj h2
    rfl

theorem prod_assoc_cardLE' (A B C : V) : A ×ˢ (B ×ˢ C) ≤# (A ×ˢ B) ×ˢ C := by
  refine cardLE_of_injective_map (fun z ↦ ⟨⟨kpair.π₁ z, kpair.π₁ (kpair.π₂ z)⟩ₖ, kpair.π₂ (kpair.π₂ z)⟩ₖ)
    (by definability) ?_ ?_
  · intro z hz
    obtain ⟨a, ha, p, hp, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨b, hb, c, hc, rfl⟩ := mem_prod_iff.mp hp
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨ha, hb⟩, hc⟩
  · intro z hz z' hz' h
    obtain ⟨a, _, p, hp, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨b, _, c, _, rfl⟩ := mem_prod_iff.mp hp
    obtain ⟨a', _, p', hp', rfl⟩ := mem_prod_iff.mp hz'
    obtain ⟨b', _, c', _, rfl⟩ := mem_prod_iff.mp hp'
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at h
    obtain ⟨h1, rfl⟩ := kpair_inj h
    obtain ⟨rfl, rfl⟩ := kpair_inj h1
    rfl

/-- `2^n × 2 ≤# 2^(n+1)`, by appending a last value. -/
theorem prod_two_cardLE_function_power_succ (n : V) :
    (((2 : ℕ) : V) ^ n) ×ˢ ((2 : ℕ) : V) ≤# ((2 : ℕ) : V) ^ succ n := by
  refine cardLE_of_injective_map (fun z ↦ kpair.π₁ z ∪ {⟨n, kpair.π₂ z⟩ₖ}) (by definability) ?_ ?_
  · intro z hz
    obtain ⟨u, hu, i, hi, rfl⟩ := mem_prod_iff.mp hz
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    have husub : u ⊆ n ×ˢ ((2 : ℕ) : V) := (mem_function_iff.mp hu).1
    have hudom : domain u = n := domain_eq_of_mem_function hu
    rw [mem_function_iff]
    refine ⟨fun p hp ↦ ?_, fun x hx ↦ ?_⟩
    · rcases mem_union_iff.mp hp with hp | hp
      · exact prod_subset_prod_of_subset (fun z hz ↦ mem_succ_iff.mpr (Or.inr hz)) (fun z hz ↦ hz) p (husub p hp)
      · rw [mem_singleton_iff] at hp
        rw [hp]
        exact kpair_mem_iff.mpr ⟨mem_succ_iff.mpr (Or.inl rfl), hi⟩
    · rcases mem_succ_iff.mp hx with rfl | hx
      · refine ⟨i, mem_union_iff.mpr (Or.inr (mem_singleton_iff.mpr rfl)), fun y hy ↦ ?_⟩
        rcases mem_union_iff.mp hy with hy | hy
        · have hxd := mem_domain_of_kpair_mem hy
          rw [hudom] at hxd
          exact (mem_irrefl x hxd).elim
        · exact (kpair_inj (mem_singleton_iff.mp hy)).2
      · have : IsFunction u := IsFunction.of_mem hu
        refine ⟨u ‘ x, mem_union_iff.mpr (Or.inl (kpair_value_mem (by rw [hudom]; exact hx))), fun y hy ↦ ?_⟩
        rcases mem_union_iff.mp hy with hy | hy
        · exact (value_eq_of_kpair_mem hy).symm
        · obtain ⟨hxn, -⟩ := kpair_inj (mem_singleton_iff.mp hy)
          rw [hxn] at hx
          exact (mem_irrefl n hx).elim
  · intro z hz z' hz' h
    obtain ⟨u, hu, i, hi, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨u', hu', i', hi', rfl⟩ := mem_prod_iff.mp hz'
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at h
    have husub : u ⊆ n ×ˢ ((2 : ℕ) : V) := (mem_function_iff.mp hu).1
    have hu'sub : u' ⊆ n ×ˢ ((2 : ℕ) : V) := (mem_function_iff.mp hu').1
    have hmem : ∀ {v v' j j' : V}, v ⊆ n ×ˢ ((2 : ℕ) : V) → v ∪ {⟨n, j⟩ₖ} = v' ∪ {⟨n, j'⟩ₖ} → v ⊆ v' := by
      intro v v' j j' hv he p hp
      have : p ∈ v' ∪ {⟨n, j'⟩ₖ} := by rw [← he]; exact mem_union_iff.mpr (Or.inl hp)
      rcases mem_union_iff.mp this with h' | h'
      · exact h'
      · rw [mem_singleton_iff] at h'
        obtain ⟨a, ha, b, -, rfl⟩ := mem_prod_iff.mp (hv p hp)
        obtain ⟨han, -⟩ := kpair_inj h'
        cases han
        exact (mem_irrefl _ ha).elim
    have hii : i = i' := by
      have : ⟨n, i⟩ₖ ∈ u' ∪ {⟨n, i'⟩ₖ} := by rw [← h]; exact mem_union_iff.mpr (Or.inr (mem_singleton_iff.mpr rfl))
      rcases mem_union_iff.mp this with h' | h'
      · obtain ⟨a, ha, b, -, he⟩ := mem_prod_iff.mp (hu'sub _ h')
        obtain ⟨han, -⟩ := kpair_inj he
        cases han
        exact (mem_irrefl _ ha).elim
      · exact (kpair_inj (mem_singleton_iff.mp h')).2
    have huu : u = u' := SetTheory.subset_antisymm (hmem husub h) (hmem hu'sub h.symm)
    rw [huu, hii]

theorem function_power_succ_cardEQ (n : V) :
    (((2 : ℕ) : V) ^ succ n) ≋ ((((2 : ℕ) : V) ^ n) ×ˢ ((2 : ℕ) : V)) :=
  ⟨function_power_succ_cardLE ((2 : ℕ) : V) n, prod_two_cardLE_function_power_succ n⟩

theorem internallyFinite_two : IsInternallyFinite ((2 : ℕ) : V) :=
  ⟨_, ofNat_mem_ω 2, CardEQ.refl _⟩

theorem internallyFinite_prod {A B : V} (hA : IsInternallyFinite A) (hB : IsInternallyFinite B) :
    IsInternallyFinite (A ×ˢ B) := by
  apply internallyFinite_induction (fun B ↦ IsInternallyFinite (A ×ˢ B)) (by definability) ?_ ?_ B hB
  · have he : A ×ˢ (∅ : V) = ∅ := by
      apply mem_ext
      intro z
      simp only [not_mem_empty, iff_false]
      intro hz
      obtain ⟨_, _, _, hb, _⟩ := mem_prod_iff.mp hz
      exact not_mem_empty hb
    rw [he]
    exact internallyFinite_empty
  · intro C c ih
    have he : A ×ˢ insert c C = (A ×ˢ C) ∪ repl (fun a ↦ ⟨a, c⟩ₖ) (by definability) A := by
      apply mem_ext
      intro z
      rw [mem_union_iff, mem_prod_iff, mem_prod_iff, repl_spec]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        rcases mem_insert.mp hb with rfl | hb
        · exact Or.inr ⟨a, ha, rfl⟩
        · exact Or.inl ⟨a, ha, b, hb, rfl⟩
      · rintro (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩)
        · exact ⟨a, ha, b, mem_insert.mpr (Or.inr hb), rfl⟩
        · exact ⟨a, ha, c, mem_insert.mpr (Or.inl rfl), rfl⟩
    rw [he]
    exact internallyFinite_union ih (internallyFinite_repl _ _ hA)

theorem internallyFinite_two_pow {n : V} (hn : n ∈ (ω : V)) : IsInternallyFinite (((2 : ℕ) : V) ^ n) := by
  apply naturalNumber_induction (fun n ↦ IsInternallyFinite (((2 : ℕ) : V) ^ n)) (by definability) ?_ ?_ n hn
  · have h := function_power_zero_cardLE (A := ((2 : ℕ) : V)) (B := succ (∅ : V)) ⟨∅, mem_succ_iff.mpr (Or.inl rfl)⟩
    exact internallyFinite_of_cardLE_natural (ω_succ_closed zero_mem_ω) h
  · intro n _ ih
    exact internallyFinite_of_cardLE (internallyFinite_prod ih internallyFinite_two) (function_power_succ_cardLE _ _)

theorem finite_cardLE_total {A B : V} (hA : IsInternallyFinite A) (hB : IsInternallyFinite B) :
    A ≤# B ∨ B ≤# A := by
  obtain ⟨n, hn, hAn⟩ := hA
  obtain ⟨m, hm, hBm⟩ := hB
  have : IsOrdinal n := IsOrdinal.nat hn
  have : IsOrdinal m := IsOrdinal.nat hm
  rcases IsOrdinal.subset_or_supset (α := n) (β := m) with h | h
  · exact Or.inl (hAn.le.trans ((cardLE_of_subset h).trans hBm.ge))
  · exact Or.inr (hBm.le.trans ((cardLE_of_subset h).trans hAn.ge))

/-- The halving lemma: if `A × 2` and `B × 2` both fit into `C`, so does `A ∪ B`. -/
theorem union_cardLE_of_double {A B C : V} (hA : IsInternallyFinite A) (hB : IsInternallyFinite B)
    (h1 : A ×ˢ ((2 : ℕ) : V) ≤# C) (h2 : B ×ˢ ((2 : ℕ) : V) ≤# C) : A ∪ B ≤# C := by
  have hB2 : disjointUnion B B ≤# C := by rw [disjointUnion_self_eq]; exact h2
  have hA2 : disjointUnion A A ≤# C := by rw [disjointUnion_self_eq]; exact h1
  rcases finite_cardLE_total hA hB with h | h
  · exact (union_cardLE_disjointUnion A B).trans ((disjointUnion_cardLE h (CardLE.refl B)).trans hB2)
  · exact (union_cardLE_disjointUnion A B).trans ((disjointUnion_cardLE (CardLE.refl A) h).trans hA2)

end ZFVP
