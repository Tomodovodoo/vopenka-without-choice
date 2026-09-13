import ZFVP.SetTheory.FiniteSequences
import ZFVP.SetTheory.FinitePartialFunctions
import ZFVP.SetTheory.MeasuredWellFounded
import ZFVP.SetTheory.Rank

/-! The tree `A^{<ω}` of finite sequences ordered by reverse inclusion: its proper-initial-segment
relation is well-founded, compatibility is comparability, and incomparable sequences branch at a
common initial segment. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The tree order on finite sequences: `s ≤ t` when `s` extends `t`. -/
noncomputable def sequenceOrder (A : V) : V := reverseInclusionOrder (finiteSequences A)

theorem sequenceOrder_poset (A : V) : IsForcingPoset (finiteSequences A) (sequenceOrder A) :=
  reverseInclusionOrder_poset _

theorem pair_mem_sequenceOrder_iff (A s t : V) :
    ⟨s, t⟩ₖ ∈ sequenceOrder A ↔ s ∈ finiteSequences A ∧ t ∈ finiteSequences A ∧ t ⊆ s :=
  pair_mem_reverseInclusionOrder _ _ _

/-- The proper-initial-segment relation on finite sequences. -/
noncomputable def properSegmentRelation (A : V) : V :=
  {p ∈ finiteSequences A ×ˢ finiteSequences A ; kpair.π₁ p ⊆ kpair.π₂ p ∧ kpair.π₁ p ≠ kpair.π₂ p}

theorem pair_mem_properSegmentRelation_iff (A t s : V) :
    ⟨t, s⟩ₖ ∈ properSegmentRelation A ↔
      t ∈ finiteSequences A ∧ s ∈ finiteSequences A ∧ t ⊆ s ∧ t ≠ s := by
  simp only [properSegmentRelation, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair,
    and_assoc]

theorem sequence_domain_subset_of_subset {A s t n m : V} (hs : s ∈ A ^ n) (ht : t ∈ A ^ m)
    (h : t ⊆ s) : m ⊆ n := by
  intro x hx
  have hxt : ⟨x, t ‘ x⟩ₖ ∈ t := by
    have : IsFunction t := IsFunction.of_mem ht
    exact kpair_value_mem (by rw [domain_eq_of_mem_function ht]; exact hx)
  have := mem_domain_of_kpair_mem (h _ hxt)
  rwa [domain_eq_of_mem_function hs] at this

theorem sequence_eq_restrict_of_subset {A s t n m : V} (hs : s ∈ A ^ n) (ht : t ∈ A ^ m)
    (h : t ⊆ s) : t = s ↾ m := by
  have : IsFunction s := IsFunction.of_mem hs
  have : IsFunction t := IsFunction.of_mem ht
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, hx, y, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function ht p hp)
    exact kpair_mem_restrict_iff.mpr ⟨h _ hp, hx⟩
  · intro hp
    obtain ⟨hps, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
    have hxt : ⟨x, t ‘ x⟩ₖ ∈ t := kpair_value_mem (by rw [domain_eq_of_mem_function ht]; exact hx)
    have := IsFunction.unique (h _ hxt) hps
    rw [← this]
    exact hxt

theorem properSegmentRelation_wellFounded (A : V) :
    IsInternallyWellFounded (properSegmentRelation A) (finiteSequences A) := by
  apply projectedRank_internallyWellFounded _ _ (fun s ↦ domain s) (by definability)
  intro t ht s hs hts
  obtain ⟨_, _, hsub, hne⟩ := (pair_mem_properSegmentRelation_iff A t s).mp hts
  obtain ⟨n, hn, hsn⟩ := (mem_finiteSequences_iff A s).mp hs
  obtain ⟨m, hm, htm⟩ := (mem_finiteSequences_iff A t).mp ht
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have : IsOrdinal m := IsOrdinal.of_mem hm
  have hmn : m ⊆ n := sequence_domain_subset_of_subset hsn htm hsub
  rw [domain_eq_of_mem_function hsn, domain_eq_of_mem_function htm]
  apply rank_mem
  rcases IsOrdinal.subset_iff.mp hmn with h | h
  · exfalso
    apply hne
    have : IsFunction s := IsFunction.of_mem hsn
    rw [sequence_eq_restrict_of_subset hsn htm hsub, h]
    exact IsFunction.restrict_eq_self s n (by rw [domain_eq_of_mem_function hsn])
  · exact h

/-- Sequences are compatible in the tree order exactly when they are comparable. -/
theorem sequence_compatible_iff {A s t : V} (hs : s ∈ finiteSequences A) (ht : t ∈ finiteSequences A) :
    ForcingCompatible (finiteSequences A) (sequenceOrder A) s t ↔ s ⊆ t ∨ t ⊆ s := by
  constructor
  · rintro ⟨u, hu, hus, hut⟩
    obtain ⟨_, _, hsu⟩ := (pair_mem_sequenceOrder_iff A u s).mp hus
    obtain ⟨_, _, htu⟩ := (pair_mem_sequenceOrder_iff A u t).mp hut
    obtain ⟨k, hk, huk⟩ := (mem_finiteSequences_iff A u).mp hu
    obtain ⟨n, hn, hsn⟩ := (mem_finiteSequences_iff A s).mp hs
    obtain ⟨m, hm, htm⟩ := (mem_finiteSequences_iff A t).mp ht
    have : IsOrdinal n := IsOrdinal.of_mem hn
    have : IsOrdinal m := IsOrdinal.of_mem hm
    have hseq : s = u ↾ n := sequence_eq_restrict_of_subset huk hsn hsu
    have hteq : t = u ↾ m := sequence_eq_restrict_of_subset huk htm htu
    rcases IsOrdinal.subset_or_supset (α := n) (β := m) with h | h
    · left
      rw [hseq, hteq]
      intro p hp
      obtain ⟨hpu, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
      exact kpair_mem_restrict_iff.mpr ⟨hpu, h x hx⟩
    · right
      rw [hseq, hteq]
      intro p hp
      obtain ⟨hpu, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
      exact kpair_mem_restrict_iff.mpr ⟨hpu, h x hx⟩
  · rintro (h | h)
    · exact ⟨t, ht, (pair_mem_sequenceOrder_iff A t s).mpr ⟨ht, hs, h⟩,
        (pair_mem_sequenceOrder_iff A t t).mpr ⟨ht, ht, fun z hz ↦ hz⟩⟩
    · exact ⟨s, hs, (pair_mem_sequenceOrder_iff A s s).mpr ⟨hs, hs, fun z hz ↦ hz⟩,
        (pair_mem_sequenceOrder_iff A s t).mpr ⟨hs, ht, h⟩⟩

/-- Incomparable sequences branch at a common initial segment. -/
theorem exists_branching_of_incomparable {A s t n m : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hs : s ∈ A ^ n) (ht : t ∈ A ^ m) (h1 : ¬s ⊆ t) (h2 : ¬t ⊆ s) :
    ∃ k ∈ (ω : V), ∃ u ∈ A ^ k, ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧
      insert ⟨k, a⟩ₖ u ⊆ s ∧ insert ⟨k, b⟩ₖ u ⊆ t := by
  have hsf : IsFunction s := IsFunction.of_mem hs
  have htf : IsFunction t := IsFunction.of_mem ht
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have : IsOrdinal m := IsOrdinal.of_mem hm
  have hsd := domain_eq_of_mem_function hs
  have htd := domain_eq_of_mem_function ht
  let K : V := {k ∈ n ∩ m ; s ‘ k ≠ t ‘ k}
  have hKne : IsNonempty K := by
    by_contra hK
    -- `s` and `t` agree on the common domain, so one extends the other
    have hagree : ∀ k, k ∈ n → k ∈ m → s ‘ k = t ‘ k := by
      intro k hkn hkm
      by_contra hne
      exact hK ⟨k, mem_sep_iff.mpr ⟨mem_inter_iff.mpr ⟨hkn, hkm⟩, hne⟩⟩
    rcases IsOrdinal.subset_or_supset (α := n) (β := m) with hnm | hmn
    · apply h1
      intro p hp
      obtain ⟨x, hx, y, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hs p hp)
      have hy : y = s ‘ x := (value_eq_of_kpair_mem hp).symm
      rw [hy, hagree x hx (hnm x hx)]
      exact kpair_value_mem (by rw [htd]; exact hnm x hx)
    · apply h2
      intro p hp
      obtain ⟨x, hx, y, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function ht p hp)
      have hy : y = t ‘ x := (value_eq_of_kpair_mem hp).symm
      rw [hy, ← hagree x (hmn x hx) hx]
      exact kpair_value_mem (by rw [hsd]; exact hmn x hx)
  obtain ⟨k, hkK, hmin⟩ := foundation K
  obtain ⟨hknm, hkne⟩ := mem_sep_iff.mp hkK
  obtain ⟨hkn, hkm⟩ := mem_inter_iff.mp hknm
  have hkω : k ∈ (ω : V) := IsOrdinal.toIsTransitive.mem_trans hkn hn
  have : IsOrdinal k := IsOrdinal.of_mem hkω
  have hkn' : k ⊆ n := IsOrdinal.toIsTransitive.transitive _ hkn
  have hkm' : k ⊆ m := IsOrdinal.toIsTransitive.transitive _ hkm
  have hrestr : s ↾ k = t ↾ k := by
    apply mem_ext
    intro p
    constructor
    · intro hp
      obtain ⟨hps, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
      have hy : y = s ‘ x := (value_eq_of_kpair_mem hps).symm
      have hagree : s ‘ x = t ‘ x := by
        by_contra hne
        exact hmin x (mem_sep_iff.mpr ⟨mem_inter_iff.mpr ⟨hkn' x hx, hkm' x hx⟩, hne⟩) hx
      rw [hy, hagree]
      exact kpair_mem_restrict_iff.mpr ⟨kpair_value_mem (by rw [htd]; exact hkm' x hx), hx⟩
    · intro hp
      obtain ⟨hpt, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
      have hy : y = t ‘ x := (value_eq_of_kpair_mem hpt).symm
      have hagree : s ‘ x = t ‘ x := by
        by_contra hne
        exact hmin x (mem_sep_iff.mpr ⟨mem_inter_iff.mpr ⟨hkn' x hx, hkm' x hx⟩, hne⟩) hx
      rw [hy, ← hagree]
      exact kpair_mem_restrict_iff.mpr ⟨kpair_value_mem (by rw [hsd]; exact hkn' x hx), hx⟩
  refine ⟨k, hkω, s ↾ k, function_restrict_mem hs hkn', s ‘ k, function_value_mem hs hkn,
    t ‘ k, function_value_mem ht hkm, hkne, ?_, ?_⟩
  · intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact kpair_value_mem (by rw [hsd]; exact hkn)
    · exact restrict_subset s k p hp
  · rw [hrestr]
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact kpair_value_mem (by rw [htd]; exact hkm)
    · exact restrict_subset t k p hp

/-- A proper initial segment of a sequence of length `n + 1` is contained in its restriction to `n`. -/
theorem subset_restrict_of_properSegment {A s t n : V} (hn : n ∈ (ω : V)) (hs : s ∈ A ^ succ n)
    (ht : t ∈ finiteSequences A) (hsub : t ⊆ s) (hne : t ≠ s) : t ⊆ s ↾ n := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  obtain ⟨m, hm, htm⟩ := (mem_finiteSequences_iff A t).mp ht
  have : IsOrdinal m := IsOrdinal.of_mem hm
  have hms : m ⊆ succ n := sequence_domain_subset_of_subset hs htm hsub
  have hmn : m ⊆ n := by
    rcases IsOrdinal.subset_iff.mp hms with h | h
    · exfalso
      apply hne
      have : IsFunction s := IsFunction.of_mem hs
      rw [sequence_eq_restrict_of_subset hs htm hsub, h]
      exact IsFunction.restrict_eq_self s (succ n) (by rw [domain_eq_of_mem_function hs])
    · rcases mem_succ_iff.mp h with h | h
      · rw [h]
      · exact IsOrdinal.toIsTransitive.transitive _ h
  rw [sequence_eq_restrict_of_subset hs htm hsub]
  intro p hp
  obtain ⟨hps, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
  exact kpair_mem_restrict_iff.mpr ⟨hps, hmn x hx⟩

end ZFVP
