import ZFVP.SetTheory.TreeBodies

/-! Every node of an internal perfect binary tree lies on a branch, already in ZF. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem perfectTree_strictExtension {T s : V} (hT : IsPerfectTree T) (hs : s ∈ T) :
    ∃ t ∈ T, s ⊆ t ∧ domain s ∈ domain t := by
  obtain ⟨t, ht, u, hu, hst, hsu, hinc⟩ := hT.2.2 s hs
  obtain ⟨hm, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp (hT.1.1 s hs)
  obtain ⟨hn, htf⟩ := (mem_finiteSequences_iff_domain _ t).mp (hT.1.1 t ht)
  have : IsOrdinal (domain s) := IsOrdinal.of_mem hm
  have : IsOrdinal (domain t) := IsOrdinal.of_mem hn
  have : IsFunction s := IsFunction.of_mem hsf
  have : IsFunction u := binarySequence_isFunction (hT.1.1 u hu)
  have hd := sequence_domain_subset_of_subset htf hsf hst
  refine ⟨t, ht, hst, ?_⟩
  rcases IsOrdinal.subset_iff.mp hd with he | hlt
  · have htf' : t ∈ ((2 : ℕ) : V) ^ domain s := by rw [he]; exact htf
    have hsame := sequence_eq_of_subset_of_domain_eq hsf htf' hst
    rw [← hsame] at hinc
    exact (not_incompatible_of_subset hsu hinc).elim
  · exact hlt

theorem perfectTree_longExtension {T s M : V} (hT : IsPerfectTree T) (hs : s ∈ T)
    (hM : M ∈ (ω : V)) : ∃ t ∈ T, s ⊆ t ∧ M ⊆ domain t := by
  apply naturalNumber_induction (fun M ↦ ∃ t ∈ T, s ⊆ t ∧ M ⊆ domain t) (by definability) ?_ ?_ M hM
  · exact ⟨s, hs, subset_refl _, empty_subset _⟩
  · intro M hM ih
    obtain ⟨u, hu, hsu, hMu⟩ := ih
    obtain ⟨t, ht, hut, hdu⟩ := perfectTree_strictExtension hT hu
    have huω := binarySequence_domain_mem (hT.1.1 u hu)
    have htω := binarySequence_domain_mem (hT.1.1 t ht)
    have : IsOrdinal M := IsOrdinal.of_mem hM
    have : IsOrdinal (domain u) := IsOrdinal.of_mem huω
    have : IsOrdinal (domain t) := IsOrdinal.of_mem htω
    have hMt : M ∈ domain t := by
      rcases IsOrdinal.subset_iff.mp hMu with rfl | hlt
      · exact hdu
      · exact IsOrdinal.toIsTransitive.mem_trans hlt hdu
    exact ⟨t, ht, subset_trans hsu hut, succ_subset_of_mem_nat htω hMt⟩

noncomputable def compatibleTreeCone (T s : V) : V := {t ∈ T ; ¬Incompatible t s}

theorem mem_compatibleTreeCone_iff (T s t : V) :
    t ∈ compatibleTreeCone T s ↔ t ∈ T ∧ ¬Incompatible t s := by simp [compatibleTreeCone]

instance compatibleTreeCone_definable : ℒₛₑₜ-function₂[V] compatibleTreeCone := by
  have h : ℒₛₑₜ-relation₃ (fun C T s : V ↦ ∀ t, t ∈ C ↔ t ∈ T ∧ ¬Incompatible t s) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_compatibleTreeCone_iff]

theorem compatibleTreeCone_isTree {T s : V} (hT : IsTree T) (hs : s ∈ binarySequences V) :
    IsTree (compatibleTreeCone T s) := by
  have : IsFunction s := binarySequence_isFunction hs
  refine ⟨fun t ht ↦ hT.1 t ((mem_compatibleTreeCone_iff T s t).mp ht).1, ?_⟩
  intro t ht n hn
  obtain ⟨htT, hnot⟩ := (mem_compatibleTreeCone_iff T s t).mp ht
  have hrT := hT.2 t htT n hn
  have : IsFunction t := binarySequence_isFunction (hT.1 t htT)
  have : IsFunction (t ↾ n) := binarySequence_isFunction (hT.1 _ hrT)
  exact (mem_compatibleTreeCone_iff T s _).mpr ⟨hrT,
    fun hinc ↦ hnot (incompatible_mono hinc (restrict_subset _ _) (subset_refl _))⟩

theorem perfectTree_branch_through {T s : V} (hT : IsPerfectTree T) (hs : s ∈ T) :
    ∃ x ∈ treeBody T, s ⊆ x := by
  have hsb := hT.1.1 s hs
  obtain ⟨hm, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hsb
  have : IsFunction s := IsFunction.of_mem hsf
  have hlevels : ∀ M ∈ (ω : V), ∃ t ∈ compatibleTreeCone T s, t ∈ ((2 : ℕ) : V) ^ M := by
    intro M hM
    obtain ⟨u, hu, hsu, hMu⟩ := perfectTree_longExtension hT hs hM
    obtain ⟨_, huf⟩ := (mem_finiteSequences_iff_domain _ u).mp (hT.1.1 u hu)
    have hr := function_restrict_mem huf hMu
    have : IsFunction u := IsFunction.of_mem huf
    have : IsFunction (u ↾ M) := IsFunction.of_mem hr
    exact ⟨u ↾ M, (mem_compatibleTreeCone_iff T s _).mpr
      ⟨tree_restrict_mem hT.1 hu hM hMu,
        not_incompatible_of_subset_subset (restrict_subset _ _) hsu⟩, hr⟩
  obtain ⟨x, hx⟩ := exists_branch_of_levels (compatibleTreeCone_isTree hT.1 hsb) hlevels
  have hxT := treeBody_mono (fun t ht ↦ ((mem_compatibleTreeCone_iff T s t).mp ht).1) x hx
  obtain ⟨hxc, hxall⟩ := (mem_treeBody_iff _ _).mp hx
  have hr := function_restrict_mem hxc (IsTransitive.transitive _ hm)
  have : IsFunction (x ↾ (domain s)) := IsFunction.of_mem hr
  have hnot := ((mem_compatibleTreeCone_iff T s _).mp (hxall _ hm)).2
  have he : x ↾ (domain s) = s := by
    apply functions_eq_of_domain_values (domain_eq_of_mem_function hr)
    intro i hi
    by_contra hne
    exact hnot ⟨i, hi, (domain_eq_of_mem_function hr) ▸ hi, hne⟩
  exact ⟨x, hxT, by rw [← he]; exact restrict_subset _ _⟩

end ZFVP
