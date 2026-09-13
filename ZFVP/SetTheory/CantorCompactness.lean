import ZFVP.SetTheory.TreeBodies
import ZFVP.SetTheory.FiniteRangeFibers

/-! Internal finite subcovers of binary tree bodies, proved in ZF. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def boundedBinaryCode (S n : V) : V :=
  {s ∈ S ; domain s ⊆ n}

theorem mem_boundedBinaryCode_iff (S n s : V) : s ∈ boundedBinaryCode S n ↔
    s ∈ S ∧ domain s ⊆ n := by simp [boundedBinaryCode]

instance boundedBinaryCode_definable : ℒₛₑₜ-function₂[V] boundedBinaryCode := by
  have h : ℒₛₑₜ-relation₃ (fun B S n : V ↦ ∀ s, s ∈ B ↔ s ∈ S ∧ domain s ⊆ n) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_boundedBinaryCode_iff]

theorem boundedBinaryCode_finite {S n : V} (hS : S ⊆ binarySequences V) (hn : n ∈ (ω : V)) :
    IsInternallyFinite (boundedBinaryCode S n) := by
  apply internallyFinite_subset (internallyFinite_powerSet
    (internallyFinite_prod (show IsInternallyFinite n from ⟨n, hn, CardEQ.refl _⟩) internallyFinite_two))
  intro s hs
  obtain ⟨hsS, hsn⟩ := (mem_boundedBinaryCode_iff _ _ _).mp hs
  obtain ⟨_, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp (hS s hsS)
  exact mem_power_iff.mpr (subset_trans (mem_function_iff.mp hsf).1
    (prod_subset_prod_of_subset hsn (subset_refl _)))

theorem treeBody_open_cover_uniform {T S : V} (hT : IsTree T) (hS : S ⊆ binarySequences V)
    (hcover : treeBody T ⊆ openFrom S) :
    ∃ n ∈ (ω : V), ∀ t ∈ levelSet T n, ∃ s ∈ S, s ⊆ t := by
  have hI : IsTree (T ∩ avoidingTree S) := by
    refine ⟨fun t ht ↦ hT.1 t (mem_inter_iff.mp ht).1, ?_⟩
    intro t ht n hn
    obtain ⟨htT, htA⟩ := mem_inter_iff.mp ht
    exact mem_inter_iff.mpr ⟨hT.2 t htT n hn, (avoidingTree_isTree S).2 t htA n hn⟩
  have hempty : ∀ c, c ∉ treeBody (T ∩ avoidingTree S) := by
    intro c hc
    rw [treeBody_inter] at hc
    obtain ⟨hcT, hcA⟩ := mem_inter_iff.mp hc
    have hcC := treeBody_subset_cantorSpace T c hcT
    exact ((mem_treeBody_avoidingTree_iff hS hcC).mp hcA)
      ((mem_openFrom_iff_meets _ _).mp (hcover c hcT)).2
  obtain ⟨n, hn, hnone⟩ := exists_empty_level_of_treeBody_empty hI hempty
  refine ⟨n, hn, ?_⟩
  intro t ht
  by_contra h
  push Not at h
  obtain ⟨htT, htn⟩ := (mem_levelSet_iff _ _ _).mp ht
  exact hnone t ((mem_levelSet_iff _ _ _).mpr ⟨mem_inter_iff.mpr ⟨htT,
    (mem_avoidingTree_iff _ _).mpr ⟨hT.1 t htT, h⟩⟩, htn⟩)

theorem treeBody_finite_subcover {T S : V} (hT : IsTree T) (hS : S ⊆ binarySequences V)
    (hcover : treeBody T ⊆ openFrom S) :
    ∃ F, F ⊆ S ∧ IsInternallyFinite F ∧ treeBody T ⊆ openFrom F := by
  obtain ⟨n, hn, hlevel⟩ := treeBody_open_cover_uniform hT hS hcover
  refine ⟨boundedBinaryCode S n,
    fun s hs ↦ ((mem_boundedBinaryCode_iff _ _ _).mp hs).1, boundedBinaryCode_finite hS hn, ?_⟩
  intro c hc
  have hcC := treeBody_subset_cantorSpace T c hc
  have ht := restrict_mem_levelSet hc hn
  obtain ⟨s, hs, hst⟩ := hlevel _ ht
  have hsf := ((mem_finiteSequences_iff_domain _ s).mp (hS s hs)).2
  have hsn : domain s ⊆ n := sequence_domain_subset_of_subset
    (function_restrict_mem hcC (IsTransitive.ω.transitive _ hn)) hsf hst
  exact (mem_openFrom_iff _ _).mpr ⟨hcC, s,
    (mem_boundedBinaryCode_iff _ _ _).mpr ⟨hs, hsn⟩,
    (subset_iff_restrict_eq hcC (hS s hs)).mp (subset_trans hst (restrict_subset _ _))⟩

end ZFVP
