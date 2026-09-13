import ZFVP.SetTheory.UsubaCollapse
import ZFVP.SetTheory.RegularSmallRank

/-! Conditions in Usuba's collapse of a rank lie in that rank when the
allowed domain sizes are below its cofinality. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem cardinalSmall_subset_hierarchy_of_cofinality {κ θ A : V} [IsOrdinal θ]
    (hκcf : κ ⊆ internalCofinality θ) (hsucc : ∀ β ∈ θ, succ β ∈ θ)
    (hzero : (0 : V) ∈ θ) (hA : IsCardinalSmall κ A) (hsub : A ⊆ hierarchy θ) :
    A ∈ hierarchy θ := by
  classical
  by_cases hn : IsNonempty A
  · obtain ⟨α, hα, hinj⟩ := hA
    obtain ⟨g, hg, hr⟩ := surjection_of_injection hinj hn
    let := IsFunction.of_mem hg
    let F := definableGraph α (fun i ↦ rank (g ‘ i)) (by definability)
    have hF : F ∈ θ ^ α := definableGraph_mem_function_of_mapsTo _ _ _ _ (by
      intro i hi
      exact (mem_hierarchy_iff_rank_mem _ θ).mp (hsub _ (function_value_mem hg hi)))
    obtain ⟨β, hβ, hb⟩ := map_below_cofinality_bounded (hκcf α hα) hF
    let := IsOrdinal.of_mem hβ
    apply mem_hierarchy_of_mem_stage (hsucc β hβ)
    rw [hierarchy_succ, mem_power_iff]
    intro x hx
    obtain ⟨i, hi⟩ := mem_range_iff.mp (hr.symm ▸ hx)
    have hiα : i ∈ α := domain_eq_of_mem_function hg ▸ mem_domain_of_kpair_mem hi
    have hgi := value_eq_of_kpair_mem hi
    have hri := hb i hiα
    rw [show F ‘ i = rank (g ‘ i) from value_definableGraph _ _ _ hiα, hgi] at hri
    exact (mem_hierarchy_iff_rank_mem _ β).mpr hri
  · have he : A = ∅ := by
      apply mem_ext
      intro z
      simp only [not_mem_empty, iff_false]
      exact fun hz ↦ hn ⟨z, hz⟩
    rw [he]
    exact ordinal_mem_hierarchy_iff.mpr hzero

theorem usubaCollapse_condition_mem_hierarchy {κ θ p : V} [IsOrdinal θ]
    (hκ : IsRegularCardinal κ) (hκcf : κ ∈ internalCofinality θ)
    (hsucc : ∀ β ∈ θ, succ β ∈ θ)
    (hp : p ∈ usubaCollapse κ (hierarchy θ)) : p ∈ hierarchy θ := by
  let := hκ.1.1
  have hκθ : κ ∈ θ := internalCofinality_subset θ κ hκcf
  have hzero : (0 : V) ∈ θ := IsOrdinal.toIsTransitive.mem_trans
    (hκ.2.1 0 (by simp)) hκθ
  obtain ⟨hpSub, hpf, hsmall⟩ := (mem_usubaCollapse _ _ _).mp hp
  let := hpf
  apply cardinalSmall_subset_hierarchy_of_cofinality
    (IsOrdinal.toIsTransitive.transitive _ hκcf) hsucc hzero
    (hsmall.of_cardLE (function_cardLE_domain p))
  intro z hz
  obtain ⟨i, hi, y, hy, rfl⟩ := mem_prod_iff.mp (hpSub z hz)
  have hiθ : i ∈ θ := IsOrdinal.toIsTransitive.mem_trans hi hκθ
  exact kpair_mem_hierarchy_limit hsucc (ordinal_subset_hierarchy θ i hiθ) hy

theorem usubaCollapse_subset_hierarchy {κ θ : V} [IsOrdinal θ]
    (hκ : IsRegularCardinal κ) (hκcf : κ ∈ internalCofinality θ)
    (hsucc : ∀ β ∈ θ, succ β ∈ θ) :
    usubaCollapse κ (hierarchy θ) ⊆ hierarchy θ :=
  fun _ hp ↦ usubaCollapse_condition_mem_hierarchy hκ hκcf hsucc hp

end ZFVP
