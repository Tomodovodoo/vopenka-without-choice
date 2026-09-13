import ZFVP.SetTheory.Cofinality
import ZFVP.SetTheory.InjectionRetraction
import ZFVP.SetTheory.FunctionComposition
import ZFVP.SetTheory.StandardNaturals

/-! Cofinality is an initial ordinal; the proof uses an explicitly constructed retraction. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem cofinalMap_precompose_surjection {α β γ f g : V} (hf : IsCofinalMap α β f)
    (hg : g ∈ β ^ γ) (hsurj : range g = β) : IsCofinalMap α γ (compose g f) := by
  have hgf := compose_function hg hf.1
  have : IsFunction f := IsFunction.of_mem hf.1
  have : IsFunction (compose g f) := IsFunction.of_mem hgf
  refine ⟨hgf, ?_⟩
  intro ξ hξ
  obtain ⟨i, hi, hξi⟩ := hf.2 ξ hξ
  obtain ⟨j, hji⟩ := mem_range_iff.mp (hsurj.symm ▸ hi)
  have hj : j ∈ γ := domain_eq_of_mem_function hg ▸ mem_domain_of_kpair_mem hji
  have hval : (compose g f) ‘ j = f ‘ i := value_eq_of_kpair_mem
    (kpair_mem_compose_iff.mpr ⟨i, hji, kpair_value_mem (by simpa only [domain_eq_of_mem_function hf.1] using hi)⟩)
  exact ⟨j, hj, hval.symm ▸ hξi⟩

theorem internalCofinality_initial (α : V) [IsOrdinal α] : IsInitialOrdinal (internalCofinality α) := by
  refine ⟨inferInstance, ?_⟩
  intro β hβ hbad
  obtain ⟨g, hg, hsurj⟩ := surjection_of_injection hbad ⟨β, hβ⟩
  obtain ⟨f, hf⟩ := cofinalMap_exists α
  exact no_cofinalMap_below_cofinality hβ ⟨compose g f, cofinalMap_precompose_surjection hf hg hsurj⟩

theorem internalCofinality_zero : internalCofinality (0 : V) = 0 := by
  exact subset_empty_iff_eq_empty.mp (internalCofinality_subset (0 : V))

theorem internalCofinality_eq_zero_iff (α : V) [IsOrdinal α] : internalCofinality α = 0 ↔ α = 0 := by
  constructor
  · intro hκ
    obtain ⟨f, hf⟩ := cofinalMap_exists α
    apply subset_empty_iff_eq_empty.mp
    intro x hx
    obtain ⟨i, hi, _⟩ := hf.2 x hx
    rw [hκ] at hi
    exact False.elim (not_mem_empty hi)
  · rintro rfl
    exact internalCofinality_zero

theorem singleton_isCofinalMap (α : V) [IsOrdinal α] :
    IsCofinalMap (succ α) (1 : V) (definableGraph (1 : V) (fun _ ↦ α) (by definability)) := by
  refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ _ ↦ by simp), ?_⟩
  intro ξ hξ
  have hz : (0 : V) ∈ (1 : V) := by simp
  refine ⟨0, hz, ?_⟩
  rw [value_definableGraph _ _ _ hz]
  rcases mem_succ_iff.mp hξ with rfl | hξ
  · exact subset_refl _
  · exact IsOrdinal.toIsTransitive.transitive _ hξ

theorem internalCofinality_succ (α : V) [IsOrdinal α] : internalCofinality (succ α) = 1 := by
  have : IsOrdinal (1 : V) := IsOrdinal.nat (by simp)
  have hle := internalCofinality_minimal (singleton_isCofinalMap α)
  rcases IsOrdinal.subset_iff.mp hle with heq | hlt
  · exact heq
  · have hzero : internalCofinality (succ α) = 0 := by
      simpa only [one_def, mem_singleton_iff] using hlt
    have hα := (internalCofinality_eq_zero_iff (succ α)).mp hzero
    have hm : α ∈ succ α := by simp
    rw [hα] at hm
    exact False.elim (not_mem_empty hm)

end ZFVP
