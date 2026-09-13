import ZFVP.SetTheory.LowenheimSkolemCardinals

/-! A nonempty set with a small transitive collapse is a surjective image of a small rank. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem surjection_extension {A B X f : V} (hAB : A ⊆ B) (hf : f ∈ X ^ A)
    (hr : range f = X) (hne : IsNonempty X) : ∃ e ∈ X ^ B, range e = X := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne.nonempty
  let F : V → V := fun x ↦ if x ∈ A then f ‘ x else x₀
  have hF : ℒₛₑₜ-function₁ F := by
    have hr : ℒₛₑₜ-relation (fun y x : V ↦
        (x ∈ A ∧ y = f ‘ x) ∨ (x ∉ A ∧ y = x₀)) := by definability
    apply Language.Definable.of_iff hr
    intro v
    change v 0 = F (v 1) ↔ _
    unfold F
    split <;> simp_all
  let e := definableGraph B F hF
  have he : e ∈ X ^ B := definableGraph_mem_function_of_mapsTo B X F hF (by
    intro x _
    dsimp only [F]
    split_ifs with hx
    · exact function_value_mem hf hx
    · exact hx₀)
  refine ⟨e, he, SetTheory.subset_antisymm (range_subset_of_mem_function he) ?_⟩
  intro y hy
  obtain ⟨x, hxy⟩ := mem_range_iff.mp (hr.symm ▸ hy)
  have hx : x ∈ A := (mem_of_mem_functions hf hxy).1
  have : IsFunction f := IsFunction.of_mem hf
  apply mem_range_of_kpair_mem
  exact (pair_mem_definableGraph_iff B F hF x y).mpr
    ⟨hAB x hx, by simpa [F, hx] using (value_eq_of_kpair_mem hxy).symm⟩

theorem HasSmallTransitiveCollapse.rank_surjection {κ X : V} [IsOrdinal κ]
    (h : HasSmallTransitiveCollapse κ X) (hne : IsNonempty X)
    (hκ : ∀ β ∈ κ, succ β ∈ κ) :
    ∃ γ ∈ κ, ∃ e ∈ X ^ (hierarchy γ), range e = X := by
  obtain ⟨C, hC, f, hf⟩ := h
  have hfun : f ∈ C ^ X := hf.2.1
  have : IsFunction f := IsFunction.of_mem hfun
  have hinj : Injective f := by
    intro x y z hx hy
    exact hf.2.2.2.1 x (mem_of_mem_functions hfun hx).1 y (mem_of_mem_functions hfun hy).1
      ((value_eq_of_kpair_mem hx).trans (value_eq_of_kpair_mem hy).symm)
  have hg : converseGraph f ∈ X ^ C := by
    simpa only [hf.2.2.1] using converseGraph_mem_function hfun hinj
  have hgr : range (converseGraph f) = X := by
    rw [range_converseGraph, domain_eq_of_mem_function hfun]
  have hrκ : rank C ∈ κ := (mem_hierarchy_iff_rank_mem _ _).mp hC
  have hsub : C ⊆ hierarchy (succ (rank C)) := by
    apply (hierarchy_transitive _).transitive
    rw [mem_hierarchy_iff_rank_mem]
    simp
  obtain ⟨e, he, her⟩ := surjection_extension hsub hg hgr hne
  exact ⟨succ (rank C), hκ _ hrκ, e, he, her⟩

end ZFVP
