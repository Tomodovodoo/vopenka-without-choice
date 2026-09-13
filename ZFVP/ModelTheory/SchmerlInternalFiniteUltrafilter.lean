import ZFVP.ModelTheory.SchmerlInternalUltrafilter

/-! Finite-cover arguments for internal ultrafilters. Finiteness throughout is
the model's own finiteness, including nonstandard finite index sets. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ultrafilter_union_mem {K U X Y : V} (hU : IsSetUltrafilter K U)
    (hXK : X ⊆ K) (hYK : Y ⊆ K) (hXY : X ∪ Y ∈ U) : X ∈ U ∨ Y ∈ U := by
  rcases hU.dichotomy hXK with hX | hcomp
  · exact Or.inl hX
  · apply Or.inr
    apply hU.upward (hU.inter hXY hcomp) hYK
    intro z hz
    obtain ⟨hzXY, hzC⟩ := mem_inter_iff.mp hz
    exact (mem_union_iff.mp hzXY).resolve_left ((mem_relativeComplement_iff _ _ _).mp hzC).2

theorem ultrafilter_finite_union_mem {K U : V} (hU : IsSetUltrafilter K U)
    {B : V} (hB : IsInternallyFinite B) (hBK : B ⊆ ℘ K) (hBU : ⋃ˢ B ∈ U) :
    ∃ X ∈ B, X ∈ U := by
  apply internallyFinite_induction
    (fun B ↦ B ⊆ ℘ K → ⋃ˢ B ∈ U → ∃ X ∈ B, X ∈ U)
    (by definability) ?_ ?_ B hB hBK hBU
  · intro _ he
    exact False.elim (hU.empty_not_mem (by simpa using he))
  · intro C X ih hsub hmem
    have hXK : X ⊆ K := mem_power_iff.mp (hsub _ (mem_insert.mpr (Or.inl rfl)))
    have hCK : C ⊆ ℘ K := fun Y hY ↦ hsub _ (mem_insert.mpr (Or.inr hY))
    have hUK : ⋃ˢ C ⊆ K := by
      intro z hz
      obtain ⟨Y, hY, hzY⟩ := mem_sUnion_iff.mp hz
      exact mem_power_iff.mp (hCK _ hY) _ hzY
    have he : ⋃ˢ insert X C = X ∪ ⋃ˢ C := by
      ext z
      simp only [mem_sUnion_iff, mem_insert, mem_union_iff]
      aesop
    rw [he] at hmem
    rcases ultrafilter_union_mem hU hXK hUK hmem with hX | hC
    · exact ⟨X, mem_insert.mpr (Or.inl rfl), hX⟩
    · obtain ⟨Y, hYC, hYU⟩ := ih hCK hC
      exact ⟨Y, mem_insert.mpr (Or.inr hYC), hYU⟩

/-- Some member of a finite definable cover of a filter-large set is large. -/
theorem ultrafilter_finite_cover {K U I Y : V} (hU : IsSetUltrafilter K U)
    (hI : IsInternallyFinite I) (hY : Y ∈ U)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hFK : ∀ i ∈ I, F i ⊆ K) (hcover : ∀ y ∈ Y, ∃ i ∈ I, y ∈ F i) :
    ∃ i ∈ I, F i ∈ U := by
  have hB : IsInternallyFinite (repl F hF I) := internallyFinite_repl F hF hI
  have hBK : repl F hF I ⊆ ℘ K := by
    intro X hX
    obtain ⟨i, hi, rfl⟩ := (repl_spec hF).mp hX
    exact mem_power_iff.mpr (hFK i hi)
  have hBU : ⋃ˢ repl F hF I ∈ U := by
    apply hU.upward hY
    · intro z hz
      obtain ⟨X, hX, hzX⟩ := mem_sUnion_iff.mp hz
      exact mem_power_iff.mp (hBK _ hX) _ hzX
    · intro y hy
      obtain ⟨i, hi, hyi⟩ := hcover y hy
      exact mem_sUnion_iff.mpr ⟨F i, (repl_spec hF).mpr ⟨i, hi, rfl⟩, hyi⟩
  obtain ⟨X, hX, hXU⟩ := ultrafilter_finite_union_mem hU hB hBK hBU
  obtain ⟨i, hi, rfl⟩ := (repl_spec hF).mp hX
  exact ⟨i, hi, hXU⟩

end ZFVP.Schmerl
