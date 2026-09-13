import ZFVP.SetTheory.FullChoicelessCardinals
import ZFVP.SetTheory.ChoicelessSupercompactExtendible

/-! The positive-level equivalence between n-choiceless extendibility
and (n+1)-choiceless supercompactness, including prescribed lower bounds. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsAlphaChoicelessExtendible.supercompact_succ {n : ℕ} {α γ : V}
    (h : IsAlphaChoicelessExtendible (n + 1) α γ) :
    IsAlphaChoicelessSupercompact (n + 2) α γ := by
  let := h.ordinal
  refine ⟨h.ordinal, h.2.1, ?_⟩
  intro μ hμ hγμ a ha
  let := hμ.ordinal
  obtain ⟨θ, hμθ, hθ⟩ := cn_unbounded (n + 2) μ
  let := hθ.ordinal
  let := hierarchy_transitive θ
  have hγθ := IsOrdinal.toIsTransitive.mem_trans hγμ hμθ
  obtain ⟨η, f, κ, hη, hf, hc, hακ, hθimage⟩ :=
    h.2.2 θ (hθ.of_le (by omega : n + 1 ≤ n + 2)) hγθ
  let := hη.ordinal
  let := hierarchy_transitive η
  have hγV := ordinal_subset_hierarchy θ γ hγθ
  let := hf.value_ordinal h.ordinal hγV
  have hγimage : γ ∈ f ‘ γ := IsOrdinal.toIsTransitive.mem_trans hγθ hθimage
  have hmove : f ‘ γ ≠ γ := by
    intro he
    rw [he] at hγimage
    exact mem_irrefl γ hγimage
  have hκγ : κ ⊆ γ := hc.2.2 γ h.ordinal ⟨hγV, hmove⟩
  exact rankEmbedding_supercompactWitness_below_image hθ hη hf hc hακ hκγ hγμ
    (IsOrdinal.toIsTransitive.mem_trans hμθ hθimage) hμθ hμ ha

theorem alphaChoicelessExtendible_iff_supercompact {n : ℕ} {α γ : V} :
    IsAlphaChoicelessExtendible (n + 1) α γ ↔ IsAlphaChoicelessSupercompact (n + 2) α γ :=
  ⟨IsAlphaChoicelessExtendible.supercompact_succ, IsAlphaChoicelessSupercompact.extendible⟩

theorem IsChoicelessExtendible.supercompact_succ {n : ℕ} {κ : V}
    (h : IsChoicelessExtendible (n + 1) κ) : IsChoicelessSupercompact (n + 2) κ :=
  ⟨h.1, h.2.1, fun α hα ↦ (h.2.2 α hα).supercompact_succ⟩

theorem IsChoicelessSupercompact.extendible {n : ℕ} {κ : V}
    (h : IsChoicelessSupercompact (n + 2) κ) : IsChoicelessExtendible (n + 1) κ :=
  ⟨h.1, h.2.1, fun α hα ↦ (h.2.2 α hα).extendible⟩

theorem choicelessExtendible_iff_supercompact {n : ℕ} {κ : V} :
    IsChoicelessExtendible (n + 1) κ ↔ IsChoicelessSupercompact (n + 2) κ :=
  ⟨IsChoicelessExtendible.supercompact_succ, IsChoicelessSupercompact.extendible⟩

theorem IsChoicelessExtendible.initial {n : ℕ} {κ : V}
    (h : IsChoicelessExtendible (n + 1) κ) : IsInitialOrdinal κ := h.supercompact_succ.initial

theorem IsChoicelessExtendible.omega_lt {n : ℕ} {κ : V}
    (h : IsChoicelessExtendible (n + 1) κ) : (ω : V) ∈ κ := h.supercompact_succ.omega_lt

end ZFVP
