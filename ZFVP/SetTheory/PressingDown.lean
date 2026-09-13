import ZFVP.SetTheory.DiagonalClubs
import ZFVP.SetTheory.InternalChoice

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def regressiveFiber (S r i : V) : V := {δ ∈ S ; r ‘ δ = i}

theorem pressing_down (hAC : InternalChoice V) {κ S r : V} (hκ : IsRegularCardinal κ)
    (hω : (ω : V) ∈ κ) (hS : IsStationaryIn S κ) (hr : ∀ δ ∈ S, r ‘ δ ∈ δ) :
    ∃ i ∈ κ, IsStationaryIn (regressiveFiber S r i) κ := by
  classical
  by_contra! hn
  let B : V → V := fun i ↦ {C ∈ ℘ κ ; IsClubIn C κ ∧ ∀ δ ∈ S, r ‘ δ = i → δ ∉ C}
  have hB : ℒₛₑₜ-function₁ B := by
    have h : ℒₛₑₜ-relation[V] (fun X i ↦ ∀ C, C ∈ X ↔ C ∈ ℘ κ ∧
      IsClubIn C κ ∧ ∀ δ ∈ S, r ‘ δ = i → δ ∉ C) := by definability
    apply Language.Definable.of_iff h
    intro v
    change v 0 = B (v 1) ↔ _
    rw [mem_ext_iff]
    simp [B]
  have hnonempty (i : V) (hi : i ∈ κ) : IsNonempty (B i) := by
    have hfiber : regressiveFiber S r i ⊆ κ := fun δ hδ ↦ hS.1 δ (mem_sep_iff.mp hδ).1
    have hno : ¬∀ C, IsClubIn C κ → ∃ δ ∈ regressiveFiber S r i, δ ∈ C :=
      fun h ↦ hn i hi ⟨hfiber, h⟩
    push Not at hno
    obtain ⟨C, hC, havoid⟩ := hno
    refine ⟨C, mem_sep_iff.mpr ⟨mem_power_iff.mpr hC.1.1, hC, ?_⟩⟩
    intro δ hδ heq
    exact havoid δ (mem_sep_iff.mpr ⟨hδ, heq⟩)
  obtain ⟨C, _, _, hchoice⟩ := choice_for_definable_family hAC κ B hB hnonempty
  have hclubs (i : V) (hi : i ∈ κ) : IsClubIn (C ‘ i) κ := (mem_sep_iff.mp (hchoice i hi)).2.1
  have havoid (i : V) (hi : i ∈ κ) : ∀ δ ∈ S, r ‘ δ = i → δ ∉ C ‘ i :=
    (mem_sep_iff.mp (hchoice i hi)).2.2
  exact no_club_family_avoiding_regressive_fibers hκ hω hS hr hclubs havoid

theorem pressing_down_of_models_ac [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] {κ S r : V}
    (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ) (hS : IsStationaryIn S κ)
    (hr : ∀ δ ∈ S, r ‘ δ ∈ δ) : ∃ i ∈ κ, IsStationaryIn (regressiveFiber S r i) κ :=
  pressing_down internalChoice_of_models_ac hκ hω hS hr

end ZFVP
