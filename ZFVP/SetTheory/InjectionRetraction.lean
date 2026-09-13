import ZFVP.SetTheory.InverseFunction

/-! A specified point extends the inverse of an injection to a surjection. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def inverseOrDefault (f a y : V) : V := by
  classical
  exact if y ∈ range f then (converseGraph f) ‘ y else a

instance inverseOrDefault_definable : ℒₛₑₜ-function₃[V] inverseOrDefault := by
  have h : ℒₛₑₜ-relation₄ (fun z f a y : V ↦
      (y ∈ range f ∧ z = (converseGraph f) ‘ y) ∨ (y ∉ range f ∧ z = a)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = inverseOrDefault (v 1) (v 2) (v 3) ↔ _
  unfold inverseOrDefault
  split <;> simp_all

noncomputable def injectionRetraction (f B a : V) : V :=
  definableGraph B (inverseOrDefault f a) (by definability)

instance injectionRetraction_definable : ℒₛₑₜ-function₃[V] injectionRetraction := by
  have h : ℒₛₑₜ-relation₄ (fun g f B a : V ↦ ∀ p, p ∈ g ↔ ∃ y ∈ B, p = ⟨y, inverseOrDefault f a y⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = injectionRetraction (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [injectionRetraction, mem_definableGraph_iff]

theorem injectionRetraction_mem_function {A B f a : V} (hf : f ∈ B ^ A)
    (hinj : Injective f) (ha : a ∈ A) : injectionRetraction f B a ∈ A ^ B := by
  apply definableGraph_mem_function_of_mapsTo
  intro y _
  unfold inverseOrDefault
  split
  · next hy => exact function_value_mem (converseGraph_mem_function hf hinj) hy
  · exact ha

theorem injectionRetraction_value {A B f a x : V} (hf : f ∈ B ^ A) (hinj : Injective f) (hx : x ∈ A) :
    (injectionRetraction f B a) ‘ (f ‘ x) = x := by
  rw [injectionRetraction, value_definableGraph _ _ _ (function_value_mem hf hx)]
  rw [inverseOrDefault, ite_eq_left (value_mem_range hf hx)]
  exact converseGraph_value_value hf hinj hx

theorem injectionRetraction_surjective {A B f a : V} (hf : f ∈ B ^ A)
    (hinj : Injective f) (ha : a ∈ A) : range (injectionRetraction f B a) = A := by
  have hg := injectionRetraction_mem_function hf hinj ha
  have : IsFunction (injectionRetraction f B a) := IsFunction.of_mem hg
  apply SetTheory.subset_antisymm (range_subset_of_mem_function hg)
  intro x hx
  have hv := injectionRetraction_value (a := a) hf hinj hx
  exact hv ▸ value_mem_range hg (function_value_mem hf hx)

theorem surjection_of_injection {A B : V} (h : A ≤# B) (hA : IsNonempty A) :
    ∃ g ∈ A ^ B, range g = A := by
  obtain ⟨f, hf, hinj⟩ := h
  obtain ⟨a, ha⟩ := hA.nonempty
  exact ⟨injectionRetraction f B a, injectionRetraction_mem_function hf hinj ha,
    injectionRetraction_surjective hf hinj ha⟩

end ZFVP
