import ZFVP.SetTheory.WellOrderedProducts

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem wellOrderable_of_separating_relation {A B : V} (hB : IsWellOrderable B)
    (Q : V → V → Prop) (hQ : ℒₛₑₜ-relation Q)
    (htotal : ∀ x ∈ A, ∃ y ∈ B, Q x y)
    (hsep : ∀ x ∈ A, ∀ z ∈ A, ∀ y ∈ B, Q x y → Q z y → x = z) :
    IsWellOrderable A := by
  obtain ⟨α, hα, f, hf, hinj⟩ := (wellOrderable_iff_cardLE_ordinal B).mp hB
  have : IsOrdinal α := hα
  let C : V → V := fun x ↦ {y ∈ B ; Q x y}
  have hC : ℒₛₑₜ-function₁ C := by
    have hh : ℒₛₑₜ-relation (fun Y x : V ↦ ∀ y, y ∈ Y ↔ y ∈ B ∧ Q x y) := by definability
    apply Language.Definable.of_iff hh
    intro v
    rw [mem_ext_iff]
    simp only [C, mem_sep_iff]
    rfl
  let F := fun x ↦ wellOrderSelection f (C x)
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  have hval (x : V) (hx : x ∈ A) : F x ∈ B ∧ Q x (F x) := by
    obtain ⟨y, hy, hxy⟩ := htotal x hx
    exact mem_sep_iff.mp (wellOrderSelection_mem hf hinj
      (fun _ h ↦ (mem_sep_iff.mp h).1) ⟨y, mem_sep_iff.mpr ⟨hy, hxy⟩⟩)
  apply wellOrderable_of_cardLE (B := B) ?_
    ((wellOrderable_iff_cardLE_ordinal B).mpr ⟨α, hα, f, hf, hinj⟩)
  refine ⟨definableGraph A F hF,
    definableGraph_mem_function_of_mapsTo A B F hF (fun x hx ↦ (hval x hx).1), ?_⟩
  intro x z y hx hz
  obtain ⟨hxA, rfl⟩ := (pair_mem_definableGraph_iff A F hF x y).mp hx
  obtain ⟨hzA, he⟩ := (pair_mem_definableGraph_iff A F hF z (F x)).mp hz
  exact hsep x hxA z hzA (F x) (hval x hxA).1 (hval x hxA).2 (he.symm ▸ (hval z hzA).2)

theorem wellOrderable_of_surjective_function {A B f : V} (hA : IsWellOrderable A)
    (hf : f ∈ B ^ A) (hr : range f = B) : IsWellOrderable B := by
  have : IsFunction f := IsFunction.of_mem hf
  apply wellOrderable_of_separating_relation hA (fun x y ↦ ⟨y, x⟩ₖ ∈ f) (by definability)
  · intro x hx
    obtain ⟨a, ha⟩ := mem_range_iff.mp (hr.symm ▸ hx)
    exact ⟨a, domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem ha, ha⟩
  · intro x _ z _ a _ hx hz
    exact IsFunction.unique hx hz

end ZFVP


