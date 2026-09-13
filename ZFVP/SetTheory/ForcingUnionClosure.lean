import ZFVP.SetTheory.WoodinCollapseDirectedClosure

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingUnionClosedAtFormula : SetTheorySemisentence 2 :=
  f“Q I. ∀ f, f ∈ !function.dfn Q I →
    (∀ i ∈ I, ∀ j ∈ I, ∃ k ∈ I, !value.dfn f i ⊆ !value.dfn f k ∧ !value.dfn f j ⊆ !value.dfn f k) →
      !sUnion.dfn (!range.dfn f) ∈ Q”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsForcingUnionClosedAt (Q I : V) : Prop :=
  ∀ f, f ∈ Q ^ I → (∀ i ∈ I, ∀ j ∈ I, ∃ k ∈ I, f ‘ i ⊆ f ‘ k ∧ f ‘ j ⊆ f ‘ k) → ⋃ˢ range f ∈ Q

instance forcingUnionClosedAtFormula_defined :
    ℒₛₑₜ-relation[V] IsForcingUnionClosedAt via forcingUnionClosedAtFormula :=
  ⟨fun v ↦ by simp [forcingUnionClosedAtFormula, IsForcingUnionClosedAt]⟩

instance isForcingUnionClosedAt_definable : ℒₛₑₜ-relation[V] IsForcingUnionClosedAt :=
  forcingUnionClosedAtFormula_defined.to_definable

theorem woodinCollapse_unionClosedAt {κ δ γ : V} (hκ : IsRegularCardinal κ)
    (hγ : γ ∈ κ) (hDC : InternalDependentChoiceAt γ) :
    IsForcingUnionClosedAt (woodinCollapse κ δ) γ := by
  intro f hf hdir
  apply (woodinCollapse_directed_union hκ hγ hDC (H := f) ?_).1
  refine ⟨hf, fun i hi j hj ↦ ?_⟩
  obtain ⟨k, hk, hki, hkj⟩ := hdir i hi j hj
  exact ⟨k, hk,
    (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨function_value_mem hf hk, function_value_mem hf hi, hki⟩,
    (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨function_value_mem hf hk, function_value_mem hf hj, hkj⟩⟩

theorem IsForcingUnionClosedAt.directedClosedAt {Q I : V} (h : IsForcingUnionClosedAt Q I) :
    IsForcingDirectedClosedAt Q (reverseInclusionOrder Q) I := by
  intro f hf
  let := IsFunction.of_mem hf.1
  have hu : ⋃ˢ range f ∈ Q := h f hf.1 (fun i hi j hj ↦ by
    obtain ⟨k, hk, hki, hkj⟩ := hf.2 i hi j hj
    exact ⟨k, hk, ((pair_mem_reverseInclusionOrder _ _ _).mp hki).2.2,
      ((pair_mem_reverseInclusionOrder _ _ _).mp hkj).2.2⟩)
  refine ⟨⋃ˢ range f, hu, fun i hi ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, function_value_mem hf.1 hi, ?_⟩⟩
  intro x hx
  exact mem_sUnion_iff.mpr ⟨f ‘ i, mem_range_of_kpair_mem
    (kpair_value_mem ((domain_eq_of_mem_function hf.1).symm ▸ hi)), hx⟩

end ZFVP
