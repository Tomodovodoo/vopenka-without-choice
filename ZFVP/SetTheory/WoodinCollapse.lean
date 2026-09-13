import ZFVP.SetTheory.CardinalSmallUnions
import ZFVP.SetTheory.FinitePartialFunctions
import ZFVP.SetTheory.DependentChoicePathUnions

/-! The local collapse of Spoerl Definition 36. The value at (α,η) lies in
V_(1+η), where the addition is ordinal addition in the stated order. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinCollapse (κ δ : V) : V :=
  {p ∈ ℘ ((κ ×ˢ δ) ×ˢ hierarchy δ) ; IsFunction p ∧ IsCardinalSmall κ (domain p) ∧
    ∀ α η x, ⟨⟨α, η⟩ₖ, x⟩ₖ ∈ p → x ∈ hierarchy (ordinalAdd (1 : V) η)}

theorem mem_woodinCollapse (κ δ p : V) : p ∈ woodinCollapse κ δ ↔
    p ⊆ (κ ×ˢ δ) ×ˢ hierarchy δ ∧ IsFunction p ∧ IsCardinalSmall κ (domain p) ∧
      ∀ α η x, ⟨⟨α, η⟩ₖ, x⟩ₖ ∈ p → x ∈ hierarchy (ordinalAdd (1 : V) η) := by
  simp only [woodinCollapse, mem_sep_iff, mem_power_iff]

instance woodinCollapse_definable : ℒₛₑₜ-function₂[V] woodinCollapse := by
  have h : ℒₛₑₜ-relation₃[V] (fun P κ δ ↦ ∀ p, p ∈ P ↔
      p ⊆ (κ ×ˢ δ) ×ˢ hierarchy δ ∧ IsFunction p ∧ IsCardinalSmall κ (domain p) ∧
        ∀ α η x, ⟨⟨α, η⟩ₖ, x⟩ₖ ∈ p → x ∈ hierarchy (ordinalAdd (1 : V) η)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinCollapse (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_woodinCollapse]

noncomputable def woodinCollapseOrder (κ δ : V) : V := reverseInclusionOrder (woodinCollapse κ δ)

instance woodinCollapseOrder_definable : ℒₛₑₜ-function₂[V] woodinCollapseOrder := by
  unfold woodinCollapseOrder
  definability

theorem woodinCollapse_poset (κ δ : V) :
    IsForcingPoset (woodinCollapse κ δ) (woodinCollapseOrder κ δ) := reverseInclusionOrder_poset _

theorem empty_mem_woodinCollapse {κ : V} (hz : (∅ : V) ∈ κ) (δ : V) :
    (∅ : V) ∈ woodinCollapse κ δ := by
  apply (mem_woodinCollapse _ _ _).mpr
  refine ⟨by simp, inferInstance, ?_, by simp⟩
  exact ⟨∅, hz, by simp⟩

theorem woodinCollapse_top {κ : V} (hz : (∅ : V) ∈ κ) (δ : V) :
    IsForcingTop (woodinCollapse κ δ) (woodinCollapseOrder κ δ) ∅ :=
  ⟨empty_mem_woodinCollapse hz δ, fun p hp ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hp, empty_mem_woodinCollapse hz δ, by simp⟩⟩

theorem woodinCollapse_subset {κ δ p q : V} (hp : p ∈ woodinCollapse κ δ) (hqp : q ⊆ p) :
    q ∈ woodinCollapse κ δ := by
  obtain ⟨hsub, hfun, hsmall, hval⟩ := (mem_woodinCollapse _ _ _).mp hp
  let := hfun
  refine (mem_woodinCollapse _ _ _).mpr
    ⟨subset_trans hqp hsub, IsFunction.ofSubset p q hqp, hsmall.subset ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
    exact mem_domain_of_kpair_mem (hqp _ hxy)
  · exact fun α η x hx ↦ hval α η x (hqp _ hx)

theorem woodinCollapse_union {κ δ B : V} (hB : ∀ p ∈ B, p ∈ woodinCollapse κ δ)
    (hC : CompatibleFunctionFamily B) (hsmall : IsCardinalSmall κ (domain (⋃ˢ B))) :
    ⋃ˢ B ∈ woodinCollapse κ δ := by
  have hF : ∀ p ∈ B, IsFunction p := fun p hp ↦ ((mem_woodinCollapse _ _ _).mp (hB p hp)).2.1
  refine (mem_woodinCollapse _ _ _).mpr ⟨?_, isFunction_sUnion hF hC, hsmall, ?_⟩
  · intro z hz
    obtain ⟨p, hp, hz⟩ := mem_sUnion_iff.mp hz
    exact ((mem_woodinCollapse _ _ _).mp (hB p hp)).1 _ hz
  · intro α η x hx
    obtain ⟨p, hp, hx⟩ := mem_sUnion_iff.mp hx
    exact ((mem_woodinCollapse _ _ _).mp (hB p hp)).2.2.2 α η x hx

theorem woodinCollapse_sequence_union {κ δ γ H : V} (hκ : IsRegularCardinal κ)
    (hγ : γ ∈ κ) (hDC : InternalDependentChoiceAt γ)
    (hH : H ∈ (woodinCollapse κ δ) ^ γ) (hC : CompatibleFunctionFamily (range H)) :
    ⋃ˢ range H ∈ woodinCollapse κ δ := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ
  let := IsFunction.of_mem hH
  have hB : ∀ p ∈ range H, p ∈ woodinCollapse κ δ := range_subset_of_mem_function hH
  apply woodinCollapse_union hB hC
  let C := definableGraph γ (fun i ↦ domain (H ‘ i)) (by definability)
  have hdC : domain C = γ := domain_definableGraph _ _ _
  have hsmall : ∀ i ∈ γ, IsCardinalSmall κ (C ‘ i) := by
    intro i hi
    rw [show C ‘ i = domain (H ‘ i) from value_definableGraph _ _ _ hi]
    exact ((mem_woodinCollapse _ _ _).mp (function_value_mem hH hi)).2.2.1
  have hu := regularCardinal_small_union hκ hγ hDC hdC hsmall
  have he : domain (⋃ˢ range H) = ⋃ˢ range C := by
    apply mem_ext
    intro x
    rw [mem_domain_sUnion_iff]
    constructor
    · rintro ⟨p, hp, hx⟩
      obtain ⟨i, hip⟩ := mem_range_iff.mp hp
      have hi : i ∈ γ := domain_eq_of_mem_function hH ▸ mem_domain_of_kpair_mem hip
      have hpi := value_eq_of_kpair_mem hip
      have hc : C ‘ i = domain p := (value_definableGraph _ _ _ hi).trans (congrArg domain hpi)
      exact mem_sUnion_iff.mpr ⟨C ‘ i, mem_range_of_kpair_mem
        (kpair_value_mem (show i ∈ domain C from hdC.symm ▸ hi)), hc.symm ▸ hx⟩
    · rintro hx
      obtain ⟨D, hD, hx⟩ := mem_sUnion_iff.mp hx
      obtain ⟨i, hiD⟩ := mem_range_iff.mp hD
      have hi : i ∈ γ := hdC ▸ mem_domain_of_kpair_mem hiD
      have hDi : D = domain (H ‘ i) := (value_eq_of_kpair_mem hiD).symm.trans
        (value_definableGraph _ _ _ hi)
      exact ⟨H ‘ i, mem_range_of_kpair_mem (kpair_value_mem
        (show i ∈ domain H from (domain_eq_of_mem_function hH).symm ▸ hi)), hDi ▸ hx⟩
  exact he.symm ▸ hu

theorem woodinCollapse_closed {κ δ γ H : V} (hκ : IsRegularCardinal κ)
    (hγ : γ ∈ κ) (hDC : InternalDependentChoiceAt γ)
    (hH : H ∈ (woodinCollapse κ δ) ^ γ)
    (hdesc : ∀ i ∈ γ, ∀ j ∈ i, ⟨H ‘ i, H ‘ j⟩ₖ ∈ woodinCollapseOrder κ δ) :
    ∃ p ∈ woodinCollapse κ δ, ∀ i ∈ γ, ⟨p, H ‘ i⟩ₖ ∈ woodinCollapseOrder κ δ := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ
  let := IsFunction.of_mem hH
  have hc := compatible_range_of_increasing hH
    (fun p hp ↦ ((mem_woodinCollapse _ _ _).mp hp).2.1)
    (fun i hi j hj ↦ ((pair_mem_reverseInclusionOrder _ _ _).mp (hdesc i hi j hj)).2.2)
  have hp := woodinCollapse_sequence_union hκ hγ hDC hH hc
  refine ⟨⋃ˢ range H, hp, fun i hi ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hp, function_value_mem hH hi, ?_⟩⟩
  intro z hz
  exact mem_sUnion_iff.mpr ⟨H ‘ i, mem_range_of_kpair_mem
    (kpair_value_mem (show i ∈ domain H from (domain_eq_of_mem_function hH).symm ▸ hi)), hz⟩

end ZFVP
