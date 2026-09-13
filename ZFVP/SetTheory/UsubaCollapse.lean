import ZFVP.SetTheory.WoodinCollapseDense
import ZFVP.SetTheory.ForcingClosure

/-! Usuba, Definition 4.6: `Col(κ,S)` consists of partial functions from
`κ` to `S` with well-orderable domain of cardinality below `κ`, ordered
by reverse inclusion. No internal Choice assumption enters the definition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def usubaCollapse (κ S : V) : V :=
  {p ∈ ℘ (κ ×ˢ S) ; IsFunction p ∧ IsCardinalSmall κ (domain p)}

theorem mem_usubaCollapse (κ S p : V) : p ∈ usubaCollapse κ S ↔
    p ⊆ κ ×ˢ S ∧ IsFunction p ∧ IsCardinalSmall κ (domain p) := by
  simp only [usubaCollapse, mem_sep_iff, mem_power_iff]

instance usubaCollapse_definable : ℒₛₑₜ-function₂[V] usubaCollapse := by
  have h : ℒₛₑₜ-relation₃[V] (fun P κ S ↦ ∀ p, p ∈ P ↔
      p ⊆ κ ×ˢ S ∧ IsFunction p ∧ IsCardinalSmall κ (domain p)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = usubaCollapse (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_usubaCollapse]

noncomputable def usubaCollapseOrder (κ S : V) : V :=
  reverseInclusionOrder (usubaCollapse κ S)

instance usubaCollapseOrder_definable : ℒₛₑₜ-function₂[V] usubaCollapseOrder := by
  unfold usubaCollapseOrder
  definability

theorem usubaCollapse_poset (κ S : V) :
    IsForcingPoset (usubaCollapse κ S) (usubaCollapseOrder κ S) :=
  reverseInclusionOrder_poset _

theorem empty_mem_usubaCollapse {κ : V} (hκ : (∅ : V) ∈ κ) (S : V) :
    (∅ : V) ∈ usubaCollapse κ S := by
  apply (mem_usubaCollapse _ _ _).mpr
  exact ⟨by simp, inferInstance, ∅, hκ, by simp⟩

theorem usubaCollapse_top {κ : V} (hκ : (∅ : V) ∈ κ) (S : V) :
    IsForcingTop (usubaCollapse κ S) (usubaCollapseOrder κ S) ∅ :=
  ⟨empty_mem_usubaCollapse hκ S, fun p hp ↦
    (pair_mem_reverseInclusionOrder _ _ _).mpr
      ⟨hp, empty_mem_usubaCollapse hκ S, by simp⟩⟩

theorem usubaCollapse_subset {κ S p q : V}
    (hp : p ∈ usubaCollapse κ S) (hqp : q ⊆ p) : q ∈ usubaCollapse κ S := by
  obtain ⟨hsub, hfun, hsmall⟩ := (mem_usubaCollapse _ _ _).mp hp
  let := hfun
  refine (mem_usubaCollapse _ _ _).mpr
    ⟨subset_trans hqp hsub, IsFunction.ofSubset p q hqp, hsmall.subset ?_⟩
  intro x hx
  obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
  exact mem_domain_of_kpair_mem (hqp _ hxy)

theorem usubaCollapse_insert {κ S p α x : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ usubaCollapse κ S) (hα : α ∈ κ) (hx : x ∈ S)
    (hfresh : α ∉ domain p) : insert ⟨α, x⟩ₖ p ∈ usubaCollapse κ S := by
  obtain ⟨hsub, hfun, hsmall⟩ := (mem_usubaCollapse _ _ _).mp hp
  let := hfun
  refine (mem_usubaCollapse _ _ _).mpr ⟨?_, IsFunction.insert p α x hfresh, ?_⟩
  · intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact kpair_mem_iff.mpr ⟨hα, hx⟩
    · exact hsub _ hz
  · simpa only [domain_insert] using hsmall.insert hκ α

theorem usubaCollapse_fresh {κ S p : V} (hκ : IsInitialOrdinal κ)
    (hp : p ∈ usubaCollapse κ S) : ∃ α ∈ κ, α ∉ domain p := by
  classical
  by_contra h
  have hsub : κ ⊆ domain p := by
    intro α hα
    by_contra ha
    exact h ⟨α, hα, ha⟩
  obtain ⟨ξ, hξ, hsmall⟩ := ((mem_usubaCollapse _ _ _).mp hp).2.2
  exact hκ.2 ξ hξ ((cardLE_of_subset hsub).trans hsmall)

theorem usubaCollapse_domain_dense {κ S α : V} (hκ : IsRegularCardinal κ)
    (hS : IsNonempty S) (hα : α ∈ κ) :
    ForcingDense (usubaCollapse κ S) (usubaCollapseOrder κ S)
      {p ∈ usubaCollapse κ S ; α ∈ domain p} := by
  classical
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, fun p hp ↦ ?_⟩
  by_cases ha : α ∈ domain p
  · exact ⟨p, mem_sep_iff.mpr ⟨hp, ha⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hp, hp, subset_refl _⟩⟩
  · obtain ⟨x, hx⟩ := hS
    have hq := usubaCollapse_insert hκ hp hα hx ha
    refine ⟨insert ⟨α, x⟩ₖ p, mem_sep_iff.mpr ⟨hq, by simp⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, hp, ?_⟩⟩
    exact fun z hz ↦ mem_insert.mpr (Or.inr hz)

theorem usubaCollapse_range_dense {κ S x : V} (hκ : IsRegularCardinal κ)
    (hx : x ∈ S) :
    ForcingDense (usubaCollapse κ S) (usubaCollapseOrder κ S)
      {p ∈ usubaCollapse κ S ; x ∈ range p} := by
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, fun p hp ↦ ?_⟩
  obtain ⟨α, hα, hfresh⟩ := usubaCollapse_fresh hκ.1 hp
  have hq := usubaCollapse_insert hκ hp hα hx hfresh
  refine ⟨insert ⟨α, x⟩ₖ p, mem_sep_iff.mpr ⟨hq, ?_⟩,
    (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, hp,
      fun z hz ↦ mem_insert.mpr (Or.inr hz)⟩⟩
  exact mem_range_of_kpair_mem (show ⟨α, x⟩ₖ ∈ insert ⟨α, x⟩ₖ p by simp)

theorem usubaCollapse_union {κ S B : V}
    (hB : ∀ p ∈ B, p ∈ usubaCollapse κ S)
    (hC : CompatibleFunctionFamily B) (hsmall : IsCardinalSmall κ (domain (⋃ˢ B))) :
    ⋃ˢ B ∈ usubaCollapse κ S := by
  have hF : ∀ p ∈ B, IsFunction p :=
    fun p hp ↦ ((mem_usubaCollapse _ _ _).mp (hB p hp)).2.1
  refine (mem_usubaCollapse _ _ _).mpr ⟨?_, isFunction_sUnion hF hC, hsmall⟩
  intro z hz
  obtain ⟨p, hp, hz⟩ := mem_sUnion_iff.mp hz
  exact ((mem_usubaCollapse _ _ _).mp (hB p hp)).1 _ hz

theorem usubaCollapse_sequence_union {κ S γ H : V} (hκ : IsRegularCardinal κ)
    (hγ : γ ∈ κ) (hDC : InternalDependentChoiceAt γ)
    (hH : H ∈ (usubaCollapse κ S) ^ γ) (hC : CompatibleFunctionFamily (range H)) :
    ⋃ˢ range H ∈ usubaCollapse κ S := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ
  let := IsFunction.of_mem hH
  apply usubaCollapse_union (range_subset_of_mem_function hH) hC
  let C := definableGraph γ (fun i ↦ domain (H ‘ i)) (by definability)
  have hdC : domain C = γ := domain_definableGraph _ _ _
  have hsmall : ∀ i ∈ γ, IsCardinalSmall κ (C ‘ i) := by
    intro i hi
    rw [show C ‘ i = domain (H ‘ i) from value_definableGraph _ _ _ hi]
    exact ((mem_usubaCollapse _ _ _).mp (function_value_mem hH hi)).2.2
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
      have hc : C ‘ i = domain p :=
        (value_definableGraph _ _ _ hi).trans (congrArg domain hpi)
      exact mem_sUnion_iff.mpr ⟨C ‘ i, mem_range_of_kpair_mem
        (kpair_value_mem (show i ∈ domain C from hdC.symm ▸ hi)), hc.symm ▸ hx⟩
    · intro hx
      obtain ⟨D, hD, hx⟩ := mem_sUnion_iff.mp hx
      obtain ⟨i, hiD⟩ := mem_range_iff.mp hD
      have hi : i ∈ γ := hdC ▸ mem_domain_of_kpair_mem hiD
      have hDi : D = domain (H ‘ i) :=
        (value_eq_of_kpair_mem hiD).symm.trans (value_definableGraph _ _ _ hi)
      exact ⟨H ‘ i, mem_range_of_kpair_mem (kpair_value_mem
        (show i ∈ domain H from (domain_eq_of_mem_function hH).symm ▸ hi)), hDi ▸ hx⟩
  exact he.symm ▸ hu

theorem usubaCollapse_closedAt {κ S γ : V} (hκ : IsRegularCardinal κ)
    (hγ : γ ∈ κ) (hDC : InternalDependentChoiceAt γ) :
    IsForcingClosedAt (usubaCollapse κ S) (usubaCollapseOrder κ S) γ := by
  intro H hH
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ
  let := IsFunction.of_mem hH.1
  have hc := compatible_range_of_increasing hH.1
    (fun p hp ↦ ((mem_usubaCollapse _ _ _).mp hp).2.1)
    (fun i hi j hj ↦ ((pair_mem_reverseInclusionOrder _ _ _).mp (hH.2 i hi j hj)).2.2)
  have hp := usubaCollapse_sequence_union hκ hγ hDC hH.1 hc
  refine ⟨⋃ˢ range H, hp, fun i hi ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hp, function_value_mem hH.1 hi, ?_⟩⟩
  intro z hz
  exact mem_sUnion_iff.mpr ⟨H ‘ i, mem_range_of_kpair_mem
    (kpair_value_mem (show i ∈ domain H from (domain_eq_of_mem_function hH.1).symm ▸ hi)), hz⟩

theorem usubaCollapse_closedBelow {κ : V} (hκ : IsRegularCardinal κ)
    (hDC : ∀ γ ∈ κ, InternalDependentChoiceAt γ) (S : V) :
    IsForcingClosedBelow (usubaCollapse κ S) (usubaCollapseOrder κ S) κ :=
  fun γ hγ ↦ usubaCollapse_closedAt hκ hγ (hDC γ hγ)

theorem usubaCollapse_denseIntersection {κ S γ D : V} (hκ : IsRegularCardinal κ)
    (hγ : γ ∈ κ) (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α)
    (hD : ∀ i ∈ γ, ForcingDense (usubaCollapse κ S) (usubaCollapseOrder κ S) (D ‘ i) ∧
      IsForcingDownwardClosed (usubaCollapse κ S) (usubaCollapseOrder κ S) (D ‘ i)) :
    ForcingDense (usubaCollapse κ S) (usubaCollapseOrder κ S)
      {q ∈ usubaCollapse κ S ; ∀ i ∈ γ, q ∈ D ‘ i} := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ
  apply forcingClosed_denseIntersection (usubaCollapse_poset κ S).1 (hDC γ hγ) ?_ hD
  intro α hαord hα
  let := hαord
  have hακ : α ∈ κ := ordinal_mem_of_subset_mem hα hγ
  exact usubaCollapse_closedAt hκ hακ (hDC α hακ)

end ZFVP
