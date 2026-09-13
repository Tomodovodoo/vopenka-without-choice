import ZFVP.SetTheory.FinitePartialFunctions
import ZFVP.SetTheory.FunctionValue

/-! The Levy collapse `Coll(ω, <κ)`: finite partial functions `p` on `ω × κ` with
`p(n, α) ∈ α`, ordered by reverse inclusion, with the empty condition on top. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def levyCollapse (κ : V) : V :=
  {p ∈ finitePartialFunctions ((ω : V) ×ˢ κ) κ ; ∀ z ∈ p, kpair.π₂ z ∈ kpair.π₂ (kpair.π₁ z)}

noncomputable def levyOrder (κ : V) : V := reverseInclusionOrder (levyCollapse κ)

theorem mem_levyCollapse_iff (κ p : V) :
    p ∈ levyCollapse κ ↔ p ∈ finitePartialFunctions ((ω : V) ×ˢ κ) κ ∧
      ∀ n α β, ⟨⟨n, α⟩ₖ, β⟩ₖ ∈ p → β ∈ α := by
  constructor
  · intro hp
    obtain ⟨hfp, hv⟩ := mem_sep_iff.mp hp
    refine ⟨hfp, fun n α β hz ↦ ?_⟩
    have := hv _ hz
    simpa using this
  · rintro ⟨hfp, hv⟩
    refine mem_sep_iff.mpr ⟨hfp, fun z hz ↦ ?_⟩
    have hz' := ((mem_finitePartialFunctions _ _ _).mp hfp).1 _ hz
    obtain ⟨x, hx, β, _, rfl⟩ := mem_prod_iff.mp hz'
    obtain ⟨n, _, α, _, rfl⟩ := mem_prod_iff.mp hx
    simpa using hv n α β hz

instance levyCollapse_definable : ℒₛₑₜ-function₁[V] levyCollapse := by
  have hd : ℒₛₑₜ-relation[V] (fun L κ ↦ ∀ p, p ∈ L ↔ p ∈ finitePartialFunctions ((ω : V) ×ˢ κ) κ ∧
    ∀ z ∈ p, kpair.π₂ z ∈ kpair.π₂ (kpair.π₁ z)) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = levyCollapse (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [levyCollapse, mem_sep_iff]

instance levyOrder_definable : ℒₛₑₜ-function₁[V] levyOrder := by
  unfold levyOrder
  definability

theorem levyCollapse_poset (κ : V) : IsForcingPoset (levyCollapse κ) (levyOrder κ) :=
  reverseInclusionOrder_poset _

theorem empty_mem_levyCollapse (κ : V) : (∅ : V) ∈ levyCollapse κ :=
  (mem_levyCollapse_iff κ ∅).mpr ⟨empty_mem_finitePartialFunctions _ _, fun _ _ _ h ↦ (not_mem_empty h).elim⟩

theorem levyCollapse_top (κ : V) : IsForcingTop (levyCollapse κ) (levyOrder κ) ∅ :=
  ⟨empty_mem_levyCollapse κ, fun p hp ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hp, empty_mem_levyCollapse κ, by simp⟩⟩

theorem levyCollapse_finitePartialFunction {κ p : V} (hp : p ∈ levyCollapse κ) :
    p ∈ finitePartialFunctions ((ω : V) ×ˢ κ) κ :=
  ((mem_levyCollapse_iff κ p).mp hp).1

theorem levyCollapse_value {κ p n α β : V} (hp : p ∈ levyCollapse κ) (h : ⟨⟨n, α⟩ₖ, β⟩ₖ ∈ p) :
    β ∈ α :=
  ((mem_levyCollapse_iff κ p).mp hp).2 n α β h

theorem levyCollapse_subset {κ p q : V} (hp : p ∈ levyCollapse κ) (hq : q ⊆ p) :
    q ∈ levyCollapse κ :=
  (mem_levyCollapse_iff κ q).mpr
    ⟨finitePartialFunction_subset (levyCollapse_finitePartialFunction hp) hq,
      fun n α β h ↦ levyCollapse_value hp (hq _ h)⟩

theorem levyCollapse_union {κ p q : V} (hp : p ∈ levyCollapse κ) (hq : q ∈ levyCollapse κ)
    (hc : ∀ x y z, ⟨x, y⟩ₖ ∈ p → ⟨x, z⟩ₖ ∈ q → y = z) : p ∪ q ∈ levyCollapse κ := by
  refine (mem_levyCollapse_iff κ _).mpr
    ⟨finitePartialFunction_union (levyCollapse_finitePartialFunction hp)
      (levyCollapse_finitePartialFunction hq) hc, fun n α β h ↦ ?_⟩
  rcases mem_union_iff.mp h with h | h
  · exact levyCollapse_value hp h
  · exact levyCollapse_value hq h

theorem levyCollapse_compatible_iff {κ p q : V} (hp : p ∈ levyCollapse κ)
    (hq : q ∈ levyCollapse κ) :
    ForcingCompatible (levyCollapse κ) (levyOrder κ) p q ↔
      ∀ x y z, ⟨x, y⟩ₖ ∈ p → ⟨x, z⟩ₖ ∈ q → y = z := by
  constructor
  · rintro ⟨r, hr, hrp, hrq⟩ x y z hxy hxz
    have : IsFunction r := ((mem_finitePartialFunctions _ _ r).mp
      (levyCollapse_finitePartialFunction hr)).2.1
    exact IsFunction.unique (((pair_mem_reverseInclusionOrder _ _ _).mp hrp).2.2 _ hxy)
      (((pair_mem_reverseInclusionOrder _ _ _).mp hrq).2.2 _ hxz)
  · intro hc
    have hu := levyCollapse_union hp hq hc
    exact ⟨p ∪ q, hu, (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, hp, subset_union_left p q⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, hq, subset_union_right p q⟩⟩

theorem levyCollapse_mono {β κ : V} (h : β ⊆ κ) : levyCollapse β ⊆ levyCollapse κ := by
  intro p hp
  obtain ⟨hfp, hv⟩ := (mem_levyCollapse_iff β p).mp hp
  obtain ⟨hsub, hfun, hfin⟩ := (mem_finitePartialFunctions _ _ p).mp hfp
  refine (mem_levyCollapse_iff κ p).mpr ⟨(mem_finitePartialFunctions _ _ p).mpr ⟨?_, hfun, hfin⟩, hv⟩
  exact subset_trans hsub (prod_subset_prod_of_subset
    (prod_subset_prod_of_subset (subset_refl _) h) h)

/-- The part of a condition below `β`. -/
noncomputable def levyCut (β p : V) : V := p ↾ ((ω : V) ×ˢ β)

theorem levyCut_subset (β p : V) : levyCut β p ⊆ p := by
  intro z hz
  exact (mem_restrict_iff.mp hz).1

theorem kpair_mem_levyCut_iff (β p x y : V) :
    ⟨x, y⟩ₖ ∈ levyCut β p ↔ ⟨x, y⟩ₖ ∈ p ∧ x ∈ (ω : V) ×ˢ β :=
  kpair_mem_restrict_iff

theorem levyCut_mem {κ β p : V} [IsOrdinal β] (hp : p ∈ levyCollapse κ) :
    levyCut β p ∈ levyCollapse β := by
  have hq := levyCollapse_subset hp (levyCut_subset β p)
  obtain ⟨hfp, hv⟩ := (mem_levyCollapse_iff κ _).mp hq
  obtain ⟨hsub, hfun, hfin⟩ := (mem_finitePartialFunctions _ _ _).mp hfp
  refine (mem_levyCollapse_iff β _).mpr ⟨(mem_finitePartialFunctions _ _ _).mpr ⟨?_, hfun, hfin⟩, hv⟩
  intro z hz
  obtain ⟨x, hx, γ, hγ, rfl⟩ := mem_prod_iff.mp (hsub _ hz)
  have hxβ : x ∈ (ω : V) ×ˢ β := ((kpair_mem_levyCut_iff β p x γ).mp hz).2
  obtain ⟨n, hn, α, hα, rfl⟩ := mem_prod_iff.mp hxβ
  have hγα : γ ∈ α := hv n α γ hz
  exact kpair_mem_iff.mpr ⟨hxβ, IsOrdinal.toIsTransitive.mem_trans hγα hα⟩

theorem levyCut_of_subset {β p : V} (hp : ∀ z ∈ p, ∃ x ∈ (ω : V) ×ˢ β, ∃ y, z = ⟨x, y⟩ₖ) :
    levyCut β p = p := by
  ext z
  constructor
  · exact fun h ↦ levyCut_subset β p _ h
  · intro hz
    exact mem_restrict_iff.mpr ⟨hz, hp z hz⟩

end ZFVP
