import ZFVP.SetTheory.LevyCollapse
import ZFVP.SetTheory.FiniteSets

/-! The ordinal support of a Levy collapse condition: the finite set of ordinals `α` with
some `(n, α)` in its domain. Cutting a condition below `β` keeps exactly the part of its
support below `β`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def ordinalSupport (p : V) : V :=
  repl (fun z ↦ kpair.π₂ (kpair.π₁ z)) (by definability) p

instance ordinalSupport_definable : ℒₛₑₜ-function₁[V] ordinalSupport := by
  unfold ordinalSupport
  definability

theorem mem_ordinalSupport_iff {κ p γ : V} (hp : p ∈ levyCollapse κ) :
    γ ∈ ordinalSupport p ↔ ∃ n β, ⟨⟨n, γ⟩ₖ, β⟩ₖ ∈ p := by
  have hsub := ((mem_finitePartialFunctions _ _ p).mp (levyCollapse_finitePartialFunction hp)).1
  constructor
  · intro h
    obtain ⟨z, hz, rfl⟩ := (repl_spec _).mp h
    obtain ⟨x, hx, β, _, rfl⟩ := mem_prod_iff.mp (hsub _ hz)
    obtain ⟨n, _, α, _, rfl⟩ := mem_prod_iff.mp hx
    exact ⟨n, β, by simpa using hz⟩
  · rintro ⟨n, β, h⟩
    exact (repl_spec _).mpr ⟨_, h, by simp⟩

theorem ordinalSupport_subset {κ p : V} (hp : p ∈ levyCollapse κ) : ordinalSupport p ⊆ κ := by
  intro γ hγ
  obtain ⟨n, β, h⟩ := (mem_ordinalSupport_iff hp).mp hγ
  have hsub := ((mem_finitePartialFunctions _ _ p).mp (levyCollapse_finitePartialFunction hp)).1
  exact (kpair_mem_iff.mp (kpair_mem_iff.mp (hsub _ h)).1).2

theorem levyCollapse_internallyFinite {κ p : V} (hp : p ∈ levyCollapse κ) :
    IsInternallyFinite p := by
  obtain ⟨_, hfun, hfin⟩ := (mem_finitePartialFunctions _ _ p).mp (levyCollapse_finitePartialFunction hp)
  exact internallyFinite_function hfin

theorem ordinalSupport_finite {κ p : V} (hp : p ∈ levyCollapse κ) :
    IsInternallyFinite (ordinalSupport p) :=
  internallyFinite_repl _ _ (levyCollapse_internallyFinite hp)

theorem ordinalSupport_mono {p q : V} (h : q ⊆ p) : ordinalSupport q ⊆ ordinalSupport p := by
  intro γ hγ
  obtain ⟨z, hz, rfl⟩ := (repl_spec _).mp hγ
  exact (repl_spec _).mpr ⟨z, h _ hz, rfl⟩

theorem levyCut_eq_of_support {κ β p : V} (hp : p ∈ levyCollapse κ)
    (h : ordinalSupport p ⊆ β) : levyCut β p = p := by
  apply levyCut_of_subset
  intro z hz
  have hsub := ((mem_finitePartialFunctions _ _ p).mp (levyCollapse_finitePartialFunction hp)).1
  obtain ⟨x, hx, δ, _, rfl⟩ := mem_prod_iff.mp (hsub _ hz)
  obtain ⟨n, hn, α, _, rfl⟩ := mem_prod_iff.mp hx
  have hα : α ∈ ordinalSupport p := (mem_ordinalSupport_iff hp).mpr ⟨n, δ, hz⟩
  exact ⟨⟨n, α⟩ₖ, kpair_mem_iff.mpr ⟨hn, h _ hα⟩, δ, rfl⟩

theorem kpair_mem_levyCut_iff' {κ β p n γ δ : V} (hp : p ∈ levyCollapse κ) :
    ⟨⟨n, γ⟩ₖ, δ⟩ₖ ∈ levyCut β p ↔ ⟨⟨n, γ⟩ₖ, δ⟩ₖ ∈ p ∧ γ ∈ β := by
  rw [kpair_mem_levyCut_iff]
  constructor
  · rintro ⟨h, hx⟩
    exact ⟨h, (kpair_mem_iff.mp hx).2⟩
  · rintro ⟨h, hγ⟩
    have hsub := ((mem_finitePartialFunctions _ _ p).mp (levyCollapse_finitePartialFunction hp)).1
    have hn : n ∈ (ω : V) := (kpair_mem_iff.mp (kpair_mem_iff.mp (hsub _ h)).1).1
    exact ⟨h, kpair_mem_iff.mpr ⟨hn, hγ⟩⟩

theorem ordinalSupport_levyCut {κ β p : V} (hp : p ∈ levyCollapse κ) :
    ordinalSupport (levyCut β p) = ordinalSupport p ∩ β := by
  have hq := levyCollapse_subset hp (levyCut_subset β p)
  ext γ
  rw [mem_inter_iff, mem_ordinalSupport_iff hq, mem_ordinalSupport_iff hp]
  constructor
  · rintro ⟨n, δ, h⟩
    obtain ⟨h, hγ⟩ := (kpair_mem_levyCut_iff' hp).mp h
    exact ⟨⟨n, δ, h⟩, hγ⟩
  · rintro ⟨⟨n, δ, h⟩, hγ⟩
    exact ⟨n, δ, (kpair_mem_levyCut_iff' hp).mpr ⟨h, hγ⟩⟩

instance levyCut_definable : ℒₛₑₜ-function₂[V] levyCut := by
  unfold levyCut
  definability

theorem levyCut_value_definable (lam f : V) : ℒₛₑₜ-function₁[V] (fun α ↦ levyCut lam (f ‘ α)) := by
  definability

theorem levyCollapse_compatible_of_cut {κ lam p q : V} (hp : p ∈ levyCollapse κ)
    (hq : q ∈ levyCollapse κ) (hpc : levyCut lam p = p) (hqc : levyCut lam q = levyCut lam p) :
    ForcingCompatible (levyCollapse κ) (levyOrder κ) p q := by
  rw [levyCollapse_compatible_iff hp hq]
  intro x y z hxy hxz
  have hxy' : ⟨x, y⟩ₖ ∈ q := by
    rw [← hpc, ← hqc] at hxy
    exact levyCut_subset _ _ _ hxy
  have hqfun : IsFunction q :=
    ((mem_finitePartialFunctions _ _ q).mp (levyCollapse_finitePartialFunction hq)).2.1
  exact IsFunction.unique (hf := hqfun) hxy' hxz

theorem levyCollapse_compatible_of_split {κ lam δ p q : V} (hp : p ∈ levyCollapse κ)
    (hq : q ∈ levyCollapse κ) (hcut : levyCut lam p = levyCut lam q)
    (hpδ : ordinalSupport p ⊆ δ) (hqδ : ordinalSupport q ∩ δ ⊆ lam) :
    ForcingCompatible (levyCollapse κ) (levyOrder κ) p q := by
  rw [levyCollapse_compatible_iff hp hq]
  intro x y z hxy hxz
  have hsub := ((mem_finitePartialFunctions _ _ _).mp (levyCollapse_finitePartialFunction hp)).1
  obtain ⟨x', hx', y', _, hxy'⟩ := mem_prod_iff.mp (hsub _ hxy)
  obtain ⟨hxx', hyy'⟩ := kpair_iff.mp hxy'
  subst hxx'
  subst hyy'
  obtain ⟨n, hn, γ, hγ, rfl⟩ := mem_prod_iff.mp hx'
  have hγp : γ ∈ ordinalSupport p := (mem_ordinalSupport_iff hp).mpr ⟨n, y, hxy⟩
  have hγq : γ ∈ ordinalSupport q := (mem_ordinalSupport_iff hq).mpr ⟨n, z, hxz⟩
  have hγlam : γ ∈ lam := hqδ _ (mem_inter_iff.mpr ⟨hγq, hpδ _ hγp⟩)
  have hcutfun : IsFunction (levyCut lam p) :=
    ((mem_finitePartialFunctions _ _ _).mp (levyCollapse_finitePartialFunction
      (levyCollapse_subset hp (levyCut_subset lam p)))).2.1
  have h1 : ⟨⟨n, γ⟩ₖ, y⟩ₖ ∈ levyCut lam p := (kpair_mem_levyCut_iff' hp).mpr ⟨hxy, hγlam⟩
  have h2 : ⟨⟨n, γ⟩ₖ, z⟩ₖ ∈ levyCut lam p := by
    rw [hcut]
    exact (kpair_mem_levyCut_iff' hq).mpr ⟨hxz, hγlam⟩
  exact IsFunction.unique (hf := hcutfun) h1 h2

end ZFVP
