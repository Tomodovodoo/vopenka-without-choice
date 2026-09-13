import ZFVP.SetTheory.OrderTypeBound
import ZFVP.SetTheory.InverseFunction
import ZFVP.SetTheory.MeasuredWellFounded

/-! Hartogs' non-embedding bound for every internal set, without AC. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def pulledMembership (D g : V) : V :=
  {p ∈ D ×ˢ D ; g ‘ (kpair.π₁ p) ∈ g ‘ (kpair.π₂ p)}

@[simp] theorem pair_mem_pulledMembership (D g x y : V) :
    ⟨x, y⟩ₖ ∈ pulledMembership D g ↔ x ∈ D ∧ y ∈ D ∧ g ‘ x ∈ g ‘ y := by
  simp [pulledMembership, and_assoc]

instance pulledMembership_definable : ℒₛₑₜ-function₂[V] pulledMembership := by
  have h : ℒₛₑₜ-relation₃ (fun R D g : V ↦ ∀ p, p ∈ R ↔
      p ∈ D ×ˢ D ∧ g ‘ (kpair.π₁ p) ∈ g ‘ (kpair.π₂ p)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = pulledMembership (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp [pulledMembership]

theorem pulledMembership_wellFounded (D g : V) : IsInternallyWellFounded (pulledMembership D g) D := by
  apply projectedRank_internallyWellFounded _ _ (fun x ↦ g ‘ x) (by definability)
  intro x _ y _ hxy
  exact rank_mem ((pair_mem_pulledMembership D g x y).mp hxy).2.2

theorem pulledMembership_wellOrder {D α g : V} [IsOrdinal α] (hg : g ∈ α ^ D) (hinj : Injective g) :
    IsInternalWellOrder (pulledMembership D g) D := by
  refine ⟨?_, pulledMembership_wellFounded D g, ?_, ?_⟩
  · intro p hp
    exact (mem_sep_iff.mp hp).1
  · intro x hx y _ z hz hxy hyz
    have : IsOrdinal (g ‘ z) := IsOrdinal.of_mem (function_value_mem hg hz)
    exact (pair_mem_pulledMembership D g x z).mpr ⟨hx, hz,
      IsOrdinal.toIsTransitive.mem_trans ((pair_mem_pulledMembership D g x y).mp hxy).2.2
        ((pair_mem_pulledMembership D g y z).mp hyz).2.2⟩
  · intro x hx y hy
    rcases (inferInstance : IsOrdinal α).trichotomy _ (function_value_mem hg hx) _ (function_value_mem hg hy)
      with hxy | heq | hyx
    · exact Or.inl ((pair_mem_pulledMembership D g x y).mpr ⟨hx, hy, hxy⟩)
    · exact Or.inr (Or.inl (injective_value_eq hg hinj hx hy heq))
    · exact Or.inr (Or.inr ((pair_mem_pulledMembership D g y x).mpr ⟨hy, hx, hyx⟩))

theorem pulledMembership_orderType {D α g : V} [IsOrdinal α] (hg : g ∈ α ^ D)
    (hinj : Injective g) (hsurj : range g = α) : internalOrderType (pulledMembership D g) D = α := by
  apply Eq.symm
  apply internalOrderType_unique (pulledMembership_wellOrder hg hinj) hg hsurj
  · intro x hx y hy heq
    exact injective_value_eq hg hinj hx hy heq
  · intro x hx y hy
    simp [hx, hy]

theorem ordinal_cardLE_mem_orderTypes {A α : V} [IsOrdinal α] (h : α ≤# A) :
    α ∈ orderTypesOfSubsets A := by
  obtain ⟨f, hf, hinj⟩ := h
  have : IsFunction f := IsFunction.of_mem hf
  have hg := converseGraph_mem_function hf hinj
  have hginj := converseGraph_injective f
  have hsurj : range (converseGraph f) = α := (range_converseGraph f).trans (domain_eq_of_mem_function hf)
  exact (mem_orderTypesOfSubsets A α).mpr ⟨range f, pulledMembership (range f) (converseGraph f),
    range_subset_of_mem_function hf, pulledMembership_wellOrder hg hginj,
    pulledMembership_orderType hg hginj hsurj⟩

theorem not_orderTypeBound_cardLE (A : V) : ¬orderTypeBound A ≤# A := by
  intro h
  obtain ⟨D, R, hD, hR, heq⟩ := (mem_orderTypesOfSubsets A _).mp (ordinal_cardLE_mem_orderTypes h)
  have hlt := orderType_lt_bound hD hR
  rw [heq] at hlt
  exact mem_irrefl (orderTypeBound A) hlt

theorem exists_ordinal_not_cardLE (A : V) : ∃ α : V, IsOrdinal α ∧ ¬α ≤# A :=
  ⟨orderTypeBound A, inferInstance, not_orderTypeBound_cardLE A⟩

end ZFVP
