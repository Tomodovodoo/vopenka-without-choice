import ZFVP.SetTheory.UniformCollapse

/-! Every internal strict well-order has a unique ordinal order type in ZF. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsInternalWellOrder (R D : V) : Prop :=
  R ⊆ D ×ˢ D ∧ IsInternallyWellFounded R D ∧
    (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, ⟨x, y⟩ₖ ∈ R → ⟨y, z⟩ₖ ∈ R → ⟨x, z⟩ₖ ∈ R) ∧
    ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ R ∨ x = y ∨ ⟨y, x⟩ₖ ∈ R

instance isInternalWellOrder_definable : ℒₛₑₜ-relation[V] IsInternalWellOrder := by
  unfold IsInternalWellOrder
  definability

theorem internalWellFounded_irrefl {R D : V} (hR : IsInternallyWellFounded R D) :
    ∀ x ∈ D, ⟨x, x⟩ₖ ∉ R := by
  apply internalWellFounded_induction hR (fun x ↦ ⟨x, x⟩ₖ ∉ R) (by definability)
  intro x hx ih hxx
  exact ih x hx hxx hxx

theorem internalWellOrder_extensional {R D : V} (hR : IsInternalWellOrder R D) : IsExtensionalOn R D := by
  intro x hx y hy hpred
  rcases hR.2.2.2 x hx y hy with hxy | heq | hyx
  · exact False.elim (internalWellFounded_irrefl hR.2.1 x hx ((hpred x hx).mpr hxy))
  · exact heq
  · exact False.elim (internalWellFounded_irrefl hR.2.1 y hy ((hpred y hy).mp hyx))

noncomputable def internalOrderType (R D : V) : V := range (mostowskiMap R D)

instance internalOrderType_definable : ℒₛₑₜ-function₂[V] internalOrderType := by
  unfold internalOrderType
  definability

theorem internalOrderType_ordinal {R D : V} (hR : IsInternalWellOrder R D) :
    IsOrdinal (internalOrderType R D) := by
  have hc := mostowskiMap_isTransitiveCollapse hR.2.1 (internalWellOrder_extensional hR)
  apply isOrdinal_iff.mpr
  refine ⟨hc.1, ?_⟩
  intro x hx y hy
  obtain ⟨u, hux⟩ := mem_range_iff.mp hx
  obtain ⟨v, hvy⟩ := mem_range_iff.mp hy
  have hf : IsFunction (mostowskiMap R D) := IsFunction.of_mem hc.2.1
  have hu : u ∈ D := domain_eq_of_mem_function hc.2.1 ▸ mem_domain_of_kpair_mem hux
  have hv : v ∈ D := domain_eq_of_mem_function hc.2.1 ▸ mem_domain_of_kpair_mem hvy
  have hxu := value_eq_of_kpair_mem hux
  have hyv := value_eq_of_kpair_mem hvy
  rcases hR.2.2.2 u hu v hv with huv | heq | hvu
  · exact Or.inl (by simpa only [hxu, hyv] using (hc.2.2.2.2 u hu v hv).mpr huv)
  · exact Or.inr (Or.inl (hxu.symm.trans ((congrArg (fun z ↦ (mostowskiMap R D) ‘ z) heq).trans hyv)))
  · exact Or.inr (Or.inr (by simpa only [hxu, hyv] using (hc.2.2.2.2 v hv u hu).mpr hvu))

theorem internalOrderType_unique {R D α f : V} (hR : IsInternalWellOrder R D)
    [IsOrdinal α] (hf : f ∈ α ^ D) (hsurj : range f = α)
    (hinj : ∀ x ∈ D, ∀ y ∈ D, f ‘ x = f ‘ y → x = y)
    (hmem : ∀ x ∈ D, ∀ y ∈ D, f ‘ x ∈ f ‘ y ↔ ⟨x, y⟩ₖ ∈ R) :
    α = internalOrderType R D := by
  have hc : IsTransitiveCollapse R D α f := ⟨inferInstance, hf, hsurj, hinj, hmem⟩
  have heq := (transitiveCollapse_unique hR.2.1 hc).2
  simpa only [internalOrderType, mostowskiMap_of_wellFounded hR.2.1] using heq

theorem ordinal_membership_wellOrder (α : V) [IsOrdinal α] :
    IsInternalWellOrder (membershipRelation α) α := by
  refine ⟨?_, membershipRelation_wellFounded α, ?_, ?_⟩
  · intro p hp
    exact (mem_sep_iff.mp hp).1
  · intro x hx y _ z hz hxy hyz
    have : IsOrdinal z := IsOrdinal.of_mem hz
    exact (pair_mem_membershipRelation α x z).mpr ⟨hx, hz,
      IsOrdinal.toIsTransitive.mem_trans ((pair_mem_membershipRelation α x y).mp hxy).2.2
        ((pair_mem_membershipRelation α y z).mp hyz).2.2⟩
  · intro x hx y hy
    rcases (inferInstance : IsOrdinal α).trichotomy x hx y hy with hxy | heq | hyx
    · exact Or.inl ((pair_mem_membershipRelation α x y).mpr ⟨hx, hy, hxy⟩)
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr ((pair_mem_membershipRelation α y x).mpr ⟨hy, hx, hyx⟩))

theorem internalOrderType_membership (α : V) [IsOrdinal α] : internalOrderType (membershipRelation α) α = α := by
  have hc := mostowskiMap_isTransitiveCollapse (membershipRelation_wellFounded α) (membershipRelation_extensional α)
  have : IsFunction (mostowskiMap (membershipRelation α) α) := IsFunction.of_mem hc.2.1
  apply mem_ext
  intro x
  change x ∈ range (mostowskiMap (membershipRelation α) α) ↔ x ∈ α
  rw [mem_range_iff]
  constructor
  · rintro ⟨y, hy⟩
    have hyα : y ∈ α := domain_eq_of_mem_function hc.2.1 ▸ mem_domain_of_kpair_mem hy
    have hxy := (collapse_membership_value α y hyα).symm.trans (value_eq_of_kpair_mem hy)
    exact hxy ▸ hyα
  · intro hx
    refine ⟨x, ?_⟩
    apply kpair_mem_iff_value.mpr
    exact ⟨by simpa only [domain_eq_of_mem_function hc.2.1] using hx,
      collapse_membership_value α x hx⟩

end ZFVP
