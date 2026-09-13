import ZFVP.SetTheory.CohenAutomorphisms
import ZFVP.SetTheory.ForcingRegular

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Restrict a Cohen condition to the rows in `E`. -/
noncomputable def cohenConditionRestrict (p E : V) : V :=
  {z ∈ p ; kpair.π₁ (kpair.π₁ z) ∈ E}

instance cohenConditionRestrict_definable : ℒₛₑₜ-function₂[V] cohenConditionRestrict := by
  have h : ℒₛₑₜ-relation₃[V] (fun q p E ↦
      ∀ z, z ∈ q ↔ z ∈ p ∧ kpair.π₁ (kpair.π₁ z) ∈ E) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = cohenConditionRestrict (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [cohenConditionRestrict, mem_sep_iff]

theorem pair_mem_cohenConditionRestrict (p E i n b : V) :
    ⟨⟨i, n⟩ₖ, b⟩ₖ ∈ cohenConditionRestrict p E ↔ ⟨⟨i, n⟩ₖ, b⟩ₖ ∈ p ∧ i ∈ E := by
  simp only [cohenConditionRestrict, mem_sep_iff, kpair.π₁_kpair]

theorem cohenConditionRestrict_subset (p E : V) : cohenConditionRestrict p E ⊆ p := sep_subset

theorem cohenConditionRestrict_condition {I p : V} (hp : p ∈ cohenConditions I) (E : V) :
    cohenConditionRestrict p E ∈ cohenConditions I :=
  finitePartialFunction_subset hp (cohenConditionRestrict_subset p E)

theorem cohenConditionRestrict_weaker {I p : V} (hp : p ∈ cohenConditions I) (E : V) :
    ⟨p, cohenConditionRestrict p E⟩ₖ ∈ cohenOrder I :=
  (pair_mem_cohenOrder _ _ _).mpr
    ⟨hp, cohenConditionRestrict_condition hp E, cohenConditionRestrict_subset p E⟩

theorem cohenConditionRestrict_support (p E : V) :
    cohenSupport (cohenConditionRestrict p E) = cohenSupport p ∩ E := by
  apply mem_ext
  intro i
  simp only [mem_cohenSupport, pair_mem_cohenConditionRestrict, mem_inter_iff]
  constructor
  · rintro ⟨n, b, hb, hi⟩
    exact ⟨⟨n, b, hb⟩, hi⟩
  · rintro ⟨⟨n, b, hb⟩, hi⟩
    exact ⟨n, b, hb, hi⟩

theorem cohenConditionRestrict_inter (p E F : V) :
    cohenConditionRestrict (cohenConditionRestrict p E) F = cohenConditionRestrict p (E ∩ F) := by
  apply mem_ext
  intro z
  simp only [cohenConditionRestrict, mem_sep_iff, mem_inter_iff]
  tauto

/-- Move all unprotected rows of `p` away from `q`; agreement on the protected restriction
then makes the resulting conditions compatible. -/
theorem cohenConditionRestrict_compatible {I E p q π : V}
    (hp : p ∈ cohenConditions I) (hq : q ∈ cohenConditions I)
    (hπ : IsInternalPermutation I π) (hfix : ∀ i ∈ E, π ‘ i = i)
    (hmove : ∀ i ∈ cohenSupport p, i ∉ E → π ‘ i ∉ cohenSupport q)
    (hle : cohenConditionRestrict p E ⊆ q) :
    ForcingCompatible (cohenConditions I) (cohenOrder I) q (cohenConditionAction I π p) := by
  have hact := cohenConditionAction_condition hπ hp
  have : IsFunction q := ((mem_finitePartialFunctions _ _ _).mp hq).2.1
  apply (finitePartialFunctions_compatible_iff hq hact).mpr
  intro x y z hxy hxz
  obtain ⟨i, hi, n, hn, rfl⟩ := mem_prod_iff.mp
    (finitePartialFunction_domain hq _ (mem_domain_of_kpair_mem hxy))
  obtain ⟨j, hjz, hij⟩ := (cohenConditionAction_pair_iff hp).mp hxz
  have hjs : j ∈ cohenSupport p := (mem_cohenSupport p j).mpr ⟨n, z, hjz⟩
  by_cases hjE : j ∈ E
  · rw [hfix j hjE] at hij
    subst i
    exact IsFunction.unique hxy
      (hle _ ((pair_mem_cohenConditionRestrict p E j n z).mpr ⟨hjz, hjE⟩))
  · exact (hmove j hjs hjE (hij ▸ (mem_cohenSupport q i).mpr ⟨n, y, hxy⟩)).elim

end ZFVP
