import ZFVP.SetTheory.EndExtensionSubsetCoding
import ZFVP.SetTheory.Hierarchy

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem ordinal_iff (j : MembershipEndExtension V W) (α : V) :
    IsOrdinal (j α) ↔ IsOrdinal α :=
  (j.bounded_defined isOrdinalFormula_bounded (fun v ↦ IsOrdinal (v 0))
    (fun v ↦ IsOrdinal (v 0)) ![α]).symm

/-- Powerset agreement below a rank makes the entire rank agree. The induction
is internal to the target, using the image of the ground hierarchy table. -/
theorem map_hierarchy_of_power_agreement (j : MembershipEndExtension V W) {κ : V} [IsOrdinal κ]
    (hp : ∀ α ∈ κ, j (℘ (hierarchy α)) = ℘ (j (hierarchy α))) :
    j (hierarchy κ) = hierarchy (j κ) := by
  let H := definableGraph (succ κ) hierarchy (hierarchy_definable (V := V))
  let F := j H
  have hv (β : V) (hβ : β ∈ succ κ) : F ‘ (j β) = j (hierarchy β) := by
    change (j H) ‘ (j β) = _
    rw [← j.map_value_total]
    exact congrArg j (value_definableGraph _ _ _ hβ)
  have hall := transfinite_induction
    (fun α : W ↦ α ∈ j (succ κ) → F ‘ α = hierarchy α) (by definability) ?_
  · let := (j.ordinal_iff κ).mpr inferInstance
    have h := hall (IsOrdinal.toOrdinal (j κ)) ((j.mem_iff _ _).mpr (mem_succ_self κ))
    change F ‘ (j κ) = hierarchy (j κ) at h
    rwa [hv κ (mem_succ_self κ)] at h
  intro α ih hα
  obtain ⟨β, hβ, hαβ⟩ := j.endExtension (succ κ) (α : W) hα
  let := IsOrdinal.of_mem hβ
  have hηκ (η : V) (hη : η ∈ β) : η ∈ κ := by
    rcases mem_succ_iff.mp hβ with rfl | hβκ
    · exact hη
    · exact IsOrdinal.toIsTransitive.mem_trans hη hβκ
  have hηeq (η : V) (hη : η ∈ β) : j (hierarchy η) = hierarchy (j η) := by
    let := IsOrdinal.of_mem hη
    let := (j.ordinal_iff η).mpr inferInstance
    have hηα : j η ∈ (α : W) := hαβ.symm ▸ (j.mem_iff _ _).mpr hη
    have hηs : η ∈ succ κ := mem_succ_iff.mpr (Or.inr (hηκ η hη))
    have hh := ih (IsOrdinal.toOrdinal (j η)) hηα ((j.mem_iff _ _).mpr hηs)
    change F ‘ (j η) = hierarchy (j η) at hh
    rwa [hv η hηs] at hh
  rw [hαβ, hv β hβ]
  let := (j.ordinal_iff β).mpr inferInstance
  apply mem_ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := j.endExtension (hierarchy β) x hx
    obtain ⟨η, hη, hyη⟩ := (mem_hierarchy_iff_of_ordinal β y).mp hy
    apply (mem_hierarchy_iff_of_ordinal (j β) (j y)).mpr
    refine ⟨j η, (j.mem_iff _ _).mpr hη, ?_⟩
    rw [← hηeq η hη]
    exact (j.subset_iff _ _).mpr hyη
  · intro hx
    obtain ⟨a, ha, hxa⟩ := (mem_hierarchy_iff_of_ordinal (j β) x).mp hx
    obtain ⟨η, hη, rfl⟩ := j.endExtension β a ha
    rw [← hηeq η hη] at hxa
    have hxp : x ∈ j (℘ (hierarchy η)) := by
      rw [hp η (hηκ η hη)]
      exact mem_power_iff.mpr hxa
    obtain ⟨y, hy, rfl⟩ := j.endExtension (℘ (hierarchy η)) x hxp
    exact (j.mem_iff _ _).mpr ((mem_hierarchy_iff_of_ordinal β y).mpr
      ⟨η, hη, mem_power_iff.mp hy⟩)

end MembershipEndExtension
end ZFVP
