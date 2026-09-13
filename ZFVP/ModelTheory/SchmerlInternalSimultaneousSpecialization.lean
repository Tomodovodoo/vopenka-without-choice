import ZFVP.ModelTheory.SchmerlInternalTaggedBranchCardinality
import ZFVP.ModelTheory.SchmerlInternalTaggedTreeChecks

/-! One actual forcing extension weakly specializes an internal family of trees
and preserves the full cofinal branches of every component. -/

set_option autoImplicit false

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace Schmerl

noncomputable def taggedComponentColor (D f j : V) : V :=
  definableGraph (D ‘ j) (fun x ↦ f ‘ ⟨j, x⟩ₖ) (by definability)

theorem taggedComponentColor_definable (D f : V) : ℒₛₑₜ-function₁[V] (taggedComponentColor D f) := by
  have hh : ℒₛₑₜ-relation[V] (fun c j ↦ ∀ p, p ∈ c ↔ ∃ x ∈ D ‘ j, p = ⟨x, f ‘ ⟨j, x⟩ₖ⟩ₖ) := by definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [taggedComponentColor, mem_definableGraph_iff]
  rfl

theorem taggedComponentColor_value {D f j x : V} (hx : x ∈ D ‘ j) :
    (taggedComponentColor D f j) ‘ x = f ‘ ⟨j, x⟩ₖ := value_definableGraph _ _ _ hx

theorem taggedComponentColor_spec {J D S f j : V} (hj : j ∈ J)
    (hf : f ∈ (ω : V) ^ internalTaggedTree J D)
    (hweak : InternallyWeakSpecialization (internalTaggedTree J D) (internalTaggedTreeOrder J D S) f) :
    taggedComponentColor D f j ∈ (ω : V) ^ (D ‘ j) ∧
      InternallyWeakSpecialization (D ‘ j) (S ‘ j) (taggedComponentColor D f j) := by
  refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun x hx ↦ function_value_mem hf (pair_mem_internalTaggedTree.mpr ⟨hj, hx⟩)), ?_⟩
  intro x hx y hy z hz hxy hxz hfx hfy
  rw [taggedComponentColor_value hx, taggedComponentColor_value hy] at hfx
  rw [taggedComponentColor_value hx, taggedComponentColor_value hz] at hfy
  exact (hweak _ (pair_mem_internalTaggedTree.mpr ⟨hj, hx⟩)
    _ (pair_mem_internalTaggedTree.mpr ⟨hj, hy⟩) _ (pair_mem_internalTaggedTree.mpr ⟨hj, hz⟩)
    ((same_pair_mem_internalTaggedTreeOrder hj hx hy).mpr hxy)
    ((same_pair_mem_internalTaggedTreeOrder hj hx hz).mpr hxz) hfx hfy).imp
    (same_pair_mem_internalTaggedTreeOrder hj hy hz).mp (same_pair_mem_internalTaggedTreeOrder hj hz hy).mp

noncomputable def taggedColorFamily (J D f : V) : V :=
  definableGraph J (taggedComponentColor D f) (taggedComponentColor_definable D f)

instance taggedColorFamily_isFunction (J D f : V) : IsFunction (taggedColorFamily J D f) :=
  inferInstanceAs (IsFunction (definableGraph _ _ _))

theorem domain_taggedColorFamily (J D f : V) : domain (taggedColorFamily J D f) = J :=
  domain_definableGraph _ _ _

theorem taggedColorFamily_spec {J D S f : V}
    (hf : f ∈ (ω : V) ^ internalTaggedTree J D)
    (hweak : InternallyWeakSpecialization (internalTaggedTree J D) (internalTaggedTreeOrder J D S) f) :
    ∀ j ∈ J, (taggedColorFamily J D f) ‘ j ∈ (ω : V) ^ (D ‘ j) ∧
      InternallyWeakSpecialization (D ‘ j) (S ‘ j) ((taggedColorFamily J D f) ‘ j) := by
  intro j hj
  rw [taggedColorFamily, value_definableGraph _ _ _ hj]
  exact taggedComponentColor_spec hj hf hweak

end Schmerl

namespace ForcingContext
open Schmerl

theorem ground_component_branch_of_tagged (F : ForcingContext V) {J D S κ r j : V}
    [IsFunction D] [IsFunction S] [IsFunction r]
    (hD : J ⊆ domain D) (hS : J ⊆ domain S) (hr : J ⊆ domain r)
    (hκ : IsNonempty κ) (hT : ∀ k ∈ J, InternalRankedTree (D ‘ k) (S ‘ k) κ (r ‘ k))
    (hpres : ∀ B : F.Model,
      IsInternalCofinalBranch (F.check (internalTaggedTree J D)) (F.check (internalTaggedTreeOrder J D S))
        (F.check κ) (F.check (internalTaggedTreeRank J D r)) B →
      ∃ C : V, IsInternalCofinalBranch (internalTaggedTree J D) (internalTaggedTreeOrder J D S) κ
        (internalTaggedTreeRank J D r) C ∧ F.check C = B)
    (hj : j ∈ J) {B : F.Model}
    (hB : IsInternalCofinalBranch (F.check (D ‘ j)) (F.check (S ‘ j)) (F.check κ) (F.check (r ‘ j)) B) :
    ∃ C : V, IsInternalCofinalBranch (D ‘ j) (S ‘ j) κ (r ‘ j) C ∧ F.check C = B := by
  have hB' : IsInternalCofinalBranch ((F.check D) ‘ (F.check j)) ((F.check S) ‘ (F.check j))
      (F.check κ) ((F.check r) ‘ (F.check j)) B := by
    simpa only [F.check_value (hD j hj), F.check_value (hS j hj), F.check_value (hr j hj)] using hB
  have hlift := tagged_branch ((F.check_mem_iff j J).mpr hj) hB'
  rw [← F.check_internalTaggedTree hD, ← F.check_internalTaggedTreeOrder hD hS,
    ← F.check_internalTaggedTreeRank hD hr hT] at hlift
  obtain ⟨C, hC, hcheckC⟩ := hpres _ hlift
  obtain ⟨i, hi⟩ := hκ
  obtain ⟨x, hxB, _⟩ := hB.2.2.1 (F.check i) ((F.check_mem_iff _ _).mpr hi)
  obtain ⟨t, _, rfl⟩ := (F.mem_check_iff (D ‘ j) x).mp (hB.1 x hxB)
  have htag : ⟨j, t⟩ₖ ∈ C := by
    apply (F.check_mem_iff _ _).mp
    rw [hcheckC, F.check_kpair]
    exact kpair_mem_iff.mpr ⟨by simp, hxB⟩
  obtain ⟨_, hCj, he⟩ := tagged_branch_projection hC htag
  refine ⟨taggedBranchProjection D j C, hCj, ?_⟩
  have hprod : ({F.check j} : F.Model) ×ˢ F.check (taggedBranchProjection D j C) = ({F.check j} : F.Model) ×ˢ B := by
    rw [← F.check_taggedSet, ← he, hcheckC]
  ext y
  have hh : ⟨F.check j, y⟩ₖ ∈ ({F.check j} : F.Model) ×ˢ F.check (taggedBranchProjection D j C) ↔
      ⟨F.check j, y⟩ₖ ∈ ({F.check j} : F.Model) ×ˢ B := by rw [hprod]
  simpa only [kpair_mem_iff, mem_singleton_iff, true_and] using hh

end ForcingContext

namespace Schmerl

/-- The family graphs and their color graph are actual internal sets. -/
theorem exists_internal_simultaneous_weak_specialization_extension [Countable V] (hAC : InternalChoice V)
    {J D S r : V} [IsFunction D] [IsFunction S] [IsFunction r]
    (hD : J ⊆ domain D) (hS : J ⊆ domain S) (hr : J ⊆ domain r)
    (hJ : J ≤# hartogsNumber (ω : V))
    (hT : ∀ j ∈ J, InternalRankedTree (D ‘ j) (S ‘ j) (hartogsNumber (ω : V)) (r ‘ j))
    (hord : ∀ j ∈ J, IsForcingPoset (D ‘ j) (S ‘ j))
    (hinj : ∀ j ∈ J, ∀ x ∈ D ‘ j, ∀ y ∈ D ‘ j,
      ⟨x, y⟩ₖ ∈ S ‘ j → (r ‘ j) ‘ x = (r ‘ j) ‘ y → x = y)
    (hcard : ∀ j ∈ J,
      internalCofinalBranches (D ‘ j) (S ‘ j) (hartogsNumber (ω : V)) (r ‘ j) ≤# hartogsNumber (ω : V)) :
    ∃ F : ForcingContext V,
      InternalChoice F.Model ∧ F.check (hartogsNumber (ω : V)) = hartogsNumber (ω : F.Model) ∧
      (∃ c : F.Model, IsFunction c ∧ domain c = F.check J ∧ ∀ j ∈ F.check J,
        c ‘ j ∈ (ω : F.Model) ^ ((F.check D) ‘ j) ∧
          InternallyWeakSpecialization ((F.check D) ‘ j) ((F.check S) ‘ j) (c ‘ j)) ∧
      ∀ j ∈ J, ∀ B : F.Model,
        IsInternalCofinalBranch (F.check (D ‘ j)) (F.check (S ‘ j)) (hartogsNumber (ω : F.Model)) (F.check (r ‘ j)) B →
        ∃ C : V, IsInternalCofinalBranch (D ‘ j) (S ‘ j) (hartogsNumber (ω : V)) (r ‘ j) C ∧ F.check C = B := by
  obtain ⟨F, hACF, hκ, ⟨f, hf, hweak⟩, hbranches⟩ := exists_internal_weak_specialization_extension hAC
    (internalTaggedTree_ranked hT) (internalTaggedTree_poset hord)
    (internalTaggedTree_rank_injective hinj) (internalTaggedTree_branches_hartogsOmega hAC hJ hcard)
  rw [F.check_internalTaggedTree hD] at hf hweak
  rw [F.check_internalTaggedTreeOrder hD hS] at hweak
  refine ⟨F, hACF, hκ,
    ⟨taggedColorFamily (F.check J) (F.check D) f, inferInstance, domain_taggedColorFamily _ _ _,
      taggedColorFamily_spec hf hweak⟩, ?_⟩
  intro j hj B hB
  rw [← hκ] at hB
  apply F.ground_component_branch_of_tagged hD hS hr
    (show IsNonempty (hartogsNumber (ω : V)) from ⟨ω, omega_mem_hartogs_omega⟩) hT ?_ hj hB
  intro A hA
  apply hbranches A
  simpa only [hκ] using hA

end Schmerl
end ZFVP
