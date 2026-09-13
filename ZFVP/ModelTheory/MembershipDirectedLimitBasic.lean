import ZFVP.ModelTheory.MembershipDirectedLimit
import ZFVP.SetTheory.EndExtensionCoding

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u v
namespace MembershipDirectedSystem
variable {I : Type u} [SemilatticeSup I] (S : MembershipDirectedSystem.{u,v} I)
variable [∀ i, Nonempty (S.Model i)] [∀ i, (S.Model i)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem stage_cover_pair (x y : S.Limit) :
    ∃ i, ∃ a b : S.Model i, x = S.fromStage i a ∧ y = S.fromStage i b := by
  obtain ⟨i, a, ha⟩ := S.stage_cover x
  obtain ⟨j, b, hb⟩ := S.stage_cover y
  exact ⟨i ⊔ j, S.inclusion le_sup_left a, S.inclusion le_sup_right b,
    ha.trans (S.fromStage_coherent le_sup_left a).symm,
    hb.trans (S.fromStage_coherent le_sup_right b).symm⟩

theorem limit_extensionality (x y : S.Limit) (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  obtain ⟨i, a, b, rfl, rfl⟩ := S.stage_cover_pair x y
  apply congrArg (S.fromStage i)
  apply mem_ext
  intro z
  simpa only [S.fromStage_mem_iff] using h (S.fromStage i z)

theorem fromStage_empty (i : I) (z : S.Limit) : z ∉ S.fromStage i ∅ := by
  intro hz
  obtain ⟨a, ha, _⟩ := S.fromStage_endExtension i ∅ z hz
  exact not_mem_empty ha

theorem fromStage_doubleton (i : I) (a b : S.Model i) (z : S.Limit) :
    z ∈ S.fromStage i (doubleton a b) ↔ z = S.fromStage i a ∨ z = S.fromStage i b := by
  constructor
  · intro hz
    obtain ⟨c, hc, rfl⟩ := S.fromStage_endExtension i _ z hz
    rcases mem_doubleton_iff.mp hc with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl) <;> rw [S.fromStage_mem_iff] <;> simp

theorem limit_pairing (x y : S.Limit) : ∃ z : S.Limit, ∀ w, w ∈ z ↔ w = x ∨ w = y := by
  obtain ⟨i, a, b, rfl, rfl⟩ := S.stage_cover_pair x y
  exact ⟨S.fromStage i (doubleton a b), S.fromStage_doubleton i a b⟩

theorem limit_union (x : S.Limit) :
    ∃ u : S.Limit, ∀ z, z ∈ u ↔ ∃ y, y ∈ x ∧ z ∈ y := by
  obtain ⟨i, a, rfl⟩ := S.stage_cover x
  refine ⟨S.fromStage i (⋃ˢ a), ?_⟩
  intro z
  constructor
  · intro hz
    obtain ⟨c, hc, rfl⟩ := S.fromStage_endExtension i _ z hz
    obtain ⟨b, hb, hcb⟩ := mem_sUnion_iff.mp hc
    exact ⟨S.fromStage i b, (S.fromStage_mem_iff i _ _).mpr hb,
      (S.fromStage_mem_iff i _ _).mpr hcb⟩
  · rintro ⟨y, hy, hz⟩
    obtain ⟨b, hb, rfl⟩ := S.fromStage_endExtension i a y hy
    obtain ⟨c, hc, rfl⟩ := S.fromStage_endExtension i b z hz
    exact (S.fromStage_mem_iff i _ _).mpr (mem_sUnion_iff.mpr ⟨b, hb, hc⟩)

theorem limit_foundation (x : S.Limit) (hx : ∃ y, y ∈ x) :
    ∃ y, y ∈ x ∧ ∀ z, z ∈ x → z ∉ y := by
  obtain ⟨i, a, rfl⟩ := S.stage_cover x
  obtain ⟨w, hw⟩ := hx
  obtain ⟨b, hb, _⟩ := S.fromStage_endExtension i a w hw
  have : IsNonempty a := ⟨b, hb⟩
  obtain ⟨c, hc, hmin⟩ := foundation a
  refine ⟨S.fromStage i c, (S.fromStage_mem_iff i _ _).mpr hc, ?_⟩
  intro z hz hzc
  obtain ⟨d, hd, rfl⟩ := S.fromStage_endExtension i a z hz
  exact hmin d hd ((S.fromStage_mem_iff i _ _).mp hzc)

theorem fromStage_succ (i : I) (a : S.Model i) (z : S.Limit) :
    z ∈ S.fromStage i (succ a) ↔ z = S.fromStage i a ∨ z ∈ S.fromStage i a := by
  constructor
  · intro hz
    obtain ⟨b, hb, rfl⟩ := S.fromStage_endExtension i _ z hz
    rcases mem_succ_iff.mp hb with rfl | hb
    · exact Or.inl rfl
    · exact Or.inr ((S.fromStage_mem_iff i _ _).mpr hb)
  · rintro (rfl | hz)
    · exact (S.fromStage_mem_iff i _ _).mpr (mem_succ_self a)
    · obtain ⟨b, hb, rfl⟩ := S.fromStage_endExtension i a z hz
      exact (S.fromStage_mem_iff i _ _).mpr (mem_succ_iff.mpr (Or.inr hb))

theorem limit_infinity (i : I) : ∃ a : S.Limit,
    (∀ e, (∀ z, z ∉ e) → e ∈ a) ∧
    (∀ x, x ∈ a → ∀ y, (∀ z, z ∈ y ↔ z = x ∨ z ∈ x) → y ∈ a) := by
  refine ⟨S.fromStage i ω, ?_, ?_⟩
  · intro e he
    have heq : e = S.fromStage i ∅ := S.limit_extensionality _ _
      (fun z ↦ iff_of_false (he z) (S.fromStage_empty i z))
    rw [heq]
    exact (S.fromStage_mem_iff i _ _).mpr empty_mem_ω
  · intro x hx y hy
    obtain ⟨b, hb, rfl⟩ := S.fromStage_endExtension i ω x hx
    have heq : y = S.fromStage i (succ b) := S.limit_extensionality _ _
      (fun z ↦ (hy z).trans (S.fromStage_succ i b z).symm)
    rw [heq]
    exact (S.fromStage_mem_iff i _ _).mpr (ω_succ_closed hb)

variable [Nonempty I]

theorem limit_models_empty : S.Limit↓[ℒₛₑₜ] ⊧ Axiom.empty := by
  obtain ⟨i⟩ := ‹Nonempty I›
  simpa [models_iff, Axiom.empty] using
    (show ∃ e : S.Limit, ∀ z, z ∉ e from ⟨S.fromStage i ∅, S.fromStage_empty i⟩)

theorem limit_models_extensionality : S.Limit↓[ℒₛₑₜ] ⊧ Axiom.extentionality := by
  simp [models_iff, Axiom.extentionality]
  intro x y
  exact ⟨by rintro rfl; simp, S.limit_extensionality x y⟩

theorem limit_models_pairing : S.Limit↓[ℒₛₑₜ] ⊧ Axiom.pairing := by
  simpa [models_iff, Axiom.pairing] using S.limit_pairing

theorem limit_models_union : S.Limit↓[ℒₛₑₜ] ⊧ Axiom.union := by
  simpa [models_iff, Axiom.union] using S.limit_union

theorem limit_models_infinity : S.Limit↓[ℒₛₑₜ] ⊧ Axiom.infinity := by
  obtain ⟨i⟩ := ‹Nonempty I›
  simp [models_iff, Axiom.infinity, isEmpty, isSucc]
  exact S.limit_infinity i

theorem limit_models_foundation : S.Limit↓[ℒₛₑₜ] ⊧ Axiom.foundation := by
  simp [models_iff, Axiom.foundation, isNonempty]
  intro x y hy
  exact S.limit_foundation x ⟨y, hy⟩

end MembershipDirectedSystem
end ZFVP
