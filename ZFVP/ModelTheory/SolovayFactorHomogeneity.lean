import ZFVP.ModelTheory.SolovayFactorLemma
import ZFVP.ModelTheory.HomogeneousTruth

/-! Homogeneity of the upper collapse over the intermediate model: automorphisms and weak
homogeneity transport along end extensions, so every context over `V[G_β ∩ D]` whose poset is the
checked upper collapse is weakly homogeneous, and statements about its ground parameters are
decided by the top condition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V W : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace MembershipEndExtension

variable (j : MembershipEndExtension V W)

theorem map_forcingAutomorphism {P R π : V} (h : IsForcingAutomorphism P R π) :
    IsForcingAutomorphism (j P) (j R) (j π) := by
  refine ⟨(j.function_iff _ _ _).mpr h.1, (j.injective_iff π).mpr h.2.1, ?_, ?_⟩
  · rw [← j.map_range, h.2.2.1]
  · intro p hp q hq
    obtain ⟨p₀, hp₀, rfl⟩ := j.endExtension P p hp
    obtain ⟨q₀, hq₀, rfl⟩ := j.endExtension P q hq
    rw [← j.map_kpair, j.mem_iff, ← j.map_value_total, ← j.map_value_total, ← j.map_kpair, j.mem_iff]
    exact h.2.2.2 p₀ hp₀ q₀ hq₀

theorem map_weaklyHomogeneous {P R one : V} (h : IsWeaklyHomogeneous P R one) :
    IsWeaklyHomogeneous (j P) (j R) (j one) := by
  intro p hp q hq
  obtain ⟨p₀, hp₀, rfl⟩ := j.endExtension P p hp
  obtain ⟨q₀, hq₀, rfl⟩ := j.endExtension P q hq
  obtain ⟨π, hπ, hone, r, hr, hrp, hrq⟩ := h p₀ hp₀ q₀ hq₀
  refine ⟨j π, j.map_forcingAutomorphism hπ, by rw [← j.map_value_total, hone], j r, (j.mem_iff _ _).mpr hr, ?_, ?_⟩
  · rw [← j.map_value_total, ← j.map_kpair, j.mem_iff]
    exact hrp
  · rw [← j.map_kpair, j.mem_iff]
    exact hrq

end MembershipEndExtension

section

variable {κ : V} {β : V} (hβ : β ⊆ κ) (N : ForcingContext V) (Z : ForcingContext N.Model)
  (hZP : Z.P = N.check (levyCollapseAbove κ β))
  (hZR : Z.R = N.check (restrictedOrder (levyOrder κ) (levyCollapseAbove κ β)))
  (hZone : Z.one = N.check ∅)

include hβ hZP hZR hZone in
/-- Any context over an intermediate model whose poset is the checked upper collapse is weakly
homogeneous. -/
theorem factorContext_homogeneous : IsWeaklyHomogeneous Z.P Z.R Z.one := by
  rw [hZP, hZR, hZone]
  exact N.checkEmbedding.map_weaklyHomogeneous (levyCollapseAbove_homogeneous hβ)

include hβ hZP hZR hZone in
/-- Truth of statements about parameters of the intermediate model is decided by the top of the
upper collapse. -/
theorem factorContext_truth_iff_top {n : ℕ} (φ : SetTheorySemisentence n) (a : Fin n → N.Model) :
    φ.Evalb (fun i ↦ Z.check (a i)) ↔
      Z.one ∈ forcingFormula Z.P Z.R φ (standardTuple (fun i ↦ checkName Z.one (a i))) :=
  Z.truth_iff_top_forces (factorContext_homogeneous hβ N Z hZP hZR hZone) φ a

end

end ZFVP
