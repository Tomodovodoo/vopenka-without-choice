import ZFVP.SetTheory.WellFoundedRecursion
import ZFVP.SetTheory.EndExtensionCoding
import ZFVP.SetTheory.EndExtensionSets
import ZFVP.SetTheory.EndExtensionRelations
import ZFVP.SetTheory.UniformCollapse
import ZFVP.SetTheory.EndExtensionWellOrdering

/-! Membership end extensions transport well-founded recursions whose step commutes with the
extension: the image of the recursion function is a recursion attempt with full domain for the
transported relation, hence equals the recursion computed in the larger model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V W : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace MembershipEndExtension

variable (j : MembershipEndExtension V W)

theorem map_predecessors (R D x : V) : j (predecessors R D x) = predecessors (j R) (j D) (j x) := by
  unfold predecessors
  rw [j.map_separation D (fun y ↦ ⟨y, x⟩ₖ ∈ R) (fun y ↦ ⟨y, j x⟩ₖ ∈ j R) (by definability)
    (by definability)]
  intro y _
  rw [← j.map_kpair, j.mem_iff]

theorem map_membershipRelation (D : V) : j (membershipRelation D) = membershipRelation (j D) := by
  unfold membershipRelation
  rw [j.map_separation (D ×ˢ D) (fun p ↦ kpair.π₁ p ∈ kpair.π₂ p) (fun p ↦ kpair.π₁ p ∈ kpair.π₂ p)
    (by definability) (by definability), j.map_prod]
  intro p hp
  obtain ⟨a, _, b, _, rfl⟩ := mem_prod_iff.mp hp
  rw [j.map_kpair]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  exact (j.mem_iff a b).symm

/-- A recursion whose step commutes with `j` is transported to the recursion in the larger model
along the transported relation. -/
theorem map_wellFoundedRecursion {R D : V} (hR : IsInternallyWellFounded R D) {R' D' : W}
    (hR' : IsInternallyWellFounded R' D') (heR : j R = R') (heD : j D = D')
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (F' : W → W → W) (hF' : ℒₛₑₜ-function₂ F')
    (hcomm : ∀ x g : V, j (F x g) = F' (j x) (j g)) :
    j (wellFoundedRecursion hR F hF) = wellFoundedRecursion hR' F' hF' := by
  symm
  rw [wellFoundedRecursion_eq_iff]
  have hf := wellFoundedRecursion_spec hR F hF
  have hfun : IsFunction (wellFoundedRecursion hR F hF) := hf.1.1
  have hdom : domain (j (wellFoundedRecursion hR F hF)) = D' := by
    rw [← j.map_domain, hf.2, heD]
  refine ⟨⟨j.map_function _, ⟨?_, ?_⟩, ?_⟩, hdom⟩
  · intro y hy
    rw [hdom] at hy
    exact hy
  · intro x _ y hy
    rw [hdom]
    exact ((mem_predecessors_iff _ _ _ _).mp hy).1
  · intro x hx
    rw [hdom, ← heD] at hx
    obtain ⟨x₀, hx₀, rfl⟩ := j.endExtension D x hx
    have hx₀' : x₀ ∈ domain (wellFoundedRecursion hR F hF) := by
      rw [hf.2]
      exact hx₀
    rw [← j.map_value _ x₀ hx₀', hf.1.2.2 x₀ hx₀', hcomm, j.map_restrict, j.map_predecessors, heR, heD]

end MembershipEndExtension

end ZFVP
