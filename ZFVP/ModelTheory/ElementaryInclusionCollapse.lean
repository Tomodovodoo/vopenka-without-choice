import ZFVP.ModelTheory.ElementaryInclusion
import ZFVP.SetTheory.SmallTransitiveInaccessibleRank
import ZFVP.SetTheory.LowenheimSkolemCardinals

/-! Elementary subsets of transitive sets have canonical transitive collapses. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsElementaryInclusion.membership_extensional {X B : V}
    (h : IsElementaryInclusion X B) (hB : IsTransitive B) :
    IsExtensionalOn (membershipRelation X) X := by
  let φ : SetTheorySemisentence 0 := “∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y”
  have ht : φ.Evalb (fun i : Fin 0 ↦ (Fin.elim0 i : SetDomain B)) := by
    simp only [φ]
    simp
    intro x y he
    apply Subtype.ext
    apply mem_ext
    intro z
    constructor
    · intro hz
      exact (he ⟨z, hB.mem_trans hz x.property⟩).mp hz
    · intro hz
      exact (he ⟨z, hB.mem_trans hz y.property⟩).mpr hz
  have hs := (h.eval_semisentence φ (fun i : Fin 0 ↦ (Fin.elim0 i : SetDomain X))).mpr ht
  simp only [φ] at hs
  simp at hs
  intro x hx y hy he
  have hxy := hs (⟨x, hx⟩ : SetDomain X) ⟨y, hy⟩ (by
    intro z
    change z.val ∈ x ↔ z.val ∈ y
    simpa only [pair_mem_membershipRelation, z.property, hx, hy, true_and] using he z.val z.property)
  exact congrArg Subtype.val hxy

theorem IsElementaryInclusion.canonicalCollapse {X B : V}
    (h : IsElementaryInclusion X B) (hB : IsTransitive B) :
    IsTransitiveCollapse (membershipRelation X) X
      (range (mostowskiMap (membershipRelation X) X)) (mostowskiMap (membershipRelation X) X) :=
  mostowskiMap_isTransitiveCollapse (membershipRelation_wellFounded X) (h.membership_extensional hB)

theorem IsElementaryInclusion.smallTransitiveCollapse {κ X B D : V}
    (h : IsElementaryInclusion X B) (hB : IsTransitive B)
    (hκ : IsChoicelessInaccessible κ) (hD : D ∈ hierarchy κ) (hcard : X ≤# D) :
    HasSmallTransitiveCollapse κ X := by
  have hc := h.canonicalCollapse hB
  by_cases hne : IsNonempty X
  · obtain ⟨g, hg, hgr⟩ := surjection_of_injection hcard hne
    have he := compose_function hg hc.2.1
    have her := range_compose_surjective hg hc.2.1 hgr hc.2.2.1
    exact ⟨_, hκ.transitive_mem_of_surjection hc.1 hD he her, _, hc⟩
  · exact (hne h.source_nonempty).elim

end ZFVP
