import ZFVP.ModelTheory.LimitRankEmbedding
import ZFVP.SetTheory.SetUltrafilter

/-! Bounded transport of subsets, intersections and relative complements. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedIntersectionFormula : SetTheorySemisentence 3 :=
  “Z X Y. !isSubsetOf Z X ∧ ∀ z ∈ X, z ∈ Z ↔ z ∈ Y”

def boundedRelativeComplementFormula : SetTheorySemisentence 3 :=
  “Z K X. !isSubsetOf Z K ∧ ∀ z ∈ K, z ∈ Z ↔ z ∉ X”

theorem boundedIntersectionFormula_bounded : IsBoundedSetFormula boundedIntersectionFormula :=
  .and (isSubsetOf_bounded.subst _) (.all (.bvar 1)
    (.and (.or (.nrel _ _) (.rel _ _)) (.or (.nrel _ _) (.rel _ _))))

theorem boundedRelativeComplementFormula_bounded : IsBoundedSetFormula boundedRelativeComplementFormula :=
  .and (isSubsetOf_bounded.subst _) (.all (.bvar 1)
    (.and (.or (.nrel _ _) (.nrel _ _)) (.or (.rel _ _) (.rel _ _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedIntersectionFormula_defined :
    Defined (fun v : Fin 3 → V ↦ v 0 = v 1 ∩ v 2) boundedIntersectionFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [boundedIntersectionFormula]
  constructor
  · rintro ⟨hs, he⟩
    apply mem_ext
    intro z
    constructor
    · intro hz
      exact mem_inter_iff.mpr ⟨hs z hz, (he z (hs z hz)).mp hz⟩
    · intro hz
      exact (he z (mem_inter_iff.mp hz).1).mpr (mem_inter_iff.mp hz).2
  · intro he
    rw [he]
    exact ⟨fun z hz ↦ (mem_inter_iff.mp hz).1, fun z hz ↦ by simp [hz]⟩

instance boundedRelativeComplementFormula_defined :
    Defined (fun v : Fin 3 → V ↦ v 0 = relativeComplement (v 1) (v 2))
      boundedRelativeComplementFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [boundedRelativeComplementFormula]
  constructor
  · rintro ⟨hs, he⟩
    apply mem_ext
    intro z
    constructor
    · intro hz
      exact mem_relativeComplement_iff _ _ _ |>.mpr ⟨hs z hz, (he z (hs z hz)).mp hz⟩
    · intro hz
      exact (he z (mem_relativeComplement_iff _ _ _ |>.mp hz).1).mpr
        (mem_relativeComplement_iff _ _ _ |>.mp hz).2
  · intro he
    rw [he]
    exact ⟨fun z hz ↦ (mem_relativeComplement_iff _ _ _ |>.mp hz).1,
      fun z hz ↦ by simp [hz]⟩

namespace IsCodedMembershipEmbedding

variable {A B f : V} [IsTransitive A] [IsTransitive B]

theorem value_subset (h : IsCodedMembershipEmbedding A B f) {X Y : V}
    (hx : X ∈ A) (hy : Y ∈ A) (hs : X ⊆ Y) : f ‘ X ⊆ f ‘ Y :=
  (h.bounded_defined_iff isSubsetOf_bounded (fun v ↦ v 0 ⊆ v 1)
    ![X, Y] (by simp [hx, hy])).mp hs

theorem value_intersection (h : IsCodedMembershipEmbedding A B f) {X Y : V}
    (hx : X ∈ A) (hy : Y ∈ A) (hi : X ∩ Y ∈ A) :
    f ‘ (X ∩ Y) = (f ‘ X) ∩ (f ‘ Y) :=
  (h.bounded_defined_iff boundedIntersectionFormula_bounded (fun v ↦ v 0 = v 1 ∩ v 2)
    ![X ∩ Y, X, Y] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hx, hy, hi])).mp rfl

theorem value_relativeComplement (h : IsCodedMembershipEmbedding A B f) {K X : V}
    (hk : K ∈ A) (hx : X ∈ A) (hc : relativeComplement K X ∈ A) :
    f ‘ (relativeComplement K X) = relativeComplement (f ‘ K) (f ‘ X) :=
  (h.bounded_defined_iff boundedRelativeComplementFormula_bounded
    (fun v ↦ v 0 = relativeComplement (v 1) (v 2))
    ![relativeComplement K X, K, X]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hk, hx, hc])).mp rfl

end IsCodedMembershipEmbedding

end ZFVP
