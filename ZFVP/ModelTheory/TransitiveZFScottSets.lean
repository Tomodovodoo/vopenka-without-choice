import ZFVP.SetTheory.LeastRankWitnesses
import ZFVP.ModelTheory.TransitiveZFAbsoluteness
import ZFVP.ModelTheory.EndExtensionOpenModels

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsLeastRankWitnessSet.mem_iff_minimal {R : V → V → Prop} {x X : V}
    (hX : IsLeastRankWitnessSet R x X) (y : V) :
    y ∈ X ↔ R x y ∧ ∀ z, R x z → rank y ⊆ rank z := by
  constructor
  · intro hy
    exact ⟨hX.witness hy, fun z hz ↦ hX.rank_minimal hy hz⟩
  · rintro ⟨hy, hmin⟩
    obtain ⟨z, hz⟩ := hX.nonempty.nonempty
    have hr : rank y = rank z := SetTheory.subset_antisymm
      (hmin z (hX.witness hz)) (hX.rank_minimal hz hy)
    obtain ⟨α, _, hm⟩ := hX
    exact (hm y).mpr ⟨hy, hr.trans ((hm z).mp hz).2⟩

def IsLocalScottSet (U : V) (R : V → V → Prop) (x X : V) : Prop :=
  X ∈ U ∧ IsNonempty X ∧ ∀ y ∈ U,
    y ∈ X ↔ R x y ∧ ∀ z ∈ U, R x z → rank y ⊆ rank z

theorem isLocalScottSet_definable (U : V) (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) :
    ℒₛₑₜ-relation (IsLocalScottSet U R) := by
  unfold IsLocalScottSet
  definability

theorem IsLocalScottSet.unique {U : V} [hU : IsTransitive U] {R : V → V → Prop}
    {x X Y : V} (hX : IsLocalScottSet U R x X) (hY : IsLocalScottSet U R x Y) : X = Y := by
  apply mem_ext
  intro y
  by_cases hy : y ∈ U
  · exact (hX.2.2 y hy).trans (hY.2.2 y hy).symm
  · exact iff_of_false (fun h ↦ hy (hU.mem_trans h hX.1)) (fun h ↦ hy (hU.mem_trans h hY.1))

theorem IsLocalScottSet.congr {U : V} {R S : V → V → Prop} {x y X : V}
    (hX : IsLocalScottSet U R x X) (hRS : ∀ z ∈ U, R x z ↔ S y z) : IsLocalScottSet U S y X := by
  refine ⟨hX.1, hX.2.1, ?_⟩
  intro z hz
  rw [hX.2.2 z hz, hRS z hz]
  apply and_congr_right
  intro _
  exact forall_congr' fun w ↦ imp_congr_right fun hw ↦ imp_congr_left (hRS w hw)

theorem transitiveZF_localScottSet_exists {U : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (R : SetDomain U → SetDomain U → Prop) (hR : ℒₛₑₜ-relation R) (S : V → V → Prop)
    (hRS : ∀ x y, R x y ↔ S x.val y.val) (x : SetDomain U) (hex : ∃ y, R x y) :
    ∃ X : V, IsLocalScottSet U S x.val X := by
  obtain ⟨X, hX, _⟩ := leastRankWitnessSet_existsUnique R hR x hex
  obtain ⟨y, hy⟩ := hX.nonempty.nonempty
  refine ⟨X.val, X.property, ⟨y.val, hy⟩, ?_⟩
  intro z hz
  let z' : SetDomain U := ⟨z, hz⟩
  have hm := hX.mem_iff_minimal z'
  change z ∈ X.val ↔ _ at hm
  rw [hm, hRS x z']
  apply and_congr_right
  intro _
  have hsub (w : SetDomain U) : rank z' ⊆ rank w ↔ rank z ⊆ rank w.val := by
    have hh := (setDomainEndExtension U).subset_iff (rank z') (rank w)
    change (rank z').val ⊆ (rank w).val ↔ _ at hh
    rw [TransitiveZF.rank_val U z', TransitiveZF.rank_val U w] at hh
    exact hh.symm
  constructor
  · intro h w hw hsw
    exact (hsub ⟨w, hw⟩).mp (h ⟨w, hw⟩ ((hRS x ⟨w, hw⟩).mpr hsw))
  · intro h w hrw
    exact (hsub w).mpr (h w.val w.property ((hRS x w).mp hrw))

end ZFVP
