import ZFVP.ModelTheory.UsubaQuotientBoundRecursion
import ZFVP.ModelTheory.ClassForcingTowerSplitProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

attribute [local instance] DefinableForcingTower.P_definable DefinableForcingTower.R_definable
  DefinableForcingTower.top_definable DefinableForcingTower.projection_definable
  DefinableForcingTower.section_definable

theorem usubaQuotientBoundRec_before_base {θ i p f j : V} [IsOrdinal i] [IsOrdinal j]
    (hji : j ⊆ i) (hp : p ∈ (T).P i) :
    usubaQuotientBoundRec θ i p f j = ((T).projection j i) ‘ p := by
  rcases IsOrdinal.subset_iff.mp hji with rfl | hj
  · rw [usubaQuotientBoundRec_base, (T).projection_self _ inferInstance p hp]
  · exact usubaQuotientBoundRec_before hj

theorem usubaQuotientBoundRec_projects_before_base {θ i p f j k : V}
    [IsOrdinal i] [IsOrdinal j] [IsOrdinal k]
    (hji : j ⊆ i) (hkj : k ⊆ j) (hp : p ∈ (T).P i) :
    ((T).projection k j) ‘ (usubaQuotientBoundRec θ i p f j) =
      usubaQuotientBoundRec θ i p f k := by
  rw [usubaQuotientBoundRec_before_base hji hp,
    usubaQuotientBoundRec_before_base (subset_trans hkj hji) hp]
  exact (T).projection_comp k j i inferInstance inferInstance inferInstance hkj hji p hp

theorem usubaQuotientBoundRec_projects_of_membership {θ η i p f : V}
    [IsOrdinal η] (hi : i ∈ η)
    (hmem : ∀ j ∈ η, usubaQuotientBoundRec θ i p f j ∈ (T).P j) :
    ∀ j ∈ η, ∀ k ∈ succ j,
      ((T).projection k j) ‘ (usubaQuotientBoundRec θ i p f j) =
        usubaQuotientBoundRec θ i p f k := by
  let := IsOrdinal.of_mem hi
  have hp : p ∈ (T).P i := by simpa only [usubaQuotientBoundRec_base] using hmem i hi
  have hall := transfinite_induction
    (fun j : V ↦ j ∈ η → ∀ k ∈ succ j,
      ((T).projection k j) ‘ (usubaQuotientBoundRec θ i p f j) =
        usubaQuotientBoundRec θ i p f k)
    (by definability) ?_
  · intro j hj
    let := IsOrdinal.of_mem hj
    exact hall (IsOrdinal.toOrdinal j) hj
  intro j ih hj k hk
  let := IsOrdinal.of_mem hk
  rcases mem_succ_iff.mp hk with rfl | hk
  · exact (T).projection_self j inferInstance _ (hmem j hj)
  by_cases hji : (j : V) ⊆ i
  · exact usubaQuotientBoundRec_projects_before_base hji
      (IsOrdinal.toIsTransitive.transitive _ hk) hp
  have hij : i ∈ (j : V) := by
    rcases IsOrdinal.mem_trichotomy i (j : V) with hij | he | hji'
    · exact hij
    · exact False.elim (hji (he ▸ subset_refl i))
    · exact False.elim (hji (IsOrdinal.toIsTransitive.transitive _ hji'))
  by_cases hsucc : (j : V) = succ (⋃ˢ (j : V))
  · have hprev : ⋃ˢ (j : V) ∈ (j : V) :=
      (congrArg (fun x : V ↦ (⋃ˢ (j : V)) ∈ x) hsucc).mpr (mem_succ_self (⋃ˢ (j : V)))
    let := IsOrdinal.of_mem hprev
    have hkp : k ⊆ ⋃ˢ (j : V) := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp (hsucc ▸ hk))
    have he := usubaTower_projection_succ hkp (hsucc ▸ hmem j hj)
    rw [usubaQuotientBoundRec_successor (hsucc ▸ hij), kpair.π₁_kpair] at he
    have hihe := ih (IsOrdinal.toOrdinal (⋃ˢ (j : V))) hprev
      (IsOrdinal.toIsTransitive.mem_trans hprev hj) k (hsucc ▸ hk)
    change ((T).projection k (⋃ˢ (j : V))) ‘
      (usubaQuotientBoundRec θ i p f (⋃ˢ (j : V))) = _ at hihe
    rw [hsucc, usubaQuotientBoundRec_successor (hsucc ▸ hij)]
    exact he.trans hihe
  · have hz : (j : V) ≠ ∅ := by rintro he; exact not_mem_empty (he ▸ hij)
    rw [usubaTower_projection_limit hz hsucc hk (hmem j hj),
      usubaQuotientBoundRec_limit hij hsucc, usubaQuotientBoundHistory_value hk]

theorem usubaQuotientBoundHistory_inverse_condition {θ η i p f : V} [IsOrdinal η]
    (hz : η ≠ ∅) (hs : η ≠ succ (⋃ˢ η)) (hi : i ∈ η)
    (hmem : ∀ j ∈ η, usubaQuotientBoundRec θ i p f j ∈ (T).P j) :
    usubaQuotientBoundHistory θ i p f η ∈ (T).P η ∧
      ((T).projection i η) ‘ (usubaQuotientBoundHistory θ i p f η) = p := by
  have hm : usubaQuotientBoundHistory θ i p f η ∈ (T).P η := by
    apply usubaTower_inverse_condition hz hs (usubaQuotientBoundHistory_table _ _ _ _ _)
    · intro j hj
      rw [usubaQuotientBoundHistory_value hj]
      exact hmem j hj
    · intro j hj k hk
      have hkη := IsOrdinal.toIsTransitive.mem_trans hk hj
      rw [usubaQuotientBoundHistory_value hj, usubaQuotientBoundHistory_value hkη]
      exact usubaQuotientBoundRec_projects_of_membership hi hmem j hj k (mem_succ_iff.mpr (Or.inr hk))
  refine ⟨hm, ?_⟩
  let := IsOrdinal.of_mem hi
  rw [usubaTower_projection_limit hz hs hi hm, usubaQuotientBoundHistory_value hi,
    usubaQuotientBoundRec_base]

end ZFVP
