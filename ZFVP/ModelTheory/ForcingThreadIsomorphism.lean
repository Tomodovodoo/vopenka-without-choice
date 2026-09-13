import ZFVP.SetTheory.ForcingThreadAction
import ZFVP.ModelTheory.ForcingIsomorphismFormula

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingInverseMapFamily (θ m : V) : V :=
  definableGraph θ (fun i ↦ converseGraph (m ‘ i)) (by definability)

instance forcingInverseMapFamily_definable : ℒₛₑₜ-function₂[V] forcingInverseMapFamily := by
  have h : ℒₛₑₜ-relation₃[V] (fun n θ m ↦ ∀ w, w ∈ n ↔ ∃ i ∈ θ, w = ⟨i, converseGraph (m ‘ i)⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingInverseMapFamily (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [forcingInverseMapFamily, mem_definableGraph_iff]

theorem forcingInverseMapFamily_value {θ m i : V} (hi : i ∈ θ) :
    (forcingInverseMapFamily θ m) ‘ i = converseGraph (m ‘ i) :=
  value_definableGraph _ _ _ hi

instance forcingThreadActionMap_definable : ℒₛₑₜ-function₃[V] forcingThreadActionMap := by
  have h : ℒₛₑₜ-relation₄[V] (fun g θ m C ↦ ∀ w, w ∈ g ↔ ∃ f ∈ C,
    w = ⟨f, forcingThreadAction θ m f⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingThreadActionMap (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingThreadActionMap, mem_definableGraph_iff]

variable {θ P R Q T U W m C D : V}
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism (P ‘ i) (R ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))

include hm in
theorem forcingThreadAction_inverse_cancel {f : V} (hf : f ∈ U ^ θ)
    (hv : ∀ i ∈ θ, f ‘ i ∈ P ‘ i) :
    forcingThreadAction θ (forcingInverseMapFamily θ m) (forcingThreadAction θ m f) = f := by
  apply forcingThreadAction_cancel hf hv
  intro i hi p hp
  rw [forcingInverseMapFamily_value hi, (hm i hi).inverse_value hp]

include hm in
theorem forcingThreadAction_cancel_inverse {f : V} (hf : f ∈ W ^ θ)
    (hv : ∀ i ∈ θ, f ‘ i ∈ Q ‘ i) :
    forcingThreadAction θ m (forcingThreadAction θ (forcingInverseMapFamily θ m) f) = f := by
  apply forcingThreadAction_cancel hf hv
  intro i hi p hp
  rw [forcingInverseMapFamily_value hi, (hm i hi).value_inverse hp]

include hm in
theorem forcingThreadActionMap_isomorphism
    (hC : ∀ f ∈ C, f ∈ U ^ θ ∧ ∀ i ∈ θ, f ‘ i ∈ P ‘ i)
    (hD : ∀ f ∈ D, f ∈ W ^ θ ∧ ∀ i ∈ θ, f ‘ i ∈ Q ‘ i)
    (hmap : ∀ f ∈ C, forcingThreadAction θ m f ∈ D)
    (hback : ∀ f ∈ D, forcingThreadAction θ (forcingInverseMapFamily θ m) f ∈ C) :
    IsForcingIsomorphism C (forcingThreadOrder θ R C) D (forcingThreadOrder θ T D)
      (forcingThreadActionMap θ m C) := by
  have hf : forcingThreadActionMap θ m C ∈ D ^ C :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ hmap
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro a b z ha hb
    obtain ⟨haC, hza⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp ha
    obtain ⟨hbC, hzb⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hb
    have he := congrArg (forcingThreadAction θ (forcingInverseMapFamily θ m)) (hza.symm.trans hzb)
    simpa only [forcingThreadAction_inverse_cancel hm (hC a haC).1 (hC a haC).2,
      forcingThreadAction_inverse_cancel hm (hC b hbC).1 (hC b hbC).2] using he
  · apply subset_antisymm (range_subset_of_mem_function hf)
    intro f hfd
    have he := forcingThreadAction_cancel_inverse hm (hD f hfd).1 (hD f hfd).2
    have hv := value_mem_range hf (hback f hfd)
    rwa [forcingThreadActionMap_value (hback f hfd), he] at hv
  · intro a ha b hb
    rw [forcingThreadActionMap_value ha, forcingThreadActionMap_value hb]
    simp only [mem_forcingThreadOrder_iff, ha, hb, hmap a ha, hmap b hb, true_and]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    rw [forcingThreadAction_value hi, forcingThreadAction_value hi]
    exact (hm i hi).2.2.2 _ ((hC a ha).2 i hi) _ ((hC b hb).2 i hi)

end ZFVP
