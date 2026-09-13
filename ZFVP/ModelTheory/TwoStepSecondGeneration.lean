import ZFVP.ModelTheory.TwoStepFirstGeneration
import ZFVP.SetTheory.EndExtensionReplacement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TwoStepModel
variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t)
  {H : Set A.Model}
  (hH : IsExternalForcingGeneric (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩) H)

theorem second_coordinate_value (p : V) (τ : ForcingName A.P) (hτ : τ.val ∈ twoStepNames Q t) :
    ((iterandContext A h hH).check (A.evaluationGraph (twoStepNames Q t) (fun _ hσ ↦ h.name hσ))) ‘
      (kpair.π₂ ((iterandContext A h hH).check (A.check ⟨p, τ.val⟩ₖ))) =
        (iterandContext A h hH).check (A.ofName τ) := by
  let B := iterandContext A h hH
  have hdom : A.check τ.val ∈ domain (A.evaluationGraph (twoStepNames Q t) (fun _ hσ ↦ h.name hσ)) := by
    rw [A.evaluationGraph_domain]
    exact (A.check_mem_iff _ _).mpr hτ
  rw [A.check_kpair, B.check_kpair, kpair.π₂_kpair, B.check_value hdom,
    A.evaluationGraph_value _ _ _ hτ]

theorem second_generic_eq_image :
    (iterandContext A h hH).genericSet =
      repl (fun a ↦ ((iterandContext A h hH).check
        (A.evaluationGraph (twoStepNames Q t) (fun _ hσ ↦ h.name hσ))) ‘ (kpair.π₂ a))
        (by definability) (internalGeneric A h hH) := by
  let B := iterandContext A h hH
  apply mem_ext
  intro x
  rw [repl_spec]
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (B.mem_genericSet_iff x).mp hx
    have hyQ := hH.1.1 y hy
    obtain ⟨τ, p, hp, hτp, rfl⟩ := (A.mem_ofName_iff ⟨Q, h.posetName⟩ y).mp hyQ
    have hτN : τ.val ∈ twoStepNames Q t := mem_union_iff.mpr (Or.inl (mem_domain_of_kpair_mem hτp))
    have hpC : ⟨p, τ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t :=
      (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨A.generic.1.1 p hp, hτN,
        atomicMembership_of_pair A.order (A.generic.1.1 p hp) hτp⟩
    exact ⟨B.check (A.check ⟨p, τ.val⟩ₖ), (internalGeneric_pair_iff A h hH p τ hpC).mpr ⟨hp, hy⟩,
      (second_coordinate_value A h hH p τ hτN).symm⟩
  · rintro ⟨a, ha, he⟩
    have haC := internalGeneric_subset A h hH a ha
    obtain ⟨b, hb, rfl⟩ := (B.mem_check_iff (A.check (twoStepConditions A.P A.R Q t)) a).mp haC
    obtain ⟨c, hc, rfl⟩ := (A.mem_check_iff (twoStepConditions A.P A.R Q t) b).mp hb
    obtain ⟨p, hp, τ, hτ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp hc
    let σ : ForcingName A.P := ⟨τ, h.name hτ⟩
    have hσH := ((internalGeneric_pair_iff A h hH p σ hc).mp ha).2
    rw [second_coordinate_value A h hH p σ hτ] at he
    rw [he]
    exact (B.check_mem_genericSet_iff (A.ofName σ)).mpr hσH

theorem second_generic_in_range :
    ∃ g : (combinedContext A h hH).Model,
      (combinedRealization A h hH).value g = (iterandContext A h hH).genericSet := by
  let C := combinedContext A h hH
  let B := iterandContext A h hH
  let L := combinedRealization A h hH
  let f := A.evaluationGraph (twoStepNames Q t) (fun _ hσ ↦ h.name hσ)
  obtain ⟨f₀, hf⟩ := first_checks_in_range A h hH f
  let g : C.Model := repl (fun a ↦ f₀ ‘ (kpair.π₂ a)) (by definability) C.genericSet
  have hg : L.value g = repl (fun a ↦ (L.value f₀) ‘ (kpair.π₂ a)) (by definability) (L.value C.genericSet) := by
    change L.embedding (repl (fun a ↦ f₀ ‘ (kpair.π₂ a)) (by definability) C.genericSet) =
      repl (fun a ↦ (L.embedding f₀) ‘ (kpair.π₂ a)) (by definability) (L.embedding C.genericSet)
    apply L.embedding.map_repl
    intro a ha
    rw [L.embedding.map_value_total, L.embedding.map_second]
  have hk : L.value C.genericSet = internalGeneric A h hH := L.value_genericSet
  refine ⟨g, hg.trans ?_⟩
  rw [second_generic_eq_image A h hH]
  apply mem_ext
  intro x
  simp only [repl_spec]
  constructor
  · rintro ⟨a, ha, he⟩
    exact ⟨a, hk ▸ ha, he.trans (congrArg (fun f' ↦ f' ‘ (kpair.π₂ a)) hf)⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨a, hk.symm ▸ ha, he.trans (congrArg (fun f' ↦ f' ‘ (kpair.π₂ a)) hf.symm)⟩

end TwoStepModel
end ZFVP
