import ZFVP.ModelTheory.TwoStepRealization
import ZFVP.ModelTheory.ForcingRealizationGeneration

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TwoStepModel
variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t)
  {H : Set A.Model}
  (hH : IsExternalForcingGeneric (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩) H)

theorem internalGeneric_section_iff (p : V) :
    ⟨(iterandContext A h hH).check (A.check p), (iterandContext A h hH).check (A.check t)⟩ₖ ∈
      internalGeneric A h hH ↔ p ∈ A.G := by
  have he : successiveGround A h hH ⟨p, t⟩ₖ =
      ⟨(iterandContext A h hH).check (A.check p), (iterandContext A h hH).check (A.check t)⟩ₖ := by
    change (iterandContext A h hH).check (A.check ⟨p, t⟩ₖ) = _
    rw [A.check_kpair, (iterandContext A h hH).check_kpair]
  rw [← he, internalGeneric_mem_iff]
  rw [kpair_mem_twoStepCombinedFilter A Q t p (⟨t, h.topName⟩ : ForcingName A.P) H]
  constructor
  · exact fun hp ↦ hp.2.1
  · intro hp
    exact ⟨twoStep_section_mem A.order A.top h (A.generic.1.1 p hp), hp,
      externalForcingFilter_top hH.1 (top A h)⟩

theorem first_generic_in_range :
    ∃ g : (combinedContext A h hH).Model,
      (combinedRealization A h hH).value g = (iterandContext A h hH).check A.genericSet := by
  let C := combinedContext A h hH
  let B := iterandContext A h hH
  let L := combinedRealization A h hH
  let g : C.Model := {p ∈ C.check A.P ; ⟨p, C.check t⟩ₖ ∈ C.genericSet}
  have hg : L.value g = {p ∈ L.value (C.check A.P) ; ⟨p, L.value (C.check t)⟩ₖ ∈ L.value C.genericSet} := by
    change L.embedding {p ∈ C.check A.P ; ⟨p, C.check t⟩ₖ ∈ C.genericSet} =
      {p ∈ L.embedding (C.check A.P) ; ⟨p, L.embedding (C.check t)⟩ₖ ∈ L.embedding C.genericSet}
    apply L.embedding.map_separation
    intro p hp
    rw [← L.embedding.map_kpair, L.embedding.mem_iff]
  rw [L.value_check, L.value_check, L.value_genericSet] at hg
  change L.value g = {p ∈ B.check (A.check A.P) ; ⟨p, B.check (A.check t)⟩ₖ ∈ internalGeneric A h hH} at hg
  refine ⟨g, hg.trans ?_⟩
  apply mem_ext
  intro y
  rw [mem_sep_iff]
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := (B.mem_check_iff (A.check A.P) y).mp hy.1
    obtain ⟨p, hp, rfl⟩ := (A.mem_check_iff A.P z).mp hz
    have hpG := (internalGeneric_section_iff A h hH p).mp hy.2
    exact (B.check_mem_iff _ _).mpr ((A.check_mem_genericSet_iff p).mpr hpG)
  · intro hy
    obtain ⟨z, hz, rfl⟩ := (B.mem_check_iff A.genericSet y).mp hy
    obtain ⟨p, hp, rfl⟩ := (A.mem_genericSet_iff z).mp hz
    exact ⟨(B.check_mem_iff _ _).mpr ((A.check_mem_iff _ _).mpr (A.generic.1.1 p hp)),
      (internalGeneric_section_iff A h hH p).mpr hp⟩

theorem first_checks_in_range (x : A.Model) :
    ∃ y : (combinedContext A h hH).Model,
      (combinedRealization A h hH).value y = (iterandContext A h hH).check x := by
  let C := combinedContext A h hH
  let B := iterandContext A h hH
  let L := combinedRealization A h hH
  obtain ⟨τ, rfl⟩ := A.ofName_surjective x
  obtain ⟨g, hg⟩ := first_generic_in_range A h hH
  refine ⟨nameValue g (C.check τ.val), ?_⟩
  have he := L.embedding.map_nameValue g (C.check τ.val)
  change L.value (nameValue g (C.check τ.val)) = nameValue (L.value g) (L.value (C.check τ.val)) at he
  rw [hg, L.value_check] at he
  have heB := B.checkEmbedding.map_nameValue A.genericSet (A.check τ.val)
  change B.check (nameValue A.genericSet (A.check τ.val)) =
    nameValue (B.check A.genericSet) (B.check (A.check τ.val)) at heB
  rw [A.nameValue_genericSet_check τ] at heB
  exact he.trans heB.symm

end TwoStepModel
end ZFVP
