import ZFVP.ModelTheory.WoodinSparseCarrierRecovery
import ZFVP.SetTheory.BoundedCodingPrimitives

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedDomainSubsetFormula : SetTheorySemisentence 2 :=
  “p a. ∀ z ∈ p, ∀ d ∈ z, ∀ x ∈ d, ∀ e ∈ z, ∀ y ∈ e,
    !boundedKpairFormula z x y → x ∈ a”

def boundedSparseCarrierCutFormula : SetTheorySemisentence 3 :=
  “B S a. !isSubsetOf B S ∧ ∀ p ∈ S, p ∈ B ↔ !boundedDomainSubsetFormula p a”

theorem boundedDomainSubsetFormula_bounded : IsBoundedSetFormula boundedDomainSubsetFormula := by
  repeat' first
    | exact (boundedKpairFormula_bounded.subst _).neg
    | exact IsBoundedSetFormula.rel _ _
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.or

theorem boundedSparseCarrierCutFormula_bounded : IsBoundedSetFormula boundedSparseCarrierCutFormula := by
  repeat' first
    | exact isSubsetOf_bounded.subst _
    | exact boundedDomainSubsetFormula_bounded.subst _
    | exact (boundedDomainSubsetFormula_bounded.subst _).neg
    | exact IsBoundedSetFormula.rel _ _
    | exact IsBoundedSetFormula.nrel _ _
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedDomainSubsetFormula_defined :
    ℒₛₑₜ-relation[V] (fun p a ↦ domain p ⊆ a) via boundedDomainSubsetFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [boundedDomainSubsetFormula]
  constructor
  · intro h x hx
    obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
    exact h ⟨x, y⟩ₖ hxy (doubleton x y) (by simp [kpair, pair_eq_doubleton])
      x (by simp) (doubleton x y) (by simp [kpair, pair_eq_doubleton]) y (by simp) rfl
  · intro h z hz d _ x _ e _ y _ he
    exact h x (mem_domain_of_kpair_mem (he ▸ hz))

instance boundedSparseCarrierCutFormula_defined :
    ℒₛₑₜ-function₂[V] sparseCarrierCut via boundedSparseCarrierCutFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [boundedSparseCarrierCutFormula]
  change (v 0 ⊆ v 1 ∧ ∀ p ∈ v 1, p ∈ v 0 ↔ domain p ⊆ v 2) ↔
    v 0 = sparseCarrierCut (v 1) (v 2)
  rw [mem_ext_iff]
  simp only [mem_sparseCarrierCut_iff]
  constructor
  · rintro ⟨hs, h⟩ p
    exact ⟨fun hp ↦ ⟨hs p hp, (h p (hs p hp)).mp hp⟩,
      fun hp ↦ (h p hp.1).mpr hp.2⟩
  · intro h
    exact ⟨fun p hp ↦ ((h p).mp hp).1, fun p hp ↦ by simpa only [hp, true_and] using h p⟩

end ZFVP
