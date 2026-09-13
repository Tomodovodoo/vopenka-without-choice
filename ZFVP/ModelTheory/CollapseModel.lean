import ZFVP.SetTheory.SetCollapse
import ZFVP.ModelTheory.ForcingChoice
import ZFVP.ModelTheory.ForcingQuotientGeneric

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def collapseContext (A : V) (G : Set V)
    (hG : IsExternalForcingGeneric (collapseConditions A) (collapseOrder A) G) : ForcingContext V :=
  ⟨collapseConditions A, collapseOrder A, ∅, G, (collapse_poset A).1, collapse_top A, hG⟩

namespace CollapseModel

variable {A : V} {G : Set V}
  (hG : IsExternalForcingGeneric (collapseConditions A) (collapseOrder A) G)

noncomputable def genericSet : (collapseContext A G hG).Model :=
  forcingGenericSet _ _ G (collapse_poset A).1 hG.1 ∅ (collapse_top A)

theorem mem_genericSet (x : (collapseContext A G hG).Model) :
    x ∈ genericSet hG ↔ ∃ p ∈ G, x = (collapseContext A G hG).check p :=
  forcingGenericSet_mem_iff _ _ G (collapse_poset A).1 hG ∅ (collapse_top A) x

noncomputable def genericFunction : (collapseContext A G hG).Model := ⋃ˢ genericSet hG

theorem mem_genericFunction (x : (collapseContext A G hG).Model) :
    x ∈ genericFunction hG ↔ ∃ p ∈ G, x ∈ (collapseContext A G hG).check p := by
  simp only [genericFunction, mem_sUnion_iff, mem_genericSet]
  constructor
  · rintro ⟨y, ⟨p, hp, rfl⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨_, ⟨p, hp, rfl⟩, hx⟩

instance genericFunction_isFunction : IsFunction (genericFunction hG) := by
  let S := collapseContext A G hG
  have hfun (p : V) (hp : p ∈ G) : IsFunction (S.check p) := by
    have : IsFunction p := ((mem_finitePartialFunctions ω A p).mp (hG.1.1 p hp)).2.1
    exact S.check_isFunction p
  apply isFunction_sUnion
  · intro f hf
    obtain ⟨p, hp, rfl⟩ := (mem_genericSet hG f).mp hf
    exact hfun p hp
  · intro f hf g hg x y z hxy hxz
    obtain ⟨p, hp, rfl⟩ := (mem_genericSet hG f).mp hf
    obtain ⟨q, hq, rfl⟩ := (mem_genericSet hG g).mp hg
    obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p hp q hq
    have hpr : p ⊆ r := ((pair_mem_reverseInclusionOrder _ _ _).mp hrp).2.2
    have hqr : q ⊆ r := ((pair_mem_reverseInclusionOrder _ _ _).mp hrq).2.2
    have : IsFunction (S.check r) := hfun r hr
    exact IsFunction.unique (f := S.check r) ((S.checkEmbedding.subset_iff p r).mpr hpr _ hxy)
      ((S.checkEmbedding.subset_iff q r).mpr hqr _ hxz)

theorem genericFunction_mem_function (hA : IsNonempty A) :
    genericFunction hG ∈ (collapseContext A G hG).check A ^ (ω : (collapseContext A G hG).Model) := by
  let S := collapseContext A G hG
  have hω : S.check (ω : V) = (ω : S.Model) := S.checkEmbedding.map_omega
  rw [← hω]
  apply mem_function.intro
  · intro z hz
    obtain ⟨p, hp, hzp⟩ := (mem_genericFunction hG z).mp hz
    have hpsub := ((mem_finitePartialFunctions ω A p).mp (hG.1.1 p hp)).1
    have hh := (S.checkEmbedding.subset_iff p (ω ×ˢ A)).mpr hpsub z hzp
    change z ∈ S.check (ω ×ˢ A) at hh
    rwa [show S.check (ω ×ˢ A) = S.check ω ×ˢ S.check A from S.checkEmbedding.map_prod ω A] at hh
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := (S.mem_check_iff ω x).mp hx
    obtain ⟨p, hpG, hp⟩ := hG.2 _ (collapse_domain_dense hn hA)
    obtain ⟨a, ha⟩ := mem_domain_iff.mp (mem_sep_iff.mp hp).2
    have hpair : ⟨S.check n, S.check a⟩ₖ ∈ genericFunction hG := by
      apply (mem_genericFunction hG _).mpr
      refine ⟨p, hpG, ?_⟩
      rw [← S.check_kpair, S.check_mem_iff]
      exact ha
    exact ⟨S.check a, hpair, fun _ h ↦ IsFunction.unique h hpair⟩

theorem genericFunction_range (hA : IsNonempty A) :
    range (genericFunction hG) = (collapseContext A G hG).check A := by
  let S := collapseContext A G hG
  apply SetTheory.subset_antisymm (range_subset_of_mem_function (genericFunction_mem_function hG hA))
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (S.mem_check_iff A x).mp hx
  obtain ⟨p, hpG, hp⟩ := hG.2 _ (collapse_range_dense ha)
  obtain ⟨n, hn⟩ := mem_range_iff.mp (mem_sep_iff.mp hp).2
  apply mem_range_of_kpair_mem (x := S.check n)
  apply (mem_genericFunction hG _).mpr
  refine ⟨p, hpG, ?_⟩
  rw [← S.check_kpair, S.check_mem_iff]
  exact hn

theorem check_wellOrderable (hA : IsNonempty A) :
    IsWellOrderable ((collapseContext A G hG).check A) :=
  wellOrderable_of_surjective_function (ordinal_wellOrderable ω)
    (genericFunction_mem_function hG hA) (genericFunction_range hG hA)

theorem internalChoice_of_svcWitness (hA : IsSVCWitness A) :
    InternalChoice (collapseContext A G hG).Model :=
  (collapseContext A G hG).internalChoice_of_svcWitness hA (check_wellOrderable hG hA.nonempty)

end CollapseModel
end ZFVP
