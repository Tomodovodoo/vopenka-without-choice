import ZFVP.ModelTheory.CohenModel
import ZFVP.ModelTheory.ForcingModelPairs
import ZFVP.SetTheory.CohenEnumerationName
import ZFVP.SetTheory.EndExtensionFinite

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CohenModel

variable {I : V} {G : Set V} (hG : IsExternalForcingGeneric (cohenConditions I) (cohenOrder I) G)

noncomputable def enumeration : (cohenContext I G hG).toForcingContext.Model :=
  (cohenContext I G hG).toForcingContext.ofName ⟨cohenEnumerationName I, cohenEnumerationName_isName I⟩

theorem mem_enumeration_iff (z : (cohenContext I G hG).toForcingContext.Model) :
    z ∈ enumeration hG ↔ ∃ i : V, ∃ hi : i ∈ I,
      z = ⟨(cohenContext I G hG).toForcingContext.check i, (cohenContext I G hG).toOrdinary (real hG i hi)⟩ₖ := by
  let S := cohenContext I G hG
  let O := S.toForcingContext
  have hv (i : V) (hi : i ∈ I) :
      O.ofName ⟨orderedPairName ∅ (checkName ∅ i) (cohenRealName I i),
        orderedPairName_isName (cohen_top I).1 (checkName_isName (cohen_top I).1 i) (cohenRealName_isName I i)⟩ =
      ⟨O.check i, S.toOrdinary (real hG i hi)⟩ₖ :=
    O.of_orderedPair ⟨checkName ∅ i, checkName_isName (cohen_top I).1 i⟩
      ⟨cohenRealName I i, cohenRealName_isName I i⟩
  rw [enumeration, O.mem_ofName_iff]
  constructor
  · rintro ⟨σ, p, _, hσp, hz⟩
    obtain ⟨i, hi, he⟩ := (mem_cohenEnumerationName I _).mp hσp
    have he' : O.ofName σ = ⟨O.check i, S.toOrdinary (real hG i hi)⟩ₖ := by
      rw [← hv i hi]
      exact congrArg O.ofName (Subtype.ext (kpair_iff.mp he).1)
    exact ⟨i, hi, hz.trans he'⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨orderedPairName ∅ (checkName ∅ i) (cohenRealName I i),
      orderedPairName_isName (cohen_top I).1 (checkName_isName (cohen_top I).1 i) (cohenRealName_isName I i)⟩,
      ∅, externalForcingFilter_top hG.1 (cohen_top I),
      (mem_cohenEnumerationName I _).mpr ⟨i, hi, rfl⟩, (hv i hi).symm⟩

theorem enumeration_function : enumeration hG ∈
    (cohenContext I G hG).toOrdinary (reals hG) ^ (cohenContext I G hG).toForcingContext.check I := by
  let S := cohenContext I G hG
  let O := S.toForcingContext
  apply mem_function.intro
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := (mem_enumeration_iff hG z).mp hz
    exact kpair_mem_iff.mpr ⟨(O.check_mem_iff i I).mpr hi,
      (S.toOrdinary_mem_iff _ _).mpr ((mem_reals_iff hG _).mpr ⟨i, hi, rfl⟩)⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := (O.mem_check_iff I x).mp hx
    refine ⟨S.toOrdinary (real hG i hi), (mem_enumeration_iff hG _).mpr ⟨i, hi, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨j, hj, he⟩ := (mem_enumeration_iff hG _).mp hy
    obtain ⟨hij, hyj⟩ := kpair_iff.mp he
    obtain rfl := (O.check_eq_iff i j).mp hij
    exact hyj

theorem enumeration_injective : Injective (enumeration hG) := by
  let S := cohenContext I G hG
  intro x y z hx hy
  obtain ⟨i, hi, hxi⟩ := (mem_enumeration_iff hG _).mp hx
  obtain ⟨j, hj, hyj⟩ := (mem_enumeration_iff hG _).mp hy
  obtain ⟨hxi, hzi⟩ := kpair_iff.mp hxi
  obtain ⟨hyj, hzj⟩ := kpair_iff.mp hyj
  have hij : i = j := (real_eq_iff hG hi hj).mp (S.toOrdinary_injective (hzi.symm.trans hzj))
  exact hxi.trans ((congrArg S.toForcingContext.check hij).trans hyj.symm)

theorem real_subset_omega (i : V) (hi : i ∈ I) : real hG i hi ⊆ (ω : (cohenContext I G hG).Model) := by
  intro x hx
  obtain ⟨n, hn, _, _, _, rfl⟩ := (mem_real_iff hG i hi x).mp hx
  rw [← (cohenContext I G hG).checkEmbedding.map_omega]
  exact ((cohenContext I G hG).check_mem_iff n ω).mpr hn

theorem reals_subset_power_omega : reals hG ⊆ ℘ (ω : (cohenContext I G hG).Model) := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := (mem_reals_iff hG x).mp hx
  exact mem_power_iff.mpr (real_subset_omega hG i hi)

end CohenModel

theorem cohen_reals_internallyInfinite {G : Set V}
    (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G) :
    IsInternallyInfinite (CohenModel.reals hG) := by
  let S := cohenContext (ω : V) G hG
  have hω : (ω : S.toForcingContext.Model) ≤# S.toOrdinary (CohenModel.reals hG) := by
    refine ⟨CohenModel.enumeration hG, ?_, CohenModel.enumeration_injective hG⟩
    have hh := CohenModel.enumeration_function hG
    change _ ∈ _ ^ S.toForcingContext.checkEmbedding (ω : V) at hh
    rwa [S.toForcingContext.checkEmbedding.map_omega] at hh
  intro hfin
  exact omega_internallyInfinite (internallyFinite_of_cardLE (S.inclusion.map_internallyFinite hfin) hω)

end ZFVP
