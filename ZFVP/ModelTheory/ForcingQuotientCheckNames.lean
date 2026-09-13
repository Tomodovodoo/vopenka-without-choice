import ZFVP.ModelTheory.ForcingQuotientNames
import ZFVP.SetTheory.AtomicCheckNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem externalForcingFilter_top {P R one : V} {G : Set V} (hG : IsExternalForcingFilter P R G)
    (hone : IsForcingTop P R one) : one ∈ G := by
  obtain ⟨p, hpG⟩ := hG.2.1
  exact hG.2.2.1 p hpG one hone.1 (hone.2 p (hG.1 p hpG))

noncomputable def forcingCheck (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) (one : V) (hone : IsForcingTop P R one) (x : V) :
    ForcingQuotient P R G hR hG :=
  forcingQuotientMk P R G hR hG ⟨checkName one x, checkName_isName hone.1 x⟩

theorem forcingCheck_eq_iff (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) (one : V) (hone : IsForcingTop P R one) (x y : V) :
    forcingCheck P R G hR hG one hone x = forcingCheck P R G hR hG one hone y ↔ x = y := by
  unfold forcingCheck
  rw [forcingQuotientMk_eq_iff]
  constructor
  · rintro ⟨p, _, hp⟩
    exact ((mem_atomicEquality_checkName_iff hR hone x y p).mp hp).2
  · intro he
    obtain ⟨p, hpG⟩ := hG.2.1
    exact ⟨p, hpG, (mem_atomicEquality_checkName_iff hR hone x y p).mpr ⟨hG.1 p hpG, he⟩⟩

theorem forcingCheck_injective (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) (one : V) (hone : IsForcingTop P R one) :
    Function.Injective (forcingCheck P R G hR hG one hone) :=
  fun _ _ h ↦ (forcingCheck_eq_iff _ _ _ _ _ _ _ _ _).mp h

theorem forcingCheck_mem_iff (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) (one : V) (hone : IsForcingTop P R one) (x y : V) :
    forcingCheck P R G hR hG one hone x ∈ forcingCheck P R G hR hG one hone y ↔ x ∈ y := by
  unfold forcingCheck
  rw [forcingQuotientMk_mem_iff]
  constructor
  · rintro ⟨p, _, hp⟩
    exact ((mem_atomicMembership_checkName_iff hR hone x y p).mp hp).2
  · intro hx
    obtain ⟨p, hpG⟩ := hG.2.1
    exact ⟨p, hpG, (mem_atomicMembership_checkName_iff hR hone x y p).mpr ⟨hG.1 p hpG, hx⟩⟩

theorem forcingCheck_endExtension (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (one : V) (hone : IsForcingTop P R one)
    (x : V) (y : ForcingQuotient P R G hR hG.1) :
    y ∈ forcingCheck P R G hR hG.1 one hone x ↔
      ∃ z ∈ x, y = forcingCheck P R G hR hG.1 one hone z := by
  unfold IsExternalForcingGeneric at hG
  obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 y
  constructor
  · intro hy
    obtain ⟨ν, s, _, hνs, he⟩ := (forcingQuotientMk_mem_subname_iff P R G hR hG σ
      ⟨checkName one x, checkName_isName hone.1 x⟩).mp hy
    obtain ⟨z, hz, hpair⟩ := (mem_checkName_iff one x _).mp hνs
    have hν : ν = (⟨checkName one z, checkName_isName hone.1 z⟩ : ForcingName P) :=
      Subtype.ext (kpair_iff.mp hpair).1
    exact ⟨z, hz, he.trans (congrArg (forcingQuotientMk P R G hR hG.1) hν)⟩
  · rintro ⟨z, hz, he⟩
    rw [he]
    exact (forcingCheck_mem_iff P R G hR hG.1 one hone z x).mpr hz

end ZFVP
