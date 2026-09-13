import ZFVP.ModelTheory.CohenOrbitEvaluation
import ZFVP.SetTheory.CohenOrbitFamilyName

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G)

noncomputable def orbitFamily (D : V) (hD : IsCohenSupportPool D) :
    (cohenContext (ω : V) G hG).Model :=
  (cohenContext (ω : V) G hG).ofName ⟨cohenOrbitFamilyName D,
    cohenOrbitFamilyName_hereditarilySymmetric hD⟩

theorem mem_orbitFamily_iff (D : V) (hD : IsCohenSupportPool D)
    (x : (cohenContext (ω : V) G hG).Model) :
    x ∈ orbitFamily hG D hD ↔ ∃ z, ∃ hz : z ∈ D,
      x = ⟨(cohenContext (ω : V) G hG).check z,
        orbitEvaluation hG (kpair.π₂ z) (hD z hz).2.1 (hD z hz).2.2.1 ⟨kpair.π₁ z, (hD z hz).1⟩⟩ₖ := by
  let S := cohenContext (ω : V) G hG
  have hv (z : V) (hz : z ∈ D) :
      S.ofName ⟨orderedPairName ∅ (checkName ∅ z)
        (cohenOrbitEvaluationName (kpair.π₂ z) (kpair.π₁ z)),
        hereditarilySymmetric_orderedPairName S.poset S.group S.normal S.top
          (hereditarilySymmetric_checkName S.poset S.group S.normal S.top z)
          (cohenOrbitEvaluationName_hereditarilySymmetric (hD z hz).2.1 (hD z hz).2.2.1 (hD z hz).1)⟩ =
      ⟨S.check z, orbitEvaluation hG (kpair.π₂ z) (hD z hz).2.1 (hD z hz).2.2.1
        ⟨kpair.π₁ z, (hD z hz).1⟩⟩ₖ :=
    S.of_orderedPairName ⟨_, hereditarilySymmetric_checkName S.poset S.group S.normal S.top z⟩
      ⟨_, cohenOrbitEvaluationName_hereditarilySymmetric (hD z hz).2.1 (hD z hz).2.2.1 (hD z hz).1⟩
  rw [orbitFamily, S.mem_ofName_iff]
  constructor
  · rintro ⟨μ, p, _, hm, hx⟩
    obtain ⟨z, hz, he⟩ := (mem_sequenceName _ _ _).mp hm
    rw [domain_cohenOrbitFamilySequence] at hz
    rw [cohenOrbitFamilySequence_value hz] at he
    refine ⟨z, hz, hx.trans ?_⟩
    rw [← hv z hz]
    exact congrArg S.ofName (Subtype.ext (kpair_iff.mp he).1)
  · rintro ⟨z, hz, hx⟩
    refine ⟨⟨_, hereditarilySymmetric_orderedPairName S.poset S.group S.normal S.top
      (hereditarilySymmetric_checkName S.poset S.group S.normal S.top z)
      (cohenOrbitEvaluationName_hereditarilySymmetric (hD z hz).2.1 (hD z hz).2.2.1 (hD z hz).1)⟩,
      ∅, externalForcingFilter_top hG.1 (cohen_top (ω : V)), ?_, hx.trans (hv z hz).symm⟩
    apply (mem_sequenceName _ _ _).mpr
    refine ⟨z, (domain_cohenOrbitFamilySequence D).symm ▸ hz, ?_⟩
    rw [cohenOrbitFamilySequence_value hz]
    rfl

theorem orbitFamily_mem_function (D : V) (hD : IsCohenSupportPool D) :
    orbitFamily hG D hD ∈ range (orbitFamily hG D hD) ^ ((cohenContext (ω : V) G hG).check D) := by
  let S := cohenContext (ω : V) G hG
  apply mem_function.intro
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := (mem_orbitFamily_iff hG D hD x).mp hx
    exact kpair_mem_iff.mpr ⟨(S.check_mem_iff _ _).mpr hz, mem_range_of_kpair_mem hx⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := (S.mem_check_iff D x).mp hx
    refine ⟨_, (mem_orbitFamily_iff hG D hD _).mpr ⟨z, hz, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨w, hw, he⟩ := (mem_orbitFamily_iff hG D hD _).mp hy
    obtain ⟨hzw, hyw⟩ := kpair_iff.mp he
    obtain rfl := (S.check_eq_iff z w).mp hzw
    exact hyw

theorem orbitFamily_value {D z : V} (hD : IsCohenSupportPool D) (hz : z ∈ D) :
    (orbitFamily hG D hD) ‘ ((cohenContext (ω : V) G hG).check z) =
      orbitEvaluation hG (kpair.π₂ z) (hD z hz).2.1 (hD z hz).2.2.1 ⟨kpair.π₁ z, (hD z hz).1⟩ := by
  have : IsFunction (orbitFamily hG D hD) := IsFunction.of_mem (orbitFamily_mem_function hG D hD)
  exact value_eq_of_kpair_mem ((mem_orbitFamily_iff hG D hD _).mpr ⟨z, hz, rfl⟩)

theorem orbitFamily_values_are_functions {D : V} (hD : IsCohenSupportPool D)
    {x : (cohenContext (ω : V) G hG).Model} (hx : x ∈ (cohenContext (ω : V) G hG).check D) :
    IsFunction ((orbitFamily hG D hD) ‘ x) := by
  obtain ⟨z, hz, rfl⟩ := ((cohenContext (ω : V) G hG).mem_check_iff D x).mp hx
  rw [orbitFamily_value hG hD hz]
  exact orbitEvaluation_isFunction hG _ _ _ _ (hD z hz).2

end CohenModel

end ZFVP
