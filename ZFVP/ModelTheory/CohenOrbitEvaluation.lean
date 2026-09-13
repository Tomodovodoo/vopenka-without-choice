import ZFVP.ModelTheory.CohenFiniteAssignmentValues
import ZFVP.ModelTheory.SymmetricModelGraph
import ZFVP.SetTheory.CohenOrbitEvaluationName
import ZFVP.SetTheory.CohenSupportOrbits

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G)

noncomputable def orbitValue (τ : (cohenContext (ω : V) G hG).Name)
    (b : V) (hb : IsInternalPermutation (ω : V) b) : (cohenContext (ω : V) G hG).Model :=
  (cohenContext (ω : V) G hG).ofName ⟨nameAction (cohenPermutation (ω : V) b) τ.val,
    hereditarilySymmetric_nameAction (cohenGroup_group (ω : V)) (cohenFilter_normal (ω : V))
      ((mem_cohenGroup (ω : V) _).mpr ⟨b, hb, rfl⟩) τ.property⟩

noncomputable def orbitEvaluation (E : V) (hEω : E ⊆ (ω : V)) (hEf : IsInternallyFinite E)
    (τ : (cohenContext (ω : V) G hG).Name) : (cohenContext (ω : V) G hG).Model :=
  (cohenContext (ω : V) G hG).ofName ⟨cohenOrbitEvaluationName E τ.val,
    cohenOrbitEvaluationName_hereditarilySymmetric hEω hEf τ.property⟩

theorem mem_orbitEvaluation_iff (E : V) (hEω : E ⊆ (ω : V)) (hEf : IsInternallyFinite E)
    (τ : (cohenContext (ω : V) G hG).Name) (z : (cohenContext (ω : V) G hG).Model) :
    z ∈ orbitEvaluation hG E hEω hEf τ ↔
      ∃ b, ∃ hb : IsInternalPermutation (ω : V) b,
        z = ⟨finiteAssignmentValue hG E hEω hEf b hb, orbitValue hG τ b hb⟩ₖ := by
  let S := cohenContext (ω : V) G hG
  have hA := cohenFiniteAssignmentName_hereditarilySymmetric hEω hEf
  have hact (b : V) (hb : IsInternalPermutation (ω : V) b) {μ : V}
      (hμ : IsHereditarilySymmetricName S.P S.Γ S.F μ) :
      IsHereditarilySymmetricName S.P S.Γ S.F (nameAction (cohenPermutation (ω : V) b) μ) :=
    hereditarilySymmetric_nameAction S.group S.normal
      ((mem_cohenGroup (ω : V) _).mpr ⟨b, hb, rfl⟩) hμ
  have hv (b : V) (hb : IsInternalPermutation (ω : V) b) :
      S.ofName ⟨orderedPairName ∅
        (nameAction (cohenPermutation (ω : V) b) (cohenFiniteAssignmentName E))
        (nameAction (cohenPermutation (ω : V) b) τ.val),
        hereditarilySymmetric_orderedPairName S.poset S.group S.normal S.top
          (hact b hb hA) (hact b hb τ.property)⟩ =
      ⟨finiteAssignmentValue hG E hEω hEf b hb, orbitValue hG τ b hb⟩ₖ :=
    S.of_orderedPairName ⟨_, hact b hb hA⟩ ⟨_, hact b hb τ.property⟩
  rw [orbitEvaluation, S.mem_ofName_iff]
  constructor
  · rintro ⟨μ, p, _, hm, hz⟩
    obtain ⟨b, hb, he⟩ := (mem_cohenOrbitEvaluationName hEω τ.property.1 _).mp hm
    refine ⟨b, hb, hz.trans ?_⟩
    rw [← hv b hb]
    exact congrArg S.ofName (Subtype.ext (kpair_iff.mp he).1)
  · rintro ⟨b, hb, hz⟩
    refine ⟨⟨_, hereditarilySymmetric_orderedPairName S.poset S.group S.normal S.top
      (hact b hb hA) (hact b hb τ.property)⟩, ∅,
      externalForcingFilter_top hG.1 (cohen_top (ω : V)), ?_, hz.trans (hv b hb).symm⟩
    exact (mem_cohenOrbitEvaluationName hEω τ.property.1 _).mpr ⟨b, hb, rfl⟩

theorem orbitEvaluation_isFunction (E : V) (hEω : E ⊆ (ω : V)) (hEf : IsInternallyFinite E)
    (τ : (cohenContext (ω : V) G hG).Name) (hE : IsCohenNameSupport τ.val E) :
    IsFunction (orbitEvaluation hG E hEω hEf τ) := by
  let S := cohenContext (ω : V) G hG
  apply isFunction_iff.mpr
  apply mem_function.intro
  · intro z hz
    obtain ⟨b, hb, rfl⟩ := (mem_orbitEvaluation_iff hG E hEω hEf τ z).mp hz
    exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hz, mem_range_of_kpair_mem hz⟩
  · intro x hx
    obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
    refine ⟨y, hxy, ?_⟩
    intro z hxz
    obtain ⟨b, hb, heyb⟩ := (mem_orbitEvaluation_iff hG E hEω hEf τ _).mp hxy
    obtain ⟨c, hc, hezc⟩ := (mem_orbitEvaluation_iff hG E hEω hEf τ _).mp hxz
    obtain ⟨hxb, hyb⟩ := kpair_iff.mp heyb
    obtain ⟨hxc, hzc⟩ := kpair_iff.mp hezc
    have hagree := finiteAssignmentValue_eq_implies_agree hG E hEω hEf b hb c hc (hxb.symm.trans hxc)
    have hn := cohenNameAction_eq_of_agree_on_support τ.property.1 hEω hE.2.2 hb hc hagree
    have hv : orbitValue hG τ b hb = orbitValue hG τ c hc :=
      congrArg S.ofName (Subtype.ext hn)
    exact hzc.trans (hv.symm.trans hyb.symm)

theorem orbitEvaluation_domain_subset (E : V) (hEω : E ⊆ (ω : V)) (hEf : IsInternallyFinite E)
    (τ : (cohenContext (ω : V) G hG).Name) :
    domain (orbitEvaluation hG E hEω hEf τ) ⊆
      reals hG ^ ((cohenContext (ω : V) G hG).check E) := by
  intro x hx
  obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
  obtain ⟨b, hb, he⟩ := (mem_orbitEvaluation_iff hG E hEω hEf τ _).mp hxy
  rw [(kpair_iff.mp he).1]
  exact finiteAssignmentValue_function hG E hEω hEf b hb

theorem orbitValue_identity (τ : (cohenContext (ω : V) G hG).Name) :
    orbitValue hG τ (identity (ω : V)) (internalPermutation_identity _) =
      (cohenContext (ω : V) G hG).ofName τ := by
  apply congrArg (cohenContext (ω : V) G hG).ofName
  apply Subtype.ext
  exact (congrArg (fun b ↦ nameAction b τ.val) (cohenPermutation_identity (ω : V))).trans
    (nameAction_identity τ.property.1)

theorem mem_range_orbitEvaluation (E : V) (hEω : E ⊆ (ω : V)) (hEf : IsInternallyFinite E)
    (τ : (cohenContext (ω : V) G hG).Name) :
    (cohenContext (ω : V) G hG).ofName τ ∈ range (orbitEvaluation hG E hEω hEf τ) := by
  have hh := (mem_orbitEvaluation_iff hG E hEω hEf τ _).mpr
    ⟨identity (ω : V), internalPermutation_identity _, rfl⟩
  rw [orbitValue_identity] at hh
  exact mem_range_of_kpair_mem hh

end CohenModel

end ZFVP
