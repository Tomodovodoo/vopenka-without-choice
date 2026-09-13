import ZFVP.ModelTheory.FefermanLevyCountable
import ZFVP.ModelTheory.SymmetricModelGraph
import ZFVP.SetTheory.DependentChoice

/-! In the Feferman-Levy extension the sequence of stage sets is a set, each stage set is
countable, and their union is the power set of omega. Hence the reals are a countable
union of countable sets, and countable choice, dependent choice and choice all fail. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The reals are a countable union of countable sets. -/
def RealsCountableUnionOfCountable (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∃ C : V, C ∈ (℘ (℘ (ω : V))) ^ (ω : V) ∧ (∀ n ∈ (ω : V), IsInternallyCountable (C ‘ n)) ∧
    ∀ x : V, x ∈ ℘ (ω : V) ↔ ∃ n ∈ (ω : V), x ∈ C ‘ n

namespace FefermanLevyModel

variable {G : Set V} (hG : IsExternalForcingGeneric (flConditions V) (flOrder V) G)

/-- The sequence of stage sets. -/
noncomputable def stageSequence : (flContext G hG).Model :=
  (flContext G hG).ofName ⟨flSequenceName V, flSequenceName_hereditarilySymmetric⟩

theorem mem_stageSequence_iff (x : (flContext G hG).Model) :
    x ∈ stageSequence hG ↔ ∃ n : V, ∃ hn : n ∈ (ω : V),
      x = ⟨(flContext G hG).check n, stageSet hG hn⟩ₖ := by
  let S := flContext G hG
  have key (i : V) (hi : i ∈ (ω : V)) :
      S.ofName ⟨orderedPairName ∅ (checkName ∅ i) (flStageName i),
        hereditarilySymmetric_orderedPairName fl_poset flGroup_group flFilter_normal fl_top
          (hereditarilySymmetric_checkName fl_poset flGroup_group flFilter_normal fl_top i)
          (flStageName_hereditarilySymmetric hi)⟩ = ⟨S.check i, stageSet hG hi⟩ₖ :=
    S.of_orderedPairName ⟨checkName ∅ i, hereditarilySymmetric_checkName fl_poset flGroup_group flFilter_normal fl_top i⟩
      ⟨flStageName i, flStageName_hereditarilySymmetric hi⟩
  rw [stageSequence, S.mem_ofName_iff]
  constructor
  · rintro ⟨ν, p, _, hνp, rfl⟩
    obtain ⟨i, hi, he⟩ := (mem_sequenceName _ _ _).mp hνp
    rw [domain_flStageSequence] at hi
    refine ⟨i, hi, ?_⟩
    have hν : ν.val = orderedPairName ∅ (checkName ∅ i) (flStageName i) := by
      rw [(kpair_iff.mp he).1, flStageSequence_value hi]
    rw [← key i hi]
    exact congrArg S.ofName (Subtype.ext hν)
  · rintro ⟨n, hn, rfl⟩
    refine ⟨⟨orderedPairName ∅ (checkName ∅ n) (flStageName n),
      hereditarilySymmetric_orderedPairName fl_poset flGroup_group flFilter_normal fl_top
        (hereditarilySymmetric_checkName fl_poset flGroup_group flFilter_normal fl_top n)
        (flStageName_hereditarilySymmetric hn)⟩, ∅, externalForcingFilter_top hG.1 fl_top, ?_, (key n hn).symm⟩
    apply (mem_sequenceName _ _ _).mpr
    refine ⟨n, by rw [domain_flStageSequence]; exact hn, ?_⟩
    rw [flStageSequence_value hn]

theorem stageSet_mem_power_power {n : V} (hn : n ∈ (ω : V)) :
    stageSet hG hn ∈ ℘ (℘ (ω : (flContext G hG).Model)) := by
  apply mem_power_iff.mpr
  intro x hx
  obtain ⟨τ, hτ, rfl⟩ := (mem_stageSet_iff hG hn x).mp hx
  exact mem_power_iff.mpr (ofName_flName_subset_omega hG hn hτ)

theorem stageSequence_mem_function :
    stageSequence hG ∈ (℘ (℘ (ω : (flContext G hG).Model))) ^ (ω : (flContext G hG).Model) := by
  let S := flContext G hG
  have hω : S.check (ω : V) = (ω : S.Model) := S.checkEmbedding.map_omega
  apply mem_function.intro
  · intro z hz
    obtain ⟨n, hn, rfl⟩ := (mem_stageSequence_iff hG z).mp hz
    exact kpair_mem_iff.mpr ⟨by rw [← hω]; exact (S.check_mem_iff n ω).mpr hn, stageSet_mem_power_power hG hn⟩
  · intro x hx
    rw [← hω] at hx
    obtain ⟨n, hn, rfl⟩ := (S.mem_check_iff ω x).mp hx
    refine ⟨stageSet hG hn, (mem_stageSequence_iff hG _).mpr ⟨n, hn, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨m, hm, he⟩ := (mem_stageSequence_iff hG _).mp hy
    obtain ⟨hnm, rfl⟩ := kpair_iff.mp he
    have hnm' : n = m := (S.check_eq_iff n m).mp hnm
    subst hnm'
    rfl

instance stageSequence_isFunction : IsFunction (stageSequence hG) :=
  IsFunction.of_mem (stageSequence_mem_function hG)

theorem stageSequence_value {n : V} (hn : n ∈ (ω : V)) :
    (stageSequence hG) ‘ ((flContext G hG).check n) = stageSet hG hn :=
  value_eq_of_kpair_mem ((mem_stageSequence_iff hG _).mpr ⟨n, hn, rfl⟩)

/-- Every real of the extension lies in some stage set and conversely. -/
theorem mem_power_omega_iff_stageSequence (x : (flContext G hG).Model) :
    x ∈ ℘ (ω : (flContext G hG).Model) ↔
      ∃ n ∈ (ω : (flContext G hG).Model), x ∈ (stageSequence hG) ‘ n := by
  let S := flContext G hG
  have hω : S.check (ω : V) = (ω : S.Model) := S.checkEmbedding.map_omega
  constructor
  · intro hx
    obtain ⟨n, hn, hxn⟩ := real_mem_stageSet hG x (mem_power_iff.mp hx)
    refine ⟨S.check n, by rw [← hω]; exact (S.check_mem_iff n ω).mpr hn, ?_⟩
    rw [stageSequence_value hG hn]
    exact hxn
  · rintro ⟨n', hn', hx⟩
    rw [← hω] at hn'
    obtain ⟨n, hn, rfl⟩ := (S.mem_check_iff ω n').mp hn'
    rw [stageSequence_value hG hn] at hx
    obtain ⟨τ, hτ, rfl⟩ := (mem_stageSet_iff hG hn x).mp hx
    exact mem_power_iff.mpr (ofName_flName_subset_omega hG hn hτ)

theorem model_reals_countableUnion (hAC : InternalChoice V) :
    RealsCountableUnionOfCountable (flContext G hG).Model := by
  let S := flContext G hG
  have hω : S.check (ω : V) = (ω : S.Model) := S.checkEmbedding.map_omega
  refine ⟨stageSequence hG, stageSequence_mem_function hG, ?_, mem_power_omega_iff_stageSequence hG⟩
  intro n' hn'
  rw [← hω] at hn'
  obtain ⟨n, hn, rfl⟩ := (S.mem_check_iff ω n').mp hn'
  rw [stageSequence_value hG hn]
  exact stageSet_countable hG hAC hn

theorem model_not_dependentChoice (hAC : InternalChoice V) :
    ¬InternalDependentChoice (flContext G hG).Model := by
  let S := flContext G hG
  have hω : S.check (ω : V) = (ω : S.Model) := S.checkEmbedding.map_omega
  apply not_dependentChoice_of_countable_cover_power_omega (C := stageSequence hG)
    (domain_eq_of_mem_function (stageSequence_mem_function hG))
  · intro n' hn'
    rw [← hω] at hn'
    obtain ⟨n, hn, rfl⟩ := (S.mem_check_iff ω n').mp hn'
    rw [stageSequence_value hG hn]
    exact stageSet_countable hG hAC hn
  · apply mem_ext
    intro x
    rw [mem_sUnion_iff, mem_power_omega_iff_stageSequence hG]
    constructor
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨n, hny⟩ := mem_range_iff.mp hy
      have hn : n ∈ (ω : S.Model) := (domain_eq_of_mem_function (stageSequence_mem_function hG)) ▸
        mem_domain_of_kpair_mem hny
      exact ⟨n, hn, (value_eq_of_kpair_mem hny).symm ▸ hxy⟩
    · rintro ⟨n, hn, hx⟩
      exact ⟨_, mem_range_of_kpair_mem (kpair_value_mem
        (by rw [domain_eq_of_mem_function (stageSequence_mem_function hG)]; exact hn)), hx⟩

theorem model_not_choice (hAC : InternalChoice V) : ¬InternalChoice (flContext G hG).Model :=
  fun h ↦ model_not_dependentChoice hG hAC (dependentChoice_of_internalChoice h)

end FefermanLevyModel
end ZFVP
