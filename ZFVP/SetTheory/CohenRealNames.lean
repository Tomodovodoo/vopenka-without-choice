import ZFVP.SetTheory.CohenSymmetricSystem
import ZFVP.SetTheory.HereditarySymmetry

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def cohenRealPairs (I i : V) : V :=
  {z ∈ (ω : V) ×ˢ cohenConditions I ; ⟨⟨i, kpair.π₁ z⟩ₖ, (1 : V)⟩ₖ ∈ kpair.π₂ z}

instance cohenRealPairs_definable : ℒₛₑₜ-function₂[V] cohenRealPairs := by
  have h : ℒₛₑₜ-relation₃[V] (fun A I i ↦ ∀ z, z ∈ A ↔
      z ∈ (ω : V) ×ˢ cohenConditions I ∧ ⟨⟨i, kpair.π₁ z⟩ₖ, (1 : V)⟩ₖ ∈ kpair.π₂ z) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = cohenRealPairs (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [cohenRealPairs, mem_sep_iff]

noncomputable def cohenRealNameEntry (z : V) : V := ⟨checkName ∅ (kpair.π₁ z), kpair.π₂ z⟩ₖ

instance cohenRealNameEntry_definable : ℒₛₑₜ-function₁[V] cohenRealNameEntry := by
  unfold cohenRealNameEntry
  definability

noncomputable def cohenRealName (I i : V) : V := repl cohenRealNameEntry (by definability) (cohenRealPairs I i)

theorem mem_cohenRealName (I i z : V) : z ∈ cohenRealName I i ↔
    ∃ n ∈ (ω : V), ∃ p ∈ cohenConditions I,
      ⟨⟨i, n⟩ₖ, (1 : V)⟩ₖ ∈ p ∧ z = ⟨checkName ∅ n, p⟩ₖ := by
  constructor
  · intro hz
    obtain ⟨u, hu, rfl⟩ := (repl_spec (by definability)).mp hz
    obtain ⟨huD, hub⟩ := mem_sep_iff.mp hu
    obtain ⟨n, hn, p, hp, rfl⟩ := mem_prod_iff.mp huD
    exact ⟨n, hn, p, hp, by simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hub,
      by simp only [cohenRealNameEntry, kpair.π₁_kpair, kpair.π₂_kpair]⟩
  · rintro ⟨n, hn, p, hp, hb, rfl⟩
    refine (repl_spec (by definability)).mpr ⟨⟨n, p⟩ₖ, mem_sep_iff.mpr ⟨kpair_mem_iff.mpr ⟨hn, hp⟩, ?_⟩, ?_⟩
    · simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hb
    · simp only [cohenRealNameEntry, kpair.π₁_kpair, kpair.π₂_kpair]

instance cohenRealName_definable : ℒₛₑₜ-function₂[V] cohenRealName := by
  have h : ℒₛₑₜ-relation₃[V] (fun A I i ↦ ∀ z, z ∈ A ↔
      ∃ n ∈ (ω : V), ∃ p ∈ cohenConditions I,
        ⟨⟨i, n⟩ₖ, (1 : V)⟩ₖ ∈ p ∧ z = ⟨checkName ∅ n, p⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = cohenRealName (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_cohenRealName]

theorem pair_mem_cohenRealName (I i σ p : V) :
    ⟨σ, p⟩ₖ ∈ cohenRealName I i ↔
      p ∈ cohenConditions I ∧ ∃ n ∈ (ω : V), σ = checkName ∅ n ∧ ⟨⟨i, n⟩ₖ, (1 : V)⟩ₖ ∈ p := by
  rw [mem_cohenRealName]
  constructor
  · rintro ⟨n, hn, q, hq, hb, he⟩
    obtain ⟨hσ, rfl⟩ := kpair_iff.mp he
    exact ⟨hq, n, hn, hσ, hb⟩
  · rintro ⟨hp, n, hn, rfl, hb⟩
    exact ⟨n, hn, p, hp, hb, rfl⟩

theorem cohenRealName_isName (I i : V) : IsForcingName (cohenConditions I) (cohenRealName I i) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨n, hn, p, hp, hb, rfl⟩ := (mem_cohenRealName I i z).mp hz
  exact ⟨checkName ∅ n, p, hp, rfl, checkName_isName (cohen_top I).1 n⟩

theorem nameAction_cohenRealName {I π i : V} (hπ : IsInternalPermutation I π) (hi : i ∈ I) :
    nameAction (cohenPermutation I π) (cohenRealName I i) = cohenRealName I (π ‘ i) := by
  have ha := cohenPermutation_automorphism hπ
  have hc (n : V) : nameAction (cohenPermutation I π) (checkName ∅ n) = checkName ∅ n :=
    nameAction_checkName (cohen_top I).1 (forcingAutomorphism_top (cohen_poset I) (cohen_top I) ha) n
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨σ, p, hσp, rfl⟩ := (mem_nameAction_iff (cohenRealName_isName I i) _ z).mp hz
    obtain ⟨hp, n, hn, rfl, hb⟩ := (pair_mem_cohenRealName I i σ p).mp hσp
    rw [hc n, cohenPermutation_value hp]
    exact (mem_cohenRealName I (π ‘ i) _).mpr
      ⟨n, hn, cohenConditionAction I π p, cohenConditionAction_condition hπ hp,
        cohenConditionAction_pair hp hb, rfl⟩
  · intro hz
    obtain ⟨n, hn, p, hp, hb, rfl⟩ := (mem_cohenRealName I (π ‘ i) z).mp hz
    obtain ⟨q, hq, heq⟩ := forcingAutomorphism_surjective ha p hp
    have heq' : cohenConditionAction I π q = p := (cohenPermutation_value hq).symm.trans heq
    obtain ⟨j, hj, hπij⟩ := (cohenConditionAction_pair_iff hq).mp (heq'.symm ▸ hb)
    have hjI := (kpair_mem_iff.mp (finitePartialFunction_domain hq _ (mem_domain_of_kpair_mem hj))).1
    have hij : i = j := injective_value_eq hπ.1 hπ.2.1 hi hjI hπij
    have hbi : ⟨⟨i, n⟩ₖ, (1 : V)⟩ₖ ∈ q := hij.symm ▸ hj
    refine (mem_nameAction_iff (cohenRealName_isName I i) _ _).mpr
      ⟨checkName ∅ n, q, (pair_mem_cohenRealName I i _ q).mpr ⟨hq, n, hn, rfl, hbi⟩, ?_⟩
    rw [hc n, heq]

theorem cohenRealName_hereditarilySymmetric {I i : V} (hi : i ∈ I) :
    IsHereditarilySymmetricName (cohenConditions I) (cohenGroup I) (cohenFilter I) (cohenRealName I i) := by
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨cohenRealName_isName I i, ?_⟩, ?_⟩
  · apply (mem_cohenFilter_iff I _).mpr
    refine ⟨nameStabilizer_subgroup (cohenGroup_group I) (cohenRealName_isName I i), {i}, ?_, ?_, ?_⟩
    · intro j hj
      exact (mem_singleton_iff.mp hj) ▸ hi
    · simpa using internallyFinite_insert (internallyFinite_empty (V := V)) i
    · intro π hπ hfix
      refine mem_sep_iff.mpr ⟨(mem_cohenGroup I _).mpr ⟨π, hπ, rfl⟩, ?_⟩
      rw [nameAction_cohenRealName hπ hi, hfix i (by simp)]
  · intro σ p hσp
    obtain ⟨_, n, _, rfl, _⟩ := (pair_mem_cohenRealName I i σ p).mp hσp
    exact hereditarilySymmetric_checkName (cohen_poset I) (cohenGroup_group I) (cohenFilter_normal I) (cohen_top I) n

end ZFVP
