import ZFVP.SetTheory.CountableCohenSystem
import ZFVP.SetTheory.CohenSetName

/-! Names for the generic subsets of the column set added on each row, and the name of
the set of all of them. Each row name is fixed by every permutation fixing its row, so
the names are hereditarily symmetric for the countable-support filter. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def countableCohenSubsetPairs (I J i : V) : V :=
  {z ∈ J ×ˢ countableCohenConditions I J ; ⟨⟨i, kpair.π₁ z⟩ₖ, (1 : V)⟩ₖ ∈ kpair.π₂ z}

instance countableCohenSubsetPairs_definable : ℒₛₑₜ-function₃[V] countableCohenSubsetPairs := by
  have h : ℒₛₑₜ-relation₄[V] (fun A I J i ↦ ∀ z, z ∈ A ↔
      z ∈ J ×ˢ countableCohenConditions I J ∧ ⟨⟨i, kpair.π₁ z⟩ₖ, (1 : V)⟩ₖ ∈ kpair.π₂ z) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = countableCohenSubsetPairs (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [countableCohenSubsetPairs, mem_sep_iff]

noncomputable def countableCohenSubsetName (I J i : V) : V :=
  repl cohenRealNameEntry (by definability) (countableCohenSubsetPairs I J i)

theorem mem_countableCohenSubsetName (I J i z : V) : z ∈ countableCohenSubsetName I J i ↔
    ∃ n ∈ J, ∃ p ∈ countableCohenConditions I J,
      ⟨⟨i, n⟩ₖ, (1 : V)⟩ₖ ∈ p ∧ z = ⟨checkName ∅ n, p⟩ₖ := by
  constructor
  · intro hz
    obtain ⟨u, hu, rfl⟩ := (repl_spec (by definability)).mp hz
    obtain ⟨huD, hub⟩ := mem_sep_iff.mp hu
    obtain ⟨n, hn, p, hp, rfl⟩ := mem_prod_iff.mp huD
    exact ⟨n, hn, p, hp, by simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hub,
      by simp only [cohenRealNameEntry, kpair.π₁_kpair, kpair.π₂_kpair]⟩
  · rintro ⟨n, hn, p, hp, hb, rfl⟩
    refine (repl_spec (by definability)).mpr
      ⟨⟨n, p⟩ₖ, mem_sep_iff.mpr ⟨kpair_mem_iff.mpr ⟨hn, hp⟩, ?_⟩, ?_⟩
    · simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hb
    · simp only [cohenRealNameEntry, kpair.π₁_kpair, kpair.π₂_kpair]

instance countableCohenSubsetName_definable : ℒₛₑₜ-function₃[V] countableCohenSubsetName := by
  have h : ℒₛₑₜ-relation₄[V] (fun A I J i ↦ ∀ z, z ∈ A ↔
      ∃ n ∈ J, ∃ p ∈ countableCohenConditions I J,
        ⟨⟨i, n⟩ₖ, (1 : V)⟩ₖ ∈ p ∧ z = ⟨checkName ∅ n, p⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = countableCohenSubsetName (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [mem_countableCohenSubsetName]

theorem pair_mem_countableCohenSubsetName (I J i σ p : V) :
    ⟨σ, p⟩ₖ ∈ countableCohenSubsetName I J i ↔
      p ∈ countableCohenConditions I J ∧
        ∃ n ∈ J, σ = checkName ∅ n ∧ ⟨⟨i, n⟩ₖ, (1 : V)⟩ₖ ∈ p := by
  rw [mem_countableCohenSubsetName]
  constructor
  · rintro ⟨n, hn, q, hq, hb, he⟩
    obtain ⟨hσ, rfl⟩ := kpair_iff.mp he
    exact ⟨hq, n, hn, hσ, hb⟩
  · rintro ⟨hp, n, hn, rfl, hb⟩
    exact ⟨n, hn, p, hp, hb, rfl⟩

theorem countableCohenSubsetName_isName (I J i : V) :
    IsForcingName (countableCohenConditions I J) (countableCohenSubsetName I J i) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨n, hn, p, hp, hb, rfl⟩ := (mem_countableCohenSubsetName I J i z).mp hz
  exact ⟨checkName ∅ n, p, hp, rfl, checkName_isName (countableCohen_top I J).1 n⟩

theorem nameAction_countableCohenSubsetName {I J π i : V} (hπ : IsInternalPermutation I π)
    (hi : i ∈ I) :
    nameAction (countableCohenPermutation I J π) (countableCohenSubsetName I J i) =
      countableCohenSubsetName I J (π ‘ i) := by
  have ha := countableCohenPermutation_automorphism (J := J) hπ
  have hc (n : V) : nameAction (countableCohenPermutation I J π) (checkName ∅ n) = checkName ∅ n :=
    nameAction_checkName (countableCohen_top I J).1
      (forcingAutomorphism_top (countableCohen_poset I J) (countableCohen_top I J) ha) n
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨σ, p, hσp, rfl⟩ :=
      (mem_nameAction_iff (countableCohenSubsetName_isName I J i) _ z).mp hz
    obtain ⟨hp, n, hn, rfl, hb⟩ := (pair_mem_countableCohenSubsetName I J i σ p).mp hσp
    rw [hc n, countableCohenPermutation_value hp]
    exact (mem_countableCohenSubsetName I J (π ‘ i) _).mpr
      ⟨n, hn, countableCohenConditionAction I J π p,
        countableCohenConditionAction_condition hπ hp,
        countableCohenConditionAction_pair hp hb, rfl⟩
  · intro hz
    obtain ⟨n, hn, p, hp, hb, rfl⟩ := (mem_countableCohenSubsetName I J (π ‘ i) z).mp hz
    obtain ⟨q, hq, heq⟩ := forcingAutomorphism_surjective ha p hp
    have heq' : countableCohenConditionAction I J π q = p :=
      (countableCohenPermutation_value hq).symm.trans heq
    obtain ⟨j, hj, hπij⟩ := (countableCohenConditionAction_pair_iff hq).mp (heq'.symm ▸ hb)
    have hjI := (kpair_mem_iff.mp
      (countablePartialFunction_domain hq _ (mem_domain_of_kpair_mem hj))).1
    have hij : i = j := injective_value_eq hπ.1 hπ.2.1 hi hjI hπij
    have hbi : ⟨⟨i, n⟩ₖ, (1 : V)⟩ₖ ∈ q := hij.symm ▸ hj
    refine (mem_nameAction_iff (countableCohenSubsetName_isName I J i) _ _).mpr
      ⟨checkName ∅ n, q, (pair_mem_countableCohenSubsetName I J i _ q).mpr ⟨hq, n, hn, rfl, hbi⟩, ?_⟩
    rw [hc n, heq]

theorem countableCohenSubsetName_hereditarilySymmetric {I J i : V} (hi : i ∈ I) (h0 : (0 : V) ∈ J) :
    IsHereditarilySymmetricName (countableCohenConditions I J) (countableCohenGroup I J)
      (countableCohenFilter I J) (countableCohenSubsetName I J i) := by
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨countableCohenSubsetName_isName I J i, ?_⟩, ?_⟩
  · apply countableCohenFilter_of_rows h0
      (nameStabilizer_subgroup (countableCohenGroup_group I J) (countableCohenSubsetName_isName I J i))
      (E := {i}) (fun j hj ↦ (mem_singleton_iff.mp hj) ▸ hi) (internallyCountable_singleton i)
    intro π hπ hfix
    refine mem_sep_iff.mpr ⟨(mem_countableCohenGroup I J _).mpr ⟨π, hπ, rfl⟩, ?_⟩
    rw [nameAction_countableCohenSubsetName hπ hi, hfix i (by simp)]
  · intro σ p hσp
    obtain ⟨_, n, _, rfl, _⟩ := (pair_mem_countableCohenSubsetName I J i σ p).mp hσp
    exact hereditarilySymmetric_checkName (countableCohen_poset I J) (countableCohenGroup_group I J)
      (countableCohenFilter_normal I J) (countableCohen_top I J) n

noncomputable def countableCohenSetName (I J : V) : V :=
  repl (fun i ↦ ⟨countableCohenSubsetName I J i, (∅ : V)⟩ₖ) (by definability) I

theorem mem_countableCohenSetName (I J z : V) : z ∈ countableCohenSetName I J ↔
    ∃ i ∈ I, z = ⟨countableCohenSubsetName I J i, (∅ : V)⟩ₖ := repl_spec _

instance countableCohenSetName_definable : ℒₛₑₜ-function₂[V] countableCohenSetName := by
  have h : ℒₛₑₜ-relation₃[V] (fun A I J ↦ ∀ z, z ∈ A ↔
      ∃ i ∈ I, z = ⟨countableCohenSubsetName I J i, (∅ : V)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = countableCohenSetName (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_countableCohenSetName]

theorem countableCohenSetName_isName (I J : V) :
    IsForcingName (countableCohenConditions I J) (countableCohenSetName I J) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨i, hi, rfl⟩ := (mem_countableCohenSetName I J z).mp hz
  exact ⟨countableCohenSubsetName I J i, ∅, (countableCohen_top I J).1, rfl,
    countableCohenSubsetName_isName I J i⟩

theorem nameAction_countableCohenSetName {I J π : V} (hπ : IsInternalPermutation I π) :
    nameAction (countableCohenPermutation I J π) (countableCohenSetName I J) =
      countableCohenSetName I J := by
  have ha := countableCohenPermutation_automorphism (J := J) hπ
  have htop := forcingAutomorphism_top (countableCohen_poset I J) (countableCohen_top I J) ha
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨σ, p, hσp, rfl⟩ := (mem_nameAction_iff (countableCohenSetName_isName I J) _ z).mp hz
    obtain ⟨i, hi, he⟩ := (mem_countableCohenSetName I J _).mp hσp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    rw [nameAction_countableCohenSubsetName hπ hi, htop]
    exact (mem_countableCohenSetName I J _).mpr ⟨π ‘ i, function_value_mem hπ.1 hi, rfl⟩
  · intro hz
    obtain ⟨j, hj, rfl⟩ := (mem_countableCohenSetName I J z).mp hz
    obtain ⟨i, hi, hij⟩ := hπ.surjective hj
    refine (mem_nameAction_iff (countableCohenSetName_isName I J) _ _).mpr
      ⟨countableCohenSubsetName I J i, ∅, (mem_countableCohenSetName I J _).mpr ⟨i, hi, rfl⟩, ?_⟩
    rw [nameAction_countableCohenSubsetName hπ hi, hij, htop]

theorem nameStabilizer_countableCohenSetName (I J : V) :
    nameStabilizer (countableCohenGroup I J) (countableCohenSetName I J) = countableCohenGroup I J := by
  ext σ
  simp only [nameStabilizer, mem_sep_iff]
  constructor
  · exact And.left
  · intro hσ
    obtain ⟨π, hπ, rfl⟩ := (mem_countableCohenGroup I J σ).mp hσ
    exact ⟨(mem_countableCohenGroup I J _).mpr ⟨π, hπ, rfl⟩, nameAction_countableCohenSetName hπ⟩

theorem countableCohenSetName_hereditarilySymmetric (I J : V) (h0 : (0 : V) ∈ J) :
    IsHereditarilySymmetricName (countableCohenConditions I J) (countableCohenGroup I J)
      (countableCohenFilter I J) (countableCohenSetName I J) := by
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨countableCohenSetName_isName I J, ?_⟩, ?_⟩
  · rw [nameStabilizer_countableCohenSetName]
    exact (countableCohenFilter_normal I J).2.1
  · intro σ p hp
    obtain ⟨i, hi, he⟩ := (mem_countableCohenSetName I J _).mp hp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact countableCohenSubsetName_hereditarilySymmetric hi h0

end ZFVP
