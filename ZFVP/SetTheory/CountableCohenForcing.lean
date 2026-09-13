import ZFVP.SetTheory.CountablePartialFunctionAutomorphisms
import ZFVP.SetTheory.CohenForcing
import ZFVP.SetTheory.ProductPermutations
import ZFVP.SetTheory.SymmetricSystems
import ZFVP.SetTheory.InternalTranspositions

/-! Countable-support Cohen forcing over a row set `I` and a column set `J`:
countable partial functions from `I × J` to `2`, with permutations of `I` acting
on the first coordinate. The columns are later taken to be the first uncountable
ordinal, so every condition leaves a column free. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def countableCohenConditions (I J : V) : V :=
  countablePartialFunctions (I ×ˢ J) 2

noncomputable def countableCohenOrder (I J : V) : V :=
  reverseInclusionOrder (countableCohenConditions I J)

instance countableCohenConditions_definable : ℒₛₑₜ-function₂[V] countableCohenConditions := by
  unfold countableCohenConditions
  definability

instance countableCohenOrder_definable : ℒₛₑₜ-function₂[V] countableCohenOrder := by
  unfold countableCohenOrder
  definability

theorem countableCohen_poset (I J : V) :
    IsForcingPoset (countableCohenConditions I J) (countableCohenOrder I J) :=
  reverseInclusionOrder_poset _

theorem countableCohen_top (I J : V) :
    IsForcingTop (countableCohenConditions I J) (countableCohenOrder I J) ∅ :=
  countablePartialFunctions_top _ _

theorem pair_mem_countableCohenOrder (I J p q : V) :
    ⟨p, q⟩ₖ ∈ countableCohenOrder I J ↔
      p ∈ countableCohenConditions I J ∧ q ∈ countableCohenConditions I J ∧ q ⊆ p :=
  pair_mem_reverseInclusionOrder _ _ _

theorem countableCohenCondition_function {I J p : V} (hp : p ∈ countableCohenConditions I J) :
    IsFunction p := ((mem_countablePartialFunctions _ _ _).mp hp).2.1

theorem countableCohenSupport_countable {I J p : V} (hp : p ∈ countableCohenConditions I J) :
    IsInternallyCountable (cohenSupport p) :=
  internallyCountable_domain ((mem_countablePartialFunctions _ _ _).mp hp).2.2

theorem countableCohenSupport_subset {I J p : V} (hp : p ∈ countableCohenConditions I J) :
    cohenSupport p ⊆ I := by
  intro i hi
  obtain ⟨n, b, hb⟩ := (mem_cohenSupport p i).mp hi
  exact (kpair_mem_iff.mp (countablePartialFunction_domain hp _ (mem_domain_of_kpair_mem hb))).1

/-- The columns used by a condition. -/
noncomputable def cohenColumns (p : V) : V := range (domain p)

instance cohenColumns_definable : ℒₛₑₜ-function₁[V] cohenColumns := by
  unfold cohenColumns
  definability

theorem mem_cohenColumns (p n : V) : n ∈ cohenColumns p ↔ ∃ i b, ⟨⟨i, n⟩ₖ, b⟩ₖ ∈ p := by
  simp only [cohenColumns, mem_range_iff, mem_domain_iff]

theorem countableCohenColumns_countable {I J p : V} (hp : p ∈ countableCohenConditions I J) :
    IsInternallyCountable (cohenColumns p) :=
  internallyCountable_range ((mem_countablePartialFunctions _ _ _).mp hp).2.2

theorem countableCohen_insert {I J p i n b : V} (hp : p ∈ countableCohenConditions I J)
    (hi : i ∈ I) (hn : n ∈ J) (hb : b ∈ (2 : V))
    (hfresh : ⟨i, n⟩ₖ ∉ domain p) : insert ⟨⟨i, n⟩ₖ, b⟩ₖ p ∈ countableCohenConditions I J :=
  countablePartialFunction_insert hp (kpair_mem_iff.mpr ⟨hi, hn⟩) hb hfresh

theorem countableCohen_coordinate_dense {I J i n : V} (hi : i ∈ I) (hn : n ∈ J) :
    ForcingDense (countableCohenConditions I J) (countableCohenOrder I J)
      {p ∈ countableCohenConditions I J ; ⟨i, n⟩ₖ ∈ domain p} :=
  countablePartialFunctions_domain_dense (kpair_mem_iff.mpr ⟨hi, hn⟩)
    (show (0 : V) ∈ 2 by simp)

/-- With uncountably many columns every condition leaves a column entirely free. -/
theorem countableCohen_fresh_column {I p : V}
    (hp : p ∈ countableCohenConditions I (hartogsNumber (ω : V))) :
    ∃ n ∈ hartogsNumber (ω : V), ∀ i, ⟨i, n⟩ₖ ∉ domain p := by
  obtain ⟨n, hn, hnf⟩ := exists_fresh_of_countable (countableCohenColumns_countable hp)
  exact ⟨n, hn, fun i hi ↦ hnf (mem_range_of_kpair_mem hi)⟩

theorem countableCohen_separate_rows {I p i j : V}
    (hp : p ∈ countableCohenConditions I (hartogsNumber (ω : V)))
    (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) :
    ∃ q ∈ countableCohenConditions I (hartogsNumber (ω : V)),
      ⟨q, p⟩ₖ ∈ countableCohenOrder I (hartogsNumber (ω : V)) ∧
      ∃ n ∈ hartogsNumber (ω : V), ⟨⟨i, n⟩ₖ, 0⟩ₖ ∈ q ∧ ⟨⟨j, n⟩ₖ, 1⟩ₖ ∈ q := by
  obtain ⟨n, hn, hfresh⟩ := countableCohen_fresh_column hp
  let r := insert ⟨⟨i, n⟩ₖ, (0 : V)⟩ₖ p
  have hr : r ∈ countableCohenConditions I (hartogsNumber (ω : V)) :=
    countableCohen_insert hp hi hn (by simp) (hfresh i)
  have hjfresh : ⟨j, n⟩ₖ ∉ domain r := by
    intro hh
    have hh' : ⟨j, n⟩ₖ = ⟨i, n⟩ₖ ∨ ⟨j, n⟩ₖ ∈ domain p := by
      simpa only [r, domain_insert, mem_insert] using hh
    rcases hh' with he | hh'
    · exact hij (kpair_iff.mp he).1.symm
    · exact hfresh j hh'
  let q := insert ⟨⟨j, n⟩ₖ, (1 : V)⟩ₖ r
  have hq : q ∈ countableCohenConditions I (hartogsNumber (ω : V)) :=
    countableCohen_insert hr hj hn (by simp) hjfresh
  refine ⟨q, hq, (pair_mem_countableCohenOrder _ _ q p).mpr ⟨hq, hp, ?_⟩, n, hn, ?_, ?_⟩
  · intro z hz
    exact mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inr hz)))
  · exact mem_insert.mpr (Or.inr (by simp [r]))
  · simp [q]

theorem countableCohen_separate_rows_dense {I i j : V} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) :
    ForcingDense (countableCohenConditions I (hartogsNumber (ω : V)))
      (countableCohenOrder I (hartogsNumber (ω : V)))
      {p ∈ countableCohenConditions I (hartogsNumber (ω : V)) ; ∃ n ∈ hartogsNumber (ω : V),
        ⟨⟨i, n⟩ₖ, 0⟩ₖ ∈ p ∧ ⟨⟨j, n⟩ₖ, 1⟩ₖ ∈ p} := by
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, fun p hp ↦ ?_⟩
  obtain ⟨q, hq, hqp, hn⟩ := countableCohen_separate_rows hp hi hj hij
  exact ⟨q, mem_sep_iff.mpr ⟨hq, hn⟩, hqp⟩

/-! ### The action of permutations of the rows -/

noncomputable def countableCohenConditionAction (I J π p : V) : V :=
  permutedGraph (productPermutation I J π) p

instance countableCohenConditionAction_definable :
    ℒₛₑₜ-function₄[V] countableCohenConditionAction := by
  unfold countableCohenConditionAction
  definability

noncomputable def countableCohenPermutation (I J π : V) : V :=
  countablePartialFunctionPermutation (I ×ˢ J) 2 (productPermutation I J π)

instance countableCohenPermutation_definable : ℒₛₑₜ-function₃[V] countableCohenPermutation := by
  unfold countableCohenPermutation
  definability

theorem countableCohenPermutation_value {I J π p : V} (hp : p ∈ countableCohenConditions I J) :
    (countableCohenPermutation I J π) ‘ p = countableCohenConditionAction I J π p :=
  countablePartialFunctionPermutation_value hp

theorem countableCohenConditionAction_condition {I J π p : V} (hπ : IsInternalPermutation I π)
    (hp : p ∈ countableCohenConditions I J) :
    countableCohenConditionAction I J π p ∈ countableCohenConditions I J :=
  permutedGraph_countable_condition (productPermutation_permutation hπ) hp

theorem countableCohenPermutation_automorphism {I J π : V} (hπ : IsInternalPermutation I π) :
    IsForcingAutomorphism (countableCohenConditions I J) (countableCohenOrder I J)
      (countableCohenPermutation I J π) :=
  countablePartialFunctionPermutation_automorphism (productPermutation_permutation hπ)

theorem countableCohenPermutation_identity (I J : V) :
    countableCohenPermutation I J (identity I) = identity (countableCohenConditions I J) := by
  unfold countableCohenPermutation
  rw [productPermutation_identity]
  exact countablePartialFunctionPermutation_identity _ _

theorem countableCohenPermutation_compose {I J π ρ : V}
    (hπ : IsInternalPermutation I π) (hρ : IsInternalPermutation I ρ) :
    countableCohenPermutation I J (compose π ρ) =
      compose (countableCohenPermutation I J π) (countableCohenPermutation I J ρ) := by
  unfold countableCohenPermutation
  rw [productPermutation_compose hπ hρ]
  exact countablePartialFunctionPermutation_compose (productPermutation_permutation hπ)
    (productPermutation_permutation hρ)

theorem countableCohenPermutation_inverse {I J π : V} (hπ : IsInternalPermutation I π) :
    countableCohenPermutation I J (converseGraph π) =
      converseGraph (countableCohenPermutation I J π) := by
  unfold countableCohenPermutation
  rw [productPermutation_inverse hπ]
  exact countablePartialFunctionPermutation_inverse (productPermutation_permutation hπ)

noncomputable def countableCohenGroup (I J : V) : V :=
  repl (countableCohenPermutation I J) (by definability) (internalPermutations I)

theorem mem_countableCohenGroup (I J σ : V) :
    σ ∈ countableCohenGroup I J ↔
      ∃ π, IsInternalPermutation I π ∧ σ = countableCohenPermutation I J π := by
  simp only [countableCohenGroup, repl_spec, mem_internalPermutations]

instance countableCohenGroup_definable : ℒₛₑₜ-function₂[V] countableCohenGroup := by
  have h : ℒₛₑₜ-relation₃[V] (fun G I J ↦ ∀ σ, σ ∈ G ↔
      ∃ π, IsInternalPermutation I π ∧ σ = countableCohenPermutation I J π) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = countableCohenGroup (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_countableCohenGroup]

theorem countableCohenGroup_group (I J : V) :
    IsForcingAutomorphismGroup (countableCohenConditions I J) (countableCohenOrder I J)
      (countableCohenGroup I J) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨π, hπ, rfl⟩ := (mem_countableCohenGroup I J σ).mp hσ
    exact countableCohenPermutation_automorphism hπ
  · exact (mem_countableCohenGroup I J _).mpr
      ⟨identity I, internalPermutation_identity I, (countableCohenPermutation_identity I J).symm⟩
  · intro σ hσ τ hτ
    obtain ⟨π, hπ, rfl⟩ := (mem_countableCohenGroup I J σ).mp hσ
    obtain ⟨ρ, hρ, rfl⟩ := (mem_countableCohenGroup I J τ).mp hτ
    exact (mem_countableCohenGroup I J _).mpr
      ⟨compose π ρ, hπ.comp hρ, (countableCohenPermutation_compose hπ hρ).symm⟩
  · intro σ hσ
    obtain ⟨π, hπ, rfl⟩ := (mem_countableCohenGroup I J σ).mp hσ
    exact (mem_countableCohenGroup I J _).mpr
      ⟨converseGraph π, hπ.inv, (countableCohenPermutation_inverse hπ).symm⟩

theorem countableCohenConditionAction_pair {I J π p i n b : V}
    (hp : p ∈ countableCohenConditions I J) (he : ⟨⟨i, n⟩ₖ, b⟩ₖ ∈ p) :
    ⟨⟨π ‘ i, n⟩ₖ, b⟩ₖ ∈ countableCohenConditionAction I J π p := by
  have : IsFunction p := countableCohenCondition_function hp
  have hic : ⟨i, n⟩ₖ ∈ I ×ˢ J :=
    countablePartialFunction_domain hp _ (mem_domain_of_kpair_mem he)
  exact (pair_mem_permutedGraph _ p _ b).mpr
    ⟨⟨i, n⟩ₖ, he, (productPermutation_value (kpair_mem_iff.mp hic).1 (kpair_mem_iff.mp hic).2).symm⟩

theorem countableCohenConditionAction_pair_iff {I J π p x n b : V}
    (hp : p ∈ countableCohenConditions I J) :
    ⟨⟨x, n⟩ₖ, b⟩ₖ ∈ countableCohenConditionAction I J π p ↔
      ∃ i, ⟨⟨i, n⟩ₖ, b⟩ₖ ∈ p ∧ x = π ‘ i := by
  have : IsFunction p := countableCohenCondition_function hp
  constructor
  · intro he
    obtain ⟨z, hz, hez⟩ := (pair_mem_permutedGraph _ p _ b).mp he
    obtain ⟨i, hi, j, hj, rfl⟩ :=
      mem_prod_iff.mp (countablePartialFunction_domain hp _ (mem_domain_of_kpair_mem hz))
    rw [productPermutation_value hi hj] at hez
    obtain ⟨hxi, rfl⟩ := kpair_iff.mp hez
    exact ⟨i, hz, hxi⟩
  · rintro ⟨i, he, rfl⟩
    exact countableCohenConditionAction_pair hp he

theorem countableCohenConditionAction_fix {I J π p : V} (hp : p ∈ countableCohenConditions I J)
    (hfix : ∀ i ∈ cohenSupport p, π ‘ i = i) : countableCohenConditionAction I J π p = p := by
  have : IsFunction p := countableCohenCondition_function hp
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨u, hu, rfl⟩ := (mem_permutedGraph _ p z).mp hz
    obtain ⟨v, b, rfl⟩ := IsFunction.mem_eq_kpair hu
    obtain ⟨i, hi, n, hn, rfl⟩ :=
      mem_prod_iff.mp (countablePartialFunction_domain hp _ (mem_domain_of_kpair_mem hu))
    have hif := hfix i ((mem_cohenSupport p i).mpr ⟨n, b, hu⟩)
    simpa only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair,
      productPermutation_value hi hn, hif] using hu
  · intro hz
    obtain ⟨v, b, rfl⟩ := IsFunction.mem_eq_kpair hz
    obtain ⟨i, hi, n, hn, rfl⟩ :=
      mem_prod_iff.mp (countablePartialFunction_domain hp _ (mem_domain_of_kpair_mem hz))
    have he := countableCohenConditionAction_pair (π := π) hp hz
    rwa [hfix i ((mem_cohenSupport p i).mpr ⟨n, b, hz⟩)] at he

theorem countableCohen_transposition_compatible {I J p i j : V}
    (hp : p ∈ countableCohenConditions I J)
    (hi : i ∈ I) (hj : j ∈ I) (hfresh : j ∉ cohenSupport p) :
    ForcingCompatible (countableCohenConditions I J) (countableCohenOrder I J) p
      (countableCohenConditionAction I J (internalTransposition I i j) p) := by
  have hπ := internalTransposition_permutation hi hj
  have hq := countableCohenConditionAction_condition (J := J) hπ hp
  have : IsFunction p := countableCohenCondition_function hp
  apply (countablePartialFunctions_compatible_iff hp hq).mpr
  intro x y z hxy hxz
  obtain ⟨k, hk, n, hn, rfl⟩ :=
    mem_prod_iff.mp (countablePartialFunction_domain hp _ (mem_domain_of_kpair_mem hxy))
  obtain ⟨l, hlz, hkl⟩ := (countableCohenConditionAction_pair_iff hp).mp hxz
  have hl : l ∈ I :=
    (kpair_mem_iff.mp (countablePartialFunction_domain hp _ (mem_domain_of_kpair_mem hlz))).1
  have hlj : l ≠ j := fun he ↦ hfresh (he ▸ (mem_cohenSupport p l).mpr ⟨n, z, hlz⟩)
  have hkj : k ≠ j := fun he ↦ hfresh (he ▸ (mem_cohenSupport p k).mpr ⟨n, y, hxy⟩)
  have hli : l ≠ i := by
    intro he
    rw [he, internalTransposition_left hi] at hkl
    exact hkj hkl
  rw [internalTransposition_fixed hl hli hlj] at hkl
  subst k
  exact IsFunction.unique hxy hlz

theorem countableCohen_transposition_fix {I J p i j : V} (hp : p ∈ countableCohenConditions I J)
    (hi : i ∉ cohenSupport p) (hj : j ∉ cohenSupport p) :
    (countableCohenPermutation I J (internalTransposition I i j)) ‘ p = p := by
  rw [countableCohenPermutation_value hp]
  apply countableCohenConditionAction_fix hp
  intro k hk
  exact internalTransposition_fixed (countableCohenSupport_subset hp k hk)
    (fun he ↦ hi (he ▸ hk)) (fun he ↦ hj (he ▸ hk))

end ZFVP
