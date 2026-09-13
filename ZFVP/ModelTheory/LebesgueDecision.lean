import ZFVP.SetTheory.LebesgueEnvelope
import ZFVP.ModelTheory.RandomName
import ZFVP.ModelTheory.PerfectSetDecision

/-! Lebesgue measurability of the sets of reals of the Levy extension definable from ground
parameters. The random reals of `V[G]` decide the formula through the ground decision set of the
random name; the union of the bodies of the (countably many) checked decision trees agrees with the
set up to the null set of non-random reals, and the measurable envelope of that union together with
the non-random reals witnesses measurability. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The union of two null sets is null. -/
theorem isNull_union (hAC : InternalChoice V) {A B : V} (hA : IsNull A) (hB : IsNull B) :
    IsNull (A ∪ B) := by
  let C : V := insert ⟨∅, A⟩ₖ (((ω : V) \ ({∅} : V)) ×ˢ ({B} : V))
  have hmemC : ∀ p, p ∈ C ↔ p = ⟨∅, A⟩ₖ ∨ ∃ n ∈ (ω : V), n ≠ ∅ ∧ p = ⟨n, B⟩ₖ := by
    intro p
    show p ∈ insert _ _ ↔ _
    rw [mem_insert]
    apply or_congr_right
    constructor
    · intro hp
      obtain ⟨n, hn, b, hb, rfl⟩ := mem_prod_iff.mp hp
      obtain ⟨hn, hn0⟩ := mem_sdiff_iff.mp hn
      rw [mem_singleton_iff] at hb hn0
      exact ⟨n, hn, hn0, by rw [hb]⟩
    · rintro ⟨n, hn, hn0, rfl⟩
      exact kpair_mem_iff.mpr ⟨mem_sdiff_iff.mpr ⟨hn, fun h ↦ hn0 (mem_singleton_iff.mp h)⟩,
        mem_singleton_iff.mpr rfl⟩
  have hC : C ∈ (insert A ({B} : V)) ^ (ω : V) := by
    rw [mem_function_iff]
    constructor
    · intro p hp
      rcases (hmemC p).mp hp with rfl | ⟨n, hn, -, rfl⟩
      · exact kpair_mem_iff.mpr ⟨zero_mem_ω, mem_insert.mpr (Or.inl rfl)⟩
      · exact kpair_mem_iff.mpr ⟨hn, mem_insert.mpr (Or.inr (mem_singleton_iff.mpr rfl))⟩
    · intro n hn
      by_cases hn0 : n = ∅
      · subst hn0
        refine ⟨A, (hmemC _).mpr (Or.inl rfl), fun y hy ↦ ?_⟩
        rcases (hmemC _).mp hy with h | ⟨k, -, hk0, h⟩
        · exact (kpair_inj h).2
        · exact (hk0 (kpair_inj h).1.symm).elim
      · refine ⟨B, (hmemC _).mpr (Or.inr ⟨n, hn, hn0, rfl⟩), fun y hy ↦ ?_⟩
        rcases (hmemC _).mp hy with h | ⟨k, -, -, h⟩
        · exact (hn0 (kpair_inj h).1).elim
        · exact (kpair_inj h).2
  have : IsFunction C := IsFunction.of_mem hC
  have hdom : domain C = (ω : V) := domain_eq_of_mem_function hC
  have hval : ∀ n ∈ (ω : V), IsNull (C ‘ n) := by
    intro n hn
    by_cases hn0 : n = ∅
    · subst hn0
      rw [value_eq_of_kpair_mem ((hmemC _).mpr (Or.inl rfl))]
      exact hA
    · rw [value_eq_of_kpair_mem ((hmemC _).mpr (Or.inr ⟨n, hn, hn0, rfl⟩))]
      exact hB
  refine isNull_mono (isNull_sUnion_range hAC hdom hval) ?_
  intro x hx
  rw [mem_sUnion_iff]
  rcases mem_union_iff.mp hx with hxA | hxB
  · exact ⟨A, mem_range_iff.mpr ⟨∅, (hmemC _).mpr (Or.inl rfl)⟩, hxA⟩
  · refine ⟨B, mem_range_iff.mpr ⟨succ ∅, (hmemC _).mpr (Or.inr ⟨succ ∅, ω_succ_closed zero_mem_ω,
      succ_empty_ne_empty, rfl⟩)⟩, hxB⟩

theorem isTree_empty : IsTree (∅ : V) :=
  ⟨fun _ hs ↦ (not_mem_empty hs).elim, fun _ hs ↦ (not_mem_empty hs).elim⟩

theorem treeBody_empty_eq : treeBody (∅ : V) = ∅ := by
  apply mem_ext
  intro x
  rw [mem_treeBody_iff]
  constructor
  · rintro ⟨-, h⟩
    exact (not_mem_empty (h ∅ zero_mem_ω)).elim
  · intro h
    exact (not_mem_empty h).elim

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

theorem nonRandom_subset : nonRandom hG ⊆ cantorSpace (levyContext κ hG).Model :=
  fun x hx ↦ ((mem_nonRandom_iff hG x).mp hx).1

include hAC hU hc hω hκ in
/-- Every set of reals of the Levy extension definable from ground parameters is Lebesgue
measurable. -/
theorem lebesgueMeasurable_of_ground_definable {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (a : Fin n → V) {X : (levyContext κ hG).Model}
    (hX : ∀ x, x ∈ X ↔ x ∈ cantorSpace (levyContext κ hG).Model ∧
      φ.Evalb (x :> fun i ↦ (levyContext κ hG).check (a i))) :
    IsLebesgueMeasurable X := by
  let W := levyContext κ hG
  have hACW : InternalChoice W.Model := W.internalChoice_of_ground hAC
  let S₁ := filterDecisionSet κ (randomConditions V) (inclusionOrder (randomConditions V))
    (binarySequences V) (randomName V) φ a
  have hS₁ : S₁ ⊆ randomConditions V := filterDecisionSet_subset _ _ _ _ _ _ _
  let T₀ : V := insert ∅ S₁
  have hT₀ : T₀ ⊆ ℘ (binarySequences V) := by
    intro T hT
    rcases mem_insert.mp hT with rfl | hT
    · exact mem_power_iff.mpr (fun s hs ↦ (not_mem_empty hs).elim)
    · exact mem_power_iff.mpr ((mem_randomConditions_iff T).mp (hS₁ T hT)).1.1
  -- the checked decision trees form a countable set of trees in `V[G]`
  obtain ⟨ν, hν, hpow⟩ := power_small_of_measurable hAC hU hc hω (binarySequences_countable hAC)
  have hT₀c : W.check T₀ ≤# (ω : W.Model) :=
    internallyCountable_of_cardLE (levy_check_countable hG hν)
      (W.checkEmbedding.map_cardLE ((cardLE_of_subset hT₀).trans hpow))
  have h0 : W.check ∅ ∈ W.check T₀ := (W.check_mem_iff _ _).mpr (mem_insert.mpr (Or.inl rfl))
  obtain ⟨E, hE, hErange⟩ := exists_surjection_of_cardLE hT₀c h0
  have hEfun : IsFunction E := IsFunction.of_mem hE
  have hEdom : domain E = (ω : W.Model) := domain_eq_of_mem_function hE
  have hEval : ∀ m ∈ (ω : W.Model), ∃ T ∈ T₀, E ‘ m = W.check T := by
    intro m hm
    obtain ⟨T, hT, hTe⟩ := (W.mem_check_iff _ _).mp (function_value_mem hE hm)
    exact ⟨T, hT, hTe⟩
  have hsurj : ∀ T ∈ T₀, ∃ m ∈ (ω : W.Model), E ‘ m = W.check T := by
    intro T hT
    have : W.check T ∈ range E := by rw [hErange]; exact (W.check_mem_iff _ _).mpr hT
    obtain ⟨m, hm⟩ := mem_range_iff.mp this
    refine ⟨m, ?_, value_eq_of_kpair_mem hm⟩
    rw [← hEdom]
    exact mem_domain_of_kpair_mem hm
  have hE' : E ∈ (℘ (binarySequences W.Model)) ^ (ω : W.Model) := by
    have hsub : W.check T₀ ⊆ ℘ (binarySequences W.Model) := by
      intro T' hT'
      obtain ⟨T, hT, rfl⟩ := (W.mem_check_iff _ _).mp hT'
      rw [← W.check_binarySequences]
      exact mem_power_iff.mpr ((W.checkEmbedding.subset_iff _ _).mpr (mem_power_iff.mp (hT₀ T hT)))
    obtain ⟨h1, h2⟩ := mem_function_iff.mp hE
    exact mem_function_iff.mpr ⟨fun p hp ↦ prod_subset_prod_of_subset (fun x hx ↦ hx) hsub p (h1 p hp), h2⟩
  have hEtree : ∀ m ∈ (ω : W.Model), IsTree (E ‘ m) := by
    intro m hm
    obtain ⟨T, hT, hTe⟩ := hEval m hm
    rw [hTe]
    rcases mem_insert.mp hT with rfl | hT
    · rw [W.check_empty]; exact isTree_empty
    · exact W.check_isTree ((mem_randomConditions_iff T).mp (hS₁ T hT)).1
  have hNnull : IsNull (nonRandom hG) := nonRandom_null hAC hU hc hω hG
  obtain ⟨g, hg, hbod, hN, hnull⟩ :=
    exists_measurable_envelope hACW hE' hEtree (nonRandom_subset hG) hNnull
  -- the random reals of `X` lie in the bodies, the random reals of the bodies lie in `X`
  have hdec : ∀ x, IsRandomOver hG x → (x ∈ X ↔ ∃ T ∈ S₁, x ∈ treeBody (W.check T)) := by
    intro x hx
    rw [hX x, random_decision hAC hU hc hω hκ hG hx φ a]
    constructor
    · rintro ⟨-, T, hTF, hTS⟩
      exact ⟨T, hTS, ((check_mem_randomFilter_iff hG x T).mp hTF).2⟩
    · rintro ⟨T, hTS, hxT⟩
      exact ⟨hx.1, T, (check_mem_randomFilter_iff hG x T).mpr
        ⟨(mem_randomConditions_iff T).mp (hS₁ T hTS), hxT⟩, hTS⟩
  refine ⟨g, hg, ?_, ?_⟩
  · intro x hx
    by_cases hxr : x ∈ nonRandom hG
    · exact hN x hxr
    have hrand : IsRandomOver hG x := ⟨((hX x).mp hx).1, hxr⟩
    obtain ⟨T, hTS, hxT⟩ := (hdec x hrand).mp hx
    obtain ⟨m, hm, hme⟩ := hsurj T (mem_insert.mpr (Or.inr hTS))
    refine hbod x ((mem_bodiesUnion_iff E x).mpr ⟨hrand.1, m, hm, ?_⟩)
    rw [hme]
    exact hxT
  · refine isNull_mono (isNull_union hACW hnull hNnull) ?_
    intro x hx
    obtain ⟨hxg, hxX⟩ := mem_sdiff_iff.mp hx
    rw [mem_union_iff]
    by_cases hxr : x ∈ nonRandom hG
    · exact Or.inr hxr
    left
    have hrand : IsRandomOver hG x := ⟨((mem_gDelta_iff g x).mp hxg).1, hxr⟩
    refine mem_sdiff_iff.mpr ⟨hxg, fun hxb ↦ hxX ?_⟩
    obtain ⟨-, m, hm, hxT⟩ := (mem_bodiesUnion_iff E x).mp hxb
    obtain ⟨T, hT, hTe⟩ := hEval m hm
    rw [hTe] at hxT
    rcases mem_insert.mp hT with rfl | hTS
    · rw [W.check_empty, treeBody_empty_eq] at hxT
      exact (not_mem_empty hxT).elim
    · exact (hdec x hrand).mpr ⟨T, hTS, hxT⟩

end

end ZFVP
