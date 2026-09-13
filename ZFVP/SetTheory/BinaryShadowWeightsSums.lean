import ZFVP.SetTheory.BinaryShadowWeights
import ZFVP.SetTheory.RationalPartialSums

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem binaryShadow_succ_cardEQ {F M : V} (hd : ∀ s ∈ F, domain s ⊆ M) :
    shadow F (succ M) ≋ (shadow F M ×ˢ ((2 : ℕ) : V)) := by
  refine ⟨shadow_succ_cardLE hd, ?_⟩
  refine cardLE_of_injective_map
    (fun z ↦ insert ⟨M, kpair.π₂ z⟩ₖ (kpair.π₁ z)) (by definability) ?_ ?_
  · intro z hz
    obtain ⟨t, ht, i, hi, rfl⟩ := mem_prod_iff.mp hz
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    obtain ⟨ht, s, hs, hst⟩ := (mem_shadow_iff _ _ _).mp ht
    exact (mem_shadow_iff _ _ _).mpr ⟨function_append_mem ht hi, s, hs,
      fun p hp ↦ mem_insert.mpr (Or.inr (hst p hp))⟩
  · intro z hz w hw he
    obtain ⟨t, ht, i, hi, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨u, hu, j, hj, rfl⟩ := mem_prod_iff.mp hw
    have ht := ((mem_shadow_iff _ _ _).mp ht).1
    have hu := ((mem_shadow_iff _ _ _).mp hu).1
    have : IsFunction t := IsFunction.of_mem ht
    have : IsFunction u := IsFunction.of_mem hu
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at he
    have hrestrict := congrArg (fun f ↦ f ↾ M) he
    rw [restrict_insert_kpair_eq_restrict_of_not_mem (mem_irrefl M),
      restrict_insert_kpair_eq_restrict_of_not_mem (mem_irrefl M)] at hrestrict
    have hte : t ↾ M = t := by rw [← domain_eq_of_mem_function ht]; exact IsFunction.restrict_eq_self t _ (subset_refl _)
    have hue : u ↾ M = u := by rw [← domain_eq_of_mem_function hu]; exact IsFunction.restrict_eq_self u _ (subset_refl _)
    rw [hte, hue] at hrestrict
    have hv := congrArg (fun f ↦ f ‘ M) he
    rw [value_insert_kpair ht hi, value_insert_kpair hu hj] at hv
    rw [hrestrict, hv]

theorem binaryShadowWeight_succ {F M : V} (hM : M ∈ (ω : V))
    (hd : ∀ s ∈ F, domain s ⊆ M) :
    binaryShadowWeight F (succ M) = binaryShadowWeight F M := by
  obtain ⟨hk, he⟩ := binaryFiniteCard_spec (shadow_finite (F := F) hM)
  have hs := binaryShadow_succ_cardEQ hd
  have hcard : binaryFiniteCard (shadow F (succ M)) =
      naturalMul (binaryFiniteCard (shadow F M)) 2 := by
    apply binaryFiniteCard_eq (naturalMul_natural hk (by simp))
    exact (binaryNatural_double_cardEQ hk).trans
      ((show (binaryFiniteCard (shadow F M) ×ˢ ((2 : ℕ) : V)) ≋
          (shadow F M ×ˢ ((2 : ℕ) : V)) from
        ⟨prod_cardLE_prod he.le (CardLE.refl _), prod_cardLE_prod he.ge (CardLE.refl _)⟩).trans hs.symm)
  let k : InternalNatural V := ⟨binaryFiniteCard (shadow F M), hk⟩
  let n : InternalNatural V := ⟨M, hM⟩
  unfold binaryShadowWeight
  rw [hcard]
  have hsucc : (n + 1).val = succ M := ordinalAdd_one_natural hM
  have hq : InternalRational.ofNatural (k * 2) * InternalRational.dyadic (n + 1) =
      InternalRational.ofNatural k * InternalRational.dyadic n := by
    rw [InternalRational.ofNatural_mul, show InternalRational.ofNatural (2 : InternalNatural V) = (2 : InternalRational V) from rfl, InternalRational.dyadic_succ]
    ring
  have hv := congrArg Subtype.val hq
  change rationalMul (rationalNatural (naturalMul k.val (2 : InternalNatural V).val)) (dyadicUnit (n + 1).val) = rationalMul (rationalNatural k.val) (dyadicUnit n.val) at hv
  rw [hsucc] at hv
  exact hv

theorem binaryShadowWeight_stable {F M N : V} (hM : M ∈ (ω : V)) (hN : N ∈ (ω : V))
    (hd : ∀ s ∈ F, domain s ⊆ M) (hMN : M ⊆ N) :
    binaryShadowWeight F N = binaryShadowWeight F M := by
  apply natural_induction_from hM (fun N ↦ binaryShadowWeight F N = binaryShadowWeight F M)
    (by definability) rfl ?_ N hN hMN
  intro N hN hMN ih
  rw [binaryShadowWeight_succ hN (fun s hs x hx ↦ hMN x (hd s hs x hx)), ih]

/-- The rational bound holds at any level bounding the family, including a specified level. -/
theorem binaryShadowWeight_smallMeasure_at {F M m : V} (hM : M ∈ (ω : V))
    (hm : m ∈ (ω : V)) (hd : ∀ s ∈ F, domain s ⊆ M) (h : SmallMeasure F m) :
    ¬InternalRationalLT (dyadicUnit m) (binaryShadowWeight F M) := by
  obtain ⟨N, hN, hdN, hc⟩ := binaryShadowWeight_smallMeasure hm h
  let a : InternalNatural V := ⟨M, hM⟩
  let b : InternalNatural V := ⟨N, hN⟩
  have h := hc (max a b).val (max a b).property (show N ⊆ (max a b).val from le_max_right a b)
  rwa [binaryShadowWeight_stable hM (max a b).property hd
    (show M ⊆ (max a b).val from le_max_left a b)] at h

noncomputable def binaryConstantWeights (M : V) : V := (ω : V) ×ˢ {dyadicUnit M}

instance binaryConstantWeights_definable : ℒₛₑₜ-function₁[V] binaryConstantWeights := by
  unfold binaryConstantWeights
  definability

theorem binaryConstantWeights_value (M : V) {n : V} (hn : n ∈ (ω : V)) :
    (binaryConstantWeights M) ‘ n = dyadicUnit M := by
  have he : binaryConstantWeights M = definableGraph (ω : V) (fun _ ↦ dyadicUnit M) (by definability) := by
    apply mem_ext
    intro p
    simp [binaryConstantWeights, mem_prod_iff, mem_definableGraph_iff]
  rw [he]
  exact value_eq_of_kpair_mem ((pair_mem_definableGraph_iff _ _ _ _ _).mpr ⟨hn, rfl⟩)

theorem binaryConstantWeights_sum {M n : V} (hM : M ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    rationalPartialSum (binaryConstantWeights M) n = rationalMul (rationalNatural n) (dyadicUnit M) := by
  apply naturalNumber_induction
    (fun n ↦ rationalPartialSum (binaryConstantWeights M) n = rationalMul (rationalNatural n) (dyadicUnit M))
    (by definability) ?_ ?_ n hn
  · simp only [rationalPartialSum_zero, rationalNatural_zero]
    exact congrArg Subtype.val (show (0 : InternalRational V) = 0 * (⟨dyadicUnit M, dyadicUnit_mem hM⟩ : InternalRational V) from (zero_mul _).symm)
  · intro n hn ih
    rw [rationalPartialSum_succ _ hn, binaryConstantWeights_value _ hn, ih]
    let k : InternalNatural V := ⟨n, hn⟩
    let d : InternalRational V := ⟨dyadicUnit M, dyadicUnit_mem hM⟩
    have he : InternalRational.ofNatural k * d + d = InternalRational.ofNatural (k + 1) * d := by
      rw [InternalRational.ofNatural_add, InternalRational.ofNatural_one]
      ring
    have hs : (k + 1).val = succ n := ordinalAdd_one_natural hn
    have hv := congrArg Subtype.val he
    change rationalAdd (rationalMul (rationalNatural k.val) d.val) d.val = rationalMul (rationalNatural (k + 1).val) d.val at hv
    rw [hs] at hv
    exact hv

/-- A finite shadow has an actual rational sum with the expected dyadic bound. -/
theorem binaryShadow_constant_sum {F M m : V} (hM : M ∈ (ω : V))
    (hm : m ∈ (ω : V)) (hd : ∀ s ∈ F, domain s ⊆ M) (h : SmallMeasure F m) :
    ¬InternalRationalLT (dyadicUnit m)
      (rationalPartialSum (binaryConstantWeights M) (binaryFiniteCard (shadow F M))) := by
  rw [binaryConstantWeights_sum hM (binaryFiniteCard_spec (shadow_finite hM)).1]
  exact binaryShadowWeight_smallMeasure_at hM hm hd h

end ZFVP
