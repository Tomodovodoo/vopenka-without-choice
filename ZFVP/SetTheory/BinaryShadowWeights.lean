import ZFVP.SetTheory.LevelCounting
import ZFVP.SetTheory.NaturalAdditionDefinable
import ZFVP.SetTheory.DyadicRationals

/-! Rational cardinal weights for finite binary shadows, in arbitrary internal ZF models. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The unique internal natural cardinal, with zero as default for infinite sets. -/
noncomputable def binaryFiniteCard (A : V) : V :=
  ⋃ˢ {n ∈ (ω : V) ; n ≋ A}

theorem mem_binaryFiniteCard_iff (A x : V) :
    x ∈ binaryFiniteCard A ↔ ∃ n ∈ (ω : V), n ≋ A ∧ x ∈ n := by
  simp only [binaryFiniteCard, mem_sUnion_iff, mem_sep_iff]
  constructor
  · rintro ⟨n, ⟨hn, he⟩, hx⟩
    exact ⟨n, hn, he, hx⟩
  · rintro ⟨n, hn, he, hx⟩
    exact ⟨n, ⟨hn, he⟩, hx⟩

def binaryFiniteCardFormula : SetTheorySemisentence 2 :=
  f“c A. ∀ x, x ∈ c ↔ ∃ n ∈ !isω, !CardEQ.dfn n A ∧ x ∈ n”

instance binaryFiniteCardFormula_defined :
    ℒₛₑₜ-function₁[V] binaryFiniteCard via binaryFiniteCardFormula :=
  ⟨fun v ↦ by
    simp [binaryFiniteCardFormula, mem_ext_iff (y := binaryFiniteCard _), mem_binaryFiniteCard_iff]⟩

instance binaryFiniteCard_definable : ℒₛₑₜ-function₁[V] binaryFiniteCard :=
  binaryFiniteCardFormula_defined.to_definable

theorem binaryFiniteCard_eq {A n : V} (hn : n ∈ (ω : V)) (he : n ≋ A) :
    binaryFiniteCard A = n := by
  have hs : {k ∈ (ω : V) ; k ≋ A} = ({n} : V) := by
    apply mem_ext
    intro k
    simp only [mem_sep_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hk, hkA⟩
      exact natural_eq_of_cardEQ hk hn (hkA.trans he.symm)
    · rintro rfl
      exact ⟨hn, he⟩
  simp [binaryFiniteCard, hs]

theorem binaryFiniteCard_spec {A : V} (hA : IsInternallyFinite A) :
    binaryFiniteCard A ∈ (ω : V) ∧ binaryFiniteCard A ≋ A := by
  obtain ⟨n, hn, hAn⟩ := hA
  rw [binaryFiniteCard_eq hn hAn.symm]
  exact ⟨hn, hAn.symm⟩

theorem binaryFiniteCard_mono {A B : V} (hA : IsInternallyFinite A)
    (hB : IsInternallyFinite B) (h : A ≤# B) : binaryFiniteCard A ⊆ binaryFiniteCard B := by
  obtain ⟨ha, hea⟩ := binaryFiniteCard_spec hA
  obtain ⟨hb, heb⟩ := binaryFiniteCard_spec hB
  exact natural_subset_of_cardLE ha hb (hea.le.trans (h.trans heb.ge))

theorem binaryNatural_double_cardEQ {n : V} (hn : n ∈ (ω : V)) :
    naturalMul n 2 ≋ (n ×ˢ ((2 : ℕ) : V)) := by
  change naturalMul n (succ 1) ≋ (n ×ˢ ((2 : ℕ) : V))
  rw [naturalMul_succ _ (by simp), naturalMul_one hn]
  exact (ordinalAdd_natural_cardEQ hn hn).trans
    (by rw [disjointUnion_self_eq])

theorem binaryPower_zero_cardEQ : (((2 : ℕ) : V) ^ (0 : V)) ≋ ((1 : ℕ) : V) := by
  constructor
  · exact function_power_zero_cardLE ⟨0, by simp⟩
  · refine cardLE_of_injective_map (fun _ ↦ (∅ : V)) (by definability) ?_ ?_
    · intro x hx
      exact empty_mem_function_empty _
    · intro x hx y hy he
      have hx0 : x = (0 : V) := by change x ∈ succ (∅ : V) at hx; simpa only [mem_succ_iff, not_mem_empty, or_false, zero_def] using hx
      have hy0 : y = (0 : V) := by change y ∈ succ (∅ : V) at hy; simpa only [mem_succ_iff, not_mem_empty, or_false, zero_def] using hy
      exact hx0.trans hy0.symm

theorem binaryPower_cardEQ {n : V} (hn : n ∈ (ω : V)) :
    (((2 : ℕ) : V) ^ n) ≋ naturalPow ((2 : ℕ) : V) n := by
  apply naturalNumber_induction (fun n ↦ (((2 : ℕ) : V) ^ n) ≋ naturalPow ((2 : ℕ) : V) n)
    (by definability) ?_ ?_ n hn
  · rw [naturalPow_zero]
    exact binaryPower_zero_cardEQ
  · intro n hn ih
    rw [naturalPow_succ _ hn]
    exact (function_power_succ_cardEQ n).trans
      ((show ((((2 : ℕ) : V) ^ n) ×ˢ ((2 : ℕ) : V)) ≋ ((naturalPow ((2 : ℕ) : V) n) ×ˢ ((2 : ℕ) : V)) from
        ⟨prod_cardLE_prod ih.le (CardLE.refl _), prod_cardLE_prod ih.ge (CardLE.refl _)⟩).trans
          (binaryNatural_double_cardEQ (naturalPow_natural (by simp) hn)).symm)

theorem binaryProd_power_zero_cardEQ (A : V) : (A ×ˢ (((2 : ℕ) : V) ^ (0 : V))) ≋ A := by
  have hz : ((2 : ℕ) : V) ^ (0 : V) = ({∅} : V) := by ext x; simp [mem_function_iff, zero_def]
  rw [hz]
  constructor
  · refine cardLE_of_injective_map kpair.π₁ (by definability) ?_ ?_
    · intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
      simpa using ha
    · intro z hz w hw he
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
      obtain ⟨c, hc, d, hd, rfl⟩ := mem_prod_iff.mp hw
      have hb0 := mem_singleton_iff.mp hb
      have hd0 := mem_singleton_iff.mp hd
      simp only [kpair.π₁_kpair] at he
      rw [he, hb0, hd0]
  · refine cardLE_of_injective_map (fun a ↦ ⟨a, ∅⟩ₖ) (by definability) ?_ ?_
    · intro a ha
      exact kpair_mem_iff.mpr ⟨ha, by simp⟩
    · intro a ha b hb he
      exact (kpair_inj he).1

theorem binaryProd_power_cardEQ {A k m : V} (hk : k ∈ (ω : V)) (hA : A ≋ k)
    (hm : m ∈ (ω : V)) : (A ×ˢ (((2 : ℕ) : V) ^ m)) ≋ naturalMul k (naturalPow ((2 : ℕ) : V) m) := by
  apply naturalNumber_induction
    (fun m ↦ (A ×ˢ (((2 : ℕ) : V) ^ m)) ≋ naturalMul k (naturalPow ((2 : ℕ) : V) m))
    (by definability) ?_ ?_ m hm
  · rw [naturalPow_zero, naturalMul_one hk]
    exact (binaryProd_power_zero_cardEQ A).trans hA
  · intro m hm ih
    have hp := naturalPow_natural (V := V) (by simp : ((2 : ℕ) : V) ∈ ω) hm
    rw [naturalPow_succ _ hm, ← naturalMul_assoc hk hp (by simp)]
    exact (show (A ×ˢ (((2 : ℕ) : V) ^ succ m)) ≋ (A ×ˢ ((((2 : ℕ) : V) ^ m) ×ˢ ((2 : ℕ) : V))) from
      ⟨prod_cardLE_prod (CardLE.refl _) (function_power_succ_cardEQ m).le,
        prod_cardLE_prod (CardLE.refl _) (function_power_succ_cardEQ m).ge⟩).trans
      ((show (A ×ˢ ((((2 : ℕ) : V) ^ m) ×ˢ ((2 : ℕ) : V))) ≋ ((A ×ˢ (((2 : ℕ) : V) ^ m)) ×ˢ ((2 : ℕ) : V)) from
        ⟨prod_assoc_cardLE' _ _ _, prod_assoc_cardLE _ _ _⟩).trans
        ((show ((A ×ˢ (((2 : ℕ) : V) ^ m)) ×ˢ ((2 : ℕ) : V)) ≋
            (naturalMul k (naturalPow ((2 : ℕ) : V) m) ×ˢ ((2 : ℕ) : V)) from
          ⟨prod_cardLE_prod ih.le (CardLE.refl _), prod_cardLE_prod ih.ge (CardLE.refl _)⟩).trans
          (binaryNatural_double_cardEQ (naturalMul_natural hk hp)).symm))

noncomputable def binaryShadowWeight (F M : V) : V :=
  rationalMul (rationalNatural (binaryFiniteCard (shadow F M))) (dyadicUnit M)

instance binaryShadowWeight_definable : ℒₛₑₜ-function₂[V] binaryShadowWeight := by
  unfold binaryShadowWeight
  definability

theorem binaryShadowWeight_mem (F : V) {M : V} (hM : M ∈ (ω : V)) :
    binaryShadowWeight F M ∈ internalRationals V :=
  rationalMul_mem (rationalNatural_mem (binaryFiniteCard_spec (shadow_finite hM)).1)
    (dyadicUnit_mem hM)

/-- The original cardinal bound implies the actual rational shadow bound. -/
theorem binaryShadowWeight_le_of_cardLE {F M m : V} (hM : M ∈ (ω : V))
    (hm : m ∈ (ω : V))
    (h : shadow F M ×ˢ (((2 : ℕ) : V) ^ m) ≤# (((2 : ℕ) : V) ^ M)) :
    ¬InternalRationalLT (dyadicUnit m) (binaryShadowWeight F M) := by
  obtain ⟨hk, he⟩ := binaryFiniteCard_spec (shadow_finite (F := F) hM)
  have hc := natural_subset_of_cardLE
    (naturalMul_natural hk (naturalPow_natural (by simp) hm))
    (naturalPow_natural (by simp) hM)
    ((binaryProd_power_cardEQ hk he.symm hm).ge.trans (h.trans (binaryPower_cardEQ hM).le))
  let k : InternalNatural V := ⟨binaryFiniteCard (shadow F M), hk⟩
  let N : InternalNatural V := ⟨M, hM⟩
  let n : InternalNatural V := ⟨m, hm⟩
  have hc' : k * n.powerTwo ≤ N.powerTwo := hc
  have hq := (InternalRational.ofNatural_le_iff _ _).mpr hc'
  rw [InternalRational.ofNatural_mul] at hq
  have hp : (0 : InternalRational V) < InternalRational.ofNatural n.powerTwo :=
    (InternalRational.ofNatural_pos_iff _).mpr n.powerTwo_pos
  have hP : (0 : InternalRational V) < InternalRational.ofNatural N.powerTwo :=
    (InternalRational.ofNatural_pos_iff _).mpr N.powerTwo_pos
  change InternalRational.ofNatural k * InternalRational.dyadic N ≤ InternalRational.dyadic n
  unfold InternalRational.dyadic
  rw [← div_eq_mul_inv, div_le_iff₀ hP, inv_mul_eq_div, le_div_iff₀ hp]
  exact hq

/-- Every sufficiently high level obeys the same rational bound. -/
theorem binaryShadowWeight_smallMeasure {F m : V} (hm : m ∈ (ω : V))
    (h : SmallMeasure F m) :
    ∃ M ∈ (ω : V), (∀ s ∈ F, domain s ⊆ M) ∧
      ∀ N ∈ (ω : V), M ⊆ N →
        ¬InternalRationalLT (dyadicUnit m) (binaryShadowWeight F N) := by
  obtain ⟨M, hM, hd, hc⟩ := smallMeasure_levels h
  exact ⟨M, hM, hd, fun N hN hMN ↦ binaryShadowWeight_le_of_cardLE hN hm (hc N hN hMN)⟩

end ZFVP



