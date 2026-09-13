import ZFVP.ModelTheory.GroundRealsHOD
import ZFVP.ModelTheory.SolovayHODBridge
import ZFVP.ModelTheory.SolovayModel
import ZFVP.SetTheory.NaturalPairing
import ZFVP.SetTheory.NaturalPredecessor

/-! The coding bridge between the two descriptions of the reals of a forcing extension: the HOD
track allows as parameters the subsets of `ω̌`, while the symmetric track produces subsets of
`(ω × ω)ˇ`. The ground model has a definable pairing code on `ω`, so a subset of `(ω × ω)ˇ` and
its image under the checked pairing code define each other from checks alone. Hence a subset of
`(ω × ω)ˇ` is definable from ground sets, reals and ordinals. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The pairing code on `ω × ω` as a set of the ground model -/

/-- The Cantor pairing code read off a Kuratowski pair. -/
noncomputable def omegaPairFun (p : V) : V := naturalPairCode (kpair.π₁ p) (kpair.π₂ p)

instance omegaPairFun_definable : ℒₛₑₜ-function₁[V] omegaPairFun := by
  unfold omegaPairFun
  definability

theorem omegaPairFun_kpair (a b : V) : omegaPairFun ⟨a, b⟩ₖ = naturalPairCode a b := by
  simp [omegaPairFun]

/-- The graph of the pairing code on `ω × ω`, a set of the ground model. -/
noncomputable def omegaPairGraph (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  definableGraph ((ω : V) ×ˢ (ω : V)) omegaPairFun omegaPairFun_definable

theorem kpair_mem_omegaPairGraph_iff (a b n : V) :
    (⟨⟨a, b⟩ₖ, n⟩ₖ : V) ∈ omegaPairGraph V ↔
      a ∈ (ω : V) ∧ b ∈ (ω : V) ∧ n = naturalPairCode a b := by
  rw [omegaPairGraph, pair_mem_definableGraph_iff, omegaPairFun_kpair]
  constructor
  · rintro ⟨hp, hn⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := mem_prod_iff.mp hp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hxy.symm
    exact ⟨hx, hy, hn⟩
  · rintro ⟨ha, hb, hn⟩
    exact ⟨mem_prod_iff.mpr ⟨a, ha, b, hb, rfl⟩, hn⟩

theorem mem_omegaPairGraph_iff (p : V) :
    p ∈ omegaPairGraph V ↔ ∃ a ∈ (ω : V), ∃ b ∈ (ω : V), p = ⟨⟨a, b⟩ₖ, naturalPairCode a b⟩ₖ := by
  rw [omegaPairGraph, mem_definableGraph_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hq
    exact ⟨a, ha, b, hb, by rw [omegaPairFun_kpair]⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨⟨a, b⟩ₖ, mem_prod_iff.mpr ⟨a, ha, b, hb, rfl⟩, by rw [omegaPairFun_kpair]⟩

/-- The pairing code is onto `ω`: every natural number is `naturalPairCode a b` for some pair of
natural numbers. -/
theorem exists_naturalPairCode {n : V} (hn : n ∈ (ω : V)) :
    ∃ a ∈ (ω : V), ∃ b ∈ (ω : V), naturalPairCode a b = n := by
  apply naturalNumber_induction
    (fun n ↦ ∃ a ∈ (ω : V), ∃ b ∈ (ω : V), naturalPairCode a b = n) (by definability) ?_ ?_ n hn
  · refine ⟨0, by simp, 0, by simp, ?_⟩
    have h0 : ordinalAdd (0 : V) 0 = 0 := by
      rw [show (0 : V) = ∅ from rfl, ordinalAdd_zero]
    rw [naturalPairCode, h0, triangular_zero, h0]
  · rintro n hn ⟨a, ha, b, hb, rfl⟩
    have hoa : IsOrdinal a := IsOrdinal.of_mem ha
    rcases internalNatural_cases hb with rfl | ⟨c, hc, rfl⟩
    · refine ⟨0, by simp, succ a, ω_succ_closed ha, ?_⟩
      have hsa : succ a ∈ (ω : V) := ω_succ_closed ha
      have hta : IsOrdinal (triangular a) := IsOrdinal.of_mem (triangular_natural ha)
      have h1 : ordinalAdd (0 : V) (succ a) = succ a := ordinalAdd_zero_left_natural hsa
      have h2 : ordinalAdd a (0 : V) = a := by
        rw [show (0 : V) = ∅ from rfl, ordinalAdd_zero]
      rw [naturalPairCode, naturalPairCode, h1, h2, triangular_succ ha, ordinalAdd_succ,
        show (0 : V) = ∅ from rfl, ordinalAdd_zero]
    · refine ⟨succ a, ω_succ_closed ha, c, hc, ?_⟩
      have hoc : IsOrdinal c := IsOrdinal.of_mem hc
      have hac : IsOrdinal (ordinalAdd a c) := IsOrdinal.of_mem (ordinalAdd_natural ha hc)
      have ht : IsOrdinal (triangular (succ (ordinalAdd a c))) :=
        IsOrdinal.of_mem (triangular_natural (ω_succ_closed (ordinalAdd_natural ha hc)))
      rw [naturalPairCode, naturalPairCode, ordinalAdd_succ_left_natural ha hc, ordinalAdd_succ,
        ordinalAdd_succ]

/-! ### The image of a subset of `(ω × ω)ˇ` under the checked pairing code -/

/-- The image of `x ⊆ (ω × ω)ˇ` under the checked pairing code: a subset of `ω̌`, obtained by
separation over `ω̌` using the check of the ground graph of the pairing code and `x`. -/
noncomputable def omegaPairImage (A : ForcingContext V) (x : A.Model) : A.Model :=
  sep (A.check (ω : V))
    (fun n ↦ ∃ p ∈ x, (⟨p, n⟩ₖ : A.Model) ∈ A.check (omegaPairGraph V)) (by definability)

/-- The preimage of `x ⊆ ω̌` under the checked pairing code: a subset of `(ω × ω)ˇ`. -/
noncomputable def omegaPairPreimage (A : ForcingContext V) (x : A.Model) : A.Model :=
  sep (A.check ((ω : V) ×ˢ (ω : V)))
    (fun p ↦ ∃ n ∈ x, (⟨p, n⟩ₖ : A.Model) ∈ A.check (omegaPairGraph V)) (by definability)

variable {A : ForcingContext V}

theorem mem_omegaPairImage_iff' (x n : A.Model) :
    n ∈ omegaPairImage A x ↔
      n ∈ A.check (ω : V) ∧ ∃ p ∈ x, (⟨p, n⟩ₖ : A.Model) ∈ A.check (omegaPairGraph V) :=
  mem_sep_iff

theorem mem_omegaPairPreimage_iff' (x p : A.Model) :
    p ∈ omegaPairPreimage A x ↔
      p ∈ A.check ((ω : V) ×ˢ (ω : V)) ∧
        ∃ n ∈ x, (⟨p, n⟩ₖ : A.Model) ∈ A.check (omegaPairGraph V) :=
  mem_sep_iff

/-- The image is a subset of `ω̌`, whatever `x` is. -/
theorem omegaPairImage_subset (x : A.Model) : omegaPairImage A x ⊆ A.check (ω : V) :=
  sep_subset

/-- The preimage is a subset of `(ω × ω)ˇ`, whatever `x` is. -/
theorem omegaPairPreimage_subset (x : A.Model) :
    omegaPairPreimage A x ⊆ A.check ((ω : V) ×ˢ (ω : V)) :=
  sep_subset

/-- Checked pairs lie in the checked graph exactly when the ground pairs do. -/
theorem check_kpair_mem_check_omegaPairGraph_iff (a b n : V) :
    (⟨A.check ⟨a, b⟩ₖ, A.check n⟩ₖ : A.Model) ∈ A.check (omegaPairGraph V) ↔
      a ∈ (ω : V) ∧ b ∈ (ω : V) ∧ n = naturalPairCode a b := by
  have h : (⟨A.check ⟨a, b⟩ₖ, A.check n⟩ₖ : A.Model) = A.check ⟨⟨a, b⟩ₖ, n⟩ₖ :=
    (A.checkEmbedding.map_kpair _ _).symm
  rw [h, A.check_mem_iff, kpair_mem_omegaPairGraph_iff]

/-- The image of `x ⊆ (ω × ω)ˇ` contains the checked code of a pair exactly when the checked pair
belongs to `x`. -/
theorem mem_omegaPairImage_iff {x : A.Model} (hx : x ⊆ A.check ((ω : V) ×ˢ (ω : V)))
    {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    A.check (naturalPairCode a b) ∈ omegaPairImage A x ↔ A.check (⟨a, b⟩ₖ : V) ∈ x := by
  rw [mem_omegaPairImage_iff']
  constructor
  · rintro ⟨-, p, hp, hpn⟩
    obtain ⟨q, hq, rfl⟩ := (A.mem_check_iff _ _).mp (hx p hp)
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_prod_iff.mp hq
    obtain ⟨-, -, he⟩ := (check_kpair_mem_check_omegaPairGraph_iff u v _).mp hpn
    obtain ⟨rfl, rfl⟩ := naturalPairCode_injective ha hb hu hv he
    exact hp
  · intro hp
    refine ⟨(A.mem_check_iff _ _).mpr ⟨_, naturalPairCode_natural ha hb, rfl⟩, _, hp, ?_⟩
    exact (check_kpair_mem_check_omegaPairGraph_iff a b _).mpr ⟨ha, hb, rfl⟩

/-! ### Definability of subsets of `(ω × ω)ˇ` -/

/-- `b` is a member of the set coded by the real `r`: `b` lies in the checked `ω × ω` and its
pairing code, computed by the checked graph `g`, lies in `r`. -/
def omegaPairDecodeFormula : SetTheorySemisentence 4 :=
  f“b q g r. b ∈ q ∧ ∃ n ∈ r, !kpair.dfn b n ∈ g”

theorem eval_omegaPairDecodeFormula {M : Type*} [SetStructure M] [Nonempty M]
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (b q g r : M) :
    omegaPairDecodeFormula.Evalb ![b, q, g, r] ↔
      b ∈ q ∧ ∃ n ∈ r, (⟨b, n⟩ₖ : M) ∈ g := by
  simp [omegaPairDecodeFormula]

/-- A subset of the checked `ω × ω` is definable from ground sets, reals and ordinals: it is
defined by the checks of `ω × ω` and of the pairing graph together with the real
`omegaPairImage A x`. -/
theorem groundRealDefinable_of_subset_check_omega_prod (x : A.Model)
    (hx : x ⊆ A.check ((ω : V) ×ˢ (ω : V))) : A.IsGroundRealDefinable x := by
  refine ⟨3, omegaPairDecodeFormula,
    ![A.check ((ω : V) ×ˢ (ω : V)), A.check (omegaPairGraph V), omegaPairImage A x], ?_, ?_⟩
  · intro i
    match i with
    | 0 => exact Or.inl ⟨(ω : V) ×ˢ (ω : V), rfl⟩
    | 1 => exact Or.inl ⟨omegaPairGraph V, rfl⟩
    | 2 => exact Or.inr (Or.inl (omegaPairImage_subset x))
  · intro b
    rw [eval_omegaPairDecodeFormula]
    constructor
    · intro hb
      have hbq := hx b hb
      obtain ⟨q, hq, rfl⟩ := (A.mem_check_iff _ _).mp hbq
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_prod_iff.mp hq
      refine ⟨hbq, A.check (naturalPairCode u v), (mem_omegaPairImage_iff hx hu hv).mpr hb, ?_⟩
      exact (check_kpair_mem_check_omegaPairGraph_iff u v _).mpr ⟨hu, hv, rfl⟩
    · rintro ⟨hb, n, hn, hbn⟩
      obtain ⟨q, hq, rfl⟩ := (A.mem_check_iff _ _).mp hb
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_prod_iff.mp hq
      obtain ⟨m, hm, rfl⟩ := (A.mem_check_iff _ _).mp (omegaPairImage_subset x _ hn)
      obtain ⟨-, -, rfl⟩ := (check_kpair_mem_check_omegaPairGraph_iff u v m).mp hbn
      exact (mem_omegaPairImage_iff hx hu hv).mp hn

/-! ### Every real is the image of a subset of the checked `ω × ω` -/

/-- The preimage of a real is definable from ground sets, reals and ordinals. -/
theorem groundRealDefinable_omegaPairPreimage (x : A.Model) :
    A.IsGroundRealDefinable (omegaPairPreimage A x) :=
  groundRealDefinable_of_subset_check_omega_prod _ (omegaPairPreimage_subset x)

/-- A real is recovered from its preimage: the pairing code is onto `ω`, so the image of the
preimage of `x ⊆ ω̌` is `x` again. -/
theorem omegaPairImage_omegaPairPreimage {x : A.Model} (hx : x ⊆ A.check (ω : V)) :
    omegaPairImage A (omegaPairPreimage A x) = x := by
  apply mem_ext
  intro n
  rw [mem_omegaPairImage_iff']
  constructor
  · rintro ⟨hnω, p, hp, hpn⟩
    obtain ⟨hpq, m, hm, hpm⟩ := (mem_omegaPairPreimage_iff' x p).mp hp
    obtain ⟨q, hq, rfl⟩ := (A.mem_check_iff _ _).mp hpq
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_prod_iff.mp hq
    obtain ⟨n₀, hn₀, rfl⟩ := (A.mem_check_iff _ _).mp hnω
    obtain ⟨m₀, hm₀, rfl⟩ := (A.mem_check_iff _ _).mp (hx m hm)
    obtain ⟨-, -, rfl⟩ := (check_kpair_mem_check_omegaPairGraph_iff u v n₀).mp hpn
    obtain ⟨-, -, rfl⟩ := (check_kpair_mem_check_omegaPairGraph_iff u v m₀).mp hpm
    exact hm
  · intro hn
    obtain ⟨n₀, hn₀, rfl⟩ := (A.mem_check_iff _ _).mp (hx n hn)
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_naturalPairCode hn₀
    refine ⟨hx _ hn, A.check (⟨a, b⟩ₖ : V), ?_, ?_⟩
    · refine (mem_omegaPairPreimage_iff' x _).mpr
        ⟨(A.mem_check_iff _ _).mpr ⟨⟨a, b⟩ₖ, mem_prod_iff.mpr ⟨a, ha, b, hb, rfl⟩, rfl⟩,
          _, hn, (check_kpair_mem_check_omegaPairGraph_iff a b _).mpr ⟨ha, hb, rfl⟩⟩
    · exact (check_kpair_mem_check_omegaPairGraph_iff a b _).mpr ⟨ha, hb, rfl⟩

/-- The converse direction of the coding: every real of the extension is the pairing image of a
subset of the checked `ω × ω`, and that subset is itself definable from ground sets, reals and
ordinals. -/
theorem subset_check_omega_prod_of_real (x : A.Model) (hx : x ⊆ A.check (ω : V)) :
    omegaPairPreimage A x ⊆ A.check ((ω : V) ×ˢ (ω : V)) ∧
      A.IsGroundRealDefinable (omegaPairPreimage A x) ∧
      omegaPairImage A (omegaPairPreimage A x) = x :=
  ⟨omegaPairPreimage_subset x, groundRealDefinable_omegaPairPreimage x,
    omegaPairImage_omegaPairPreimage hx⟩

/-! ### The Levy collapse -/

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

omit [IsOrdinal κ] in
/-- A subset of the checked `ω × ω` in the Levy extension is definable from ground sets, reals
and ordinals. -/
theorem solovay_groundRealDefinable_omega_prod (c : (levyContext κ hG).Model)
    (hc2 : c ⊆ (levyContext κ hG).check ((ω : V) ×ˢ (ω : V))) :
    (levyContext κ hG).IsGroundRealDefinable c :=
  groundRealDefinable_of_subset_check_omega_prod c hc2

include hAC hU hc hω hκ in
/-- A subset of the checked `ω × ω` is ordinal definable over the Levy extension from the Solovay
parameter class: it is a member of the Solovay class model as soon as its members are. -/
theorem solovayPf_omega_prod_real (c : (levyContext κ hG).Model)
    (hc2 : c ⊆ (levyContext κ hG).check ((ω : V) ×ˢ (ω : V))) :
    IsOD solovayPf c (solovayParam κ hG) :=
  ForcingContext.isOD_of_groundRealDefinable (levyContext κ hG) solovayPf
    (solovayPf_check hAC hU hc hω hκ hG) (solovayPf_real hG)
    (solovay_groundRealDefinable_omega_prod hG c hc2)

end

end ZFVP
