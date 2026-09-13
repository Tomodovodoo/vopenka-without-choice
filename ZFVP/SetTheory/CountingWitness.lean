import ZFVP.SetTheory.InverseFunction
import ZFVP.SetTheory.NaturalPairing

/-! An injection of an ordinal into `ω` is definable from reals: it is the inverse of the unique
order isomorphism between the coded well-order on naturals and the ordinal. Automorphisms of
ordinals are trivial, which gives uniqueness. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An order-preserving bijection of an ordinal onto itself is the identity. -/
theorem ordinal_automorphism_value_eq {α h : V} [IsOrdinal α] (hh : h ∈ α ^ α)
    (hinj : ∀ x ∈ α, ∀ y ∈ α, h ‘ x = h ‘ y → x = y)
    (hsurj : ∀ z ∈ α, ∃ x ∈ α, h ‘ x = z)
    (hord : ∀ x ∈ α, ∀ y ∈ α, (x ∈ y ↔ h ‘ x ∈ h ‘ y)) :
    ∀ x ∈ α, h ‘ x = x := by
  by_contra hne
  push_neg at hne
  let S : V := {x ∈ α ; h ‘ x ≠ x}
  have hSne : IsNonempty S := by
    obtain ⟨x, hx, hne⟩ := hne
    exact ⟨x, mem_sep_iff.mpr ⟨hx, hne⟩⟩
  obtain ⟨x, hxS, hmin⟩ := foundation S
  obtain ⟨hxα, hxne⟩ := mem_sep_iff.mp hxS
  have hfix : ∀ y ∈ x, h ‘ y = y := by
    intro y hy
    by_contra hy'
    exact hmin y (mem_sep_iff.mpr ⟨IsOrdinal.toIsTransitive.mem_trans hy hxα, hy'⟩) hy
  have hsub : x ⊆ h ‘ x := by
    intro y hy
    have hyα : y ∈ α := IsOrdinal.toIsTransitive.mem_trans hy hxα
    have := (hord y hyα x hxα).mp hy
    rwa [hfix y hy] at this
  have hhxα : h ‘ x ∈ α := function_value_mem hh hxα
  haveI : IsOrdinal x := IsOrdinal.of_mem hxα
  haveI : IsOrdinal (h ‘ x) := IsOrdinal.of_mem hhxα
  rcases IsOrdinal.mem_trichotomy (α := x) (β := h ‘ x) with hlt | heq | hgt
  · obtain ⟨z, hzα, hz⟩ := hsurj x hxα
    haveI : IsOrdinal z := IsOrdinal.of_mem hzα
    rcases IsOrdinal.mem_trichotomy (α := z) (β := x) with hzx | rfl | hxz
    · rw [hfix z hzx] at hz
      rw [hz] at hzx
      exact mem_irrefl x hzx
    · exact hxne hz
    · have := (hord x hxα z hzα).mp hxz
      rw [hz] at this
      exact mem_irrefl (h ‘ x) (hsub _ this)
  · exact hxne heq.symm
  · exact mem_irrefl (h ‘ x) (hsub _ hgt)

/-- The real coding the image of the membership order of `α` under `e`, using the pairing `g`. -/
noncomputable def orderReal (g e α : V) : V :=
  {n ∈ (ω : V) ; ∃ x ∈ α, ∃ y ∈ α, x ∈ y ∧ n = g ‘ ⟨e ‘ x, e ‘ y⟩ₖ}

theorem mem_orderReal_iff (g e α n : V) :
    n ∈ orderReal g e α ↔ n ∈ (ω : V) ∧ ∃ x ∈ α, ∃ y ∈ α, x ∈ y ∧ n = g ‘ ⟨e ‘ x, e ‘ y⟩ₖ := by
  simp only [orderReal, mem_sep_iff]

theorem orderReal_subset (g e α : V) : orderReal g e α ⊆ (ω : V) := fun n hn ↦ (mem_sep_iff.mp hn).1

theorem pair_mem_orderReal_iff {g e α : V} (hg : g ∈ (ω : V) ^ ((ω : V) ×ˢ (ω : V)))
    (hginj : Injective g) (he : e ∈ (ω : V) ^ α) (heinj : Injective e) {m n : V}
    (hm : m ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    g ‘ ⟨m, n⟩ₖ ∈ orderReal g e α ↔ ∃ x ∈ α, ∃ y ∈ α, x ∈ y ∧ m = e ‘ x ∧ n = e ‘ y := by
  rw [mem_orderReal_iff]
  constructor
  · rintro ⟨_, x, hx, y, hy, hxy, heq⟩
    have hex : e ‘ x ∈ (ω : V) := function_value_mem he hx
    have hey : e ‘ y ∈ (ω : V) := function_value_mem he hy
    have hpq := injective_value_eq hg hginj (kpair_mem_iff.mpr ⟨hm, hn⟩) (kpair_mem_iff.mpr ⟨hex, hey⟩) heq
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hpq
    exact ⟨x, hx, y, hy, hxy, rfl, rfl⟩
  · rintro ⟨x, hx, y, hy, hxy, rfl, rfl⟩
    exact ⟨function_value_mem hg (kpair_mem_iff.mpr ⟨hm, hn⟩), x, hx, y, hy, hxy, rfl⟩

/-- `b ∈ e` where `e` is the inverse of the order isomorphism from `(D, r)` onto `α`; `r` is
decoded through the pairing `g`. -/
def countingWitnessFormula : SetTheorySemisentence 5 :=
  f“b α D g r. ∃ f ∈ !function.dfn α D, !Injective.dfn f ∧ !range.dfn α f ∧
    (∀ m ∈ D, ∀ n ∈ D, (!value.dfn f m ∈ !value.dfn f n ↔ !value.dfn g (!kpair.dfn m n) ∈ r)) ∧
    ∃ x n, b = !kpair.dfn x n ∧ !kpair.dfn n x ∈ f”

theorem eval_countingWitnessFormula (b α D g r : V) :
    countingWitnessFormula.Evalb ![b, α, D, g, r] ↔
      ∃ f ∈ α ^ D, Injective f ∧ α = range f ∧
        (∀ m ∈ D, ∀ n ∈ D, (f ‘ m ∈ f ‘ n ↔ g ‘ ⟨m, n⟩ₖ ∈ r)) ∧
        ∃ x n, b = ⟨x, n⟩ₖ ∧ ⟨n, x⟩ₖ ∈ f := by
  simp [countingWitnessFormula]

/-- An injection of an ordinal into `ω` is defined by `countingWitnessFormula` from the
ordinal, its range, the pairing, and the order real. -/
theorem mem_iff_countingWitness {α g e : V} [IsOrdinal α]
    (hg : g ∈ (ω : V) ^ ((ω : V) ×ˢ (ω : V))) (hginj : Injective g)
    (he : e ∈ (ω : V) ^ α) (heinj : Injective e) (b : V) :
    b ∈ e ↔ countingWitnessFormula.Evalb ![b, α, range e, g, orderReal g e α] := by
  rw [eval_countingWitnessFormula]
  haveI : IsFunction e := IsFunction.of_mem he
  have hdom : domain e = α := domain_eq_of_mem_function he
  have hrange : ∀ m ∈ range e, m ∈ (ω : V) := fun m hm ↦ range_subset_of_mem_function he m hm
  have hval : ∀ x ∈ α, e ‘ x ∈ range e := fun x hx ↦ value_mem_range he hx
  constructor
  · intro hb
    have hbp := subset_prod_of_mem_function he b hb
    obtain ⟨x, hx, n, _, rfl⟩ := mem_prod_iff.mp hbp
    have hn : n = e ‘ x := (value_eq_of_kpair_mem hb).symm
    refine ⟨converseGraph e, converseGraph_mem_function he heinj, converseGraph_injective e,
      by rw [range_converseGraph, hdom], ?_, x, n, rfl, (pair_mem_converseGraph _ _ _).mpr hb⟩
    intro m hm n hn
    obtain ⟨x', hx'⟩ := mem_range_iff.mp hm
    obtain ⟨y', hy'⟩ := mem_range_iff.mp hn
    have hx'α : x' ∈ α := hdom ▸ mem_domain_of_kpair_mem hx'
    have hy'α : y' ∈ α := hdom ▸ mem_domain_of_kpair_mem hy'
    have hm' : m = e ‘ x' := (value_eq_of_kpair_mem hx').symm
    have hn' : n = e ‘ y' := (value_eq_of_kpair_mem hy').symm
    subst hm' hn'
    rw [converseGraph_value_value he heinj hx'α, converseGraph_value_value he heinj hy'α,
      pair_mem_orderReal_iff hg hginj he heinj (hrange _ hm) (hrange _ hn)]
    constructor
    · intro h
      exact ⟨x', hx'α, y', hy'α, h, rfl, rfl⟩
    · rintro ⟨x, hx, y, hy, hxy, h1, h2⟩
      rw [injective_value_eq he heinj hx'α hx h1, injective_value_eq he heinj hy'α hy h2]
      exact hxy
  · rintro ⟨f, hf, hfinj, hfr, hord, x, n, rfl, hnx⟩
    haveI : IsFunction f := IsFunction.of_mem hf
    have hfdom : domain f = range e := domain_eq_of_mem_function hf
    have hnD : n ∈ range e := hfdom ▸ mem_domain_of_kpair_mem hnx
    have hxn : f ‘ n = x := value_eq_of_kpair_mem hnx
    -- the composite `f ∘ e` is an automorphism of `α`
    let F : V → V := fun y ↦ f ‘ (e ‘ y)
    have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
    let h := definableGraph α F hF
    have hh : h ∈ α ^ α :=
      definableGraph_mem_function_of_mapsTo α α F hF (fun y hy ↦ function_value_mem hf (hval y hy))
    have hhv : ∀ y ∈ α, h ‘ y = f ‘ (e ‘ y) := fun y hy ↦ value_definableGraph α F hF hy
    have hid : ∀ y ∈ α, h ‘ y = y := by
      apply ordinal_automorphism_value_eq hh
      · intro y₁ hy₁ y₂ hy₂ heq
        rw [hhv y₁ hy₁, hhv y₂ hy₂] at heq
        exact injective_value_eq he heinj hy₁ hy₂
          (injective_value_eq hf hfinj (hval y₁ hy₁) (hval y₂ hy₂) heq)
      · intro z hz
        rw [hfr] at hz
        obtain ⟨m, hm⟩ := mem_range_iff.mp hz
        have hmD : m ∈ range e := hfdom ▸ mem_domain_of_kpair_mem hm
        obtain ⟨y, hy⟩ := mem_range_iff.mp hmD
        have hyα : y ∈ α := hdom ▸ mem_domain_of_kpair_mem hy
        refine ⟨y, hyα, ?_⟩
        rw [hhv y hyα, value_eq_of_kpair_mem hy]
        exact value_eq_of_kpair_mem hm
      · intro y₁ hy₁ y₂ hy₂
        rw [hhv y₁ hy₁, hhv y₂ hy₂, hord _ (hval y₁ hy₁) _ (hval y₂ hy₂),
          pair_mem_orderReal_iff hg hginj he heinj (hrange _ (hval y₁ hy₁)) (hrange _ (hval y₂ hy₂))]
        constructor
        · intro h12
          exact ⟨y₁, hy₁, y₂, hy₂, h12, rfl, rfl⟩
        · rintro ⟨x₁, hx₁, x₂, hx₂, hlt, h1, h2⟩
          rw [injective_value_eq he heinj hy₁ hx₁ h1, injective_value_eq he heinj hy₂ hx₂ h2]
          exact hlt
    obtain ⟨y, hy⟩ := mem_range_iff.mp hnD
    have hyα : y ∈ α := hdom ▸ mem_domain_of_kpair_mem hy
    have hny : n = e ‘ y := (value_eq_of_kpair_mem hy).symm
    have hxy : x = y := by
      rw [← hxn, hny, ← hhv y hyα, hid y hyα]
    rw [hxy]
    exact hy

end ZFVP
