import ZFVP.SetTheory.InternalNaturalArithmetic
import Mathlib.Tactic.Ring

/-! Rational numbers as internal equivalence classes of signed fractions.
Every numerator and denominator is an element of the model's whole omega.
The external subtype interface is used only to prove algebraic identities;
the code space, equivalence classes and quotient are actual internal sets. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rationalCodeSpaceFormula : SetTheorySemisentence 1 :=
  f“C. ∀ c, c ∈ C ↔ ∃ a ∈ !isω, ∃ b ∈ !isω, ∃ d ∈ !isω,
    d ≠ !isEmpty ∧ c = !kpair.dfn (!kpair.dfn a b) d”

def rationalCodeEquivFormula : SetTheorySemisentence 2 :=
  f“c e. !ordinalAddFormula
      (!naturalMulFormula (!kpair.π₁.dfn (!kpair.π₁.dfn c)) (!kpair.π₂.dfn e))
      (!naturalMulFormula (!kpair.π₂.dfn (!kpair.π₁.dfn e)) (!kpair.π₂.dfn c)) =
    !ordinalAddFormula
      (!naturalMulFormula (!kpair.π₂.dfn (!kpair.π₁.dfn c)) (!kpair.π₂.dfn e))
      (!naturalMulFormula (!kpair.π₁.dfn (!kpair.π₁.dfn e)) (!kpair.π₂.dfn c))”

def rationalClassFormula : SetTheorySemisentence 2 :=
  f“q c. ∀ e, e ∈ q ↔ e ∈ !rationalCodeSpaceFormula ∧ !rationalCodeEquivFormula c e”

def internalRationalsFormula : SetTheorySemisentence 1 :=
  f“Q. ∀ q, q ∈ Q ↔ ∃ c ∈ !rationalCodeSpaceFormula, !rationalClassFormula q c”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def rationalCodeSpace (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V := ((ω : V) ×ˢ (ω : V)) ×ˢ ((ω : V) \ {0})

theorem mem_rationalCodeSpace_iff (c : V) :
    c ∈ rationalCodeSpace V ↔ ∃ a ∈ (ω : V), ∃ b ∈ (ω : V),
      ∃ d ∈ (ω : V), d ≠ 0 ∧ c = ⟨⟨a, b⟩ₖ, d⟩ₖ := by
  simp only [rationalCodeSpace, mem_prod_iff, mem_sdiff_iff, mem_singleton_iff]
  constructor
  · rintro ⟨p, ⟨a, ha, b, hb, rfl⟩, d, ⟨hd, hdn⟩, he⟩
    exact ⟨a, ha, b, hb, d, hd, hdn, he⟩
  · rintro ⟨a, ha, b, hb, d, hd, hdn, rfl⟩
    exact ⟨⟨a, b⟩ₖ, ⟨a, ha, b, hb, rfl⟩, d, ⟨hd, hdn⟩, rfl⟩

instance rationalCodeSpaceFormula_defined :
    ℒₛₑₜ-function₀[V] (rationalCodeSpace V) via rationalCodeSpaceFormula :=
  ⟨fun v ↦ by
    simp [rationalCodeSpaceFormula, mem_ext_iff (y := rationalCodeSpace V),
      mem_rationalCodeSpace_iff, zero_def]⟩

def RationalCodeEquiv (c e : V) : Prop :=
  ordinalAdd (naturalMul (kpair.π₁ (kpair.π₁ c)) (kpair.π₂ e))
      (naturalMul (kpair.π₂ (kpair.π₁ e)) (kpair.π₂ c)) =
    ordinalAdd (naturalMul (kpair.π₂ (kpair.π₁ c)) (kpair.π₂ e))
      (naturalMul (kpair.π₁ (kpair.π₁ e)) (kpair.π₂ c))

instance rationalCodeEquivFormula_defined :
    ℒₛₑₜ-relation[V] RationalCodeEquiv via rationalCodeEquivFormula :=
  ⟨fun v ↦ by simp [rationalCodeEquivFormula, RationalCodeEquiv]⟩

instance rationalCodeEquiv_definable : ℒₛₑₜ-relation[V] RationalCodeEquiv :=
  rationalCodeEquivFormula_defined.to_definable

namespace InternalNatural

theorem rational_balance_trans (a b d u v e s t f : InternalNatural V)
    (he : e ≠ 0)
    (h₁ : a * e + v * d = b * e + u * d)
    (h₂ : u * f + t * e = v * f + s * e) :
    a * f + t * d = b * f + s * d := by
  apply cancel_mul_right he
  apply cancel_add_left (a := v * d * f + u * d * f)
  calc
    v * d * f + u * d * f + (a * f + t * d) * e =
        (a * e + v * d) * f + (u * f + t * e) * d := by ring
    _ = (b * e + u * d) * f + (v * f + s * e) * d := by rw [h₁, h₂]
    _ = v * d * f + u * d * f + (b * f + s * d) * e := by ring

end InternalNatural

theorem rationalCodeEquiv_refl {c : V} (hc : c ∈ rationalCodeSpace V) :
    RationalCodeEquiv c c := by
  obtain ⟨a, ha, b, hb, d, hd, _, rfl⟩ := (mem_rationalCodeSpace_iff c).mp hc
  simp only [RationalCodeEquiv, kpair.π₁_kpair, kpair.π₂_kpair]
  exact ordinalAdd_comm_natural (naturalMul_natural ha hd) (naturalMul_natural hb hd)

theorem rationalCodeEquiv_symm {c e : V} (hc : c ∈ rationalCodeSpace V)
    (he : e ∈ rationalCodeSpace V) (h : RationalCodeEquiv c e) : RationalCodeEquiv e c := by
  obtain ⟨a, ha, b, hb, d, hd, _, rfl⟩ := (mem_rationalCodeSpace_iff c).mp hc
  obtain ⟨u, hu, v, hv, f, hf, _, rfl⟩ := (mem_rationalCodeSpace_iff e).mp he
  simp only [RationalCodeEquiv, kpair.π₁_kpair, kpair.π₂_kpair] at h ⊢
  rw [ordinalAdd_comm_natural (naturalMul_natural hu hd) (naturalMul_natural hb hf),
    ordinalAdd_comm_natural (naturalMul_natural hv hd) (naturalMul_natural ha hf)]
  exact h.symm

theorem rationalCodeEquiv_trans {c e g : V} (hc : c ∈ rationalCodeSpace V)
    (he : e ∈ rationalCodeSpace V) (hg : g ∈ rationalCodeSpace V)
    (h₁ : RationalCodeEquiv c e) (h₂ : RationalCodeEquiv e g) : RationalCodeEquiv c g := by
  obtain ⟨a, ha, b, hb, d, hd, _, rfl⟩ := (mem_rationalCodeSpace_iff c).mp hc
  obtain ⟨u, hu, v, hv, e, heω, hen, rfl⟩ := (mem_rationalCodeSpace_iff e).mp he
  obtain ⟨s, hs, t, ht, f, hf, _, rfl⟩ := (mem_rationalCodeSpace_iff g).mp hg
  simp only [RationalCodeEquiv, kpair.π₁_kpair, kpair.π₂_kpair] at h₁ h₂ ⊢
  have hn : (⟨e, heω⟩ : InternalNatural V) ≠ 0 := fun h ↦ hen (congrArg Subtype.val h)
  have H := InternalNatural.rational_balance_trans
    ⟨a, ha⟩ ⟨b, hb⟩ ⟨d, hd⟩ ⟨u, hu⟩ ⟨v, hv⟩ ⟨e, heω⟩ ⟨s, hs⟩ ⟨t, ht⟩ ⟨f, hf⟩
    hn (Subtype.ext h₁) (Subtype.ext h₂)
  exact congrArg Subtype.val H

noncomputable def rationalClass (c : V) : V :=
  {e ∈ rationalCodeSpace V ; RationalCodeEquiv c e}

theorem mem_rationalClass_iff (c e : V) :
    e ∈ rationalClass c ↔ e ∈ rationalCodeSpace V ∧ RationalCodeEquiv c e := by
  simp [rationalClass]

instance rationalClassFormula_defined :
    ℒₛₑₜ-function₁[V] rationalClass via rationalClassFormula :=
  ⟨fun v ↦ by simp [rationalClassFormula, mem_ext_iff (y := rationalClass _),
    mem_rationalClass_iff]⟩

instance rationalClass_definable : ℒₛₑₜ-function₁[V] rationalClass :=
  rationalClassFormula_defined.to_definable

theorem rationalClass_eq_iff {c e : V} (hc : c ∈ rationalCodeSpace V)
    (he : e ∈ rationalCodeSpace V) : rationalClass c = rationalClass e ↔ RationalCodeEquiv c e := by
  constructor
  · intro h
    have hm : e ∈ rationalClass e := (mem_rationalClass_iff e e).mpr ⟨he, rationalCodeEquiv_refl he⟩
    rw [← h] at hm
    exact ((mem_rationalClass_iff c e).mp hm).2
  · intro h
    apply mem_ext
    intro g
    simp only [mem_rationalClass_iff]
    constructor
    · rintro ⟨hg, hcg⟩
      exact ⟨hg, rationalCodeEquiv_trans he hc hg (rationalCodeEquiv_symm hc he h) hcg⟩
    · rintro ⟨hg, heg⟩
      exact ⟨hg, rationalCodeEquiv_trans hc he hg h heg⟩

noncomputable def internalRationals (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V := repl rationalClass (by definability) (rationalCodeSpace V)

theorem mem_internalRationals_iff (q : V) :
    q ∈ internalRationals V ↔ ∃ c ∈ rationalCodeSpace V, q = rationalClass c := by
  simp [internalRationals]

instance internalRationalsFormula_defined :
    ℒₛₑₜ-function₀[V] (internalRationals V) via internalRationalsFormula :=
  ⟨fun v ↦ by simp [internalRationalsFormula, mem_ext_iff (y := internalRationals V),
    mem_internalRationals_iff]⟩

theorem rationalClass_mem_internalRationals {c : V} (hc : c ∈ rationalCodeSpace V) :
    rationalClass c ∈ internalRationals V :=
  (mem_internalRationals_iff _).mpr ⟨c, hc, rfl⟩

theorem internalRational_nonempty {q : V} (hq : q ∈ internalRationals V) : IsNonempty q := by
  obtain ⟨c, hc, rfl⟩ := (mem_internalRationals_iff q).mp hq
  exact ⟨c, (mem_rationalClass_iff c c).mpr ⟨hc, rationalCodeEquiv_refl hc⟩⟩

end ZFVP
