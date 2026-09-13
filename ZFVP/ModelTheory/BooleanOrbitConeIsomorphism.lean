import ZFVP.ModelTheory.BooleanOrbitValueMap
import ZFVP.ModelTheory.BooleanOrbitInverse
import ZFVP.ModelTheory.LevyConeIsomorphism

/-! The core of Jech, Set Theory, Lemma 25.5 for the Boolean completion: an orbit filter and the
generic are carried to each other by an isomorphism of cones.

Write `e b` for `‖b̌ ∈ τ‖` and `d c` for `‖č ∈ σ‖`, where `τ` names the orbit filter `H` and `σ`
names the generic. Three facts are already available. Below one condition `p` met by the generic
the map `e` is monotone, preserves intersections and kills the zero
(`exists_orbitValue_condition`). A condition is met by the generic exactly when `d` of it lies in
`H` (`exists_ground_name_boolGenericSet`), which with the defining property of `τ`
(`exists_booleanValueFamily`) says that the composite `e ∘ d` agrees with the identity on the
conditions met by the generic. And `H` is generic over the ground model on the completion
(`filterTrace_externalGeneric`).

The construction turns these into an isomorphism in three steps.

First, the pointwise agreement `c is met by G ↔ e (d c) is met by G` is upgraded to an identity
below a single condition: the conditions lying in one of the regular sets `c ∩ ¬e (d c)`,
`¬c ∩ e (d c)`, or having no extension in any of them, are dense, and the first two kinds are
refuted inside the generic, so the generic contains a condition whose regular cone `p₁` satisfies
`e (d c) ∩ p₁ = c ∩ p₁` for every `c` of the completion at once
(`exists_condition_eq_of_meets_agree`, `exists_condition_valueMap_inverse_eq`).

Second, the kernel of `e` is avoided by a density argument on the side of `H`. The conditions `b`
with `e b ∩ p = ∅` and the conditions no nonzero part of which is of that kind are together dense
in the completion, so `H` contains one of the two. A condition of the first kind would have the
generic meet both `e b` and `p`, which are disjoint, so `H` contains a condition `q` below which
`e` is nonzero on `p` (`exists_trace_condition_valueMap_nonzero`). This replaces the injectivity
that `e` does not have globally.

Third, with `p` shrunk to `e q ∩ p` the map `b ↦ e b ∩ p` sends the cone below `q` onto the cone
below `p`, with inverse `c ↦ d c ∩ q`; monotonicity and preservation of intersections give the
order in both directions, and nonvanishing gives injectivity. `IsOrbitConeData` collects the
clauses used, `orbitConeData_isomorphism` builds the isomorphism from them, and
`exists_orbit_cone_isomorphism` is the statement of Lemma 25.5: an isomorphism of the cone below a
condition of `H` onto the cone below a condition of the generic, carrying the one filter to the
other.

The data are closed under shrinking on either side (`orbitConeData_shrink_left`,
`orbitConeData_shrink_right`), which gives the two variants in which one of the two conditions is
the regular cone of a condition of the base poset
(`exists_orbit_cone_isomorphism_coneRegular_left`, `..._right`). Both cannot be asked for at once:
an isomorphism of the cone below `q` onto the cone below `p` sends `q` to `p`, so once one side is
prescribed the other is its image, and the image of a regular cone under `e` need not be a regular
cone.

`InternalChoice V` is used through `exists_valueMap_inverse` (the atomic truth lemma for `H`) and
through `filterTrace_externalGeneric` (a dense set contains a maximal antichain). `[Countable V]`
is not used anywhere in this module. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable {A : ForcingContext V}

/-! ### Cones of the completion -/

/-- Membership in the cone of the completion below a condition is inclusion. -/
theorem mem_forcingCone_boolean_iff {P R b₀ b : V} (hb₀ : b₀ ∈ booleanConditions P R) :
    b ∈ forcingCone (booleanConditions P R) (booleanOrder P R) b₀ ↔
      b ∈ booleanConditions P R ∧ b ⊆ b₀ := by
  rw [mem_forcingCone_iff, kpair_mem_booleanOrder_iff]
  exact ⟨fun h ↦ ⟨h.1, h.2.2.2⟩, fun h ↦ ⟨h.1, h.1, hb₀, h.2⟩⟩

/-- The intersection of two conditions of the completion is either a condition or empty. -/
theorem inter_booleanConditions_cases {P R b c : V} (hb : b ∈ booleanConditions P R)
    (hc : c ∈ booleanConditions P R) :
    b ∩ c ∈ booleanConditions P R ∨ b ∩ c = (∅ : V) := by
  by_cases hne : ∃ z : V, z ∈ b ∩ c
  · exact Or.inl ((mem_booleanConditions_iff P R _).mpr
      ⟨forcingRegular_inter (booleanConditions_regular hb) (booleanConditions_regular hc), hne⟩)
  · refine Or.inr (mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hne, fun hz ↦ ?_⟩))
    exact absurd hz not_mem_empty

/-! ### One condition on which a family and its image agree -/

/-- If a definable map `F` sends each member of a ground set of regular sets to a regular set that
the generic meets exactly when it meets the member, then one condition met by the generic makes
the two agree as sets: `F d ∩ p₁ = d ∩ p₁` for every `d` of the family.

The conditions lying in one of the regular sets `d ∩ ¬F d`, `¬d ∩ F d`, or having no extension in
any of them, are dense; a condition of the first two kinds in the generic contradicts the
agreement, so the generic contains a condition `r` of the third kind, and `p₁` is its regular
cone. -/
theorem exists_condition_eq_of_meets_agree (A : ForcingContext V) {Dom : V} {F : V → V}
    (hF : ℒₛₑₜ-function₁[V] F)
    (hDreg : ∀ d ∈ Dom, IsForcingRegular A.P A.R d)
    (hFreg : ∀ d ∈ Dom, IsForcingRegular A.P A.R (F d))
    (hagree : ∀ d ∈ Dom, ((∃ q ∈ A.G, q ∈ d) ↔ ∃ q ∈ A.G, q ∈ F d)) :
    ∃ p₁ ∈ booleanConditions A.P A.R, (∃ q ∈ A.G, q ∈ p₁) ∧
      ∀ d ∈ Dom, F d ∩ p₁ = d ∩ p₁ := by
  obtain ⟨Y, hY⟩ : ∃ Y : V, ∀ y : V, y ∈ Y ↔
      (∃ d ∈ Dom, y = d ∩ forcingNegation A.P A.R (F d)) ∨
      (∃ d ∈ Dom, y = forcingNegation A.P A.R d ∩ F d) := by
    refine ⟨repl (fun d ↦ d ∩ forcingNegation A.P A.R (F d)) (by definability) Dom ∪
      repl (fun d ↦ forcingNegation A.P A.R d ∩ F d) (by definability) Dom, fun y ↦ ?_⟩
    rw [mem_union_iff, repl_spec, repl_spec]
  have hYreg : ∀ y ∈ Y, IsForcingRegular A.P A.R y := by
    intro y hy
    rcases (hY y).mp hy with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
    · exact forcingRegular_inter (hDreg d hd)
        (forcingNegation_regular A.order (hFreg d hd).2.1)
    · exact forcingRegular_inter (forcingNegation_regular A.order (hDreg d hd).2.1) (hFreg d hd)
  obtain ⟨Dn, hDn, hDnmem⟩ := exists_dense_decideFamily A.order Y
  obtain ⟨r, hrG, hrDn⟩ := A.generic.2 Dn hDn
  obtain ⟨hrP, hcases⟩ := hDnmem r hrDn
  have hnocase : ∀ y ∈ Y, r ∉ y := by
    intro y hy hry
    rcases (hY y).mp hy with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
    · obtain ⟨hrd, hrn⟩ := mem_inter_iff.mp hry
      obtain ⟨q, hqG, hqe⟩ := (hagree d hd).mp ⟨r, hrG, hrd⟩
      obtain ⟨t, htP, htr, htq⟩ := externalForcingFilter_compatible A.generic.1 hrG hqG
      have h1 : t ∈ F d := (hFreg d hd).2.1 q hqe t htP htq
      have h2 : t ∈ forcingNegation A.P A.R (F d) :=
        (forcingNegation_regular A.order (hFreg d hd).2.1).2.1 r hrn t htP htr
      have hemp := inter_forcingNegation_eq_empty A.order (hFreg d hd).1
      rw [SetTheory.mem_ext_iff] at hemp
      exact not_mem_empty ((hemp t).mp (mem_inter_iff.mpr ⟨h1, h2⟩))
    · obtain ⟨hrn, hre⟩ := mem_inter_iff.mp hry
      obtain ⟨q, hqG, hqd⟩ := (hagree d hd).mpr ⟨r, hrG, hre⟩
      obtain ⟨t, htP, htr, htq⟩ := externalForcingFilter_compatible A.generic.1 hrG hqG
      have h1 : t ∈ d := (hDreg d hd).2.1 q hqd t htP htq
      have h2 : t ∈ forcingNegation A.P A.R d :=
        (forcingNegation_regular A.order (hDreg d hd).2.1).2.1 r hrn t htP htr
      have hemp := inter_forcingNegation_eq_empty A.order (hDreg d hd).1
      rw [SetTheory.mem_ext_iff] at hemp
      exact not_mem_empty ((hemp t).mp (mem_inter_iff.mpr ⟨h1, h2⟩))
  have hsep : ∀ y ∈ Y, ∀ t ∈ A.P, (⟨t, r⟩ₖ : V) ∈ A.R → t ∉ y := by
    rcases hcases with ⟨y, hy, hry⟩ | h
    · exact absurd hry (hnocase y hy)
    · exact h
  have hdisj : ∀ y ∈ Y, ∀ z : V, z ∈ coneRegular A.P A.R r → z ∈ y → False := by
    intro y hy z hz hzy
    obtain ⟨hzP, hh⟩ := mem_coneRegular_iff.mp hz
    obtain ⟨u, huP, hur, huz⟩ := hh z hzP (A.order.2.1 z hzP)
    exact hsep y hy u huP hur ((hYreg y hy).2.1 z hzy u huP huz)
  refine ⟨coneRegular A.P A.R r, coneRegular_mem_booleanConditions A.order hrP,
    ⟨r, hrG, self_mem_coneRegular A.order hrP⟩, fun d hd ↦ ?_⟩
  have hdreg := hDreg d hd
  have hfdreg := hFreg d hd
  have hy1 : d ∩ forcingNegation A.P A.R (F d) ∈ Y := (hY _).mpr (Or.inl ⟨d, hd, rfl⟩)
  have hy2 : forcingNegation A.P A.R d ∩ F d ∈ Y := (hY _).mpr (Or.inr ⟨d, hd, rfl⟩)
  have hcone : IsForcingRegular A.P A.R (coneRegular A.P A.R r) := coneRegular_regular A.order r
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨hze, hzp⟩ := mem_inter_iff.mp hz
    refine mem_inter_iff.mpr ⟨?_, hzp⟩
    by_contra hzd
    obtain ⟨t, ht, htz⟩ := exists_forcingNegation_of_not_mem (hfdreg.1 z hze) hzd hdreg.2.2
    have htP : t ∈ A.P := forcingNegation_subset _ _ _ t ht
    exact hdisj _ hy2 t (hcone.2.1 z hzp t htP htz)
      (mem_inter_iff.mpr ⟨ht, hfdreg.2.1 z hze t htP htz⟩)
  · intro hz
    obtain ⟨hzd, hzp⟩ := mem_inter_iff.mp hz
    refine mem_inter_iff.mpr ⟨?_, hzp⟩
    by_contra hze
    obtain ⟨t, ht, htz⟩ := exists_forcingNegation_of_not_mem (hdreg.1 z hzd) hze hfdreg.2.2
    have htP : t ∈ A.P := forcingNegation_subset _ _ _ t ht
    exact hdisj _ hy1 t (hcone.2.1 z hzp t htP htz)
      (mem_inter_iff.mpr ⟨hdreg.2.1 z hzd t htP htz, ht⟩)

/-! ### The composite of the value map and its inverse, below one condition -/

/-- The inverse map of the value map, `d c = ‖č ∈ σ‖`. -/
noncomputable def orbitInverseValue (A : ForcingContext V) (σ c : V) : V :=
  booleanValueBase A.P A.R (checkName A.P c) σ

theorem orbitInverseValue_definable (A : ForcingContext V) (σ : V) :
    ℒₛₑₜ-function₁[V] (A.orbitInverseValue σ) := by
  have := booleanValueBase_definable (V := V) A.P A.R
  have := checkName_definable (V := V)
  unfold orbitInverseValue
  definability

theorem orbitInverseValue_regular (A : ForcingContext V) (σ c : V) :
    IsForcingRegular A.P A.R (A.orbitInverseValue σ c) :=
  booleanValueBase_regular A.order _ _

/-- The value map composed with its inverse is the identity below one condition met by the
generic, uniformly over the whole completion: `‖(‖č ∈ σ‖)ˇ ∈ τ‖ ∩ p₁ = c ∩ p₁` for every
condition `c`. Together with the two names this is the whole input of the construction. -/
theorem exists_condition_valueMap_inverse_eq (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    (hPf : ∀ y : A.Model, Pf.Evalb ![y, p] → ∃ a : V, y = A.check a) :
    ∃ τ σ : V, (∀ b : V, (A.check b ∈ H ↔ ∃ q ∈ A.G, q ∈ A.booleanMemValue τ b)) ∧
      (∀ c ∈ booleanConditions A.P A.R,
        (A.check c ∈ A.boolGenericSet ↔ A.check (A.orbitInverseValue σ c) ∈ H)) ∧
      ∃ p₁ ∈ booleanConditions A.P A.R, (∃ q ∈ A.G, q ∈ p₁) ∧
        ∀ c ∈ booleanConditions A.P A.R,
          A.booleanMemValue τ (A.orbitInverseValue σ c) ∩ p₁ = c ∩ p₁ := by
  obtain ⟨τ, -, hval⟩ := A.exists_booleanValueFamily H
  obtain ⟨σ, -, -, hd₀⟩ := exists_ground_name_boolGenericSet hAC hH hPf
  have hd : ∀ c ∈ booleanConditions A.P A.R,
      (A.check c ∈ A.boolGenericSet ↔ A.check (A.orbitInverseValue σ c) ∈ H) := hd₀
  have hcomp : ∀ c ∈ booleanConditions A.P A.R,
      ((∃ q ∈ A.G, q ∈ c) ↔ ∃ q ∈ A.G, q ∈ A.booleanMemValue τ (A.orbitInverseValue σ c)) := by
    intro c hc
    rw [← hval, ← hd c hc, A.check_mem_boolGenericSet_iff]
    exact ⟨fun h ↦ ⟨(mem_regularSets_iff _ _ _).mpr (booleanConditions_regular hc), h⟩, And.right⟩
  have hFdef : ℒₛₑₜ-function₁[V] (fun c ↦ A.booleanMemValue τ (A.orbitInverseValue σ c)) := by
    have := A.booleanMemValue_definable τ
    have := A.orbitInverseValue_definable σ
    definability
  obtain ⟨p₁, hp₁B, hp₁G, hp₁⟩ := A.exists_condition_eq_of_meets_agree hFdef
    (fun c hc ↦ booleanConditions_regular hc)
    (fun c _ ↦ A.booleanMemValue_regular τ _) hcomp
  exact ⟨τ, σ, hval, hd, p₁, hp₁B, hp₁G, hp₁⟩

/-! ### A condition of the filter on which the value map does not vanish -/

/-- A condition of the orbit filter below which the value map is nonzero on `p₀`. The conditions
`b` with `‖b̌ ∈ τ‖ ∩ p₀ = ∅` and the conditions no nonzero part of which is of that kind are
together dense in the completion, and `H` is generic over the ground model, so `H` contains one of
the two kinds. The first kind is impossible: it would have the generic meet the disjoint sets
`‖b̌ ∈ τ‖` and `p₀`. -/
theorem exists_trace_condition_valueMap_nonzero (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    {τ : V} (hval : ∀ b : V, (A.check b ∈ H ↔ ∃ q ∈ A.G, q ∈ A.booleanMemValue τ b))
    {p₀ : V} (hp₀G : ∃ q ∈ A.G, q ∈ p₀) (hp₀reg : IsForcingRegular A.P A.R p₀) :
    ∃ q₀ ∈ booleanConditions A.P A.R, A.check q₀ ∈ H ∧
      ∀ b ∈ booleanConditions A.P A.R, b ⊆ q₀ → ∃ z : V, z ∈ A.booleanMemValue τ b ∩ p₀ := by
  classical
  have hdef : ℒₛₑₜ-function₁[V] (A.booleanMemValue τ) := A.booleanMemValue_definable τ
  set D : V := sep (booleanConditions A.P A.R)
    (fun b ↦ (A.booleanMemValue τ b ∩ p₀ = (∅ : V)) ∨
      (∀ c ∈ booleanConditions A.P A.R, c ⊆ b →
        ¬ (A.booleanMemValue τ c ∩ p₀ = (∅ : V)))) (by definability) with hDdef
  have hmemD : ∀ b : V, b ∈ D ↔ b ∈ booleanConditions A.P A.R ∧
      ((A.booleanMemValue τ b ∩ p₀ = (∅ : V)) ∨
        (∀ c ∈ booleanConditions A.P A.R, c ⊆ b →
          ¬ (A.booleanMemValue τ c ∩ p₀ = (∅ : V)))) := fun b ↦ by rw [hDdef]; exact mem_sep_iff
  have hDdense : ForcingDense (booleanConditions A.P A.R) (booleanOrder A.P A.R) D := by
    refine ⟨sep_subset, fun u hu ↦ ?_⟩
    by_cases hbad : ∃ c ∈ booleanConditions A.P A.R, c ⊆ u ∧
        A.booleanMemValue τ c ∩ p₀ = (∅ : V)
    · obtain ⟨c, hc, hcu, hce⟩ := hbad
      exact ⟨c, (hmemD c).mpr ⟨hc, Or.inl hce⟩,
        (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hc, hu, hcu⟩⟩
    · refine ⟨u, (hmemD u).mpr ⟨hu, Or.inr (fun c hc hcu hce ↦ hbad ⟨c, hc, hcu, hce⟩)⟩,
        (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hu, hu, subset_refl _⟩⟩
  have hgen := filterTrace_externalGeneric hAC hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2.1
    hH.2.2.2.2.2.1
  obtain ⟨q₀, hq₀T, hq₀D⟩ := hgen.2 D hDdense
  have hq₀H : A.check q₀ ∈ H := hq₀T
  obtain ⟨hq₀B, hq₀cases⟩ := (hmemD q₀).mp hq₀D
  refine ⟨q₀, hq₀B, hq₀H, fun b hb hbq ↦ ?_⟩
  have hgood : ∀ c ∈ booleanConditions A.P A.R, c ⊆ q₀ →
      ¬ (A.booleanMemValue τ c ∩ p₀ = (∅ : V)) := by
    rcases hq₀cases with hzero | hgood
    · exfalso
      obtain ⟨w, hwG, hwe⟩ := (hval q₀).mp hq₀H
      obtain ⟨w', hw'G, hw'p⟩ := hp₀G
      obtain ⟨t, htP, htw, htw'⟩ := externalForcingFilter_compatible A.generic.1 hwG hw'G
      have h1 : t ∈ A.booleanMemValue τ q₀ :=
        (A.booleanMemValue_regular τ q₀).2.1 w hwe t htP htw
      have h2 : t ∈ p₀ := hp₀reg.2.1 w' hw'p t htP htw'
      rw [SetTheory.mem_ext_iff] at hzero
      exact not_mem_empty ((hzero t).mp (mem_inter_iff.mpr ⟨h1, h2⟩))
    · exact hgood
  by_contra hne
  refine hgood b hb hbq (mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hne, fun hz ↦ ?_⟩))
  exact absurd hz not_mem_empty

/-! ### The clauses of the construction -/

/-- The clauses on a pair `(p, q)` of Boolean conditions that make `b ↦ ‖b̌ ∈ τ‖ ∩ p` an
isomorphism of the cone below `q` onto the cone below `p`, with `c ↦ ‖č ∈ σ‖ ∩ q` as inverse:
below `p` the value map is monotone, preserves intersections and kills the zero; the composite
with the inverse map is the identity below `p`; `p` lies below the value of `q`; and the value map
is nonzero on `p` at every nonzero condition below `q`. -/
def IsOrbitConeData (A : ForcingContext V) (τ σ p q : V) : Prop :=
  p ∈ booleanConditions A.P A.R ∧ q ∈ booleanConditions A.P A.R ∧
  (∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R, b ⊆ c →
    A.booleanMemValue τ b ∩ p ⊆ A.booleanMemValue τ c) ∧
  (∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R,
    A.booleanMemValue τ b ∩ A.booleanMemValue τ c ∩ p ⊆ A.booleanMemValue τ (b ∩ c)) ∧
  A.booleanMemValue τ (∅ : V) ∩ p = (∅ : V) ∧
  (∀ c ∈ booleanConditions A.P A.R,
    A.booleanMemValue τ (A.orbitInverseValue σ c) ∩ p = c ∩ p) ∧
  p ⊆ A.booleanMemValue τ q ∧
  (∀ b ∈ booleanConditions A.P A.R, b ⊆ q → ∃ z : V, z ∈ A.booleanMemValue τ b ∩ p)

/-- Below `p` the value map takes intersections to intersections exactly. -/
theorem orbitConeData_inter_eq {τ σ p q : V} (hdata : A.IsOrbitConeData τ σ p q)
    {b c : V} (hb : b ∈ booleanConditions A.P A.R) (hc : c ∈ booleanConditions A.P A.R) :
    A.booleanMemValue τ (b ∩ c) ∩ p = A.booleanMemValue τ b ∩ A.booleanMemValue τ c ∩ p := by
  obtain ⟨hpB, hqB, hmono, hmeet, hzero, hinv, hptop, hnz⟩ := hdata
  apply SetTheory.subset_antisymm
  · rcases inter_booleanConditions_cases hb hc with hbcB | hbce
    · intro z hz
      obtain ⟨hzv, hzp⟩ := mem_inter_iff.mp hz
      refine mem_inter_iff.mpr ⟨mem_inter_iff.mpr ⟨?_, ?_⟩, hzp⟩
      · exact hmono _ hbcB _ hb (fun y hy ↦ (mem_inter_iff.mp hy).1) z (mem_inter_iff.mpr ⟨hzv, hzp⟩)
      · exact hmono _ hbcB _ hc (fun y hy ↦ (mem_inter_iff.mp hy).2) z (mem_inter_iff.mpr ⟨hzv, hzp⟩)
    · intro z hz
      rw [hbce] at hz
      rw [SetTheory.mem_ext_iff] at hzero
      exact absurd ((hzero z).mp hz) not_mem_empty
  · intro z hz
    exact mem_inter_iff.mpr ⟨hmeet b hb c hc z hz, (mem_inter_iff.mp hz).2⟩

/-- The map of the construction sends the cone below `q` into the cone below `p`. -/
theorem orbitConeData_value_mem {τ σ p q : V} (hdata : A.IsOrbitConeData τ σ p q)
    {b : V} (hb : b ∈ booleanConditions A.P A.R) (hbq : b ⊆ q) :
    A.booleanMemValue τ b ∩ p ∈ booleanConditions A.P A.R ∧
      A.booleanMemValue τ b ∩ p ⊆ p := by
  obtain ⟨hpB, hqB, hmono, hmeet, hzero, hinv, hptop, hnz⟩ := hdata
  refine ⟨(mem_booleanConditions_iff _ _ _).mpr
    ⟨forcingRegular_inter (A.booleanMemValue_regular τ b) (booleanConditions_regular hpB),
      hnz b hb hbq⟩, fun z hz ↦ (mem_inter_iff.mp hz).2⟩

/-- The map of the construction reflects inclusion, hence is injective on the cone below `q`. -/
theorem orbitConeData_subset_of_value_subset {τ σ p q : V} (hdata : A.IsOrbitConeData τ σ p q)
    {b c : V} (hb : b ∈ booleanConditions A.P A.R) (hc : c ∈ booleanConditions A.P A.R)
    (hbq : b ⊆ q)
    (hsub : A.booleanMemValue τ b ∩ p ⊆ A.booleanMemValue τ c ∩ p) : b ⊆ c := by
  obtain ⟨hpB, hqB, hmono, hmeet, hzero, hinv, hptop, hnz⟩ := hdata
  by_contra hbc
  obtain ⟨z, hzb, hzc⟩ : ∃ z : V, z ∈ b ∧ z ∉ c := by
    by_contra hcon
    exact hbc (fun z hz ↦ by
      by_contra hzc
      exact hcon ⟨z, hz, hzc⟩)
  have hbreg := booleanConditions_regular hb
  have hcreg := booleanConditions_regular hc
  obtain ⟨w, hwn, hwz⟩ := exists_forcingNegation_of_not_mem (hbreg.1 z hzb) hzc hcreg.2.2
  have hwP : w ∈ A.P := forcingNegation_subset _ _ _ w hwn
  have hwb : w ∈ b := hbreg.2.1 z hzb w hwP hwz
  have hnB : b ∩ forcingNegation A.P A.R c ∈ booleanConditions A.P A.R :=
    (mem_booleanConditions_iff _ _ _).mpr
      ⟨forcingRegular_inter hbreg (forcingNegation_regular A.order hcreg.2.1),
        w, mem_inter_iff.mpr ⟨hwb, hwn⟩⟩
  obtain ⟨y, hy⟩ := hnz _ hnB (subset_trans (fun t ht ↦ (mem_inter_iff.mp ht).1) hbq)
  obtain ⟨hyv, hyp⟩ := mem_inter_iff.mp hy
  have hyb : y ∈ A.booleanMemValue τ b :=
    hmono _ hnB _ hb (fun t ht ↦ (mem_inter_iff.mp ht).1) y (mem_inter_iff.mpr ⟨hyv, hyp⟩)
  have hyc : y ∈ A.booleanMemValue τ c :=
    (mem_inter_iff.mp (hsub y (mem_inter_iff.mpr ⟨hyb, hyp⟩))).1
  have hmem : y ∈ A.booleanMemValue τ ((b ∩ forcingNegation A.P A.R c) ∩ c) :=
    hmeet _ hnB _ hc y (mem_inter_iff.mpr ⟨mem_inter_iff.mpr ⟨hyv, hyc⟩, hyp⟩)
  have hemp : (b ∩ forcingNegation A.P A.R c) ∩ c = (∅ : V) := by
    have h := inter_forcingNegation_eq_empty A.order hcreg.1
    rw [SetTheory.mem_ext_iff] at h
    apply mem_ext
    intro t
    refine ⟨fun ht ↦ ?_, fun ht ↦ absurd ht not_mem_empty⟩
    obtain ⟨htn, htc⟩ := mem_inter_iff.mp ht
    exact (h t).mp (mem_inter_iff.mpr ⟨htc, (mem_inter_iff.mp htn).2⟩)
  rw [hemp] at hmem
  rw [SetTheory.mem_ext_iff] at hzero
  exact not_mem_empty ((hzero y).mp (mem_inter_iff.mpr ⟨hmem, hyp⟩))

/-- The inverse map sends the cone below `p` into the cone below `q`, and the composite is the
identity there. -/
theorem orbitConeData_inverse_value {τ σ p q : V} (hdata : A.IsOrbitConeData τ σ p q)
    {c : V} (hc : c ∈ booleanConditions A.P A.R) (hcp : c ⊆ p) :
    (A.orbitInverseValue σ c ∩ q) ∈ booleanConditions A.P A.R ∧
      A.orbitInverseValue σ c ∩ q ⊆ q ∧
      A.booleanMemValue τ (A.orbitInverseValue σ c ∩ q) ∩ p = c := by
  obtain ⟨hpB, hqB, hmono, hmeet, hzero, hinv, hptop, hnz⟩ := hdata
  have hdata' : A.IsOrbitConeData τ σ p q := ⟨hpB, hqB, hmono, hmeet, hzero, hinv, hptop, hnz⟩
  have hcp' : c ∩ p = c := by
    apply mem_ext
    intro z
    exact ⟨fun hz ↦ (mem_inter_iff.mp hz).1, fun hz ↦ mem_inter_iff.mpr ⟨hz, hcp z hz⟩⟩
  have hne : ∃ z : V, z ∈ c := booleanConditions_nonempty hc
  -- the inverse value is nonzero
  have hdB : A.orbitInverseValue σ c ∈ booleanConditions A.P A.R := by
    refine (mem_booleanConditions_iff _ _ _).mpr ⟨A.orbitInverseValue_regular σ c, ?_⟩
    by_contra hno
    have hdempty : A.orbitInverseValue σ c = (∅ : V) :=
      mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hno, fun hz ↦ absurd hz not_mem_empty⟩)
    have h := hinv c hc
    rw [hdempty, hzero, hcp'] at h
    obtain ⟨z, hz⟩ := hne
    rw [SetTheory.mem_ext_iff] at h
    exact not_mem_empty ((h z).mpr hz)
  -- the intersection with `q` has the same value below `p`
  have hkey : A.booleanMemValue τ (A.orbitInverseValue σ c ∩ q) ∩ p = c := by
    rw [A.orbitConeData_inter_eq hdata' hdB hqB]
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨hzi, hzp⟩ := mem_inter_iff.mp hz
      have hzd : z ∈ A.booleanMemValue τ (A.orbitInverseValue σ c) := (mem_inter_iff.mp hzi).1
      have := hinv c hc
      rw [SetTheory.mem_ext_iff] at this
      exact (mem_inter_iff.mp ((this z).mp (mem_inter_iff.mpr ⟨hzd, hzp⟩))).1
    · intro hz
      have hzp : z ∈ p := hcp z hz
      have := hinv c hc
      rw [SetTheory.mem_ext_iff] at this
      have hzd : z ∈ A.booleanMemValue τ (A.orbitInverseValue σ c) :=
        (mem_inter_iff.mp ((this z).mpr (mem_inter_iff.mpr ⟨hz, hzp⟩))).1
      exact mem_inter_iff.mpr ⟨mem_inter_iff.mpr ⟨hzd, hptop z hzp⟩, hzp⟩
  refine ⟨?_, fun z hz ↦ (mem_inter_iff.mp hz).2, hkey⟩
  refine (mem_booleanConditions_iff _ _ _).mpr
    ⟨forcingRegular_inter (A.orbitInverseValue_regular σ c) (booleanConditions_regular hqB), ?_⟩
  by_contra hno
  have hempty : A.orbitInverseValue σ c ∩ q = (∅ : V) :=
    mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hno, fun hz ↦ absurd hz not_mem_empty⟩)
  rw [hempty, hzero] at hkey
  obtain ⟨z, hz⟩ := hne
  rw [← hkey] at hz
  exact not_mem_empty hz

/-! ### The isomorphism of cones -/

/-- The construction: from the clauses of `IsOrbitConeData`, the map `b ↦ ‖b̌ ∈ τ‖ ∩ p` is an
isomorphism of the cone of the completion below `q` onto the cone below `p`. -/
theorem orbitConeData_isomorphism {τ σ p q : V} (hdata : A.IsOrbitConeData τ σ p q) :
    ∃ ψ : V,
      IsForcingIsomorphism
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q))
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p)) ψ ∧
      ∀ b ∈ booleanConditions A.P A.R, b ⊆ q → ψ ‘ b = A.booleanMemValue τ b ∩ p := by
  obtain ⟨hpB, hqB, hmono, hmeet, hzero, hinv, hptop, hnz⟩ := hdata
  have hdata' : A.IsOrbitConeData τ σ p q := ⟨hpB, hqB, hmono, hmeet, hzero, hinv, hptop, hnz⟩
  set Cq : V := forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q with hCq
  set Cp : V := forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p with hCp
  have hmemq : ∀ b : V, b ∈ Cq ↔ b ∈ booleanConditions A.P A.R ∧ b ⊆ q :=
    fun b ↦ mem_forcingCone_boolean_iff hqB
  have hmemp : ∀ c : V, c ∈ Cp ↔ c ∈ booleanConditions A.P A.R ∧ c ⊆ p :=
    fun c ↦ mem_forcingCone_boolean_iff hpB
  set F : V → V := fun b ↦ A.booleanMemValue τ b ∩ p with hF
  set Gm : V → V := fun c ↦ A.orbitInverseValue σ c ∩ q with hGm
  have hFdef : ℒₛₑₜ-function₁[V] F := by
    have := A.booleanMemValue_definable τ
    rw [hF]
    definability
  have hFP : ∀ b ∈ Cq, F b ∈ Cp := by
    intro b hb
    obtain ⟨hbB, hbq⟩ := (hmemq b).mp hb
    obtain ⟨h1, h2⟩ := A.orbitConeData_value_mem hdata' hbB hbq
    exact (hmemp _).mpr ⟨h1, h2⟩
  have hGQ : ∀ c ∈ Cp, Gm c ∈ Cq := by
    intro c hc
    obtain ⟨hcB, hcp⟩ := (hmemp c).mp hc
    obtain ⟨h1, h2, -⟩ := A.orbitConeData_inverse_value hdata' hcB hcp
    exact (hmemq _).mpr ⟨h1, h2⟩
  have hFG : ∀ c ∈ Cp, F (Gm c) = c := by
    intro c hc
    obtain ⟨hcB, hcp⟩ := (hmemp c).mp hc
    exact (A.orbitConeData_inverse_value hdata' hcB hcp).2.2
  have hFmono : ∀ b ∈ Cq, ∀ c ∈ Cq, b ⊆ c → F b ⊆ F c := by
    intro b hb c hc hbc z hz
    obtain ⟨hbB, hbq⟩ := (hmemq b).mp hb
    obtain ⟨hcB, hcq⟩ := (hmemq c).mp hc
    exact mem_inter_iff.mpr ⟨hmono b hbB c hcB hbc z hz, (mem_inter_iff.mp hz).2⟩
  have hFrefl : ∀ b ∈ Cq, ∀ c ∈ Cq, F b ⊆ F c → b ⊆ c := by
    intro b hb c hc hsub
    obtain ⟨hbB, hbq⟩ := (hmemq b).mp hb
    obtain ⟨hcB, hcq⟩ := (hmemq c).mp hc
    exact A.orbitConeData_subset_of_value_subset hdata' hbB hcB hbq hsub
  have hFinj : ∀ b ∈ Cq, ∀ c ∈ Cq, F b = F c → b = c := by
    intro b hb c hc he
    exact SetTheory.subset_antisymm (hFrefl b hb c hc (fun z hz ↦ he ▸ hz))
      (hFrefl c hc b hb (fun z hz ↦ he ▸ hz))
  have hGF : ∀ b ∈ Cq, Gm (F b) = b := by
    intro b hb
    have hFb : F b ∈ Cp := hFP b hb
    have h1 : F (Gm (F b)) = F b := hFG _ hFb
    exact hFinj _ (hGQ _ hFb) b hb h1
  have hord : ∀ b ∈ Cq, ∀ c ∈ Cq, (⟨b, c⟩ₖ : V) ∈ restrictedOrder (booleanOrder A.P A.R) Cq ↔
      (⟨F b, F c⟩ₖ : V) ∈ restrictedOrder (booleanOrder A.P A.R) Cp := by
    intro b hb c hc
    rw [kpair_mem_restrictedOrder_iff, kpair_mem_restrictedOrder_iff,
      kpair_mem_booleanOrder_iff, kpair_mem_booleanOrder_iff]
    obtain ⟨hbB, hbq⟩ := (hmemq b).mp hb
    obtain ⟨hcB, hcq⟩ := (hmemq c).mp hc
    have hFbB := ((hmemp _).mp (hFP b hb)).1
    have hFcB := ((hmemp _).mp (hFP c hc)).1
    constructor
    · intro h
      exact ⟨⟨hFbB, hFcB, hFmono b hb c hc h.1.2.2⟩, hFP b hb, hFP c hc⟩
    · intro h
      exact ⟨⟨hbB, hcB, hFrefl b hb c hc h.1.2.2⟩, hb, hc⟩
  refine ⟨definableGraph Cq F hFdef,
    isForcingIsomorphism_of_inverse F Gm hFdef hFP hGQ hGF hFG hord, fun b hbB hbq ↦ ?_⟩
  exact value_definableGraph _ _ _ ((hmemq b).mpr ⟨hbB, hbq⟩)

/-! ### Shrinking the two conditions -/

/-- The clauses are inherited by a smaller condition on the side of the generic: the matching
condition on the other side is the inverse value of the new one. -/
theorem orbitConeData_shrink_left {τ σ p q : V} (hdata : A.IsOrbitConeData τ σ p q)
    {p' : V} (hp'B : p' ∈ booleanConditions A.P A.R) (hp'p : p' ⊆ p) :
    A.IsOrbitConeData τ σ p' (A.orbitInverseValue σ p' ∩ q) := by
  obtain ⟨hpB, hqB, hmono, hmeet, hzero, hinv, hptop, hnz⟩ := hdata
  have hdata' : A.IsOrbitConeData τ σ p q := ⟨hpB, hqB, hmono, hmeet, hzero, hinv, hptop, hnz⟩
  obtain ⟨hq'B, hq'q, hq'val⟩ := A.orbitConeData_inverse_value hdata' hp'B hp'p
  have hshrink : ∀ X Y : V, X ∩ p = Y ∩ p → X ∩ p' = Y ∩ p' := by
    intro X Y h
    rw [SetTheory.mem_ext_iff] at h
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨hzX, hzp'⟩ := mem_inter_iff.mp hz
      exact mem_inter_iff.mpr
        ⟨(mem_inter_iff.mp ((h z).mp (mem_inter_iff.mpr ⟨hzX, hp'p z hzp'⟩))).1, hzp'⟩
    · intro hz
      obtain ⟨hzY, hzp'⟩ := mem_inter_iff.mp hz
      exact mem_inter_iff.mpr
        ⟨(mem_inter_iff.mp ((h z).mpr (mem_inter_iff.mpr ⟨hzY, hp'p z hzp'⟩))).1, hzp'⟩
  refine ⟨hp'B, hq'B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb c hc hbc z hz
    exact hmono b hb c hc hbc z (mem_inter_iff.mpr
      ⟨(mem_inter_iff.mp hz).1, hp'p z (mem_inter_iff.mp hz).2⟩)
  · intro b hb c hc z hz
    exact hmeet b hb c hc z (mem_inter_iff.mpr
      ⟨(mem_inter_iff.mp hz).1, hp'p z (mem_inter_iff.mp hz).2⟩)
  · have h := hshrink (A.booleanMemValue τ (∅ : V)) (∅ : V) (by
      rw [hzero]
      apply mem_ext
      intro z
      exact ⟨fun hz ↦ absurd hz not_mem_empty, fun hz ↦ (mem_inter_iff.mp hz).1⟩)
    rw [h]
    apply mem_ext
    intro z
    exact ⟨fun hz ↦ (mem_inter_iff.mp hz).1, fun hz ↦ absurd hz not_mem_empty⟩
  · intro c hc
    exact hshrink _ _ (hinv c hc)
  · intro z hz
    have hzp : z ∈ p := hp'p z hz
    have hzv : z ∈ A.booleanMemValue τ (A.orbitInverseValue σ p' ∩ q) ∩ p := by
      rw [hq'val]
      exact hz
    exact (mem_inter_iff.mp hzv).1
  · intro b hb hbq'
    have hbq : b ⊆ q := subset_trans hbq' hq'q
    obtain ⟨z, hz⟩ := hnz b hb hbq
    obtain ⟨hzv, hzp⟩ := mem_inter_iff.mp hz
    have hzp' : z ∈ p' := by
      rw [← hq'val]
      refine mem_inter_iff.mpr ⟨?_, hzp⟩
      exact hmono b hb _ hq'B hbq' z (mem_inter_iff.mpr ⟨hzv, hzp⟩)
    exact ⟨z, mem_inter_iff.mpr ⟨hzv, hzp'⟩⟩

/-- The clauses are inherited by a smaller condition on the side of the filter: the matching
condition on the other side is the value of the new one. -/
theorem orbitConeData_shrink_right {τ σ p q : V} (hdata : A.IsOrbitConeData τ σ p q)
    {q' : V} (hq'B : q' ∈ booleanConditions A.P A.R) (hq'q : q' ⊆ q) :
    A.IsOrbitConeData τ σ (A.booleanMemValue τ q' ∩ p) q' := by
  obtain ⟨hpB, hqB, hmono, hmeet, hzero, hinv, hptop, hnz⟩ := hdata
  have hdata' : A.IsOrbitConeData τ σ p q := ⟨hpB, hqB, hmono, hmeet, hzero, hinv, hptop, hnz⟩
  set p' : V := A.booleanMemValue τ q' ∩ p with hp'
  have hp'p : p' ⊆ p := fun z hz ↦ (mem_inter_iff.mp hz).2
  have hp'B : p' ∈ booleanConditions A.P A.R := (A.orbitConeData_value_mem hdata' hq'B hq'q).1
  have hkey : ∀ b : V, b ∈ booleanConditions A.P A.R → b ⊆ q' →
      A.booleanMemValue τ b ∩ p' = A.booleanMemValue τ b ∩ p := by
    intro b hb hbq'
    apply mem_ext
    intro z
    constructor
    · intro hz
      exact mem_inter_iff.mpr ⟨(mem_inter_iff.mp hz).1, hp'p z (mem_inter_iff.mp hz).2⟩
    · intro hz
      obtain ⟨hzv, hzp⟩ := mem_inter_iff.mp hz
      exact mem_inter_iff.mpr ⟨hzv, mem_inter_iff.mpr
        ⟨hmono b hb q' hq'B hbq' z (mem_inter_iff.mpr ⟨hzv, hzp⟩), hzp⟩⟩
  have hshrink : ∀ X Y : V, X ∩ p = Y ∩ p → X ∩ p' = Y ∩ p' := by
    intro X Y h
    rw [SetTheory.mem_ext_iff] at h
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨hzX, hzp'⟩ := mem_inter_iff.mp hz
      exact mem_inter_iff.mpr
        ⟨(mem_inter_iff.mp ((h z).mp (mem_inter_iff.mpr ⟨hzX, hp'p z hzp'⟩))).1, hzp'⟩
    · intro hz
      obtain ⟨hzY, hzp'⟩ := mem_inter_iff.mp hz
      exact mem_inter_iff.mpr
        ⟨(mem_inter_iff.mp ((h z).mpr (mem_inter_iff.mpr ⟨hzY, hp'p z hzp'⟩))).1, hzp'⟩
  refine ⟨hp'B, hq'B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb c hc hbc z hz
    exact hmono b hb c hc hbc z (mem_inter_iff.mpr
      ⟨(mem_inter_iff.mp hz).1, hp'p z (mem_inter_iff.mp hz).2⟩)
  · intro b hb c hc z hz
    exact hmeet b hb c hc z (mem_inter_iff.mpr
      ⟨(mem_inter_iff.mp hz).1, hp'p z (mem_inter_iff.mp hz).2⟩)
  · have h := hshrink (A.booleanMemValue τ (∅ : V)) (∅ : V) (by
      rw [hzero]
      apply mem_ext
      intro z
      exact ⟨fun hz ↦ absurd hz not_mem_empty, fun hz ↦ (mem_inter_iff.mp hz).1⟩)
    rw [h]
    apply mem_ext
    intro z
    exact ⟨fun hz ↦ (mem_inter_iff.mp hz).1, fun hz ↦ absurd hz not_mem_empty⟩
  · intro c hc
    exact hshrink _ _ (hinv c hc)
  · intro z hz
    exact (mem_inter_iff.mp hz).1
  · intro b hb hbq'
    rw [hkey b hb hbq']
    exact hnz b hb (subset_trans hbq' hq'q)

/-! ### Lemma 25.5 for the Boolean completion -/

/-- The two conditions of the construction, with the clauses, the membership of one in the generic
and of the other in the filter. -/
theorem exists_orbitConeData (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    (hPf : ∀ y : A.Model, Pf.Evalb ![y, p] → ∃ a : V, y = A.check a) :
    ∃ τ σ p₀ q₀ : V,
      (∀ b : V, (A.check b ∈ H ↔ ∃ q ∈ A.G, q ∈ A.booleanMemValue τ b)) ∧
      (∀ c ∈ booleanConditions A.P A.R,
        (A.check c ∈ A.boolGenericSet ↔ A.check (A.orbitInverseValue σ c) ∈ H)) ∧
      (∃ r ∈ A.G, r ∈ p₀) ∧ A.check q₀ ∈ H ∧
      A.IsOrbitConeData τ σ p₀ q₀ := by
  classical
  obtain ⟨τ, σ, hval, hd, p₁, hp₁B, hp₁G, hp₁⟩ :=
    exists_condition_valueMap_inverse_eq hAC hH hPf
  obtain ⟨p₂, hp₂B, hp₂G, hmono, hmeet, hzero, -⟩ := A.exists_orbitValue_condition hH hval
  -- intersect the two conditions inside the generic
  have hreg₁ := booleanConditions_regular hp₁B
  have hreg₂ := booleanConditions_regular hp₂B
  obtain ⟨w, hwG, hwp⟩ := meets_inter hreg₂ hreg₁ hp₂G hp₁G
  set p₃ : V := p₂ ∩ p₁ with hp₃
  have hp₃B : p₃ ∈ booleanConditions A.P A.R :=
    (mem_booleanConditions_iff _ _ _).mpr ⟨forcingRegular_inter hreg₂ hreg₁, w, hwp⟩
  have hp₃G : ∃ r ∈ A.G, r ∈ p₃ := ⟨w, hwG, hwp⟩
  have hp₃₂ : p₃ ⊆ p₂ := fun z hz ↦ (mem_inter_iff.mp hz).1
  have hp₃₁ : p₃ ⊆ p₁ := fun z hz ↦ (mem_inter_iff.mp hz).2
  have hmono₃ : ∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R, b ⊆ c →
      A.booleanMemValue τ b ∩ p₃ ⊆ A.booleanMemValue τ c := by
    intro b hb c hc hbc z hz
    exact hmono b hb c hc hbc z
      (mem_inter_iff.mpr ⟨(mem_inter_iff.mp hz).1, hp₃₂ z (mem_inter_iff.mp hz).2⟩)
  have hmeet₃ : ∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R,
      A.booleanMemValue τ b ∩ A.booleanMemValue τ c ∩ p₃ ⊆ A.booleanMemValue τ (b ∩ c) := by
    intro b hb c hc z hz
    exact hmeet b hb c hc z
      (mem_inter_iff.mpr ⟨(mem_inter_iff.mp hz).1, hp₃₂ z (mem_inter_iff.mp hz).2⟩)
  have hzero₃ : A.booleanMemValue τ (∅ : V) ∩ p₃ = (∅ : V) := by
    rw [SetTheory.mem_ext_iff] at hzero
    apply mem_ext
    intro z
    refine ⟨fun hz ↦ ?_, fun hz ↦ absurd hz not_mem_empty⟩
    obtain ⟨hzv, hzp⟩ := mem_inter_iff.mp hz
    exact (hzero z).mp (mem_inter_iff.mpr ⟨hzv, hp₃₂ z hzp⟩)
  have hinv₃ : ∀ c ∈ booleanConditions A.P A.R,
      A.booleanMemValue τ (A.orbitInverseValue σ c) ∩ p₃ = c ∩ p₃ := by
    intro c hc
    have h := hp₁ c hc
    rw [SetTheory.mem_ext_iff] at h
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨hzv, hzp⟩ := mem_inter_iff.mp hz
      exact mem_inter_iff.mpr
        ⟨(mem_inter_iff.mp ((h z).mp (mem_inter_iff.mpr ⟨hzv, hp₃₁ z hzp⟩))).1, hzp⟩
    · intro hz
      obtain ⟨hzc, hzp⟩ := mem_inter_iff.mp hz
      exact mem_inter_iff.mpr
        ⟨(mem_inter_iff.mp ((h z).mpr (mem_inter_iff.mpr ⟨hzc, hp₃₁ z hzp⟩))).1, hzp⟩
  -- a condition of the filter on which the value map does not vanish
  obtain ⟨q₀, hq₀B, hq₀H, hq₀nz⟩ :=
    exists_trace_condition_valueMap_nonzero hAC hH hval hp₃G (booleanConditions_regular hp₃B)
  -- the matching condition of the generic
  set p₀ : V := A.booleanMemValue τ q₀ ∩ p₃ with hp₀
  have hp₀B : p₀ ∈ booleanConditions A.P A.R :=
    (mem_booleanConditions_iff _ _ _).mpr
      ⟨forcingRegular_inter (A.booleanMemValue_regular τ q₀) (booleanConditions_regular hp₃B),
        hq₀nz q₀ hq₀B (subset_refl _)⟩
  have hp₀G : ∃ r ∈ A.G, r ∈ p₀ :=
    meets_inter (A.booleanMemValue_regular τ q₀) (booleanConditions_regular hp₃B)
      ((hval q₀).mp hq₀H) hp₃G
  have hp₀p₃ : p₀ ⊆ p₃ := fun z hz ↦ (mem_inter_iff.mp hz).2
  have hdata : A.IsOrbitConeData τ σ p₀ q₀ := by
    refine ⟨hp₀B, hq₀B, ?_, ?_, ?_, ?_, fun z hz ↦ (mem_inter_iff.mp hz).1, ?_⟩
    · intro b hb c hc hbc z hz
      exact hmono₃ b hb c hc hbc z
        (mem_inter_iff.mpr ⟨(mem_inter_iff.mp hz).1, hp₀p₃ z (mem_inter_iff.mp hz).2⟩)
    · intro b hb c hc z hz
      exact hmeet₃ b hb c hc z
        (mem_inter_iff.mpr ⟨(mem_inter_iff.mp hz).1, hp₀p₃ z (mem_inter_iff.mp hz).2⟩)
    · rw [SetTheory.mem_ext_iff] at hzero₃
      apply mem_ext
      intro z
      refine ⟨fun hz ↦ ?_, fun hz ↦ absurd hz not_mem_empty⟩
      obtain ⟨hzv, hzp⟩ := mem_inter_iff.mp hz
      exact (hzero₃ z).mp (mem_inter_iff.mpr ⟨hzv, hp₀p₃ z hzp⟩)
    · intro c hc
      have h := hinv₃ c hc
      rw [SetTheory.mem_ext_iff] at h
      apply mem_ext
      intro z
      constructor
      · intro hz
        obtain ⟨hzv, hzp⟩ := mem_inter_iff.mp hz
        exact mem_inter_iff.mpr
          ⟨(mem_inter_iff.mp ((h z).mp (mem_inter_iff.mpr ⟨hzv, hp₀p₃ z hzp⟩))).1, hzp⟩
      · intro hz
        obtain ⟨hzc, hzp⟩ := mem_inter_iff.mp hz
        exact mem_inter_iff.mpr
          ⟨(mem_inter_iff.mp ((h z).mpr (mem_inter_iff.mpr ⟨hzc, hp₀p₃ z hzp⟩))).1, hzp⟩
    · intro b hb hbq
      obtain ⟨z, hz⟩ := hq₀nz b hb hbq
      obtain ⟨hzv, hzp⟩ := mem_inter_iff.mp hz
      refine ⟨z, mem_inter_iff.mpr ⟨hzv, mem_inter_iff.mpr ⟨?_, hzp⟩⟩⟩
      exact hmono₃ b hb q₀ hq₀B hbq z (mem_inter_iff.mpr ⟨hzv, hzp⟩)
  exact ⟨τ, σ, p₀, q₀, hval, hd, hp₀G, hq₀H, hdata⟩

/-- The filter transfer for the map of the construction. -/
theorem orbitConeData_filter_transfer {τ σ p₀ q₀ : V} {H : A.Model}
    (hdata : A.IsOrbitConeData τ σ p₀ q₀)
    (hval : ∀ b : V, (A.check b ∈ H ↔ ∃ q ∈ A.G, q ∈ A.booleanMemValue τ b))
    (hp₀G : ∃ r ∈ A.G, r ∈ p₀) {ψ : V}
    (hψ : ∀ b ∈ booleanConditions A.P A.R, b ⊆ q₀ → ψ ‘ b = A.booleanMemValue τ b ∩ p₀) :
    ∀ c ∈ booleanConditions A.P A.R, c ⊆ q₀ →
      (A.check c ∈ H ↔ A.check (ψ ‘ c) ∈ A.boolGenericSet) := by
  intro c hc hcq
  have hval₀ := A.orbitConeData_value_mem hdata hc hcq
  rw [hψ c hc hcq, hval c, A.check_mem_boolGenericSet_iff]
  constructor
  · intro hm
    refine ⟨(mem_regularSets_iff _ _ _).mpr (booleanConditions_regular hval₀.1), ?_⟩
    exact meets_inter (A.booleanMemValue_regular τ c) (booleanConditions_regular hdata.1) hm hp₀G
  · rintro ⟨-, r, hrG, hr⟩
    exact ⟨r, hrG, (mem_inter_iff.mp hr).1⟩

/-- Jech, Set Theory, Lemma 25.5 for the Boolean completion. An orbit filter `H` and the generic
filter are carried to each other by an isomorphism of cones: there are a condition `q₀` of `H`, a
condition `p₀` met by the generic, and an isomorphism `ψ` of the cone of the completion below `q₀`
onto the cone below `p₀` with `č ∈ H` exactly when `ψ c` is met by the generic. The map is
`c ↦ ‖č ∈ τ‖ ∩ p₀` for a ground name `τ` of `H`. -/
theorem exists_orbit_cone_isomorphism (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    (hPf : ∀ y : A.Model, Pf.Evalb ![y, p] → ∃ a : V, y = A.check a) :
    ∃ p₀ ∈ booleanConditions A.P A.R, ∃ q₀ ∈ booleanConditions A.P A.R, ∃ ψ : V,
      (∃ r ∈ A.G, r ∈ p₀) ∧ A.check q₀ ∈ H ∧
      IsForcingIsomorphism
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q₀)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q₀))
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p₀)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p₀)) ψ ∧
      ∀ c ∈ booleanConditions A.P A.R, c ⊆ q₀ →
        (A.check c ∈ H ↔ A.check (ψ ‘ c) ∈ A.boolGenericSet) := by
  obtain ⟨τ, σ, p₀, q₀, hval, -, hp₀G, hq₀H, hdata⟩ := exists_orbitConeData hAC hH hPf
  obtain ⟨ψ, hiso, hψ⟩ := A.orbitConeData_isomorphism hdata
  exact ⟨p₀, hdata.1, q₀, hdata.2.1, ψ, hp₀G, hq₀H, hiso,
    A.orbitConeData_filter_transfer hdata hval hp₀G hψ⟩

/-- The isomorphism, the filter transfer and the formula for the map, from the clauses together
with the two memberships. -/
theorem exists_cone_isomorphism_of_data {τ σ p₀ q₀ : V} {H : A.Model}
    (hdata : A.IsOrbitConeData τ σ p₀ q₀)
    (hval : ∀ b : V, (A.check b ∈ H ↔ ∃ q ∈ A.G, q ∈ A.booleanMemValue τ b))
    (hp₀G : ∃ r ∈ A.G, r ∈ p₀) :
    ∃ ψ : V,
      IsForcingIsomorphism
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q₀)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q₀))
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p₀)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p₀)) ψ ∧
      (∀ c ∈ booleanConditions A.P A.R, c ⊆ q₀ →
        (A.check c ∈ H ↔ A.check (ψ ‘ c) ∈ A.boolGenericSet)) ∧
      ∀ b ∈ booleanConditions A.P A.R, b ⊆ q₀ → ψ ‘ b = A.booleanMemValue τ b ∩ p₀ := by
  obtain ⟨ψ, hiso, hψ⟩ := A.orbitConeData_isomorphism hdata
  exact ⟨ψ, hiso, A.orbitConeData_filter_transfer hdata hval hp₀G hψ, hψ⟩

/-- Shrinking the condition of the generic keeps the matching condition inside the filter. -/
theorem check_orbitInverseValue_inter_mem {σ q p' : V} {H : A.Model}
    (hfilter : ∀ u ∈ H, ∀ u' ∈ H, u ∩ u' ∈ H)
    (hd : ∀ c ∈ booleanConditions A.P A.R,
      (A.check c ∈ A.boolGenericSet ↔ A.check (A.orbitInverseValue σ c) ∈ H))
    (hp'B : p' ∈ booleanConditions A.P A.R) (hp'G : ∃ r ∈ A.G, r ∈ p')
    (hqH : A.check q ∈ H) :
    A.check (A.orbitInverseValue σ p' ∩ q) ∈ H := by
  have h1 : A.check p' ∈ A.boolGenericSet :=
    (A.check_mem_boolGenericSet_iff p').mpr
      ⟨(mem_regularSets_iff _ _ _).mpr (booleanConditions_regular hp'B), hp'G⟩
  rw [A.check_inter]
  exact hfilter _ ((hd p' hp'B).mp h1) _ hqH

/-- Below a condition of the orbit filter there is a regular cone of a condition of the base poset
whose check lies in the filter. The conditions that are such a cone below `q` and the conditions
disjoint from `q` are dense in the completion, and `H` is generic over the ground model; the
second kind would put the empty set in `H`. -/
theorem exists_trace_coneRegular_below (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    {q : V} (hqB : q ∈ booleanConditions A.P A.R) (hqH : A.check q ∈ H) :
    ∃ r ∈ A.P, coneRegular A.P A.R r ⊆ q ∧ A.check (coneRegular A.P A.R r) ∈ H := by
  classical
  set D : V := sep (booleanConditions A.P A.R)
    (fun b ↦ (∃ r ∈ A.P, b = coneRegular A.P A.R r ∧ b ⊆ q) ∨ b ∩ q = (∅ : V))
    (by definability) with hDdef
  have hmemD : ∀ b : V, b ∈ D ↔ b ∈ booleanConditions A.P A.R ∧
      ((∃ r ∈ A.P, b = coneRegular A.P A.R r ∧ b ⊆ q) ∨ b ∩ q = (∅ : V)) :=
    fun b ↦ by rw [hDdef]; exact mem_sep_iff
  have hqreg := booleanConditions_regular hqB
  have hDdense : ForcingDense (booleanConditions A.P A.R) (booleanOrder A.P A.R) D := by
    refine ⟨sep_subset, fun u hu ↦ ?_⟩
    have hureg := booleanConditions_regular hu
    by_cases hne : ∃ z : V, z ∈ u ∩ q
    · obtain ⟨z, hz⟩ := hne
      have hzP : z ∈ A.P := hureg.1 z (mem_inter_iff.mp hz).1
      have hsub : coneRegular A.P A.R z ⊆ u ∩ q :=
        coneRegular_subset_of_mem A.order (forcingRegular_inter hureg hqreg) hz
      refine ⟨coneRegular A.P A.R z, (hmemD _).mpr
        ⟨coneRegular_mem_booleanConditions A.order hzP,
          Or.inl ⟨z, hzP, rfl, fun t ht ↦ (mem_inter_iff.mp (hsub t ht)).2⟩⟩, ?_⟩
      exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨coneRegular_mem_booleanConditions A.order hzP, hu,
          fun t ht ↦ (mem_inter_iff.mp (hsub t ht)).1⟩
    · refine ⟨u, (hmemD u).mpr ⟨hu, Or.inr (mem_ext (fun z ↦
        ⟨fun hz ↦ absurd ⟨z, hz⟩ hne, fun hz ↦ absurd hz not_mem_empty⟩))⟩,
        (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hu, hu, subset_refl _⟩⟩
  have hgen := filterTrace_externalGeneric hAC hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2.1
    hH.2.2.2.2.2.1
  obtain ⟨b, hbT, hbD⟩ := hgen.2 D hDdense
  have hbH : A.check b ∈ H := hbT
  obtain ⟨hbB, hcases⟩ := (hmemD b).mp hbD
  rcases hcases with ⟨r, hrP, rfl, hsub⟩ | hempty
  · exact ⟨r, hrP, hsub, hbH⟩
  · exfalso
    have hinter : A.check (b ∩ q) ∈ H := by
      rw [A.check_inter]
      exact hH.2.2.1 _ hbH _ hqH
    rw [hempty] at hinter
    obtain ⟨z, hz⟩ := hH.2.2.2.1 _ hinter
    rw [A.check_empty] at hz
    exact not_mem_empty hz

/-- Lemma 25.5 with the condition on the side of the generic taken to be the regular cone of a
condition of the base poset lying in the generic filter. -/
theorem exists_orbit_cone_isomorphism_coneRegular_left (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    (hPf : ∀ y : A.Model, Pf.Evalb ![y, p] → ∃ a : V, y = A.check a) :
    ∃ r ∈ A.G, ∃ q₀ ∈ booleanConditions A.P A.R, ∃ ψ : V,
      A.check q₀ ∈ H ∧
      IsForcingIsomorphism
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q₀)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q₀))
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (coneRegular A.P A.R r))
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (coneRegular A.P A.R r))) ψ ∧
      ∀ c ∈ booleanConditions A.P A.R, c ⊆ q₀ →
        (A.check c ∈ H ↔ A.check (ψ ‘ c) ∈ A.boolGenericSet) := by
  obtain ⟨τ, σ, p₀, q₀, hval, hd, hp₀G, hq₀H, hdata⟩ := exists_orbitConeData hAC hH hPf
  obtain ⟨r, hrG, hrp⟩ := hp₀G
  have hrP : r ∈ A.P := A.generic.1.1 r hrG
  have hp'B : coneRegular A.P A.R r ∈ booleanConditions A.P A.R :=
    coneRegular_mem_booleanConditions A.order hrP
  have hp'p : coneRegular A.P A.R r ⊆ p₀ :=
    coneRegular_subset_of_mem A.order (booleanConditions_regular hdata.1) hrp
  have hp'G : ∃ t ∈ A.G, t ∈ coneRegular A.P A.R r :=
    ⟨r, hrG, self_mem_coneRegular A.order hrP⟩
  have hdata' := A.orbitConeData_shrink_left hdata hp'B hp'p
  have hq'H : A.check (A.orbitInverseValue σ (coneRegular A.P A.R r) ∩ q₀) ∈ H :=
    A.check_orbitInverseValue_inter_mem hH.2.2.1 hd hp'B hp'G hq₀H
  obtain ⟨ψ, hiso, htr, -⟩ := A.exists_cone_isomorphism_of_data hdata' hval hp'G
  exact ⟨r, hrG, _, hdata'.2.1, ψ, hq'H, hiso, htr⟩

/-- Lemma 25.5 with the condition on the side of the orbit filter taken to be the regular cone of
a condition of the base poset. -/
theorem exists_orbit_cone_isomorphism_coneRegular_right (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    (hPf : ∀ y : A.Model, Pf.Evalb ![y, p] → ∃ a : V, y = A.check a) :
    ∃ r' ∈ A.P, ∃ p₀ ∈ booleanConditions A.P A.R, ∃ ψ : V,
      (∃ t ∈ A.G, t ∈ p₀) ∧ A.check (coneRegular A.P A.R r') ∈ H ∧
      IsForcingIsomorphism
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (coneRegular A.P A.R r'))
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (coneRegular A.P A.R r')))
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p₀)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p₀)) ψ ∧
      ∀ c ∈ booleanConditions A.P A.R, c ⊆ coneRegular A.P A.R r' →
        (A.check c ∈ H ↔ A.check (ψ ‘ c) ∈ A.boolGenericSet) := by
  obtain ⟨τ, σ, p₀, q₀, hval, hd, hp₀G, hq₀H, hdata⟩ := exists_orbitConeData hAC hH hPf
  obtain ⟨r', hr'P, hr'q, hr'H⟩ := exists_trace_coneRegular_below hAC hH hdata.2.1 hq₀H
  have hq'B : coneRegular A.P A.R r' ∈ booleanConditions A.P A.R :=
    coneRegular_mem_booleanConditions A.order hr'P
  have hdata' := A.orbitConeData_shrink_right hdata hq'B hr'q
  have hp'G : ∃ t ∈ A.G, t ∈ A.booleanMemValue τ (coneRegular A.P A.R r') ∩ p₀ :=
    meets_inter (A.booleanMemValue_regular τ _) (booleanConditions_regular hdata.1)
      ((hval _).mp hr'H) hp₀G
  obtain ⟨ψ, hiso, htr, -⟩ := A.exists_cone_isomorphism_of_data hdata' hval hp'G
  exact ⟨r', hr'P, _, hdata'.1, ψ, hp'G, hr'H, hiso, htr⟩

/-! ### The isomorphism is the identity on the support algebra -/

/-- Lemma 25.5 for an orbit filter over a support of nice names: the condition on the side of the
generic can be taken to be the regular cone of a condition of the generic filter, and below the
two conditions the isomorphism is the identity on the support algebra, `ψ (d ∩ q₀) = d ∩ p₀`. -/
theorem exists_orbit_cone_isomorphism_support (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {s k : V} [IsFunction s] (hsdom : domain s = k)
    (hs : ∀ i ∈ k, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P
      ((ω : V) ×ˢ (ω : V)) (s ‘ i))
    {p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p H)
    (hPf : ∀ y : A.Model, Pf.Evalb ![y, p] → ∃ a : V, y = A.check a) :
    ∃ r ∈ A.G, ∃ q₀ ∈ booleanConditions A.P A.R, ∃ ψ : V,
      A.check q₀ ∈ H ∧
      IsForcingIsomorphism
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q₀)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q₀))
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (coneRegular A.P A.R r))
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (coneRegular A.P A.R r))) ψ ∧
      (∀ c ∈ booleanConditions A.P A.R, c ⊆ q₀ →
        (A.check c ∈ H ↔ A.check (ψ ‘ c) ∈ A.boolGenericSet)) ∧
      ∀ d ∈ supportAlgebraBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s),
        d ∩ q₀ ∈ booleanConditions A.P A.R →
        ψ ‘ (d ∩ q₀) = d ∩ coneRegular A.P A.R r := by
  classical
  obtain ⟨τ, σ, p₀, q₀, hval, hd, hp₀G, hq₀H, hdata⟩ := exists_orbitConeData hAC hH hPf
  obtain ⟨p₁, hp₁B, hp₁G, hp₁⟩ :=
    exists_condition_booleanMemValue_eq_on_supportAlgebra hAC hsdom hs hH hval
  obtain ⟨w, hwG, hw⟩ := meets_inter (booleanConditions_regular hdata.1)
    (booleanConditions_regular hp₁B) hp₀G hp₁G
  have hwP : w ∈ A.P := A.generic.1.1 w hwG
  set p' : V := coneRegular A.P A.R w with hp'
  have hp'B : p' ∈ booleanConditions A.P A.R := coneRegular_mem_booleanConditions A.order hwP
  have hp'G : ∃ t ∈ A.G, t ∈ p' := ⟨w, hwG, self_mem_coneRegular A.order hwP⟩
  have hp'p₀ : p' ⊆ p₀ := coneRegular_subset_of_mem A.order
    (booleanConditions_regular hdata.1) (mem_inter_iff.mp hw).1
  have hp'p₁ : p' ⊆ p₁ := coneRegular_subset_of_mem A.order
    (booleanConditions_regular hp₁B) (mem_inter_iff.mp hw).2
  have hdata' := A.orbitConeData_shrink_left hdata hp'B hp'p₀
  have hq'H : A.check (A.orbitInverseValue σ p' ∩ q₀) ∈ H :=
    A.check_orbitInverseValue_inter_mem hH.2.2.1 hd hp'B hp'G hq₀H
  obtain ⟨ψ, hiso, htr, hψ⟩ := A.exists_cone_isomorphism_of_data hdata' hval hp'G
  refine ⟨w, hwG, _, hdata'.2.1, ψ, hq'H, hiso, htr, fun dd hdd hddq ↦ ?_⟩
  have hddB : dd ∈ booleanConditions A.P A.R := by
    refine (mem_booleanConditions_iff _ _ _).mpr
      ⟨((mem_algebraPreimage_iff _ _ _ _).mp hdd).1, ?_⟩
    obtain ⟨z, hz⟩ := booleanConditions_nonempty hddq
    exact ⟨z, (mem_inter_iff.mp hz).1⟩
  have hsupp : A.booleanMemValue τ dd ∩ p' = dd ∩ p' := by
    have h := hp₁ dd hdd hddB
    rw [SetTheory.mem_ext_iff] at h
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨hzv, hzp⟩ := mem_inter_iff.mp hz
      exact mem_inter_iff.mpr
        ⟨(mem_inter_iff.mp ((h z).mp (mem_inter_iff.mpr ⟨hzv, hp'p₁ z hzp⟩))).1, hzp⟩
    · intro hz
      obtain ⟨hzd, hzp⟩ := mem_inter_iff.mp hz
      exact mem_inter_iff.mpr
        ⟨(mem_inter_iff.mp ((h z).mpr (mem_inter_iff.mpr ⟨hzd, hp'p₁ z hzp⟩))).1, hzp⟩
  rw [hψ _ hddq (fun z hz ↦ (mem_inter_iff.mp hz).2),
    A.orbitConeData_inter_eq hdata' hddB hdata'.2.1]
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨hzi, hzp⟩ := mem_inter_iff.mp hz
    have hz' : z ∈ A.booleanMemValue τ dd ∩ p' :=
      mem_inter_iff.mpr ⟨(mem_inter_iff.mp hzi).1, hzp⟩
    rw [hsupp] at hz'
    exact mem_inter_iff.mpr ⟨(mem_inter_iff.mp hz').1, hzp⟩
  · intro hz
    obtain ⟨hzd, hzp⟩ := mem_inter_iff.mp hz
    have hz' : z ∈ dd ∩ p' := mem_inter_iff.mpr ⟨hzd, hzp⟩
    rw [← hsupp] at hz'
    exact mem_inter_iff.mpr
      ⟨mem_inter_iff.mpr ⟨(mem_inter_iff.mp hz').1, hdata'.2.2.2.2.2.2.1 z hzp⟩, hzp⟩

end ForcingContext

end ZFVP
