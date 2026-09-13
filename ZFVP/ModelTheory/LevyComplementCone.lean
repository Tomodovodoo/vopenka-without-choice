import ZFVP.ModelTheory.LevyConeIsomorphism

/-! Complementary cone isomorphisms for the Levy collapse.

An isomorphism of the cone `B|b0` with the cone `B|c0` of the Boolean completion lifts to an
automorphism of `B` only when the complementary cones `B|¬b0` and `B|¬c0` are matched as well
(`exists_booleanAutomorphism_of_cone_isomorphisms`). For cones of the form `b0 = coneRegular r`
and `c0 = coneRegular r'` with `r`, `r'` conditions of `Coll(ω, <κ)` the complementary
isomorphism is free: an automorphism `π` of the collapse with `π r = r'` lifts to an automorphism
`Θ = booleanLift π` of `B`, and an automorphism carries the complement of `b0` to the complement
of `c0`, so it restricts to an isomorphism of both pairs of cones at once.

The automorphism of the collapse is built here by swapping values. If `p` and `q` are conditions
with the same domain, the map exchanging, at every coordinate `z`, the value `p(z)` with the
value `q(z)` and leaving all other values alone is an involution of `Coll(ω, <κ)` carrying `p`
to `q`. It needs no hypothesis on `κ`: the two swapped values sit in the same column, so they are
interchangeable. Any two conditions extend to conditions with the same domain, which is the
shape-matching step.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Swapping the values of two conditions -/

/-- The swapped value, as a function of the entry `w = ⟨z, γ⟩`. Taking the entry as a single
argument keeps the arity at three, which is what the definability tactic can compose. -/
noncomputable def levySwapEntry (p q w : V) : V :=
  ⋃ˢ {δ ∈ ℘ (kpair.π₂ w ∪ (p ‘ (kpair.π₁ w) ∪ q ‘ (kpair.π₁ w))) ;
    (w ∈ p ∧ kpair.π₁ w ∈ domain q ∧ δ = q ‘ (kpair.π₁ w)) ∨
    (w ∈ q ∧ kpair.π₁ w ∈ domain p ∧ w ∉ p ∧ δ = p ‘ (kpair.π₁ w)) ∨
    (¬ ((w ∈ p ∧ kpair.π₁ w ∈ domain q) ∨ (w ∈ q ∧ kpair.π₁ w ∈ domain p)) ∧ δ = kpair.π₂ w)}

instance levySwapEntry_definable : ℒₛₑₜ-function₃[V] levySwapEntry := by
  have h : ℒₛₑₜ-relation₄[V] (fun d p q w ↦ ∀ x, x ∈ d ↔ ∃ δ,
      (δ ∈ ℘ (kpair.π₂ w ∪ (p ‘ (kpair.π₁ w) ∪ q ‘ (kpair.π₁ w))) ∧
        ((w ∈ p ∧ kpair.π₁ w ∈ domain q ∧ δ = q ‘ (kpair.π₁ w)) ∨
        (w ∈ q ∧ kpair.π₁ w ∈ domain p ∧ w ∉ p ∧ δ = p ‘ (kpair.π₁ w)) ∨
        (¬ ((w ∈ p ∧ kpair.π₁ w ∈ domain q) ∨ (w ∈ q ∧ kpair.π₁ w ∈ domain p)) ∧
          δ = kpair.π₂ w))) ∧ x ∈ δ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = levySwapEntry (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [levySwapEntry, mem_sUnion_iff, mem_sep_iff]

/-- The value obtained from `γ` at the coordinate `z` by exchanging the value of `p` at `z` with
the value of `q` at `z`. Away from those two values, and off the common domain of `p` and `q`,
it is `γ` itself. The ambient set of the separation is a power set only to have a definable set
containing the three candidate values. -/
noncomputable def levySwapValue (p q z γ : V) : V := levySwapEntry p q ⟨z, γ⟩ₖ

theorem levySwapValue_eq (p q z γ : V) :
    levySwapValue p q z γ = ⋃ˢ {δ ∈ ℘ (γ ∪ (p ‘ z ∪ q ‘ z)) ;
      (⟨z, γ⟩ₖ ∈ p ∧ z ∈ domain q ∧ δ = q ‘ z) ∨
      (⟨z, γ⟩ₖ ∈ q ∧ z ∈ domain p ∧ ⟨z, γ⟩ₖ ∉ p ∧ δ = p ‘ z) ∨
      (¬ ((⟨z, γ⟩ₖ ∈ p ∧ z ∈ domain q) ∨ (⟨z, γ⟩ₖ ∈ q ∧ z ∈ domain p)) ∧ δ = γ)} := by
  simp only [levySwapValue, levySwapEntry, kpair.π₁_kpair, kpair.π₂_kpair]

/-- Reading off the swapped value: if exactly one candidate satisfies the clause, that is the
value. -/
theorem levySwapValue_of_unique {p q z γ δ : V}
    (h : ∀ ε, (ε ∈ ℘ (γ ∪ (p ‘ z ∪ q ‘ z)) ∧
      ((⟨z, γ⟩ₖ ∈ p ∧ z ∈ domain q ∧ ε = q ‘ z) ∨
      (⟨z, γ⟩ₖ ∈ q ∧ z ∈ domain p ∧ ⟨z, γ⟩ₖ ∉ p ∧ ε = p ‘ z) ∨
      (¬ ((⟨z, γ⟩ₖ ∈ p ∧ z ∈ domain q) ∨ (⟨z, γ⟩ₖ ∈ q ∧ z ∈ domain p)) ∧ ε = γ))) ↔ ε = δ) :
    levySwapValue p q z γ = δ := by
  apply mem_ext
  intro x
  rw [levySwapValue_eq, mem_sUnion_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ((h y).mp (mem_sep_iff.mp hy)) ▸ hxy
  · intro hx
    exact ⟨δ, mem_sep_iff.mpr ((h δ).mpr rfl), hx⟩

theorem self_mem_swapPower (p q z γ : V) : γ ∈ ℘ (γ ∪ (p ‘ z ∪ q ‘ z)) :=
  mem_power_iff.mpr (subset_union_left _ _)

theorem left_mem_swapPower (p q z γ : V) : p ‘ z ∈ ℘ (γ ∪ (p ‘ z ∪ q ‘ z)) :=
  mem_power_iff.mpr (subset_trans (subset_union_left _ _) (subset_union_right _ _))

theorem right_mem_swapPower (p q z γ : V) : q ‘ z ∈ ℘ (γ ∪ (p ‘ z ∪ q ‘ z)) :=
  mem_power_iff.mpr (subset_trans (subset_union_right _ _) (subset_union_right _ _))

/-- On a value of `p` at a coordinate where `q` is defined, the swap gives the value of `q`. -/
theorem levySwapValue_left {p q z γ : V} (hp : ⟨z, γ⟩ₖ ∈ p) (hq : z ∈ domain q) :
    levySwapValue p q z γ = q ‘ z := by
  apply levySwapValue_of_unique
  intro ε
  constructor
  · rintro ⟨-, (⟨-, -, he⟩ | ⟨-, -, hnp, -⟩ | ⟨hn, -⟩)⟩
    · exact he
    · exact absurd hp hnp
    · exact absurd (Or.inl ⟨hp, hq⟩) hn
  · rintro rfl
    exact ⟨right_mem_swapPower p q z γ, Or.inl ⟨hp, hq, rfl⟩⟩

/-- On a value of `q` that is not a value of `p`, at a coordinate where `p` is defined, the swap
gives the value of `p`. -/
theorem levySwapValue_right {p q z γ : V} (hq : ⟨z, γ⟩ₖ ∈ q) (hp : z ∈ domain p)
    (hnp : ⟨z, γ⟩ₖ ∉ p) : levySwapValue p q z γ = p ‘ z := by
  apply levySwapValue_of_unique
  intro ε
  constructor
  · rintro ⟨-, (⟨hmem, -, -⟩ | ⟨-, -, -, he⟩ | ⟨hn, -⟩)⟩
    · exact absurd hmem hnp
    · exact he
    · exact absurd (Or.inr ⟨hq, hp⟩) hn
  · rintro rfl
    exact ⟨left_mem_swapPower p q z γ, Or.inr (Or.inl ⟨hq, hp, hnp, rfl⟩)⟩

/-- Everywhere else the swap is the identity. -/
theorem levySwapValue_fixed {p q z γ : V}
    (hn : ¬ ((⟨z, γ⟩ₖ ∈ p ∧ z ∈ domain q) ∨ (⟨z, γ⟩ₖ ∈ q ∧ z ∈ domain p))) :
    levySwapValue p q z γ = γ := by
  apply levySwapValue_of_unique
  intro ε
  constructor
  · rintro ⟨-, (⟨h1, h2, -⟩ | ⟨h1, h2, -, -⟩ | ⟨-, he⟩)⟩
    · exact absurd (Or.inl ⟨h1, h2⟩) hn
    · exact absurd (Or.inr ⟨h1, h2⟩) hn
    · exact he
  · rintro rfl
    exact ⟨self_mem_swapPower p q z ε, Or.inr (Or.inr ⟨hn, rfl⟩)⟩

/-- The swapped value is one of three things: the old value, the value of `p`, or the value
of `q`. -/
theorem levySwapValue_cases (p q z γ : V) :
    levySwapValue p q z γ = γ ∨ (z ∈ domain p ∧ levySwapValue p q z γ = p ‘ z) ∨
      (z ∈ domain q ∧ levySwapValue p q z γ = q ‘ z) := by
  by_cases h1 : ⟨z, γ⟩ₖ ∈ p ∧ z ∈ domain q
  · exact Or.inr (Or.inr ⟨h1.2, levySwapValue_left h1.1 h1.2⟩)
  · by_cases h2 : ⟨z, γ⟩ₖ ∈ q ∧ z ∈ domain p
    · have hnp : ⟨z, γ⟩ₖ ∉ p := fun h ↦ h1 ⟨h, mem_domain_of_kpair_mem h2.1⟩
      exact Or.inr (Or.inl ⟨h2.2, levySwapValue_right h2.1 h2.2 hnp⟩)
    · exact Or.inl (levySwapValue_fixed (by rintro (h | h); exacts [h1 h, h2 h]))

/-- The swap is an involution on values. -/
theorem levySwapValue_involutive {p q : V} (hpf : IsFunction p) (hqf : IsFunction q) (z γ : V) :
    levySwapValue p q z (levySwapValue p q z γ) = γ := by
  have := hpf
  have := hqf
  by_cases h1 : ⟨z, γ⟩ₖ ∈ p ∧ z ∈ domain q
  · rw [levySwapValue_left h1.1 h1.2]
    have hqz : ⟨z, q ‘ z⟩ₖ ∈ q := kpair_value_mem h1.2
    have hpz : z ∈ domain p := mem_domain_of_kpair_mem h1.1
    by_cases h2 : ⟨z, q ‘ z⟩ₖ ∈ p
    · rw [levySwapValue_left h2 h1.2]
      exact IsFunction.unique h2 h1.1
    · rw [levySwapValue_right hqz hpz h2]
      exact value_eq_of_kpair_mem h1.1
  · by_cases h2 : ⟨z, γ⟩ₖ ∈ q ∧ z ∈ domain p
    · have hnp : ⟨z, γ⟩ₖ ∉ p := fun h ↦ h1 ⟨h, mem_domain_of_kpair_mem h2.1⟩
      rw [levySwapValue_right h2.1 h2.2 hnp]
      have hpz : ⟨z, p ‘ z⟩ₖ ∈ p := kpair_value_mem h2.2
      have hqz : z ∈ domain q := mem_domain_of_kpair_mem h2.1
      rw [levySwapValue_left hpz hqz]
      exact value_eq_of_kpair_mem h2.1
    · have hn : ¬ ((⟨z, γ⟩ₖ ∈ p ∧ z ∈ domain q) ∨ (⟨z, γ⟩ₖ ∈ q ∧ z ∈ domain p)) := by
        rintro (h | h)
        exacts [h1 h, h2 h]
      rw [levySwapValue_fixed hn, levySwapValue_fixed hn]

/-! ### The induced map on conditions -/

/-- The condition `r` with the values of `p` and `q` swapped at every coordinate. -/
noncomputable def levySwapCondition (p q r : V) : V :=
  definableGraph (domain r) (fun z ↦ levySwapEntry p q ⟨z, r ‘ z⟩ₖ) (by definability)

instance levySwapCondition_isFunction (p q r : V) : IsFunction (levySwapCondition p q r) :=
  definableGraph_isFunction _ _ _

theorem levySwapCondition_domain (p q r : V) : domain (levySwapCondition p q r) = domain r :=
  domain_definableGraph _ _ _

theorem levySwapCondition_value {p q r z : V} (hz : z ∈ domain r) :
    (levySwapCondition p q r) ‘ z = levySwapValue p q z (r ‘ z) :=
  value_definableGraph _ _ _ hz

theorem levySwapEntry_kpair (p q z γ : V) :
    levySwapEntry p q ⟨z, γ⟩ₖ = levySwapValue p q z γ := rfl

theorem kpair_mem_levySwapCondition_iff (p q r z γ : V) :
    ⟨z, γ⟩ₖ ∈ levySwapCondition p q r ↔ z ∈ domain r ∧ γ = levySwapValue p q z (r ‘ z) :=
  pair_mem_definableGraph_iff _ _ _ _ _

/-- Swapping values sends conditions to conditions. -/
theorem levySwapCondition_mem {κ p q r : V} (hp : p ∈ levyCollapse κ) (hq : q ∈ levyCollapse κ)
    (hr : r ∈ levyCollapse κ) : levySwapCondition p q r ∈ levyCollapse κ := by
  have := levyCollapse_isFunction hp
  have := levyCollapse_isFunction hq
  have := levyCollapse_isFunction hr
  have hpsub := ((mem_finitePartialFunctions _ _ _).mp (levyCollapse_finitePartialFunction hp)).1
  have hqsub := ((mem_finitePartialFunctions _ _ _).mp (levyCollapse_finitePartialFunction hq)).1
  have hrsub := ((mem_finitePartialFunctions _ _ _).mp (levyCollapse_finitePartialFunction hr)).1
  refine (mem_levyCollapse_iff κ _).mpr ⟨(mem_finitePartialFunctions _ _ _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · intro w hw
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hw
    obtain ⟨hz, rfl⟩ := (kpair_mem_levySwapCondition_iff p q r x y).mp hw
    set z := x with hzdef
    have hzD : z ∈ (ω : V) ×ˢ κ :=
      finitePartialFunction_domain (levyCollapse_finitePartialFunction hr) z hz
    refine kpair_mem_iff.mpr ⟨hzD, ?_⟩
    rcases levySwapValue_cases p q z (r ‘ z) with he | ⟨hzp, he⟩ | ⟨hzq, he⟩
    · rw [he]
      exact (kpair_mem_iff.mp (hrsub _ (kpair_value_mem hz))).2
    · rw [he]
      exact (kpair_mem_iff.mp (hpsub _ (kpair_value_mem hzp))).2
    · rw [he]
      exact (kpair_mem_iff.mp (hqsub _ (kpair_value_mem hzq))).2
  · exact definableGraph_isFunction _ _ _
  · rw [levySwapCondition_domain]
    exact ((mem_finitePartialFunctions _ _ _).mp (levyCollapse_finitePartialFunction hr)).2.2
  · intro n α β hmem
    obtain ⟨hz, rfl⟩ := (kpair_mem_levySwapCondition_iff p q r _ _).mp hmem
    rcases levySwapValue_cases p q ⟨n, α⟩ₖ (r ‘ ⟨n, α⟩ₖ) with he | ⟨hzp, he⟩ | ⟨hzq, he⟩
    · rw [he]
      exact levyCollapse_value hr (kpair_value_mem hz)
    · rw [he]
      exact levyCollapse_value hp (kpair_value_mem hzp)
    · rw [he]
      exact levyCollapse_value hq (kpair_value_mem hzq)

/-- Swapping values twice is the identity. -/
theorem levySwapCondition_involutive {p q r : V} (hpf : IsFunction p) (hqf : IsFunction q)
    (hrf : IsFunction r) : levySwapCondition p q (levySwapCondition p q r) = r := by
  have := hrf
  apply functions_eq_of_domain_values
  · rw [levySwapCondition_domain, levySwapCondition_domain]
  · intro z hz
    rw [levySwapCondition_domain, levySwapCondition_domain] at hz
    rw [levySwapCondition_value (by rw [levySwapCondition_domain]; exact hz),
      levySwapCondition_value hz, levySwapValue_involutive hpf hqf]

/-- Swapping values is monotone for inclusion. -/
theorem levySwapCondition_mono {p q r s : V} (hrf : IsFunction r) (hsf : IsFunction s)
    (hrs : r ⊆ s) : levySwapCondition p q r ⊆ levySwapCondition p q s := by
  have := hrf
  have := hsf
  intro w hw
  obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hw
  obtain ⟨hz, rfl⟩ := (kpair_mem_levySwapCondition_iff p q r x y).mp hw
  have hmem : ⟨x, r ‘ x⟩ₖ ∈ s := hrs _ (kpair_value_mem hz)
  have hzs : x ∈ domain s := mem_domain_of_kpair_mem hmem
  refine (kpair_mem_levySwapCondition_iff p q s x _).mpr ⟨hzs, ?_⟩
  rw [value_eq_of_kpair_mem hmem]

/-- Two conditions with the same domain are exchanged by the swap. -/
theorem levySwapCondition_self {p q : V} (hpf : IsFunction p) (hqf : IsFunction q)
    (hdom : domain p = domain q) : levySwapCondition p q p = q := by
  have := hpf
  have := hqf
  apply functions_eq_of_domain_values
  · rw [levySwapCondition_domain, hdom]
  · intro z hz
    rw [levySwapCondition_domain] at hz
    rw [levySwapCondition_value hz,
      levySwapValue_left (kpair_value_mem hz) (hdom ▸ hz)]

/-! ### The automorphism of the collapse -/

theorem levySwapCondition_definable (p q : V) :
    ℒₛₑₜ-function₁ (fun r : V ↦ levySwapCondition p q r) := by
  have h : ℒₛₑₜ-relation[V] (fun s r ↦ ∀ w, w ∈ s ↔
      ∃ z ∈ domain r, w = ⟨z, levySwapEntry p q ⟨z, r ‘ z⟩ₖ⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = levySwapCondition p q (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [levySwapCondition, mem_definableGraph_iff]

/-- The automorphism of `Coll(ω, <κ)` exchanging the values of `p` and `q`. -/
noncomputable def levySwapAutomorphism (κ p q : V) : V :=
  definableGraph (levyCollapse κ) (fun r ↦ levySwapCondition p q r)
    (levySwapCondition_definable p q)

theorem levySwapAutomorphism_value {κ p q r : V} (hr : r ∈ levyCollapse κ) :
    (levySwapAutomorphism κ p q) ‘ r = levySwapCondition p q r :=
  value_definableGraph _ _ _ hr

theorem levySwapAutomorphism_isForcingAutomorphism {κ p q : V} (hp : p ∈ levyCollapse κ)
    (hq : q ∈ levyCollapse κ) :
    IsForcingAutomorphism (levyCollapse κ) (levyOrder κ) (levySwapAutomorphism κ p q) := by
  have hpf := levyCollapse_isFunction hp
  have hqf := levyCollapse_isFunction hq
  show IsForcingIsomorphism (levyCollapse κ) (levyOrder κ) (levyCollapse κ) (levyOrder κ) _
  unfold levyOrder levySwapAutomorphism
  exact reverseInclusion_isomorphism_of_inverse (fun r ↦ levySwapCondition p q r)
    (fun r ↦ levySwapCondition p q r) (levySwapCondition_definable p q)
    (fun r hr ↦ levySwapCondition_mem hp hq hr)
    (fun r hr ↦ levySwapCondition_mem hp hq hr)
    (fun r hr ↦ levySwapCondition_involutive hpf hqf (levyCollapse_isFunction hr))
    (fun r hr ↦ levySwapCondition_involutive hpf hqf (levyCollapse_isFunction hr))
    (fun r hr s hs h ↦ levySwapCondition_mono (levyCollapse_isFunction hr)
      (levyCollapse_isFunction hs) h)
    (fun r hr s hs h ↦ levySwapCondition_mono (levyCollapse_isFunction hr)
      (levyCollapse_isFunction hs) h)

/-- Two conditions of the Levy collapse with the same domain are carried to each other by an
automorphism of the collapse. -/
theorem exists_levyAutomorphism_of_domain_eq {κ r r' : V} (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ) (hdom : domain r = domain r') :
    ∃ π, IsForcingAutomorphism (levyCollapse κ) (levyOrder κ) π ∧ π ‘ r = r' :=
  ⟨levySwapAutomorphism κ r r', levySwapAutomorphism_isForcingAutomorphism hr hr',
    by rw [levySwapAutomorphism_value hr]
       exact levySwapCondition_self (levyCollapse_isFunction hr) (levyCollapse_isFunction hr')
         hdom⟩

/-! ### Restricting an automorphism to a cone -/

/-- An automorphism carrying the cone below `b` into the cone below `c` restricts to a forcing
isomorphism of the two cones. -/
theorem exists_coneRestriction_isomorphism {Q S Θ b c : V} (hΘ : IsForcingAutomorphism Q S Θ)
    (hbc : ∀ x ∈ Q, ⟨x, b⟩ₖ ∈ S ↔ ⟨Θ ‘ x, c⟩ₖ ∈ S) :
    ∃ f, IsForcingIsomorphism (forcingCone Q S b) (restrictedOrder S (forcingCone Q S b))
      (forcingCone Q S c) (restrictedOrder S (forcingCone Q S c)) f := by
  have : IsFunction Θ := IsFunction.of_mem hΘ.1
  have hFP : ∀ x ∈ forcingCone Q S b, Θ ‘ x ∈ forcingCone Q S c := by
    intro x hx
    obtain ⟨hxQ, hxb⟩ := (mem_forcingCone_iff _ _ _ _).mp hx
    exact (mem_forcingCone_iff _ _ _ _).mpr
      ⟨function_value_mem hΘ.1 hxQ, (hbc x hxQ).mp hxb⟩
  have hGQ : ∀ y ∈ forcingCone Q S c, (converseGraph Θ) ‘ y ∈ forcingCone Q S b := by
    intro y hy
    obtain ⟨hyQ, hyc⟩ := (mem_forcingCone_iff _ _ _ _).mp hy
    obtain ⟨a, ha, rfl⟩ := forcingAutomorphism_surjective hΘ y hyQ
    rw [converseGraph_value_value hΘ.1 hΘ.2.1 ha]
    exact (mem_forcingCone_iff _ _ _ _).mpr ⟨ha, (hbc a ha).mpr hyc⟩
  refine ⟨definableGraph (forcingCone Q S b) (fun x ↦ Θ ‘ x) (by definability),
    isForcingIsomorphism_of_inverse (fun x ↦ Θ ‘ x) (fun y ↦ (converseGraph Θ) ‘ y)
      (by definability) hFP hGQ ?_ ?_ ?_⟩
  · intro x hx
    exact converseGraph_value_value hΘ.1 hΘ.2.1 ((mem_forcingCone_iff _ _ _ _).mp hx).1
  · intro y hy
    exact value_converseGraph_value hΘ.1 hΘ.2.1
      (hΘ.2.2.1.symm ▸ ((mem_forcingCone_iff _ _ _ _).mp hy).1)
  · intro x hx y hy
    have hxQ := ((mem_forcingCone_iff _ _ _ _).mp hx).1
    have hyQ := ((mem_forcingCone_iff _ _ _ _).mp hy).1
    rw [kpair_mem_restrictedOrder_iff, kpair_mem_restrictedOrder_iff]
    simp only [hx, hy, hFP x hx, hFP y hy, and_true]
    exact hΘ.2.2.2 x hxQ y hyQ

/-! ### The two cone isomorphisms for a pair of conditions -/

section Cones

variable {κ r r' : V}

/-- The lift of an automorphism of the collapse to the Boolean completion carries the regular
cone of `r` to the regular cone of the image of `r`. -/
theorem booleanLift_coneRegular {π : V}
    (hπ : IsForcingAutomorphism (levyCollapse κ) (levyOrder κ) π) (hr : r ∈ levyCollapse κ) :
    (booleanLift (levyCollapse κ) (levyOrder κ) π) ‘ (coneRegular (levyCollapse κ) (levyOrder κ) r)
      = coneRegular (levyCollapse κ) (levyOrder κ) (π ‘ r) := by
  rw [booleanLift_value (coneRegular_mem_booleanConditions (levyCollapse_poset κ).1 hr)]
  exact imageAction_coneRegular hπ hr

/-- The two cones of a condition and its image are matched by the lifted automorphism: the
positive cone by the image of the regular cone, the complementary cone by the image of its
negation. -/
theorem levy_cone_isomorphism_of_domain_eq (hr : r ∈ levyCollapse κ) (hr' : r' ∈ levyCollapse κ)
    (hdom : domain r = domain r') :
    ∃ f, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (coneRegular (levyCollapse κ) (levyOrder κ) r))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (coneRegular (levyCollapse κ) (levyOrder κ) r)))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (coneRegular (levyCollapse κ) (levyOrder κ) r'))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (coneRegular (levyCollapse κ) (levyOrder κ) r'))) f := by
  obtain ⟨π, hπ, hval⟩ := exists_levyAutomorphism_of_domain_eq hr hr' hdom
  have hΘ := booleanLift_isForcingAutomorphism hπ
  have hb0 := coneRegular_mem_booleanConditions (levyCollapse_poset κ).1 hr
  have himg : (booleanLift (levyCollapse κ) (levyOrder κ) π) ‘
      (coneRegular (levyCollapse κ) (levyOrder κ) r) =
      coneRegular (levyCollapse κ) (levyOrder κ) r' := by
    rw [booleanLift_coneRegular hπ hr, hval]
  refine exists_coneRestriction_isomorphism hΘ (fun x hx ↦ ?_)
  rw [← himg]
  exact hΘ.2.2.2 x hx _ hb0

/-- The complementary cone isomorphism, in the form asked for by
`exists_booleanAutomorphism_of_cone_isomorphisms`. -/
theorem levy_complement_cone_isomorphism_of_domain_eq (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ) (hdom : domain r = domain r') :
    ∃ g, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingNegation (levyCollapse κ) (levyOrder κ)
          (coneRegular (levyCollapse κ) (levyOrder κ) r)))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r))))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingNegation (levyCollapse κ) (levyOrder κ)
          (coneRegular (levyCollapse κ) (levyOrder κ) r')))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r')))) g := by
  obtain ⟨π, hπ, hval⟩ := exists_levyAutomorphism_of_domain_eq hr hr' hdom
  have hΘ := booleanLift_isForcingAutomorphism hπ
  have hb0 := coneRegular_mem_booleanConditions (levyCollapse_poset κ).1 hr
  have hb0sub : coneRegular (levyCollapse κ) (levyOrder κ) r ⊆ levyCollapse κ :=
    ((mem_booleanConditions_iff _ _ _).mp hb0).1.1
  have himg : imageAction π (forcingNegation (levyCollapse κ) (levyOrder κ)
      (coneRegular (levyCollapse κ) (levyOrder κ) r)) =
      forcingNegation (levyCollapse κ) (levyOrder κ)
        (coneRegular (levyCollapse κ) (levyOrder κ) r') := by
    rw [forcingNegation_image hπ hb0sub, imageAction_coneRegular hπ hr, hval]
  refine exists_coneRestriction_isomorphism hΘ (fun x hx ↦ ?_)
  by_cases hn0 : forcingNegation (levyCollapse κ) (levyOrder κ)
      (coneRegular (levyCollapse κ) (levyOrder κ) r) ∈
      booleanConditions (levyCollapse κ) (levyOrder κ)
  · have hΘn : (booleanLift (levyCollapse κ) (levyOrder κ) π) ‘
        (forcingNegation (levyCollapse κ) (levyOrder κ)
          (coneRegular (levyCollapse κ) (levyOrder κ) r)) =
        forcingNegation (levyCollapse κ) (levyOrder κ)
          (coneRegular (levyCollapse κ) (levyOrder κ) r') := by
      rw [booleanLift_value hn0]
      exact himg
    rw [← hΘn]
    exact hΘ.2.2.2 x hx _ hn0
  · have hempty : forcingNegation (levyCollapse κ) (levyOrder κ)
        (coneRegular (levyCollapse κ) (levyOrder κ) r) = (∅ : V) := by
      by_contra hne
      obtain ⟨s, hs⟩ : ∃ s, s ∈ forcingNegation (levyCollapse κ) (levyOrder κ)
          (coneRegular (levyCollapse κ) (levyOrder κ) r) := by
        by_contra hno
        exact hne (mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hno,
          fun hz ↦ absurd hz not_mem_empty⟩))
      exact hn0 ((mem_booleanConditions_iff _ _ _).mpr
        ⟨forcingNegation_regular (levyCollapse_poset κ).1
          ((mem_booleanConditions_iff _ _ _).mp hb0).1.2.1, s, hs⟩)
    have hempty' : forcingNegation (levyCollapse κ) (levyOrder κ)
        (coneRegular (levyCollapse κ) (levyOrder κ) r') = (∅ : V) := by
      rw [← himg, hempty, imageAction_empty]
    rw [hempty, hempty']
    constructor
    · intro h
      exact absurd ((kpair_mem_booleanOrder_iff _ _ _ _).mp h).2.1
        (fun hb ↦ not_mem_empty ((mem_booleanConditions_iff _ _ _).mp hb).2.choose_spec)
    · intro h
      exact absurd ((kpair_mem_booleanOrder_iff _ _ _ _).mp h).2.1
        (fun hb ↦ not_mem_empty ((mem_booleanConditions_iff _ _ _).mp hb).2.choose_spec)

/-- Both cone isomorphisms at once, fed to the lifting lemma: for conditions `r`, `r'` of the
Levy collapse with the same domain there is an automorphism of the Boolean completion that agrees
below the regular cone of `r` with the isomorphism of the cones. -/
theorem levy_exists_booleanAutomorphism_of_domain_eq (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ) (hdom : domain r = domain r') :
    ∃ Θ ∈ forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)),
      ∃ f, IsForcingIsomorphism
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (coneRegular (levyCollapse κ) (levyOrder κ) r))
        (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ))
            (coneRegular (levyCollapse κ) (levyOrder κ) r)))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (coneRegular (levyCollapse κ) (levyOrder κ) r'))
        (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ))
            (coneRegular (levyCollapse κ) (levyOrder κ) r'))) f ∧
        ∀ b ∈ booleanConditions (levyCollapse κ) (levyOrder κ),
          b ∩ coneRegular (levyCollapse κ) (levyOrder κ) r ∈
            booleanConditions (levyCollapse κ) (levyOrder κ) →
          (Θ ‘ b) ∩ coneRegular (levyCollapse κ) (levyOrder κ) r' =
            f ‘ (b ∩ coneRegular (levyCollapse κ) (levyOrder κ) r) := by
  obtain ⟨f, hf⟩ := levy_cone_isomorphism_of_domain_eq hr hr' hdom
  obtain ⟨g, hg⟩ := levy_complement_cone_isomorphism_of_domain_eq hr hr' hdom
  obtain ⟨Θ, hΘmem, hΘval, -⟩ := exists_booleanAutomorphism_of_cone_isomorphisms
    (levyCollapse_poset κ).1 (coneRegular_mem_booleanConditions (levyCollapse_poset κ).1 hr)
    (coneRegular_mem_booleanConditions (levyCollapse_poset κ).1 hr') hf hg
  exact ⟨Θ, hΘmem, f, hf, hΘval⟩

end Cones

/-! ### Matching the shapes -/

/-- Any two conditions of the Levy collapse have extensions with the same domain: fill each one
in on the coordinates used by the other. Extension is superset, since the order is reverse
inclusion. -/
theorem exists_common_domain_extensions {κ r r' : V} (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ) :
    ∃ r₁ r₁', r₁ ∈ levyCollapse κ ∧ r₁' ∈ levyCollapse κ ∧ r ⊆ r₁ ∧ r' ⊆ r₁' ∧
      domain r₁ = domain r₁' := by
  have := levyCollapse_isFunction hr
  have := levyCollapse_isFunction hr'
  set A : V := {w ∈ r' ; kpair.π₁ w ∉ domain r} with hA
  set B : V := {w ∈ r ; kpair.π₁ w ∉ domain r'} with hB
  have hAsub : A ⊆ r' := sep_subset
  have hBsub : B ⊆ r := sep_subset
  have hA' : A ∈ levyCollapse κ := levyCollapse_subset hr' hAsub
  have hB' : B ∈ levyCollapse κ := levyCollapse_subset hr hBsub
  have h1 : r ∪ A ∈ levyCollapse κ := by
    refine levyCollapse_union hr hA' (fun x y z hxy hxz ↦ ?_)
    obtain ⟨-, hnot⟩ := mem_sep_iff.mp hxz
    simp only [kpair.π₁_kpair] at hnot
    exact absurd (mem_domain_of_kpair_mem hxy) hnot
  have h2 : r' ∪ B ∈ levyCollapse κ := by
    refine levyCollapse_union hr' hB' (fun x y z hxy hxz ↦ ?_)
    obtain ⟨-, hnot⟩ := mem_sep_iff.mp hxz
    simp only [kpair.π₁_kpair] at hnot
    exact absurd (mem_domain_of_kpair_mem hxy) hnot
  have hdomain : ∀ s t : V, IsFunction s → IsFunction t →
      domain (s ∪ {w ∈ t ; kpair.π₁ w ∉ domain s}) = domain s ∪ domain t := by
    intro s t hs ht
    have := hs
    have := ht
    apply mem_ext
    intro x
    rw [mem_domain_iff, mem_union_iff]
    constructor
    · rintro ⟨y, hy⟩
      rcases mem_union_iff.mp hy with hy | hy
      · exact Or.inl (mem_domain_of_kpair_mem hy)
      · exact Or.inr (mem_domain_of_kpair_mem (mem_sep_iff.mp hy).1)
    · rintro (hx | hx)
      · exact ⟨s ‘ x, mem_union_iff.mpr (Or.inl (kpair_value_mem hx))⟩
      · by_cases hxs : x ∈ domain s
        · exact ⟨s ‘ x, mem_union_iff.mpr (Or.inl (kpair_value_mem hxs))⟩
        · refine ⟨t ‘ x, mem_union_iff.mpr (Or.inr (mem_sep_iff.mpr ⟨kpair_value_mem hx, ?_⟩))⟩
          simpa only [kpair.π₁_kpair] using hxs
  refine ⟨r ∪ A, r' ∪ B, h1, h2, subset_union_left _ _, subset_union_left _ _, ?_⟩
  rw [hA, hB, hdomain r r' inferInstance inferInstance, hdomain r' r inferInstance inferInstance]
  apply mem_ext
  intro x
  simp only [mem_union_iff]
  tauto

/-- Shape matching and the automorphism together: any two conditions of the Levy collapse have
extensions that an automorphism of the collapse carries to each other. The two cone theorems
above then apply to the pair of extensions. -/
theorem exists_levyAutomorphism_of_extensions {κ r r' : V} (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ) :
    ∃ r₁ r₁' π, r₁ ∈ levyCollapse κ ∧ r₁' ∈ levyCollapse κ ∧ r ⊆ r₁ ∧ r' ⊆ r₁' ∧
      domain r₁ = domain r₁' ∧
      IsForcingAutomorphism (levyCollapse κ) (levyOrder κ) π ∧ π ‘ r₁ = r₁' := by
  obtain ⟨r₁, r₁', h1, h2, hs1, hs2, hdom⟩ := exists_common_domain_extensions hr hr'
  obtain ⟨π, hπ, hval⟩ := exists_levyAutomorphism_of_domain_eq h1 h2 hdom
  exact ⟨r₁, r₁', π, h1, h2, hs1, hs2, hdom, hπ, hval⟩

end ZFVP
