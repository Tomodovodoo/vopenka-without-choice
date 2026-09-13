import ZFVP.ModelTheory.OmegaJonssonEmbedding
import ZFVP.SetTheory.PiOneInitialOrdinal
import ZFVP.SetTheory.BoundedNaturals
import ZFVP.SetTheory.FunctionValue

/-! A Pi-two formula for the omega-Jonsson predicate, and transfer of the predicate along a coded
self-embedding of a `C(2)` rank stage. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Bounded form of `IsFunction`: every element is a Kuratowski pair and the pairs are single
valued. The witnesses `x`, `y` are found inside the pair itself, so all quantifiers are bounded. -/
def boundedIsFunctionFormula : SetTheorySemisentence 1 :=
  “F. (∀ p ∈ F, ∃ d ∈ p, ∃ x ∈ d, ∃ y ∈ d, !boundedKpairFormula p x y) ∧
    ∀ p ∈ F, ∀ q ∈ F, ∀ d ∈ p, ∀ x ∈ d, ∀ y ∈ d, ∀ e ∈ q, ∀ z ∈ e,
      !boundedKpairFormula p x y → !boundedKpairFormula q x z → y = z”

theorem boundedIsFunctionFormula_bounded : IsBoundedSetFormula boundedIsFunctionFormula :=
  .and
    (.all (.bvar 0) (.exs (.bvar 0) (.exs (.bvar 0) (.exs (.bvar 1)
      (boundedKpairFormula_bounded.subst _)))))
    (.all (.bvar 0) (.all (.bvar 1) (.all (.bvar 1) (.all (.bvar 0) (.all (.bvar 1)
      (.all (.bvar 3) (.all (.bvar 0)
        (.or (boundedKpairFormula_bounded.subst _).neg
          (.or (boundedKpairFormula_bounded.subst _).neg (.rel _ _))))))))))

/-- Bounded form of `x ∈ domain F`: the pair witnessing membership lies in `F`, and its second
coordinate lies inside that pair. -/
def boundedMemDomainFormula : SetTheorySemisentence 2 :=
  “x F. ∃ p ∈ F, ∃ d ∈ p, ∃ y ∈ d, !boundedKpairFormula p x y”

theorem boundedMemDomainFormula_bounded : IsBoundedSetFormula boundedMemDomainFormula :=
  .exs (.bvar 1) (.exs (.bvar 0) (.exs (.bvar 0) (boundedKpairFormula_bounded.subst _)))

/-- The second clause of the omega-Jonsson predicate, with the quantifier over `domain F` replaced
by quantifiers bounded by `F` and its elements. -/
def omegaJonssonDomainConditionFormula : SetTheorySemisentence 2 :=
  “F l. ∀ p ∈ F, ∀ d ∈ p, ∀ x ∈ d, !boundedMemDomainFormula x F →
    x ⊆ l ∧ ∃ v ∈ l, !boundedPairMemberFormula F x v”

theorem omegaJonssonDomainConditionFormula_bounded :
    IsBoundedSetFormula omegaJonssonDomainConditionFormula :=
  .all (.bvar 0) (.all (.bvar 0) (.all (.bvar 0)
    (.or (boundedMemDomainFormula_bounded.subst _).neg
      (.and (isSubsetOf_bounded.subst _)
        (.exs (.bvar 4) (boundedPairMemberFormula_bounded.subst _))))))

/-- `a` carries a surjection from `ω`. The two existentials are the only unbounded ones left in the
omega-Jonsson predicate. -/
def omegaJonssonEnumerationFormula : SetTheorySemisentence 1 :=
  “a. ∃ g w, !boundedOmegaFormula w ∧ !boundedFunctionFormula g w a ∧
    ∀ y ∈ a, ∃ n ∈ w, !boundedPairMemberFormula g n y”

theorem omegaJonssonEnumerationFormula_sigmaOne : IsSigmaFormula 1 omegaJonssonEnumerationFormula :=
  .exs (.exs (.bounded
    (.and (boundedOmegaFormula_bounded.subst _)
      (.and (boundedFunctionFormula_bounded.subst _)
        (.all (.bvar 2) (.exs (.bvar 1) (boundedPairMemberFormula_bounded.subst _)))))))

/-- The positive part of the omega-Jonsson clause: some countably enumerated subset of `A` lies in
the domain of `F` and is sent to `c`. -/
def omegaJonssonWitnessFormula : SetTheorySemisentence 3 :=
  “F A c. ∃ a, !boundedMemDomainFormula a F ∧ a ⊆ A ∧ !omegaJonssonEnumerationFormula a ∧
    !boundedPairMemberFormula F a c”

theorem omegaJonssonWitnessFormula_sigmaOne : IsSigmaFormula 1 omegaJonssonWitnessFormula :=
  .exs (.and (.bounded (boundedMemDomainFormula_bounded.subst _))
    (.and (.bounded (isSubsetOf_bounded.subst _))
      (.and (omegaJonssonEnumerationFormula_sigmaOne.subst _)
        (.bounded (boundedPairMemberFormula_bounded.subst _)))))

/-- The omega-Jonsson predicate in prenex Pi-two shape: the injection witnessing `l ≤# A` is pulled
out as a universal quantifier, and the enumeration is the only remaining unbounded existential. -/
def omegaJonssonPiTwoFormula : SetTheorySemisentence 2 :=
  “F l. !boundedIsFunctionFormula F ∧ !omegaJonssonDomainConditionFormula F l ∧
    ∀ A i, (A ⊆ l ∧ !boundedInjectionFormula i l A) → ∀ c ∈ l, !omegaJonssonWitnessFormula F A c”

theorem omegaJonssonPiTwoFormula_piTwo : IsPiFormula 2 omegaJonssonPiTwoFormula :=
  .and (.bounded (boundedIsFunctionFormula_bounded.subst _))
    (.and (.bounded (omegaJonssonDomainConditionFormula_bounded.subst _))
      (.all (.all (.or
        (.bounded (IsBoundedSetFormula.and (isSubsetOf_bounded.subst _)
          (boundedInjectionFormula_bounded.subst _)).neg)
        (.boundedAll (.bvar 3) (omegaJonssonWitnessFormula_sigmaOne.subst _).raise)))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedIsFunctionFormula_defined :
    ℒₛₑₜ-predicate[V] IsFunction via boundedIsFunctionFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp only [boundedIsFunctionFormula]
  simp
  constructor
  · rintro ⟨hpair, huniq⟩
    have hsingle : ∀ x y z : V, ⟨x, y⟩ₖ ∈ v 0 → ⟨x, z⟩ₖ ∈ v 0 → y = z := by
      intro x y z hy hz
      refine huniq _ hy _ hz {x, y} (by simp [kpair]) x (by simp) y (by simp) {x, z}
        (by simp [kpair]) z (by simp) rfl rfl
    have hsub : v 0 ⊆ domain (v 0) ×ˢ range (v 0) := by
      intro p hp
      obtain ⟨d, hd, x, hx, y, hy, rfl⟩ := hpair p hp
      exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hp, mem_range_of_kpair_mem hp⟩
    refine isFunction_iff.mpr (mem_function.intro hsub ?_)
    intro x hx
    obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
    exact ⟨y, hy, fun z hz ↦ hsingle x z y hz hy⟩
  · intro hF
    constructor
    · intro p hp
      obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hp
      exact ⟨{x, y}, by simp [kpair], x, by simp, y, by simp, rfl⟩
    · intro p hp q hq d hd x hx y hy e he z hz hpxy hqxz
      exact IsFunction.unique (hpxy ▸ hp) (hqxz ▸ hq)

instance boundedMemDomainFormula_defined :
    ℒₛₑₜ-relation[V] (fun x F : V ↦ x ∈ domain F) via boundedMemDomainFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp only [boundedMemDomainFormula]
  simp
  constructor
  · rintro ⟨d, y, hp, -, -⟩
    exact mem_domain_of_kpair_mem hp
  · intro hx
    obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
    exact ⟨{v 0, y}, y, hy, by simp [kpair], by simp⟩

/-- The second clause of the omega-Jonsson predicate written with quantifiers over `F`. -/
def OmegaJonssonDomainCondition (F l : V) : Prop :=
  ∀ p ∈ F, ∀ d ∈ p, ∀ x ∈ d, x ∈ domain F → x ⊆ l ∧ ∃ v ∈ l, ⟨x, v⟩ₖ ∈ F

instance omegaJonssonDomainConditionFormula_defined :
    ℒₛₑₜ-relation[V] OmegaJonssonDomainCondition via omegaJonssonDomainConditionFormula :=
  ⟨fun v ↦ by simp [omegaJonssonDomainConditionFormula, OmegaJonssonDomainCondition]⟩

theorem omegaJonssonDomainCondition_iff {F l : V} [IsFunction F] :
    OmegaJonssonDomainCondition F l ↔ ∀ x ∈ domain F, x ⊆ l ∧ F ‘ x ∈ l := by
  constructor
  · intro h x hx
    obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
    obtain ⟨hsub, v, hv, hxv⟩ := h ⟨x, y⟩ₖ hy {x, y} (by simp [kpair]) x (by simp) hx
    exact ⟨hsub, value_eq_of_kpair_mem hxv ▸ hv⟩
  · intro h p hp d hd x hx hxd
    obtain ⟨hsub, hval⟩ := h x hxd
    exact ⟨hsub, F ‘ x, hval, kpair_value_mem hxd⟩

/-- `a` is the range of a function from `ω`. -/
def OmegaJonssonEnumerable (a : V) : Prop := ∃ g, g ∈ a ^ (ω : V) ∧ range g = a

instance omegaJonssonEnumerationFormula_defined :
    ℒₛₑₜ-predicate[V] OmegaJonssonEnumerable via omegaJonssonEnumerationFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp only [omegaJonssonEnumerationFormula, OmegaJonssonEnumerable]
  simp
  constructor
  · rintro ⟨g, hg, honto⟩
    refine ⟨g, hg, ?_⟩
    apply SetTheory.subset_antisymm
    · exact range_subset_of_subset_prod (subset_prod_of_mem_function hg)
    · intro y hy
      obtain ⟨n, -, hn⟩ := honto y hy
      exact mem_range_of_kpair_mem hn
  · rintro ⟨g, hg, hrange⟩
    refine ⟨g, hg, ?_⟩
    intro y hy
    rw [← hrange] at hy
    obtain ⟨n, hn⟩ := mem_range_iff.mp hy
    exact ⟨n, (kpair_mem_iff.mp (subset_prod_of_mem_function hg _ hn)).1, hn⟩

/-- Some countably enumerated subset of `A` lies in the domain of `F` and is sent to `c`. -/
def OmegaJonssonWitness (F A c : V) : Prop :=
  ∃ a, a ∈ domain F ∧ a ⊆ A ∧ OmegaJonssonEnumerable a ∧ ⟨a, c⟩ₖ ∈ F

instance omegaJonssonWitnessFormula_defined :
    ℒₛₑₜ-relation₃[V] OmegaJonssonWitness via omegaJonssonWitnessFormula :=
  ⟨fun v ↦ by simp [omegaJonssonWitnessFormula, OmegaJonssonWitness]⟩

theorem eval_omegaJonssonPiTwoFormula (F lam : V) :
    omegaJonssonPiTwoFormula.Evalb ![F, lam] ↔ IsOmegaJonsson F lam := by
  simp only [omegaJonssonPiTwoFormula]
  simp [IsOmegaJonsson, CardLE, OmegaJonssonWitness, OmegaJonssonEnumerable]
  intro hfun
  have := hfun
  constructor
  · rintro ⟨hdom, hcl⟩
    refine ⟨omegaJonssonDomainCondition_iff.mp hdom, ?_⟩
    intro A hA i hi hinj c hc
    obtain ⟨g, h1, h2, h3, h4⟩ := hcl A i hA hi hinj c hc
    exact ⟨g, h1, h2, h3, value_eq_of_kpair_mem h4⟩
  · rintro ⟨hdom, hcl⟩
    refine ⟨omegaJonssonDomainCondition_iff.mpr hdom, ?_⟩
    intro A i hA hi hinj c hc
    obtain ⟨g, h1, h2, h3, h4⟩ := hcl A hA i hi hinj c hc
    exact ⟨g, h1, h2, h3, h4 ▸ kpair_value_mem h1⟩

theorem omegaJonssonPiTwoFormula_defines :
    Defined (fun v : Fin 2 → V ↦ IsOmegaJonsson (v 0) (v 1)) omegaJonssonPiTwoFormula := by
  refine ⟨fun v ↦ ?_⟩
  have hv : ![v 0, v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [← hv]
  exact eval_omegaJonssonPiTwoFormula (v 0) (v 1)

/-- The image of an omega-Jonsson function under a coded self-embedding of a `C(2)` rank stage is
omega-Jonsson for the image of the ordinal. -/
theorem IsOmegaJonsson.value_cn_two {δ f F lam : V} (hδ : Cn 2 δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
    (hF : F ∈ hierarchy δ) (hlam : lam ∈ hierarchy δ) (hJ : IsOmegaJonsson F lam) :
    IsOmegaJonsson (f ‘ F) (f ‘ lam) := by
  have hv : ∀ i, (![F, lam] : Fin 2 → V) i ∈ hierarchy δ := by
    intro i
    exact Fin.cases hF (fun j ↦ Fin.cases hlam (fun t ↦ Fin.elim0 t) j) i
  have : Defined (fun v : Fin 2 → V ↦ IsOmegaJonsson (v 0) (v 1)) omegaJonssonPiTwoFormula :=
    omegaJonssonPiTwoFormula_defines
  have hiff := rankSelfEmbedding_defined_iff (m := 1) hδ h omegaJonssonPiTwoFormula_piTwo
    (fun w ↦ IsOmegaJonsson (w 0) (w 1)) ![F, lam] hv
  exact hiff.mp hJ

end ZFVP
