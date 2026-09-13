import ZFVP.ModelTheory.SolovaySymmetricSubalgebraModel
import ZFVP.ModelTheory.LevySupportAlgebraClosure
import ZFVP.ModelTheory.LevyGaloisFactor

/-! Where the support algebra route to Lemma 9.3 stops.

`ZFVP/ModelTheory/SolovaySymmetricSubalgebraModel.lean` reduces the forward half of
Karagila-Schilhan Lemma 9.3 to two hypotheses: the Galois step `GaloisStep`, and the
uniform-support hypothesis `hfix` of `inSubalgebraModel_of_uniformSupport`, which asks that every
name in the closure of `τ`, not just `τ` itself, be fixed by the forced stabilizer of the one
support `E`. This file records that the second hypothesis is not a technicality that a later wave
can remove: dropping it makes the conclusion false, while the Galois step at `E = ∅` is already
proved (`levy_galoisStep_empty` in `ZFVP/ModelTheory/LevyGaloisFactor.lean`).

Two things are proved, in the language of the task that asked for them: (c) and (b). Not (a): no
concrete name of the Solovay system with a value outside the ground model is built here, so the
refutation of the general statement is conditional on a nontriviality hypothesis that is stated
explicitly and not proved.

(c) is `not_uniformSupport_empty_of_value_not_ground`. The route to it is the evaluation lemma
`ofName_eq_check_of_subnamesForcedIn`: if every condition forces every subname inside the name
closure of `τ` to belong to its name (`SubnamesForcedIn`), then the value of `τ` is the check of
the ground set `groundValue τ` obtained by forgetting the conditions. As with
`forcedEqual_nameReduct`, the proof is an induction on names in the ground model producing a forced
equality, since the valuation recursion inside the extension is not available. The hypothesis holds
in two cases. First, when every name in the closure of `τ` is fixed by every automorphism of the
completion of a weakly homogeneous poset: then each Boolean value `‖ν ∈ μ‖` is invariant, hence the
top by `eq_top_of_imageAction_fixed` (`subnamesForcedIn_of_invariant_closure`). Since the forced
stabilizer of `∅` is the whole automorphism group (`forcedStabilizer_empty`), this is exactly the
uniform-support hypothesis at `E = ∅`, so a name of the Solovay system satisfying it has a ground
value, and a name whose value is not a ground set fails it. Second, when `τ` is a name over the
sub-poset of the base support algebra of the empty support, which is the one-element poset
(`eq_top_of_mem_subalgebraConditions_empty`), so all conditions of the name are the top.

(b) is `not_solovaySupportAlgebraClaim_of_nonground_invariant_name`. The second case above gives
`exists_check_eq_of_inSubalgebraModel_empty`: the intermediate extension by the support algebra of
the empty support is the ground model. The support algebra of `∅` is the two-element algebra
(`supportAlgebra_empty_subset`, using `generatedSubalgebra_minimal`), and the only nonzero
condition of `RO(P)` whose cone lies in it is the top. So if the forward half of Lemma 9.3 held for
every hereditarily symmetric name at a support algebra of one of its supports
(`SolovaySupportAlgebraClaim`), then every name supported by `∅`, that is fixed by the whole
automorphism group up to forced equality, would have a ground value. One name with a non-ground
value and empty support refutes the claim. The expected witness is the name for the set of reals of
the symmetric model, which is fixed by every automorphism while its subnames, the names for the
individual reals, are not; building that name and proving its value is not a ground set is what is
left, and is the whole gap between (b) and (a).

What is not claimed. Nothing here refutes `inSubalgebraModel_of_uniformSupport` or
`inSubalgebraModel_of_hereditarilySymmetric`, which are true as stated; what is refuted is the
statement obtained by dropping the uniform-support hypothesis, and only under the nontriviality
hypothesis named above. The statements about `E = ∅` are about `E = ∅` and say nothing about a
general finite support `E`, where the Galois step itself is still open. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The ground set coded by a name all of whose subnames are forced in -/

/-- The step of the recursion: forget the conditions and keep the values of the subnames. -/
noncomputable def groundValueStep (_μ f : V) : V := range f

instance groundValueStep_definable : ℒₛₑₜ-function₂[V] groundValueStep := by
  unfold groundValueStep
  definability

/-- The ground set read off a name by ignoring the conditions: `{groundValue ν : ν ∈ dom τ}`. -/
noncomputable def groundValue (τ : V) : V :=
  subnameRecursion groundValueStep groundValueStep_definable τ

instance groundValue_definable : ℒₛₑₜ-function₁[V] groundValue := by
  unfold groundValue
  infer_instance

theorem mem_groundValue_iff (τ z : V) :
    z ∈ groundValue τ ↔ ∃ ν ∈ domain τ, z = groundValue ν := by
  have he := subnameRecursion_equation groundValueStep groundValueStep_definable τ
  rw [groundValue, he, groundValueStep, range_definableGraph, repl_spec]
  exact Iff.rfl

theorem groundValue_mem_of_mem_domain {τ ν : V} (hν : ν ∈ domain τ) :
    groundValue ν ∈ groundValue τ :=
  (mem_groundValue_iff τ _).mpr ⟨ν, hν, rfl⟩

/-! ### Names whose subnames are forced in by every condition -/

/-- Every condition forces every subname of every name in the closure of `τ` to belong to it. -/
def SubnamesForcedIn (P R τ : V) : Prop :=
  ∀ μ ∈ nameClosure τ, ∀ ν ∈ domain μ, atomicMembership P R ν μ = P

/-- A name all of whose subnames are forced in by every condition is forced equal to the check of
the ground set that forgets its conditions. -/
theorem forcedEqual_checkName_groundValue {P R one τ : V} (hR : IsForcingPreorder P R)
    (hone : IsForcingTop P R one) (hτ : SubnamesForcedIn P R τ) :
    ForcedEqual P R τ (checkName one (groundValue τ)) := by
  have h := projectedRank_induction (nameClosure τ) (fun x : V ↦ x) (by definability)
    (fun μ ↦ ForcedEqual P R μ (checkName one (groundValue μ))) (by definability) ?_
  · exact h τ (mem_nameClosure_self τ)
  intro μ hμ ih p hp
  have ihν : ∀ ν ∈ domain μ, ForcedEqual P R ν (checkName one (groundValue ν)) := by
    intro ν hν
    obtain ⟨s, hs⟩ := mem_domain_iff.mp hν
    exact ih ν (nameClosure_closed τ μ hμ ν hν) (rank_subname_lt hs)
  refine (mem_atomicEquality_iff _ _ _ _ _).mpr ⟨hp, ?_, ?_⟩
  · -- every subname of `μ` is matched by its check inside the check name
    intro υ s hs q hq _ _
    have hυd : υ ∈ domain μ := mem_domain_iff.mpr ⟨s, hs⟩
    refine ⟨q, hq, hR.2.1 q hq, checkName one (groundValue υ), one, ?_, hone.2 q hq, ?_⟩
    · exact (mem_checkName_iff one (groundValue μ) _).mpr
        ⟨groundValue υ, groundValue_mem_of_mem_domain hυd, rfl⟩
    · exact ihν υ hυd q hq
  · -- every entry of the check name is matched by a subname of `μ`, using that it is forced in
    intro ν t ht q hq _ _
    obtain ⟨x, hx, hpair⟩ := (mem_checkName_iff one (groundValue μ) _).mp ht
    obtain ⟨hνe, -⟩ := kpair_iff.mp hpair
    obtain ⟨υ, hυ, hxe⟩ := (mem_groundValue_iff μ x).mp hx
    have hforced : q ∈ atomicMembership P R υ μ := by
      rw [hτ μ hμ υ hυ]
      exact hq
    obtain ⟨-, hh⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hforced
    obtain ⟨r, hr, hrq, υ', s, hs, hrs, he⟩ := hh q hq (hR.2.1 q hq)
    have hsym : r ∈ atomicEquality P R (checkName one (groundValue υ)) υ := by
      have h1 := ihν υ hυ r hr
      rwa [atomicEquality_symm P R υ (checkName one (groundValue υ))] at h1
    have hfin : r ∈ atomicEquality P R (checkName one (groundValue υ)) υ' :=
      atomicEquality_trans hR _ _ _ _ hsym he
    refine ⟨r, hr, hrq, υ', s, hs, hrs, ?_⟩
    rw [hνe, hxe, atomicEquality_symm P R υ' (checkName one (groundValue υ))]
    exact hfin

/-! ### The value of such a name is a ground set -/

namespace ForcingContext

/-- If every condition forces every subname inside the name closure of `τ` to belong to its name,
then the value of `τ` is the check of a ground set. -/
theorem ofName_eq_check_of_subnamesForcedIn (A : ForcingContext V) (τ : ForcingName A.P)
    (hτ : SubnamesForcedIn A.P A.R τ.val) :
    A.ofName τ = A.check (groundValue τ.val) := by
  obtain ⟨p, hpG⟩ := A.generic.1.2.1
  refine (forcingQuotientMk_eq_iff A.P A.R A.G A.order A.generic.1 τ
    ⟨checkName A.one (groundValue τ.val), checkName_isName A.top.1 _⟩).mpr ⟨p, hpG, ?_⟩
  exact forcedEqual_checkName_groundValue A.order A.top hτ p (A.generic.1.1 p hpG)

/-- The value of such a name lies in the ground model. -/
theorem exists_check_eq_ofName_of_subnamesForcedIn (A : ForcingContext V) (τ : ForcingName A.P)
    (hτ : SubnamesForcedIn A.P A.R τ.val) : ∃ x : V, A.ofName τ = A.check x :=
  ⟨groundValue τ.val, A.ofName_eq_check_of_subnamesForcedIn τ hτ⟩

end ForcingContext

/-! ### The forced stabilizer of the empty support -/

theorem forcedStabilizer_empty (P R Γ : V) : forcedStabilizer P R Γ (∅ : V) = Γ := by
  apply mem_ext
  intro π
  rw [mem_forcedStabilizer]
  exact ⟨And.left, fun h ↦ ⟨h, fun τ hτ ↦ (not_mem_empty hτ).elim⟩⟩

/-- A Boolean value `‖ν ∈ μ‖` between two names fixed by every automorphism of the completion of a
weakly homogeneous poset is the top, as soon as `ν` is a subname of `μ`. -/
theorem atomicMembership_eq_top_of_invariant {P R one μ ν : V} (hP : ∃ p, p ∈ P)
    (hR : IsForcingPreorder P R) (hhom : IsWeaklyHomogeneous P R one)
    (hμ : IsForcingName (booleanConditions P R) μ) (hν : ν ∈ domain μ)
    (hfix : ∀ Θ ∈ forcingAutomorphisms (booleanConditions P R) (booleanOrder P R),
      nameAction Θ μ = μ ∧ nameAction Θ ν = ν) :
    atomicMembership (booleanConditions P R) (booleanOrder P R) ν μ = booleanConditions P R := by
  have hBo : IsForcingPreorder (booleanConditions P R) (booleanOrder P R) :=
    (booleanOrder_poset P R).1
  obtain ⟨C, hC⟩ := mem_domain_iff.mp hν
  obtain ⟨σ', q, hqB, hz, -⟩ := (forcingName_iff _ _).mp hμ _ hC
  have hCB : C ∈ booleanConditions P R := by
    rw [(kpair_iff.mp hz).2]
    exact hqB
  clear hz hqB
  have hne : ∃ D, D ∈ atomicMembership (booleanConditions P R) (booleanOrder P R) ν μ :=
    ⟨C, atomicMembership_of_pair hBo hCB hC⟩
  have hA : atomicMembership (booleanConditions P R) (booleanOrder P R) ν μ ∈
      booleanConditions (booleanConditions P R) (booleanOrder P R) :=
    (mem_booleanConditions_iff _ _ _).mpr ⟨atomicMembership_regular hBo ν μ, hne⟩
  have hνn : IsForcingName (booleanConditions P R) ν :=
    forcingName_mem_closure hμ (nameClosure_closed μ μ (mem_nameClosure_self μ) ν hν)
  refine eq_top_of_imageAction_fixed (booleanOrder_weaklyHomogeneous hP hR hhom) hA ?_
  intro Θ hΘ _
  obtain ⟨hμΘ, hνΘ⟩ := hfix Θ ((mem_forcingAutomorphisms_iff _ _ _).mpr hΘ)
  exact imageAction_atomicMembership_eq_self hΘ hνn hμ hνΘ hμΘ

/-- If every name in the closure of `τ` is fixed by every automorphism of the completion, then
every condition forces every subname inside the closure to belong to its name. -/
theorem subnamesForcedIn_of_invariant_closure {P R one τ : V} (hP : ∃ p, p ∈ P)
    (hR : IsForcingPreorder P R) (hhom : IsWeaklyHomogeneous P R one)
    (hτ : IsForcingName (booleanConditions P R) τ)
    (hfix : ∀ μ ∈ nameClosure τ, ∀ Θ ∈ forcingAutomorphisms (booleanConditions P R)
      (booleanOrder P R), nameAction Θ μ = μ) :
    SubnamesForcedIn (booleanConditions P R) (booleanOrder P R) τ := by
  intro μ hμ ν hν
  have hνc : ν ∈ nameClosure τ := nameClosure_closed τ μ hμ ν hν
  exact atomicMembership_eq_top_of_invariant hP hR hhom (forcingName_mem_closure hτ hμ) hν
    (fun Θ hΘ ↦ ⟨hfix μ hμ Θ hΘ, hfix ν hνc Θ hΘ⟩)

/-! ### The support algebra of the empty support is the two-element algebra -/

/-- The two-element algebra `{0, 1}` of a poset. -/
noncomputable def trivialAlgebra (P : V) : V := insert (∅ : V) ({P} : V)

theorem mem_trivialAlgebra_iff (P b : V) : b ∈ trivialAlgebra P ↔ b = (∅ : V) ∨ b = P := by
  unfold trivialAlgebra
  rw [mem_insert, mem_singleton_iff]

theorem regularJoin_eq_empty_of_all_empty {P R X : V} (hR : IsForcingPreorder P R)
    (h : ∀ A ∈ X, A = (∅ : V)) : regularJoin P R X = (∅ : V) := by
  apply mem_ext
  intro p
  refine ⟨fun hp ↦ ?_, fun hp ↦ (not_mem_empty hp).elim⟩
  obtain ⟨hpP, hh⟩ := (mem_regularJoin_iff _ _ _ _).mp hp
  obtain ⟨r, ⟨A, hA, hrA⟩, -⟩ := hh p hpP (hR.2.1 p hpP)
  rw [h A hA] at hrA
  exact (not_mem_empty hrA).elim

theorem isCompleteSubalgebra_trivialAlgebra {P R : V} (hR : IsForcingPreorder P R) :
    IsCompleteSubalgebra P R (trivialAlgebra P) := by
  refine ⟨fun b hb ↦ ?_, mem_insert.mpr (Or.inr (mem_singleton_iff.mpr rfl)), fun b hb ↦ ?_,
    fun X hX ↦ ?_⟩
  · rcases (mem_trivialAlgebra_iff P b).mp hb with rfl | rfl
    · exact (mem_regularSets_iff _ _ _).mpr (forcingRegular_empty hR)
    · exact (mem_regularSets_iff _ _ _).mpr (forcingRegular_top _ _)
  · rcases (mem_trivialAlgebra_iff P b).mp hb with rfl | rfl
    · rw [forcingNegation_empty]
      exact (mem_trivialAlgebra_iff P P).mpr (Or.inr rfl)
    · rw [forcingNegation_top hR]
      exact (mem_trivialAlgebra_iff _ _).mpr (Or.inl rfl)
  · by_cases hP : P ∈ X
    · refine (mem_trivialAlgebra_iff P _).mpr (Or.inr (SetTheory.subset_antisymm
        (regularJoin_subset_poset P R X) (subset_regularJoin hR hP (forcingRegular_top P R))))
    · refine (mem_trivialAlgebra_iff P _).mpr (Or.inl (regularJoin_eq_empty_of_all_empty hR ?_))
      intro A hA
      rcases (mem_trivialAlgebra_iff P A).mp (hX A hA) with rfl | rfl
      · rfl
      · exact absurd hA hP

/-- The support algebra of the empty set of names is the two-element algebra. -/
theorem supportAlgebra_empty_subset (P R one K : V) :
    supportAlgebra (booleanConditions P R) (booleanOrder P R) one K (∅ : V) ⊆
      trivialAlgebra (booleanConditions P R) := by
  refine generatedSubalgebra_minimal
    (isCompleteSubalgebra_trivialAlgebra (booleanOrder_poset P R).1) (fun b hb ↦ ?_)
  obtain ⟨k, -, σ, hσ, -⟩ := (mem_supportValues_iff _ _ _ _ _ _).mp hb
  exact (not_mem_empty hσ).elim

/-- The sub-poset of the base support algebra of the empty support is the one-element poset: the
only nonzero condition of `RO(P)` whose cone lies in the two-element algebra is the top. -/
theorem eq_top_of_mem_subalgebraConditions_empty {P R one K b : V} (hP : ∃ p, p ∈ P)
    (hR : IsForcingPreorder P R)
    (hb : b ∈ subalgebraConditions P R (supportAlgebraBase P R one K (∅ : V))) : b = P := by
  obtain ⟨hbD, hbB⟩ := (mem_subalgebraConditions_iff _ _ _ _).mp hb
  obtain ⟨hreg, hcone⟩ := (mem_algebraPreimage_iff _ _ _ _).mp hbD
  rcases (mem_trivialAlgebra_iff _ _).mp (supportAlgebra_empty_subset P R one K _ hcone)
    with h0 | h1
  · exfalso
    have hself : b ∈ coneRegular (booleanConditions P R) (booleanOrder P R) b :=
      self_mem_coneRegular (booleanOrder_poset P R).1 hbB
    rw [h0] at hself
    exact not_mem_empty hself
  · have hPcone : P ∈ coneRegular (booleanConditions P R) (booleanOrder P R) b := by
      rw [h1]
      exact top_mem_booleanConditions hP
    exact SetTheory.subset_antisymm hreg.1
      ((mem_coneRegular_boolean_iff hR hreg).mp hPcone).2

/-- A name over that one-element poset has every subname forced in by every condition. -/
theorem subnamesForcedIn_of_name_over_empty_subalgebra {P R one K τ : V} (hP : ∃ p, p ∈ P)
    (hR : IsForcingPreorder P R)
    (hτ : IsForcingName (subalgebraConditions P R (supportAlgebraBase P R one K (∅ : V))) τ) :
    SubnamesForcedIn (booleanConditions P R) (booleanOrder P R) τ := by
  have hBo : IsForcingPreorder (booleanConditions P R) (booleanOrder P R) :=
    (booleanOrder_poset P R).1
  have hone : IsForcingTop (booleanConditions P R) (booleanOrder P R) P := booleanOrder_top hP
  intro μ hμ ν hν
  have hμQ := forcingName_mem_closure hτ hμ
  obtain ⟨C, hC⟩ := mem_domain_iff.mp hν
  obtain ⟨σ', q, hqQ, hz, -⟩ := (forcingName_iff _ _).mp hμQ _ hC
  have hCtop : C = P := by
    rw [(kpair_iff.mp hz).2]
    exact eq_top_of_mem_subalgebraConditions_empty hP hR hqQ
  rw [hCtop] at hC
  refine SetTheory.subset_antisymm (atomicMembership_subset _ _ _ _) (fun r hr ↦ ?_)
  exact atomicMembership_mono hBo (atomicMembership_of_pair hBo hone.1 hC) hr (hone.2 r hr)

namespace ForcingContext

/-- The intermediate extension by the support algebra of the empty support is the ground model. -/
theorem exists_check_eq_of_inSubalgebraModel_empty (A : ForcingContext V) {K : V}
    (hD : IsCompleteSubalgebra A.P A.R (supportAlgebraBase A.P A.R A.P K (∅ : V)))
    {x : A.booleanContext.Model} (hx : A.InSubalgebraModel hD x) :
    ∃ v : V, x = A.booleanContext.check v := by
  have hx' : A.booleanContext.InRestrictedModel
      (A.subalgebraConditions_subset_boolean
        (D := supportAlgebraBase A.P A.R A.P K (∅ : V)))
      (A.top_mem_subalgebraConditions hD) (hD.trace_generic A.order A.generic) x := hx
  obtain ⟨ρ, rfl⟩ := (A.booleanContext.inRestrictedModel_iff _ _ _ x).mp hx'
  refine ⟨groundValue ρ.val, A.booleanContext.ofName_eq_check_of_subnamesForcedIn _ ?_⟩
  exact subnamesForcedIn_of_name_over_empty_subalgebra ⟨A.one, A.top.1⟩ A.order ρ.property

end ForcingContext

/-! ### The empty support for the Levy collapse -/

/-- The uniform-support hypothesis of `inSubalgebraModel_of_uniformSupport` at `E = ∅` forces the
value into the ground model: if every name in the closure of `τ` is fixed by the forced stabilizer
of the empty set, which is the whole automorphism group of the completion, then the value of `τ` in
the Boolean extension of the Levy collapse is the check of a ground set. -/
theorem levy_ofName_eq_check_of_uniformSupport_empty {κ : V} {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
    (τ : ForcingName (levyContext κ hG).booleanContext.P)
    (hfix : ∀ μ ∈ nameClosure τ.val, ∀ Θ ∈ forcedStabilizer
      (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ))
      (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))) (∅ : V), nameAction Θ μ = μ) :
    ∃ x : V, (levyContext κ hG).booleanContext.ofName τ =
      (levyContext κ hG).booleanContext.check x := by
  refine (levyContext κ hG).booleanContext.exists_check_eq_ofName_of_subnamesForcedIn τ ?_
  refine subnamesForcedIn_of_invariant_closure (one := ∅) ⟨∅, empty_mem_levyCollapse κ⟩
    (levyCollapse_poset κ).1 (levyCollapse_homogeneous κ) τ.property (fun μ hμ Θ hΘ ↦ ?_)
  refine hfix μ hμ Θ ?_
  rw [forcedStabilizer_empty]
  exact hΘ

/-- The same for a name of the Solovay symmetric system: its value is a ground set. -/
theorem solovay_ofName_eq_check_of_uniformSupport_empty {κ : V} {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
    (τ : (levySolovayContext κ hG).Name)
    (hfix : ∀ μ ∈ nameClosure τ.val, ∀ Θ ∈ forcedStabilizer
      (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ))
      (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))) (∅ : V), nameAction Θ μ = μ) :
    ∃ x : V, (levySolovayContext κ hG).ofName τ = (levySolovayContext κ hG).check x := by
  obtain ⟨x, hx⟩ := levy_ofName_eq_check_of_uniformSupport_empty hG ⟨τ.val, τ.property.1⟩ hfix
  exact ⟨x, (levySolovayContext κ hG).toOrdinary_injective hx⟩

/-- The point of failure, stated as the contrapositive: a name of the Solovay system whose value is
not a ground set does not satisfy the uniform-support hypothesis of
`inSubalgebraModel_of_uniformSupport` at `E = ∅`. Since `GaloisStep` at `E = ∅` is proved
(`levy_galoisStep_empty`), the uniform-support hypothesis is the only thing standing between that
lemma and a false conclusion for such a name. -/
theorem not_uniformSupport_empty_of_value_not_ground {κ : V} {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
    (τ : (levySolovayContext κ hG).Name)
    (hnot : ∀ x : V, (levySolovayContext κ hG).ofName τ ≠ (levySolovayContext κ hG).check x) :
    ¬ ∀ μ ∈ nameClosure τ.val, ∀ Θ ∈ forcedStabilizer
      (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ))
      (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))) (∅ : V), nameAction Θ μ = μ := by
  intro hfix
  obtain ⟨x, hx⟩ := solovay_ofName_eq_check_of_uniformSupport_empty hG τ hfix
  exact hnot x hx

/-! ### The forward half of Lemma 9.3 in the form quantified over all supports -/

/-- The forward half of Karagila-Schilhan Lemma 9.3, read as a claim about every hereditarily
symmetric name of the Solovay system and every finite support of it: the value of the name lies in
the extension by the support algebra of that support. This is the shape of the conclusion of
`inSubalgebraModel_of_hereditarilySymmetric` and `inSubalgebraModel_of_uniformSupport` with their
hypotheses dropped. -/
def SolovaySupportAlgebraClaim (κ : V) {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G) : Prop :=
  ∀ (τ : (levySolovayContext κ hG).Name) (E : V), IsInternallyFinite E →
    (∀ σ ∈ E, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) σ) →
    forcedStabilizer (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))) E ⊆
      nameStabilizer (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))) τ.val →
    ∃ hD : IsCompleteSubalgebra (levyContext κ hG).P (levyContext κ hG).R
      (supportAlgebraBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
        ((ω : V) ×ˢ (ω : V)) E),
      (levyContext κ hG).InSubalgebraModel hD
        ((levyContext κ hG).booleanEquiv
          (solovaySymmetricInclusion hG ((levySolovayContext κ hG).ofName τ)))

/-- The claim fails as soon as the Solovay model has one set that is not a ground set and whose
name is supported by the empty set, that is, fixed by the whole automorphism group up to forced
equality. The nontriviality is the hypothesis `hnonground` and is not proved here. -/
theorem not_solovaySupportAlgebraClaim_of_nonground_invariant_name {κ : V} {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
    (τ : (levySolovayContext κ hG).Name)
    (hsupp : forcedStabilizer (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))) (∅ : V) ⊆
      nameStabilizer (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))) τ.val)
    (hnonground : ∀ x : V,
      (levySolovayContext κ hG).ofName τ ≠ (levySolovayContext κ hG).check x) :
    ¬ SolovaySupportAlgebraClaim κ hG := by
  intro hclaim
  obtain ⟨hD, hx⟩ := hclaim τ (∅ : V) internallyFinite_empty
    (fun σ hσ ↦ (not_mem_empty hσ).elim) hsupp
  obtain ⟨v, hv⟩ := (levyContext κ hG).exists_check_eq_of_inSubalgebraModel_empty hD hx
  refine hnonground v ((levySolovayContext κ hG).toOrdinary_injective ?_)
  show (levyContext κ hG).booleanContext.ofName ⟨τ.val, τ.property.1⟩ =
    (levyContext κ hG).booleanContext.check v
  rw [← hv]
  exact (Equiv.apply_symm_apply _ _).symm

end ZFVP
