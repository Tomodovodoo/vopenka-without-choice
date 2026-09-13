import ZFVP.ModelTheory.SolovayRangeInternal
import ZFVP.SetTheory.NameRank
import ZFVP.SetTheory.SymmetricPowerName
import ZFVP.ModelTheory.ForcingFunctionValues

/-! The reverse inclusion of the paper's Lemma `lem:Solovay-symmetric`.

Every set of the Levy extension that is hereditarily definable from ground sets, reals and
ordinals is the image of an element of the Solovay symmetric model
(`hereditarilyGroundRealDefinable_mem_range`), so `Sol` is contained in the range of the
comparison map (`hod_subset_range`).

The proof has three parts.

The name of a definable class. Fix a symmetric system `(P, R, Γ, F)`, an ordinal `α`, a formula
`φ` with one free variable and `n` parameters, and names `v` for the parameters. The name is

  `{⟨σ, p⟩ : σ ∈ boundedSymmetricNames P Γ F α, p ⊩ φ(σ, v)}`.

Its value is the class defined by `φ` cut down to the values of the names of rank below `α`
(`mem_ofName_definableClass_iff`). It is hereditarily symmetric because the bounded class of names
is closed under the group action (`nameAction_mem_boundedSymmetricNames`) and the forcing relation
is equivariant (`forcingFormula_nameAction_iff`), so every automorphism fixing all the parameter
names fixes the whole name. Those automorphisms form the finite intersection `stabilizerMeet` of
the parameter stabilizers, which is in the filter. This gives the successor step
`exists_symmetricName_of_bounded`, transported to the Solovay comparison map in
`mem_range_niceInclusion_of_definable`.

The rank bound. The successor step needs one ordinal `α` bounding the names of all members of
`x` at once. `InSolovayRangeBelowInternal` refines the internal description of the range from
`ZFVP.ModelTheory.SolovayRangeInternal` by the rank of the name, so it is again a definable
predicate of the extension, and Collection inside the extension turns the pointwise bounds into a
single one (`exists_solovay_rank_bound`). Reading that bound back in the ground model uses that
the rank of the subname tree is absolute for end extensions (`MembershipEndExtension.map_nameRank`).

The induction. Membership in the range is internally definable, so the induction may run inside
the extension: `projectedRank_induction` over the transitive closure of `{x}`, with the external
hereditary definability hypothesis supplied at each step.

This discharges the hypothesis `hnm` of `ZFVP.ModelTheory.SolovaySymmetricRange` in its
hereditary form. The form stated there, definability of `x` alone, is too strong to be provable:
the double power set of `ω̌` computed in the extension is definable with no parameters, but under
choice in the ground model it has members, for instance a well ordering of the reals, that are not
in the symmetric model, and the range is transitive. Only the hereditary form is used by
`hod_subset_range_of_names`, which applies its hypothesis to a set coming out of `IsHOD`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The name rank is absolute for end extensions -/

theorem mem_nameRankStep_iff (τ g z : V) :
    z ∈ nameRankStep τ g ↔ ∃ σ ∈ domain τ, z ∈ succ (g ‘ σ) := by
  simp only [nameRankStep, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨y, ⟨σ, hσ, rfl⟩, hz⟩
    exact ⟨σ, hσ, hz⟩
  · rintro ⟨σ, hσ, hz⟩
    exact ⟨_, ⟨σ, hσ, rfl⟩, hz⟩

namespace MembershipEndExtension

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_nameRankStep (j : MembershipEndExtension V W) (τ g : V) :
    j (nameRankStep τ g) = nameRankStep (j τ) (j g) := by
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := j.endExtension _ z hz
    obtain ⟨σ, hσ, hy2⟩ := (mem_nameRankStep_iff τ g y).mp hy
    refine (mem_nameRankStep_iff _ _ _).mpr ⟨j σ, ?_, ?_⟩
    · rw [← j.map_relationDomain]
      exact (j.mem_iff _ _).mpr hσ
    · have hm := (j.mem_iff y (succ (g ‘ σ))).mpr hy2
      rwa [j.map_succ, j.map_value_total] at hm
  · intro hz
    obtain ⟨σ', hσ', hz2⟩ := (mem_nameRankStep_iff (j τ) (j g) z).mp hz
    rw [← j.map_relationDomain] at hσ'
    obtain ⟨σ, hσ, rfl⟩ := j.endExtension _ σ' hσ'
    rw [← j.map_value_total, ← j.map_succ] at hz2
    obtain ⟨y, hy, rfl⟩ := j.endExtension _ z hz2
    rw [j.mem_iff]
    exact (mem_nameRankStep_iff _ _ _).mpr ⟨σ, hσ, hy⟩

theorem map_nameRankRecursion (j : MembershipEndExtension V W) {N f : V}
    (hf : IsSubnameRecursion N nameRankStep f) :
    IsSubnameRecursion (j N) nameRankStep (j f) := by
  have : IsFunction f := hf.1
  refine ⟨j.map_function f, ?_, ?_⟩
  · rw [← j.map_relationDomain, hf.2.1]
  · intro x hx
    obtain ⟨τ, hτ, rfl⟩ := j.endExtension N x hx
    rw [← j.map_value_total, hf.2.2 τ hτ, j.map_nameRankStep, j.map_restrict,
      j.map_relationDomain]

/-- The rank of the subname tree is absolute for membership end extensions. -/
theorem map_nameRank (j : MembershipEndExtension V W) (τ : V) :
    j (nameRank τ) = nameRank (j τ) := by
  let f := subnameRecursionTable (nameRankStep : V → V → V) nameRankStep_definable τ
  have hf : IsSubnameRecursion (nameClosure τ) nameRankStep f :=
    subnameRecursionTable_spec _ _ _
  have hg := j.map_nameRankRecursion hf
  have hτ : j τ ∈ j (nameClosure τ) := (j.mem_iff _ _).mpr (mem_nameClosure_self τ)
  have he := subnameRecursion_coherent (j.map_subnameClosed (nameClosure_closed τ))
    (nameClosure_closed (j τ)) hg
    (subnameRecursionTable_spec (nameRankStep : W → W → W) nameRankStep_definable (j τ))
    (j τ) hτ (mem_nameClosure_self (j τ))
  change j (f ‘ τ) = _
  rw [j.map_value_total]
  exact he

end MembershipEndExtension

/-! ### The common stabilizer of finitely many names -/

/-- The intersection of the stabilizers of the names `v 0, …, v (n-1)`, with the whole group for
the empty tuple. -/
noncomputable def stabilizerMeet (Γ : V) : {n : ℕ} → (Fin n → V) → V
  | 0, _ => Γ
  | _ + 1, v => nameStabilizer Γ (v 0) ∩ stabilizerMeet Γ (fun i ↦ v i.succ)

theorem stabilizerMeet_subset_group (Γ : V) :
    ∀ {n : ℕ} (v : Fin n → V), stabilizerMeet Γ v ⊆ Γ := by
  intro n
  induction n with
  | zero => intro v z hz; exact hz
  | succ n ih =>
    intro v z hz
    have h : z ∈ nameStabilizer Γ (v 0) := (mem_inter_iff.mp hz).1
    exact (mem_sep_iff.mp h).1

theorem stabilizerMeet_fixes (Γ : V) :
    ∀ {n : ℕ} (v : Fin n → V) {π : V}, π ∈ stabilizerMeet Γ v →
      ∀ i, nameAction π (v i) = v i := by
  intro n
  induction n with
  | zero => intro v π _ i; exact Fin.elim0 i
  | succ n ih =>
    intro v π hπ i
    have h0 : π ∈ nameStabilizer Γ (v 0) := (mem_inter_iff.mp hπ).1
    have hrest : π ∈ stabilizerMeet Γ (fun j ↦ v j.succ) := (mem_inter_iff.mp hπ).2
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact (mem_sep_iff.mp h0).2
    · exact ih (fun j ↦ v j.succ) hrest j

theorem stabilizerMeet_mem_filter {P Γ F : V} (hF : IsNormalSubgroupFilter P Γ F) :
    ∀ {n : ℕ} (v : Fin n → V), (∀ i, nameStabilizer Γ (v i) ∈ F) → stabilizerMeet Γ v ∈ F := by
  intro n
  induction n with
  | zero => intro v _; exact hF.2.1
  | succ n ih =>
    intro v hv
    exact hF.2.2.2.1 _ (hv 0) _ (ih (fun i ↦ v i.succ) (fun i ↦ hv i.succ))

/-! ### The name of a definable class -/

/-- The conditions forcing `φ(σ, v)`, as a function of `σ`. -/
noncomputable def classNameConditions (P R : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → V) (σ : V) : V :=
  forcingFormula P R φ (standardTuple (σ :> v))

instance classNameConditions_definable (P R : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → V) : ℒₛₑₜ-function₁[V] (classNameConditions P R φ v) := by
  change ℒₛₑₜ-function₁[V]
    fun σ ↦ forcingFormula P R φ (assignmentPrepend (n : V) (standardTuple v) σ)
  definability

/-- The name of the class defined by `φ` with parameter names `v`, cut down to the hereditarily
symmetric names of rank below `α`. -/
noncomputable def definableClassName (P R Γ F α : V) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) : V :=
  {z ∈ boundedSymmetricNames P Γ F α ×ˢ P ;
    kpair.π₂ z ∈ classNameConditions P R φ v (kpair.π₁ z)}

theorem mem_definableClassName_iff (P R Γ F α : V) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) (σ p : V) :
    ⟨σ, p⟩ₖ ∈ definableClassName P R Γ F α φ v ↔
      σ ∈ boundedSymmetricNames P Γ F α ∧ p ∈ P ∧
        p ∈ forcingFormula P R φ (standardTuple (σ :> v)) := by
  simp only [definableClassName, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair,
    classNameConditions]
  tauto

theorem definableClassName_isName (P R Γ F α : V) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) :
    IsForcingName P (definableClassName P R Γ F α φ v) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨σ, hσ, p, hp, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  exact ⟨σ, p, hp, rfl, ((mem_boundedSymmetricNames_iff _ _ _ _ _).mp hσ).1⟩

theorem nameAction_mem_boundedSymmetricNames_iff {P R Γ F π α σ : V}
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hF : IsNormalSubgroupFilter P Γ F)
    (hπ : π ∈ Γ) (hσ : IsForcingName P σ) :
    nameAction π σ ∈ boundedSymmetricNames P Γ F α ↔ σ ∈ boundedSymmetricNames P Γ F α := by
  constructor
  · intro h
    have := nameAction_mem_boundedSymmetricNames hΓ hF (hΓ.2.2.2 π hπ) h
    rwa [nameAction_inverse_cancel (hΓ.1 π hπ) hσ] at this
  · exact nameAction_mem_boundedSymmetricNames hΓ hF hπ

/-- An automorphism fixing every parameter name fixes the class name. -/
theorem nameAction_definableClassName_fixed {P R Γ F π α : V} {n : ℕ}
    (hR : IsForcingPreorder P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hπ : π ∈ Γ)
    (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) (hv : ∀ i, IsForcingName P (v i))
    (hfix : ∀ i, nameAction π (v i) = v i) :
    nameAction π (definableClassName P R Γ F α φ v) = definableClassName P R Γ F α φ v := by
  have ha := hΓ.1 π hπ
  have hn := definableClassName_isName P R Γ F α φ v
  apply nameAction_eq_of_pair_iff ha hn hn
  intro σ hσ p hp
  rw [mem_definableClassName_iff, mem_definableClassName_iff]
  have hb := nameAction_mem_boundedSymmetricNames_iff (α := α) hΓ hF hπ hσ
  have hnames : ∀ i, IsForcingName P ((σ :> v) i) := by
    intro i
    exact Fin.cases hσ hv i
  have hcond := forcingFormula_nameAction_iff hR ha φ (σ :> v) hnames hp
  have he : (fun i ↦ nameAction π ((σ :> v) i)) = (nameAction π σ :> v) := by
    funext i
    exact Fin.cases rfl (fun j ↦ hfix j) i
  rw [he] at hcond
  constructor
  · rintro ⟨h1, _, h2⟩
    exact ⟨hb.mp h1, hp, hcond.mp h2⟩
  · rintro ⟨h1, _, h2⟩
    exact ⟨hb.mpr h1, function_value_mem ha.1 hp, hcond.mpr h2⟩

/-- The class name is hereditarily symmetric as soon as all the parameter names are symmetric. -/
theorem hereditarilySymmetric_definableClassName {P R Γ F α : V} {n : ℕ}
    (hR : IsForcingPreorder P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F)
    (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V)
    (hv : ∀ i, IsForcingName P (v i)) (hs : ∀ i, nameStabilizer Γ (v i) ∈ F) :
    IsHereditarilySymmetricName P Γ F (definableClassName P R Γ F α φ v) := by
  have hn := definableClassName_isName P R Γ F α φ v
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨hn, ?_⟩, ?_⟩
  · apply hF.2.2.1 _ (stabilizerMeet_mem_filter hF v hs) _ (nameStabilizer_subgroup hΓ hn)
    intro π hπ
    have hπΓ : π ∈ Γ := stabilizerMeet_subset_group Γ v π hπ
    refine mem_sep_iff.mpr ⟨hπΓ, ?_⟩
    exact nameAction_definableClassName_fixed hR hΓ hF hπΓ φ v hv
      (stabilizerMeet_fixes Γ v hπ)
  · intro σ p hp
    exact ((mem_boundedSymmetricNames_iff _ _ _ _ _).mp
      ((mem_definableClassName_iff _ _ _ _ _ _ _ _ _).mp hp).1).2.2

/-! ### The value of the class name -/

namespace ForcingContext

variable (S : ForcingContext V)

/-- The class name as a name of `S`. -/
noncomputable def definableClass (Γ F α : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (w : Fin n → ForcingName S.P) : ForcingName S.P :=
  ⟨definableClassName S.P S.R Γ F α φ (fun i ↦ (w i).val),
    definableClassName_isName _ _ _ _ _ _ _⟩

/-- The value of the class name: the sets satisfying `φ` that are values of hereditarily
symmetric names of rank below `α`. -/
theorem mem_ofName_definableClass_iff (Γ F α : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (w : Fin n → ForcingName S.P) (y : S.Model) :
    y ∈ S.ofName (S.definableClass Γ F α φ w) ↔
      (∃ τ : ForcingName S.P, τ.val ∈ boundedSymmetricNames S.P Γ F α ∧ S.ofName τ = y) ∧
        φ.Evalb (y :> fun i ↦ S.ofName (w i)) := by
  have hval : ∀ ν : ForcingName S.P, (fun i ↦ ((ν :> w) i).val) = (ν.val :> fun i ↦ (w i).val) := by
    intro ν
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  have hname : ∀ ν : ForcingName S.P,
      (fun i ↦ S.ofName ((ν :> w) i)) = (S.ofName ν :> fun i ↦ S.ofName (w i)) := by
    intro ν
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  rw [S.mem_ofName_iff]
  constructor
  · rintro ⟨ν, p, hpG, hmem, rfl⟩
    obtain ⟨hb, -, hc⟩ := (mem_definableClassName_iff _ _ _ _ _ _ _ _ _).mp hmem
    refine ⟨⟨ν, hb, rfl⟩, ?_⟩
    have ht := S.formula_truth φ (ν :> w)
    rw [hname ν, hval ν] at ht
    exact ht.mpr ⟨p, hpG, hc⟩
  · rintro ⟨⟨τ, hτb, rfl⟩, hφ⟩
    have ht := S.formula_truth φ (τ :> w)
    rw [hname τ, hval τ] at ht
    obtain ⟨p, hpG, hp⟩ := ht.mp hφ
    refine ⟨τ, p, hpG, ?_, rfl⟩
    exact (mem_definableClassName_iff _ _ _ _ _ _ _ _ _).mpr
      ⟨hτb, (forcingFormula_regular S.order φ _).1 p hp, hp⟩

/-! ### The successor step -/

/-- If the members of `x` are exactly the sets satisfying `φ` with hereditarily symmetric
parameter names, and every member of `x` is the value of a hereditarily symmetric name of rank
below `α`, then `x` itself is the value of a hereditarily symmetric name. -/
theorem exists_symmetricName_of_bounded {Γ F α : V} {n : ℕ}
    (hΓ : IsForcingAutomorphismGroup S.P S.R Γ) (hF : IsNormalSubgroupFilter S.P Γ F)
    (φ : SetTheorySemisentence (n + 1)) (w : Fin n → ForcingName S.P)
    (hw : ∀ i, IsHereditarilySymmetricName S.P Γ F (w i).val) (x : S.Model)
    (hx : ∀ y : S.Model, y ∈ x ↔ φ.Evalb (y :> fun i ↦ S.ofName (w i)))
    (hbd : ∀ y ∈ x, ∃ τ : ForcingName S.P,
      τ.val ∈ boundedSymmetricNames S.P Γ F α ∧ S.ofName τ = y) :
    ∃ τ : ForcingName S.P, IsHereditarilySymmetricName S.P Γ F τ.val ∧ S.ofName τ = x := by
  refine ⟨S.definableClass Γ F α φ w, ?_, ?_⟩
  · exact hereditarilySymmetric_definableClassName S.order hΓ hF φ _
      (fun i ↦ (w i).property) (fun i ↦ (hereditarilySymmetric_symmetric (hw i)).2)
  · apply mem_ext
    intro y
    rw [S.mem_ofName_definableClass_iff]
    constructor
    · rintro ⟨-, hφ⟩
      exact (hx y).mpr hφ
    · intro hy
      exact ⟨hbd y hy, (hx y).mp hy⟩

/-! ### The successor step for the symmetric model inside the extension -/

/-- Successor step of the reverse inclusion. If `x` is defined in the extension by a formula
whose parameters lie in the symmetric model, and every member of `x` is the image of the value
of a hereditarily symmetric name of rank below `α`, then `x` is in the range of the inclusion. -/
theorem mem_range_niceInclusion_of_definable (A : ForcingContext V) (K α : V) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (x : A.Model) (v : Fin n → A.Model)
    (hv : ∀ i, v i ∈ Set.range (A.niceInclusion K))
    (hx : ∀ b : A.Model, b ∈ x ↔ φ.Evalb (b :> v))
    (hbd : ∀ y ∈ x, ∃ τ : (A.niceSymmetricContext K).Name,
      τ.val ∈ boundedSymmetricNames (A.niceSymmetricContext K).P
        (A.niceSymmetricContext K).Γ (A.niceSymmetricContext K).F α ∧
      A.niceInclusion K ((A.niceSymmetricContext K).ofName τ) = y) :
    x ∈ Set.range (A.niceInclusion K) := by
  classical
  set S := A.niceSymmetricContext K with hS
  set B := A.booleanContext with hB
  have he : ∀ u w : A.Model, A.booleanEquiv u ∈ A.booleanEquiv w ↔ u ∈ w :=
    A.booleanEquiv_mem_iff
  -- names for the parameters
  have hpar : ∀ i, ∃ σ : S.Name,
      B.ofName ⟨σ.val, σ.property.1⟩ = A.booleanEquiv (v i) := by
    intro i
    obtain ⟨y, hy⟩ := hv i
    obtain ⟨σ, rfl⟩ := S.ofName_surjective y
    exact ⟨σ, by rw [← hy, A.booleanEquiv_niceInclusion]; rfl⟩
  choose σ hσ using hpar
  set w : Fin n → ForcingName B.P := fun i ↦ ⟨(σ i).val, (σ i).property.1⟩ with hw
  have hwv : ∀ i, B.ofName (w i) = A.booleanEquiv (v i) := hσ
  -- the definition transfers to the Boolean extension
  have htr : ∀ u : B.Model, u ∈ A.booleanEquiv x ↔ φ.Evalb (u :> fun i ↦ B.ofName (w i)) := by
    intro u
    have hb := (he (A.booleanEquiv.symm u) x)
    rw [Equiv.apply_symm_apply] at hb
    rw [hb, hx]
    have hev := evalb_of_memEquiv A.booleanEquiv he φ (A.booleanEquiv.symm u :> v)
    have hfun : (fun i ↦ A.booleanEquiv ((A.booleanEquiv.symm u :> v) i)) =
        (u :> fun i ↦ B.ofName (w i)) := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact Equiv.apply_symm_apply _ _
      · exact (hwv j).symm
    rw [hev, hfun]
  -- the bound transfers as well
  have hbd' : ∀ u ∈ A.booleanEquiv x, ∃ τ : ForcingName B.P,
      τ.val ∈ boundedSymmetricNames B.P S.Γ S.F α ∧ B.ofName τ = u := by
    intro u hu
    have hu' : A.booleanEquiv.symm u ∈ x := by
      have := (he (A.booleanEquiv.symm u) x)
      rw [Equiv.apply_symm_apply] at this
      exact this.mp hu
    obtain ⟨τ, hτb, hτv⟩ := hbd _ hu'
    refine ⟨⟨τ.val, τ.property.1⟩, hτb, ?_⟩
    have := congrArg A.booleanEquiv hτv
    rw [A.booleanEquiv_niceInclusion, Equiv.apply_symm_apply] at this
    exact this
  obtain ⟨τ, hτ, hτx⟩ := B.exists_symmetricName_of_bounded S.group S.normal φ w
    (fun i ↦ (σ i).property) (A.booleanEquiv x) htr hbd'
  refine ⟨S.ofName ⟨τ.val, hτ⟩, ?_⟩
  apply A.booleanEquiv.injective
  rw [A.booleanEquiv_niceInclusion]
  exact hτx

end ForcingContext

/-! ### A rank bound on the names, read inside the extension -/

section

variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `InSolovayRangeInternal` with a bound on the rank of the name: `x` is the value of a ground
hereditarily symmetric name whose subname tree has rank below `β`. -/
def InSolovayRangeBelowInternal (x β r : M) : Prop :=
  ∃ τ : M, IsGround τ (kpair.π₁ r) ∧
    IsHereditarilySymmetricName (kpair.π₁ (kpair.π₂ r))
      (kpair.π₁ (kpair.π₂ (kpair.π₂ r)))
      (kpair.π₁ (kpair.π₂ (kpair.π₂ (kpair.π₂ r)))) τ ∧
    nameRank τ ∈ β ∧
    x = nameValue (kpair.π₂ (kpair.π₂ (kpair.π₂ (kpair.π₂ r)))) τ

instance inSolovayRangeBelowInternal_definable :
    ℒₛₑₜ-relation₃[M] InSolovayRangeBelowInternal := by
  unfold InSolovayRangeBelowInternal
  definability

theorem inSolovayRangeBelowInternal_mono {x β γ r : M} (h : β ⊆ γ)
    (hx : InSolovayRangeBelowInternal x β r) : InSolovayRangeBelowInternal x γ r := by
  obtain ⟨τ, h1, h2, h3, h4⟩ := hx
  exact ⟨τ, h1, h2, h _ h3, h4⟩

end

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- The hereditarily symmetric names of the Solovay system whose rank is below `α`. -/
noncomputable def solovayBoundedNames (α : V) : V :=
  boundedSymmetricNames (levySolovayContext κ hG).P (levySolovayContext κ hG).Γ
    (levySolovayContext κ hG).F α

include hAC hU hc hω hκ in
/-- The bounded internal predicate at a checked ordinal says exactly that `x` is the image of the
value of a hereditarily symmetric name of rank below that ordinal. -/
theorem solovay_rangeBelow_iff (x : (levyContext κ hG).Model) (α : V) :
    InSolovayRangeBelowInternal x ((levyContext κ hG).check α) (solovayRangeParameter hG) ↔
      ∃ τ : (levySolovayContext κ hG).Name, τ.val ∈ solovayBoundedNames hG α ∧
        solovaySymmetricInclusion hG ((levySolovayContext κ hG).ofName τ) = x := by
  have hmr : ∀ τ : V, nameRank ((levyContext κ hG).check τ) =
      (levyContext κ hG).check (nameRank τ) :=
    fun τ ↦ ((levyContext κ hG).checkEmbedding.map_nameRank τ).symm
  constructor
  · rintro ⟨t, hgr, hsym, hrk, hval⟩
    rw [solovayRangeParameter_ground] at hgr
    obtain ⟨τ, rfl⟩ := levy_check_of_isGround hAC hU hc hω hκ hG hgr
    rw [solovayRangeParameter_P, solovayRangeParameter_group,
      solovayRangeParameter_filter] at hsym
    rw [solovayRangeParameter_generic] at hval
    have hsym' := ((levyContext κ hG).checkEmbedding.hereditarilySymmetricName_map_iff
      (levySolovayContext κ hG).P (levySolovayContext κ hG).Γ
      (levySolovayContext κ hG).F τ).mp hsym
    rw [hmr τ] at hrk
    have hrk' : nameRank τ ∈ α := ((levyContext κ hG).check_mem_iff _ _).mp hrk
    refine ⟨⟨τ, hsym'⟩, ?_, ?_⟩
    · exact (mem_boundedSymmetricNames_iff _ _ _ _ _).mpr ⟨hsym'.1, hrk', hsym'⟩
    · rw [hval]
      exact (levyContext κ hG).niceInclusion_ofName _ ⟨τ, hsym'⟩
  · rintro ⟨τ, hb, rfl⟩
    obtain ⟨hn, hrk, hsym⟩ := (mem_boundedSymmetricNames_iff _ _ _ _ _).mp hb
    refine ⟨(levyContext κ hG).check τ.val, ?_, ?_, ?_, ?_⟩
    · rw [solovayRangeParameter_ground]
      exact levy_isGround_check hAC hU hc hω hκ hG τ.val
    · rw [solovayRangeParameter_P, solovayRangeParameter_group, solovayRangeParameter_filter]
      exact ((levyContext κ hG).checkEmbedding.hereditarilySymmetricName_map_iff
        (levySolovayContext κ hG).P (levySolovayContext κ hG).Γ
        (levySolovayContext κ hG).F τ.val).mpr τ.property
    · rw [hmr τ.val]
      exact ((levyContext κ hG).check_mem_iff _ _).mpr hrk
    · rw [solovayRangeParameter_generic]
      exact (levyContext κ hG).niceInclusion_ofName _ τ

include hAC hU hc hω hκ in
/-- Collection inside the extension bounds the ranks of the names needed for the members of a
set all of whose members are in the range. -/
theorem exists_solovay_rank_bound (x : (levyContext κ hG).Model)
    (hsub : ∀ y ∈ x, y ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG))) :
    ∃ α : V, ∀ y ∈ x, ∃ τ : (levySolovayContext κ hG).Name,
      τ.val ∈ solovayBoundedNames hG α ∧
      solovaySymmetricInclusion hG ((levySolovayContext κ hG).ofName τ) = y := by
  have hstep : ∀ y ∈ x, ∃ β : (levyContext κ hG).Model,
      IsOrdinal β ∧ InSolovayRangeBelowInternal y β (solovayRangeParameter hG) := by
    intro y hy
    obtain ⟨t, hgr, hsym, hval⟩ :=
      (solovay_range_iff_internal hAC hU hc hω hκ hG y).mp (hsub y hy)
    have : IsOrdinal (nameRank t) := isOrdinal_nameRank t
    exact ⟨succ (nameRank t), inferInstance, t, hgr, hsym, mem_succ_self _, hval⟩
  obtain ⟨B, hB⟩ := collection x
    (fun y β ↦ IsOrdinal β ∧ InSolovayRangeBelowInternal y β (solovayRangeParameter hG))
    (by definability) hstep
  have hγ : ∀ y ∈ x, InSolovayRangeBelowInternal y (ordinalSup B) (solovayRangeParameter hG) := by
    intro y hy
    obtain ⟨β, hβB, hβo, hβ⟩ := hB y hy
    exact inSolovayRangeBelowInternal_mono (subset_ordinalSup hβo hβB) hβ
  obtain ⟨α, hαo, hα⟩ := (levyContext κ hG).ordinal_eq_check (ordinalSup B)
  refine ⟨α, fun y hy ↦ ?_⟩
  refine (solovay_rangeBelow_iff hAC hU hc hω hκ hG y α).mp ?_
  rw [← hα]
  exact hγ y hy

/-! ### The reverse inclusion -/

include hAC hU hc hω hκ in
/-- Reverse half of the paper's Lemma `lem:Solovay-symmetric`: every set of the Levy extension
that is hereditarily definable from ground sets, reals and ordinals is the image of an element of
the Solovay symmetric model. The induction runs over the transitive closure of `{x}`; the
induction hypothesis is the internally definable predicate `InSolovayRangeInternal`. -/
theorem hereditarilyGroundRealDefinable_mem_range (x : (levyContext κ hG).Model)
    (hx : (levyContext κ hG).IsHereditarilyGroundRealDefinable x) :
    x ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) := by
  have hkey : ∀ y ∈ transitiveClosure ({x} : (levyContext κ hG).Model),
      InSolovayRangeInternal y (solovayRangeParameter hG) := by
    apply projectedRank_induction (transitiveClosure ({x} : (levyContext κ hG).Model))
      (fun z : (levyContext κ hG).Model ↦ z) (by definability)
      (fun y ↦ InSolovayRangeInternal y (solovayRangeParameter hG)) (by definability)
    intro y hy ih
    have hmem : ∀ z ∈ y, z ∈ transitiveClosure ({x} : (levyContext κ hG).Model) :=
      fun z hz ↦ (transitiveClosure_transitive _).mem_trans hz hy
    have hrange : ∀ z ∈ y, z ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) := by
      intro z hz
      exact (solovay_range_iff_internal hAC hU hc hω hκ hG z).mpr
        (ih z (hmem z hz) (rank_mem hz))
    obtain ⟨n, φ, v, hvpar, hφ⟩ := hx y hy
    obtain ⟨α, hα⟩ := exists_solovay_rank_bound hAC hU hc hω hκ hG y hrange
    refine (solovay_range_iff_internal hAC hU hc hω hκ hG y).mp ?_
    exact (levyContext κ hG).mem_range_niceInclusion_of_definable ((ω : V) ×ˢ (ω : V)) α φ y v
      (fun i ↦ parameters_in_range hG (hvpar i)) hφ hα
  exact (solovay_range_iff_internal hAC hU hc hω hκ hG x).mpr
    (hkey x (ForcingContext.self_mem_transitiveClosure_singleton x))

include hAC hU hc hω hκ in
/-- The inclusion `Sol ⊆ range` of the paper's Lemma `lem:Solovay-symmetric`. -/
theorem hod_subset_range :
    {y : (levyContext κ hG).Model | IsHOD solovayPf y (solovayParam κ hG)} ⊆
      Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) := by
  intro y hy
  exact hereditarilyGroundRealDefinable_mem_range hAC hU hc hω hκ hG y
    ((solovay_isHOD_iff hAC hU hc hω hκ hG y).mp hy)

end

end ZFVP
