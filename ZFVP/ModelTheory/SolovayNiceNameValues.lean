import ZFVP.ModelTheory.SolovaySymmetricContext
import ZFVP.ModelTheory.SymmetricModelOrdinals
import ZFVP.ModelTheory.ForcingModelRank

/-! Values of nice names in the Boolean extension, and what that puts inside the Solovay
symmetric model. The value of the nice name of `τ` over a ground set `K` is the part of the value
of `τ` that lies inside `Ǩ`, so every subset of `Ǩ` in the extension is the value of a saturated
nice name, hence of a hereditarily symmetric name. Transporting along the isomorphism between the
poset extension and the Boolean extension, the ground sets, the ordinals and the subsets of
`(ω × ω)ˇ` of the poset extension all lie in the range of the symmetric model, and that range is
closed downwards under membership. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable (A : ForcingContext V)

/-- The nice name over `K` of a Boolean name, as a Boolean name. -/
noncomputable def booleanNiceName (K : V) (τ : ForcingName A.booleanContext.P) :
    ForcingName A.booleanContext.P :=
  ⟨niceName A.booleanContext.P A.booleanContext.R A.booleanContext.one K τ.val,
    niceName_isName _ _ _ A.booleanContext.top.1⟩

/-- The value of the nice name of `τ` over `K`: the members of the value of `τ` that lie in `Ǩ`. -/
theorem mem_ofName_booleanNiceName_iff (K : V) (τ : ForcingName A.booleanContext.P)
    (x : A.booleanContext.Model) :
    x ∈ A.booleanContext.ofName (A.booleanNiceName K τ) ↔
      x ∈ A.booleanContext.check K ∧ x ∈ A.booleanContext.ofName τ := by
  constructor
  · intro hx
    obtain ⟨ν, p, hpG, hpair, rfl⟩ := (A.booleanContext.mem_ofName_iff _ x).mp hx
    obtain ⟨k, hk, p', _, heq, hp⟩ := (mem_niceName_iff _ _ _ _ _ _).mp hpair
    obtain ⟨hν, rfl⟩ := kpair_iff.mp heq
    have hνe : ν = ⟨checkName A.booleanContext.one k,
        checkName_isName A.booleanContext.top.1 k⟩ := Subtype.ext hν
    subst hνe
    refine ⟨(A.booleanContext.check_mem_iff k K).mpr hk, ?_⟩
    exact (forcingQuotientMk_mem_iff _ _ _ _ _ _ _).mpr ⟨_, hpG, hp⟩
  · rintro ⟨hxK, hxτ⟩
    obtain ⟨k, hk, rfl⟩ := (A.booleanContext.mem_check_iff K x).mp hxK
    obtain ⟨p, hpG, hp⟩ := (forcingQuotientMk_mem_iff
      A.booleanContext.P A.booleanContext.R A.booleanContext.G A.booleanContext.order
      A.booleanContext.generic.1 ⟨checkName A.booleanContext.one k,
        checkName_isName A.booleanContext.top.1 k⟩ τ).mp hxτ
    refine (A.booleanContext.mem_ofName_iff _ _).mpr
      ⟨⟨checkName A.booleanContext.one k, checkName_isName A.booleanContext.top.1 k⟩,
        p, hpG, ?_, rfl⟩
    exact (mem_niceName_iff _ _ _ _ _ _).mpr
      ⟨k, hk, p, atomicMembership_subset _ _ _ _ p hp, rfl, hp⟩

/-- The value of a nice name is the separation of the value of `τ` inside `Ǩ`. -/
theorem ofName_booleanNiceName_eq (K : V) (τ : ForcingName A.booleanContext.P) :
    A.booleanContext.ofName (A.booleanNiceName K τ) =
      {z ∈ A.booleanContext.check K ; z ∈ A.booleanContext.ofName τ} := by
  apply mem_ext_iff.mpr
  intro z
  rw [mem_sep_iff, A.mem_ofName_booleanNiceName_iff]

/-- The nice name of a Boolean name is hereditarily symmetric for the nice-name filter. -/
noncomputable def niceSymmetricName (K : V) (τ : ForcingName A.booleanContext.P) :
    (A.niceSymmetricContext K).Name :=
  ⟨(A.booleanNiceName K τ).val,
    saturatedNiceName_hereditarilySymmetric (A.niceSymmetricContext K).poset
      (A.niceSymmetricContext K).group A.booleanContext.top
      (niceName_saturated A.booleanContext.order A.booleanContext.top τ.val)⟩

theorem niceSymmetricName_saturated (K : V) (τ : ForcingName A.booleanContext.P) :
    IsSaturatedNiceName A.booleanContext.P A.booleanContext.R A.booleanContext.one K
      (A.niceSymmetricName K τ).val :=
  niceName_saturated A.booleanContext.order A.booleanContext.top τ.val

theorem toOrdinary_ofName_niceSymmetricName (K : V) (τ : ForcingName A.booleanContext.P) :
    (A.niceSymmetricContext K).toOrdinary ((A.niceSymmetricContext K).ofName
      (A.niceSymmetricName K τ)) = A.booleanContext.ofName (A.booleanNiceName K τ) := rfl

/-- Every subset of `Ǩ` in the Boolean extension is the value of a saturated nice name, and that
name is hereditarily symmetric for the nice-name filter. -/
theorem exists_saturatedNiceName (K : V) (x : A.booleanContext.Model)
    (hx : x ⊆ A.booleanContext.check K) :
    ∃ τ : (A.niceSymmetricContext K).Name,
      IsSaturatedNiceName A.booleanContext.P A.booleanContext.R A.booleanContext.one K τ.val ∧
      (A.niceSymmetricContext K).toOrdinary ((A.niceSymmetricContext K).ofName τ) = x := by
  obtain ⟨σ, rfl⟩ := A.booleanContext.ofName_surjective x
  refine ⟨A.niceSymmetricName K σ, A.niceSymmetricName_saturated K σ, ?_⟩
  have key : A.booleanContext.ofName (A.booleanNiceName K σ) = A.booleanContext.ofName σ := by
    apply mem_ext_iff.mpr
    intro z
    rw [A.mem_ofName_booleanNiceName_iff]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hx z h, h⟩⟩
  exact (A.toOrdinary_ofName_niceSymmetricName K σ).trans key

/-- The symmetric model of the nice-name system, seen inside the poset extension. -/
noncomputable def niceInclusion (K : V) : (A.niceSymmetricContext K).Model → A.Model :=
  fun y ↦ A.booleanEquiv.symm ((A.niceSymmetricContext K).toOrdinary y)

theorem booleanEquiv_niceInclusion (K : V) (y : (A.niceSymmetricContext K).Model) :
    A.booleanEquiv (A.niceInclusion K y) = (A.niceSymmetricContext K).toOrdinary y :=
  A.booleanEquiv.apply_symm_apply _

theorem niceInclusion_injective (K : V) : Function.Injective (A.niceInclusion K) := by
  intro x y h
  apply (A.niceSymmetricContext K).toOrdinary_injective
  rw [← A.booleanEquiv_niceInclusion, ← A.booleanEquiv_niceInclusion, h]

theorem niceInclusion_mem_iff (K : V) (x y : (A.niceSymmetricContext K).Model) :
    A.niceInclusion K x ∈ A.niceInclusion K y ↔ x ∈ y := by
  rw [← A.booleanEquiv_mem_iff, A.booleanEquiv_niceInclusion, A.booleanEquiv_niceInclusion]
  exact (A.niceSymmetricContext K).toOrdinary_mem_iff x y

theorem niceInclusion_check (K a : V) :
    A.niceInclusion K ((A.niceSymmetricContext K).check a) = A.check a := by
  apply A.booleanEquiv.injective
  rw [A.booleanEquiv_niceInclusion, A.booleanEquiv_check]
  rfl

/-- Ground sets lie in the range of the symmetric model. -/
theorem check_mem_range_niceInclusion (K a : V) :
    A.check a ∈ Set.range (A.niceInclusion K) :=
  ⟨(A.niceSymmetricContext K).check a, A.niceInclusion_check K a⟩

theorem booleanEquiv_subset_check (K : V) {x : A.Model} (hx : x ⊆ A.check K) :
    A.booleanEquiv x ⊆ A.booleanContext.check K := by
  intro z hz
  obtain ⟨w, rfl⟩ := A.booleanEquiv.surjective z
  rw [← A.booleanEquiv_check, A.booleanEquiv_mem_iff]
  exact hx w ((A.booleanEquiv_mem_iff w x).mp hz)

/-- Every subset of `Ǩ` in the poset extension lies in the range of the symmetric model. -/
theorem subset_check_mem_range_niceInclusion (K : V) {x : A.Model} (hx : x ⊆ A.check K) :
    x ∈ Set.range (A.niceInclusion K) := by
  obtain ⟨τ, _, hτ⟩ := A.exists_saturatedNiceName K (A.booleanEquiv x)
    (A.booleanEquiv_subset_check K hx)
  refine ⟨(A.niceSymmetricContext K).ofName τ, ?_⟩
  apply A.booleanEquiv.injective
  rw [A.booleanEquiv_niceInclusion, hτ]

/-- Ordinals of the poset extension lie in the range of the symmetric model. -/
theorem ordinal_mem_range_niceInclusion (K : V) (x : A.Model) [IsOrdinal x] :
    x ∈ Set.range (A.niceInclusion K) := by
  obtain ⟨β, _, rfl⟩ := A.ordinal_eq_check x
  exact A.check_mem_range_niceInclusion K β

/-- The range of the symmetric model is closed downwards under membership: the symmetric model
is an inner model of the extension, not merely a subclass. -/
theorem range_niceInclusion_transitive (K : V) :
    ∀ x ∈ Set.range (A.niceInclusion K), ∀ y : A.Model, y ∈ x →
      y ∈ Set.range (A.niceInclusion K) := by
  rintro _ ⟨z, rfl⟩ y hy
  have hmem : A.booleanEquiv y ∈ (A.niceSymmetricContext K).toOrdinary z := by
    rw [← A.booleanEquiv_niceInclusion K z]
    exact (A.booleanEquiv_mem_iff _ _).mpr hy
  obtain ⟨w, _, hw⟩ := (A.niceSymmetricContext K).inclusion.endExtension z _ hmem
  refine ⟨w, ?_⟩
  apply A.booleanEquiv.injective
  rw [A.booleanEquiv_niceInclusion]
  exact hw.symm

/-! ### The Solovay system `O(B, Ṙ)` -/

/-- The Solovay symmetric model seen inside the poset extension. -/
noncomputable def solovayInclusion : A.solovayContext.Model → A.Model :=
  A.niceInclusion ((ω : V) ×ˢ (ω : V))

theorem solovayInclusion_injective : Function.Injective A.solovayInclusion :=
  A.niceInclusion_injective _

theorem solovayInclusion_mem_iff (x y : A.solovayContext.Model) :
    A.solovayInclusion x ∈ A.solovayInclusion y ↔ x ∈ y :=
  A.niceInclusion_mem_iff _ x y

theorem solovay_check_mem_range (a : V) : A.check a ∈ Set.range A.solovayInclusion :=
  A.check_mem_range_niceInclusion _ a

theorem solovay_ordinal_mem_range (x : A.Model) [IsOrdinal x] :
    x ∈ Set.range A.solovayInclusion :=
  A.ordinal_mem_range_niceInclusion _ x

theorem subset_check_omega_prod_mem_range {x : A.Model}
    (hx : x ⊆ A.check ((ω : V) ×ˢ (ω : V))) : x ∈ Set.range A.solovayInclusion :=
  A.subset_check_mem_range_niceInclusion _ hx

theorem solovay_range_transitive :
    ∀ x ∈ Set.range A.solovayInclusion, ∀ y : A.Model, y ∈ x →
      y ∈ Set.range A.solovayInclusion :=
  A.range_niceInclusion_transitive _

end ForcingContext
end ZFVP
