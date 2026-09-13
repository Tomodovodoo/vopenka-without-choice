import ZFVP.ModelTheory.SolovayNiceNameValues
import ZFVP.ModelTheory.SolovayRealCoding
import ZFVP.ModelTheory.SymmetricModelSeparation
import ZFVP.SetTheory.BoundedCodingPrimitives

/-! Every real of a forcing extension lies in the Solovay symmetric model, in the coding the
`HOD` track uses.

The symmetric model of the Solovay system is built over `K = ω × ω`, so what its nice names hand
back directly are the subsets of `(ω × ω)ˇ`. The `HOD` track instead takes subsets of `ω̌` as its
parameters. The two are matched by the checked pairing code of `ZFVP.ModelTheory.SolovayRealCoding`:
a subset of `ω̌` is the image of its preimage, and that image is a separation over `ω̌` by a
bounded formula whose parameters are the preimage and the check of the ground pairing graph.

Separation transfers because the inclusion of the symmetric model into the extension is a
membership end extension, so bounded formulas are absolute between the two. That is the only
absoluteness used here; the inclusion is not assumed elementary. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The section of a formula in its first variable is a definable predicate. -/
theorem evalbSection_definable {M : Type*} [SetStructure M] {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (v : Fin n → M) :
    ℒₛₑₜ-predicate (fun u ↦ φ.Evalb (u :> v)) := by
  have hφ : Language.Definable ℒₛₑₜ (fun w : Fin (n + 1) → M ↦ φ.Evalb w) :=
    (show Defined (fun w : Fin (n + 1) → M ↦ φ.Evalb w) φ from ⟨fun _ ↦ Iff.rfl⟩).to_definable
  apply Language.Definable.substitution hφ (f := fun i w ↦ (w 0 :> v) i)
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change Language.DefinableFunction ℒₛₑₜ (fun w : Fin 1 → M ↦ w 0)
    definability
  · change Language.DefinableFunction ℒₛₑₜ (fun (_ : Fin 1 → M) ↦ v j)
    definability

/-! ### A bounded formula for the pairing image -/

/-- `z` is the code of some pair in `y`: there is `p ∈ y` with `⟨p, z⟩ₖ ∈ g`. Bounded, with `y`
and `g` as parameters. -/
def omegaPairImageFormula : SetTheorySemisentence 3 :=
  “z y g. ∃ p ∈ y, !boundedPairMemberFormula g p z”

theorem omegaPairImageFormula_bounded : IsBoundedSetFormula omegaPairImageFormula :=
  .exs _ (boundedPairMemberFormula_bounded.subst _)

theorem eval_omegaPairImageFormula {M : Type*} [SetStructure M] [Nonempty M]
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (z y g : M) :
    omegaPairImageFormula.Evalb ![z, y, g] ↔ ∃ p ∈ y, (⟨p, z⟩ₖ : M) ∈ g := by
  simp [omegaPairImageFormula]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable (A : ForcingContext V)

/-! ### The Solovay inclusion as a membership end extension -/

/-- The inclusion of the Solovay symmetric model into the extension, packaged as a membership end
extension. Injectivity and preservation of membership come from `solovayInclusion_injective` and
`solovayInclusion_mem_iff`; the end extension property is `solovay_range_transitive`. -/
noncomputable def solovayEndExtension :
    MembershipEndExtension A.solovayContext.Model A.Model where
  toFun := A.solovayInclusion
  injective := A.solovayInclusion_injective
  mem_iff := A.solovayInclusion_mem_iff
  endExtension := by
    intro x y hy
    obtain ⟨z, rfl⟩ := A.solovay_range_transitive _ ⟨x, rfl⟩ y hy
    exact ⟨z, (A.solovayInclusion_mem_iff z x).mp hy, rfl⟩

theorem solovayEndExtension_apply (x : A.solovayContext.Model) :
    A.solovayEndExtension x = A.solovayInclusion x := rfl

/-! ### Closure of the range under bounded separation -/

/-- A subset of an element of the range carved out by a bounded formula with parameters in the
range is again in the range. The formula is evaluated in the extension; boundedness is what makes
that agree with its evaluation in the symmetric model, since the inclusion is a membership end
extension. -/
theorem sep_mem_range {x : A.Model} (hx : x ∈ Set.range A.solovayInclusion) {n : ℕ}
    {φ : SetTheorySemisentence (n + 1)} (hφ : IsBoundedSetFormula φ) (v : Fin n → A.Model)
    (hv : ∀ i, v i ∈ Set.range A.solovayInclusion) :
    sep x (fun z ↦ φ.Evalb (z :> v)) (evalbSection_definable φ v) ∈
      Set.range A.solovayInclusion := by
  obtain ⟨x₀, rfl⟩ := hx
  choose v₀ hv₀ using hv
  have hvv : (fun i ↦ A.solovayInclusion (v₀ i)) = v := funext hv₀
  have habs (z : A.solovayContext.Model) :
      φ.Evalb (z :> v₀) ↔ φ.Evalb (A.solovayInclusion z :> v) := by
    have h := A.solovayEndExtension.bounded_elementary hφ (z :> v₀)
    rw [A.solovayEndExtension.map_cons] at h
    simpa only [solovayEndExtension_apply, hvv] using h
  obtain ⟨b, hb⟩ := A.solovayContext.separation φ v₀ x₀
  refine ⟨b, ?_⟩
  apply mem_ext
  intro w
  rw [mem_sep_iff]
  constructor
  · intro hw
    obtain ⟨z, hz, rfl⟩ := A.solovayEndExtension.endExtension b w hw
    obtain ⟨hzx, hzφ⟩ := (hb z).mp hz
    exact ⟨(A.solovayInclusion_mem_iff z x₀).mpr hzx, (habs z).mp hzφ⟩
  · rintro ⟨hwx, hwφ⟩
    obtain ⟨z, hz, rfl⟩ := A.solovayEndExtension.endExtension x₀ w hwx
    exact (A.solovayInclusion_mem_iff z b).mpr ((hb z).mpr ⟨hz, (habs z).mpr hwφ⟩)

/-! ### Subsets of the checked `ω` -/

/-- The pairing image, written as a separation by the bounded formula. -/
theorem omegaPairImage_eq_sep (y : A.Model) :
    omegaPairImage A y =
      sep (A.check (ω : V))
        (fun z ↦ omegaPairImageFormula.Evalb (z :> ![y, A.check (omegaPairGraph V)]))
        (evalbSection_definable _ _) := by
  apply mem_ext
  intro z
  rw [mem_omegaPairImage_iff', mem_sep_iff]
  exact and_congr_right fun _ ↦
    (eval_omegaPairImageFormula z y (A.check (omegaPairGraph V))).symm

/-- Every subset of `ω̌` in the extension lies in the Solovay symmetric model. This is the
statement `Ṙ_can^H = R` of the paper in the coding the `HOD` track uses. -/
theorem subset_check_omega_mem_range {x : A.Model} (hx : x ⊆ A.check (ω : V)) :
    x ∈ Set.range A.solovayInclusion := by
  have hkey := A.sep_mem_range (A.solovay_check_mem_range (ω : V)) omegaPairImageFormula_bounded
    ![omegaPairPreimage A x, A.check (omegaPairGraph V)] (fun i ↦ by
      match i with
      | 0 => exact A.subset_check_omega_prod_mem_range (omegaPairPreimage_subset x)
      | 1 => exact A.solovay_check_mem_range _)
  rw [← A.omegaPairImage_eq_sep (omegaPairPreimage A x),
    omegaPairImage_omegaPairPreimage hx] at hkey
  exact hkey

/-! ### The Cantor space form -/

/-- A member of Cantor space is a subset of `(ω × ω)ˇ`: it is a function from `ω` to `2`, hence a
set of pairs with both coordinates in `ω`. -/
theorem cantorSpace_subset_check_omega_prod {x : A.Model} (hx : x ∈ cantorSpace A.Model) :
    x ⊆ A.check ((ω : V) ×ˢ (ω : V)) := by
  have h2ω : ((2 : ℕ) : V) ⊆ (ω : V) := IsTransitive.transitive _ two_mem_omega
  have hsub : (ω : V) ×ˢ ((2 : ℕ) : V) ⊆ (ω : V) ×ˢ (ω : V) := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
    exact mem_prod_iff.mpr ⟨a, ha, b, h2ω b hb, rfl⟩
  have hxp : x ⊆ A.check ((ω : V) ×ˢ ((2 : ℕ) : V)) := by
    have hprod : A.check ((ω : V) ×ˢ ((2 : ℕ) : V)) =
        A.check (ω : V) ×ˢ A.check ((2 : ℕ) : V) :=
      A.checkEmbedding.map_prod _ _
    have hωc : A.check (ω : V) = (ω : A.Model) := A.check_omega_eq
    have h2c : A.check ((2 : ℕ) : V) = (((2 : ℕ) : A.Model)) :=
      A.checkEmbedding.map_numeral 2
    rw [hprod, hωc, h2c]
    exact (mem_function_iff.mp hx).1
  intro z hz
  have := hxp z hz
  obtain ⟨q, hq, rfl⟩ := (A.mem_check_iff _ _).mp this
  exact (A.mem_check_iff _ _).mpr ⟨q, hsub q hq, rfl⟩

/-- Every real of the extension, read as a member of Cantor space, lies in the Solovay symmetric
model. -/
theorem mem_cantorSpace_mem_range {x : A.Model} (hx : x ∈ cantorSpace A.Model) :
    x ∈ Set.range A.solovayInclusion :=
  A.subset_check_omega_prod_mem_range (A.cantorSpace_subset_check_omega_prod hx)

/-! ### The parameters of the Solovay class -/

/-- Every allowed parameter of the Solovay class lies in the symmetric model: ground sets, subsets
of `ω̌` and ordinals. -/
theorem solovay_parameters_mem_range {x : A.Model} (hx : A.IsSolovayParameter x) :
    x ∈ Set.range A.solovayInclusion := by
  rcases hx with ⟨a, rfl⟩ | hsub | hord
  · exact A.solovay_check_mem_range a
  · exact A.subset_check_omega_mem_range hsub
  · have := hord
    exact A.solovay_ordinal_mem_range x

end ForcingContext
end ZFVP
