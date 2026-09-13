import ZFVP.ModelTheory.LevyGroundChange
import ZFVP.ModelTheory.HomogeneousTruth
import ZFVP.SetTheory.LevyCollapseFull
import ZFVP.ModelTheory.GroundRealsHOD
import ZFVP.ModelTheory.SolovayLocalization

/-! Lemma Solovay-localization of the paper: a set of ordinals of the Levy extension definable
from ground sets, reals and ordinals lies in a bounded stage `V[G_ξ]`. The parameters are
localized to a stage, the ground is changed to that stage, and homogeneity of the Levy collapse
over the stage lets the top condition decide membership, so the set is the check of a set of the
stage defined through the forcing relation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω in
/-- A subset of a checked set definable from localized parameters lies in a bounded stage. -/
theorem localized_subset_check_of_definable {x : (levyContext κ hG).Model} {θ : V}
    (hx : x ⊆ (levyContext κ hG).check θ) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → (levyContext κ hG).Model) (hv : ∀ i, IsLocalized hG (v i))
    (hmem : ∀ b, b ∈ x ↔ φ.Evalb (b :> v)) : IsLocalized hG x := by
  obtain ⟨ξ, hξ, hall⟩ := isLocalized_tuple hG hω v hv
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hξ' : ξ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ hξ
  choose y hy using hall
  obtain ⟨G', hG', g, hgmem, hgval⟩ := exists_ground_change hAC hU hc hω hG ξ hξ
  let N := levySubContext ξ hξ' hG
  let L := levySubRealization ξ hξ' hG
  let W := levyContext κ hG
  let W' := levyContext (N.check κ) hG'
  have : IsOrdinal (N.check κ) := (N.check_ordinal_iff κ).mpr inferInstance
  have hhom : IsWeaklyHomogeneous W'.P W'.R W'.one := levyCollapse_homogeneous (N.check κ)
  -- membership through the ground change and homogeneity
  have hdecide : ∀ α : N.Model, L.value α ∈ x ↔
      W'.one ∈ forcingFormula W'.P W'.R φ (standardTuple (fun i ↦ checkName W'.one ((α :> y) i))) := by
    intro α
    rw [hmem, evalb_of_memEquiv g hgmem φ]
    have hfun : (fun i ↦ g ((L.value α :> v) i)) = fun i ↦ W'.check ((α :> y) i) := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact hgval α
      · simp only [Matrix.cons_val_succ]
        rw [← hy j]
        exact hgval (y j)
    rw [hfun]
    exact W'.truth_iff_top_forces hhom φ (α :> y)
  let y₀ : N.Model := {α ∈ N.check θ ;
    W'.one ∈ forcingFormula W'.P W'.R φ (standardTuple (fun i ↦ checkName W'.one ((α :> y) i)))}
  refine ⟨ξ, hξ, y₀, g.injective ?_⟩
  rw [hgval y₀]
  apply mem_ext
  intro b
  constructor
  · intro hb
    obtain ⟨α, hα, rfl⟩ := (W'.mem_check_iff _ _).mp hb
    obtain ⟨-, hforce⟩ := mem_sep_iff.mp hα
    rw [← hgval α, hgmem]
    exact (hdecide α).mpr hforce
  · intro hb
    obtain ⟨b', rfl⟩ := g.surjective b
    have hb' : b' ∈ x := (hgmem b' x).mp hb
    obtain ⟨β, hβ, rfl⟩ := (W.mem_check_iff _ _).mp (hx b' hb')
    have hβ' : W.check β = L.value (N.check β) := (L.value_check β).symm
    rw [hβ', hgval]
    rw [W'.check_mem_iff]
    refine mem_sep_iff.mpr ⟨(N.check_mem_iff _ _).mpr hβ, ?_⟩
    rw [← hdecide, ← hβ']
    exact hb'

include hAC hU hc hω hκ in
/-- Lemma Solovay-localization: a set of ordinals definable from ground sets, reals and ordinals
lies in a bounded stage. -/
theorem groundRealDefinable_subset_check_localized {x : (levyContext κ hG).Model} {θ : V}
    (hx : x ⊆ (levyContext κ hG).check θ) (hdef : (levyContext κ hG).IsGroundRealDefinable x) :
    IsLocalized hG x := by
  obtain ⟨n, φ, v, hv, hmem⟩ := hdef
  exact localized_subset_check_of_definable hAC hU hc hω hG hx φ v
    (fun i ↦ isLocalized_parameter hAC hU hc hω hκ hG (hv i)) hmem

end

end ZFVP
