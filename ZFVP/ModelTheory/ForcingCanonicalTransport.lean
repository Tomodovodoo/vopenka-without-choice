import ZFVP.ModelTheory.ForcingIsomorphismWoodinSuccessor
import ZFVP.ModelTheory.ForcingIsomorphismNames
import ZFVP.ModelTheory.ForcingIsomorphismGenericContext
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Canonical name and generic transport by an internal forcing isomorphism.
The inverse is the converse graph, and both induced name maps are fixed. -/
structure IsCanonicalForcingTransport (P R Q S f : V) : Prop where
  iso : IsForcingIsomorphism P R Q S f
  nameForward {τ : V} (hτ : IsForcingName P τ) : IsForcingName Q (nameAction f τ)
  nameBackward {τ : V} (hτ : IsForcingName Q τ) : IsForcingName P (nameAction (converseGraph f) τ)
  nameLeftInverse {τ : V} (hτ : IsForcingName P τ) : nameAction (converseGraph f) (nameAction f τ) = τ
  nameRightInverse {τ : V} (hτ : IsForcingName Q τ) : nameAction f (nameAction (converseGraph f) τ) = τ
  checked {one : V} (hone : one ∈ P) (x : V) :
    nameAction f (checkName one x) = checkName (f ‘ one) x
  hierarchy {ζ τ : V} [IsOrdinal ζ] (hτ : IsForcingName P τ) :
    nameAction f τ ∈ forcingNameHierarchy Q ζ ↔ τ ∈ forcingNameHierarchy P ζ
  saturated {ζ N : V} [IsOrdinal ζ] (hN : IsForcingName P N) :
    nameAction f (forcingSaturatedName P R (forcingNameHierarchy P ζ) N) =
      forcingSaturatedName Q S (forcingNameHierarchy Q ζ) (nameAction f N)
  formula (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
      {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V) (hv : ∀ i, IsForcingName P (v i))
      {p : V} (hp : p ∈ P) :
    (f ‘ p ∈ forcingFormula Q S φ (standardTuple (fun i ↦ nameAction f (v i))) ↔
      p ∈ forcingFormula P R φ (standardTuple v))
  genericRoundtrip {G : Set V} (hG : IsExternalForcingFilter P R G)
      (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S) :
    forcingProjectionGeneric P R (converseGraph f) (forcingProjectionGeneric Q S f G) = G
  prefixCutoffPredicate {one top : V}

    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top)
    (hft : f ‘ one = top) (κ δ : V) :
    (IsWoodinPrefixCutoff P R one κ δ ↔ IsWoodinPrefixCutoff Q S top κ δ )
  prefixCutoff {one top : V}

    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top)
    (hft : f ‘ one = top) (κ : V) :
    (woodinPrefixCutoff P R one κ = woodinPrefixCutoff Q S top κ )
  saturatedPrefix {one top δ : V}
    [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top)
    (hft : f ‘ one = top) (κ : V) :
    (nameAction f (saturatedWoodinPrefixPosetName P R one κ δ) =
      saturatedWoodinPrefixPosetName Q S top κ δ )
  model (A : ForcingContext V) (hAP : A.P = P) (hAR : A.R = R) (hS : IsForcingPreorder Q S) :
    let hf : IsForcingIsomorphism A.P A.R Q S f := by simpa only [hAP, hAR] using iso
    let B := A.isomorphismImage hf hS
    ∃ e : A.Model ≃ B.Model,
      (∀ x y : A.Model, e x ∈ e y ↔ x ∈ y) ∧
      (∀ x : V, e (A.check x) = B.check x) ∧
      (∀ τ : ForcingName A.P, e (A.ofName τ) =
        B.ofName ⟨nameAction f τ.val, nameAction_isName hf.1 τ.property⟩) ∧
      (∀ τ : ForcingName Q, e.symm (B.ofName τ) =
        A.ofName ⟨nameAction (converseGraph f) τ.val, nameAction_isName hf.inverse_maps τ.property⟩) ∧
      (∀ γ : V, e (hartogsNumber (A.check γ)) = hartogsNumber (B.check γ)) ∧
      (∀ γ : V, InternalDependentChoiceAt (A.check γ) ↔ InternalDependentChoiceAt (B.check γ))

theorem IsForcingIsomorphism.canonicalTransport {P R Q S f : V}
    (hf : IsForcingIsomorphism P R Q S f) : IsCanonicalForcingTransport P R Q S f where
  iso := hf
  nameForward := nameAction_isName hf.1
  nameBackward := nameAction_isName hf.inverse_maps
  nameLeftInverse := hf.name_inverse_cancel
  nameRightInverse := hf.name_cancel_inverse
  checked := nameAction_checkName_map
  hierarchy := hf.name_hierarchy_iff
  saturated := hf.saturated_name
  formula hR hS := forcingFormula_isomorphism_iff hR hS hf
  genericRoundtrip := hf.generic_inverse_image
  prefixCutoffPredicate := hf.prefix_cutoff_iff
  prefixCutoff := hf.prefix_cutoff
  saturatedPrefix := hf.saturated_prefix_name
  model A hAP hAR hS := by
    let h : IsForcingIsomorphism A.P A.R Q S f := by simpa only [hAP, hAR] using hf
    refine ⟨A.isomorphismImageEquiv h hS, A.isomorphismImageEquiv_mem h hS,
      A.isomorphismImageEquiv_check h hS, A.isomorphismImageEquiv_name h hS,
      A.isomorphismImageEquiv_symm_name h hS, ?_, ?_⟩
    · exact A.isomorphismModelEquiv_hartogs (A.isomorphismImage h hS) h
        (A.isomorphismImage_pullback h hS)
    · exact A.isomorphismModelEquiv_dependentChoiceAt (A.isomorphismImage h hS) h
        (A.isomorphismImage_pullback h hS)
theorem IsCanonicalForcingTransport.map_top {P R Q S f one : V}
    (h : IsCanonicalForcingTransport P R Q S f) (ht : IsForcingTop P R one) :
    IsForcingTop Q S (f ‘ one) := h.iso.map_top ht

theorem IsForcingIsomorphism.generic_projection_commutes {P R Q S f A T π ρ : V}
    (hf : IsForcingIsomorphism P R Q S f) (hR : IsForcingPreorder P R)
    {G : Set V} (hG : IsExternalForcingFilter P R G)
    (hc : ∀ p ∈ P, ρ ‘ (f ‘ p) = π ‘ p) :
    forcingProjectionGeneric A T ρ (forcingProjectionGeneric Q S f G) =
      forcingProjectionGeneric A T π G := by
  have himage {q : V} (hq : q ∈ Q) :
      q ∈ forcingProjectionGeneric Q S f G ↔ (converseGraph f) ‘ q ∈ G := by
    constructor
    · rintro ⟨_, p, hp, hpq⟩
      apply hG.2.2.1 p hp _ (function_value_mem hf.inverse_maps hq)
      have hh := (hf.inverse.2.2.2 _ (function_value_mem hf.1 (hG.1 p hp)) q hq).mp hpq
      simpa only [hf.inverse_value (hG.1 p hp)] using hh
    · intro hqg
      refine ⟨hq, (converseGraph f) ‘ q, hqg, ?_⟩
      have hi := function_value_mem hf.inverse_maps hq
      have hh := (hf.2.2.2 _ hi _ hi).mp (hR.2.1 _ hi)
      simpa only [hf.value_inverse hq] using hh
  ext a
  constructor
  · rintro ⟨ha, q, hq, hqa⟩
    have hi := function_value_mem hf.inverse_maps hq.1
    have he := hc _ hi
    rw [hf.value_inverse hq.1] at he
    exact ⟨ha, (converseGraph f) ‘ q, (himage hq.1).mp hq, by simpa only [he] using hqa⟩
  · rintro ⟨ha, p, hp, hpa⟩
    have hpP := hG.1 p hp
    refine ⟨ha, f ‘ p, ?_, ?_⟩
    · apply (himage (function_value_mem hf.1 hpP)).mpr
      simpa only [hf.inverse_value hpP] using hp
    · simpa only [hc p hpP] using hpa


end ZFVP

