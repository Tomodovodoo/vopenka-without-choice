import ZFVP.ModelTheory.ForcingBaseChange
import ZFVP.ModelTheory.ClassForcingQuotientClosed
import ZFVP.ModelTheory.EndExtensionBasics

/-! The forcing half of the paper's Proposition `prop:countability-essential`.

`ZFVP.ModelTheory.ClassForcingQuotientClosed` shows that the inclusion of a name submodel into
the full forcing quotient is a membership end extension: old sets get no new members. Here we
add the two remaining steps of the paper's argument.

* If some element of the quotient is not the value of any name in `N`, the inclusion is a
  proper end extension.
* If the name submodel is a dead end for `ZF` and the full quotient models `ZF`, then no such
  element exists: every element of the quotient is the value of a name in `N`, so the extension
  adds no set.

The file also carries a transport lemma for the dead-end property along a membership-preserving
equivalence, so that the abstract model produced by Enayat's Theorem 5.17 can be identified with
a name submodel. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-- The dead-end property transports along a membership-preserving bijection. -/
theorem IsZFDeadEnd.of_equiv {V W : Type u} [SetStructure V] [SetStructure W] [Nonempty V]
    [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (e : V ≃ W)
    (he : ∀ x y : V, x ∈ y ↔ e x ∈ e y) (h : IsZFDeadEnd V) : IsZFDeadEnd W := by
  intro U _ _ _ j hp
  obtain ⟨w, hw⟩ := hp
  exact h U ((MembershipEndExtension.ofEquiv e (fun x y ↦ (he x y).symm)).trans j) ⟨w, fun v ↦ hw (e v)⟩

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ClassForcingQuotient

variable (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (N : V → Prop) (hnames : ∀ x, N x → IsForcingName P x)
    (hsub : ∀ τ, N τ → ∀ σ p, ⟨σ, p⟩ₖ ∈ τ → N σ)

include hsub

/-- An element of the forcing quotient that is not the value of any name in `N` makes the
inclusion of the name submodel a proper end extension. -/
theorem inclusion_isProper (x : ForcingQuotient P R G hR hG.1)
    (hx : ∀ σ : {y : V // N y}, (ofName P R G hR hG.1 N hnames σ).val ≠ x) :
    (inclusion P R G hR hG N hnames hsub).IsProper := by
  refine ⟨x, fun v hv ↦ ?_⟩
  obtain ⟨σ, rfl⟩ := ofName_surjective P R G hR hG.1 N hnames v
  exact hx σ hv

/-- Restated through non-surjectivity of the name map. -/
theorem inclusion_isProper_of_not_surjective
    (h : ¬ Function.Surjective
      (fun σ : {y : V // N y} ↦ (ofName P R G hR hG.1 N hnames σ).val)) :
    (inclusion P R G hR hG N hnames hsub).IsProper := by
  rw [Function.Surjective] at h
  push_neg at h
  obtain ⟨x, hx⟩ := h
  exact inclusion_isProper P R G hR hG N hnames hsub x hx

/-- The paper's conclusion. If the name submodel is a dead end for `ZF` and the full forcing
quotient models `ZF`, then the quotient adds no set: every one of its elements is already the
value of a name in `N`. Otherwise the inclusion would be a proper end extension to a model of
`ZF`, which a dead end does not have. -/
theorem surjective_of_isZFDeadEnd [Nonempty {y : V // N y}]
    [(ClassForcingQuotient P R G hR hG.1 N hnames)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hZF : (ForcingQuotient P R G hR hG.1)↓[ℒₛₑₜ] ⊧* 𝗭𝗙)
    (hdead : IsZFDeadEnd (ClassForcingQuotient P R G hR hG.1 N hnames))
    (x : ForcingQuotient P R G hR hG.1) :
    ∃ σ : {y : V // N y}, (ofName P R G hR hG.1 N hnames σ).val = x := by
  have := hZF
  by_contra hx
  push_neg at hx
  exact hdead (ForcingQuotient P R G hR hG.1) (inclusion P R G hR hG N hnames hsub)
    (inclusion_isProper P R G hR hG N hnames hsub x hx)

end ClassForcingQuotient
end ZFVP
