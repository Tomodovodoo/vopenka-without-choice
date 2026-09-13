import ZFVP.ModelTheory.ForcingQuotientValuation
import ZFVP.ModelTheory.ClassForcingQuotient
import ZFVP.ModelTheory.TransitiveZFSymmetry

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

abbrev SymmetricForcingQuotient (P R Γ F : SetDomain U) (G : V)
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G) :=
  ClassForcingQuotient P R {p : SetDomain U | p.val ∈ G} hR
    ((groundForcingGeneric_iff_external U P R G hG.1.1).mp hG).1
    (IsHereditarilySymmetricName P Γ F) (fun _ h ↦ h.1)

noncomputable def symmetricQuotientValue (P R Γ F : SetDomain U) (G : V)
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G)
    (x : SymmetricForcingQuotient U P R Γ F G hR hG) :
    SetDomain (symmetricExtensionDomain U P.val Γ.val F.val G) :=
  ⟨(forcingQuotientValue U P R G hR hG x.val).val, by
    obtain ⟨τ, hτ, hx⟩ := x.property
    rw [hx]
    exact (mem_symmetricExtensionDomain_iff _ _ _ _ _ _).mpr
      ⟨τ.val, τ.property, (hereditarilySymmetricName_iff U P Γ F τ).mp hτ, rfl⟩⟩

theorem symmetricQuotientValue_ofName (P R Γ F : SetDomain U) (G : V)
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G)
    (τ : {x : SetDomain U // IsHereditarilySymmetricName P Γ F x}) :
    (symmetricQuotientValue U P R Γ F G hR hG
      (ClassForcingQuotient.ofName P R _ hR _ _ _ τ)).val = nameValue G τ.val.val := rfl

theorem symmetricQuotientValue_bijective (P R Γ F : SetDomain U) (G : V)
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G) :
    Function.Bijective (symmetricQuotientValue U P R Γ F G hR hG) := by
  constructor
  · intro x y he
    apply Subtype.ext
    apply (forcingQuotientValue_bijective U P R G hR hG).1
    have heval := congrArg (fun z : SetDomain (symmetricExtensionDomain U P.val Γ.val F.val G) ↦ z.val) he
    exact Subtype.ext heval
  · intro x
    obtain ⟨τ, hτU, hτH, he⟩ := (mem_symmetricExtensionDomain_iff _ _ _ _ _ _).mp x.property
    let τ' : SetDomain U := ⟨τ, hτU⟩
    let σ : {x : SetDomain U // IsHereditarilySymmetricName P Γ F x} :=
      ⟨τ', (hereditarilySymmetricName_iff U P Γ F τ').mpr hτH⟩
    exact ⟨ClassForcingQuotient.ofName P R _ hR _ _ _ σ, Subtype.ext he.symm⟩

theorem symmetricQuotientValue_mem_iff (P R Γ F : SetDomain U) (G : V)
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G)
    (x y : SymmetricForcingQuotient U P R Γ F G hR hG) :
    symmetricQuotientValue U P R Γ F G hR hG x ∈ symmetricQuotientValue U P R Γ F G hR hG y ↔ x ∈ y :=
  forcingQuotientValue_mem_iff U P R G hR hG x.val y.val

noncomputable def symmetricQuotientEquiv (P R Γ F : SetDomain U) (G : V)
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G) :
    SymmetricForcingQuotient U P R Γ F G hR hG ≃ SetDomain (symmetricExtensionDomain U P.val Γ.val F.val G) :=
  Equiv.ofBijective (symmetricQuotientValue U P R Γ F G hR hG)
    (symmetricQuotientValue_bijective U P R Γ F G hR hG)

theorem symmetricQuotientEquiv_mem_iff (P R Γ F : SetDomain U) (G : V)
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G)
    (x y : SymmetricForcingQuotient U P R Γ F G hR hG) :
    symmetricQuotientEquiv U P R Γ F G hR hG x ∈ symmetricQuotientEquiv U P R Γ F G hR hG y ↔ x ∈ y :=
  symmetricQuotientValue_mem_iff U P R Γ F G hR hG x y

end TransitiveZF
end ZFVP
