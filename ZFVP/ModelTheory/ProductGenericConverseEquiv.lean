import ZFVP.ModelTheory.ProductGenericConverse

/-! The two-step extension `V[G₁][H]` is the product extension `V[G₁ × H]`, as membership
structures over the ground model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- Transport a context over `A.Model` along an equality `A = B`. -/
def castContext {A B : ForcingContext V} (h : A = B) (Q : ForcingContext A.Model) :
    ForcingContext B.Model := h ▸ Q

/-- The model of a transported context. -/
def castContextEquiv {A B : ForcingContext V} (h : A = B) (Q : ForcingContext A.Model) :
    Q.Model ≃ (castContext h Q).Model := by
  subst h
  exact Equiv.refl _

theorem castContextEquiv_mem_iff {A B : ForcingContext V} (h : A = B) (Q : ForcingContext A.Model)
    (x y : Q.Model) : castContextEquiv h Q x ∈ castContextEquiv h Q y ↔ x ∈ y := by
  subst h
  rfl

theorem castContextEquiv_check {A B : ForcingContext V} (h : A = B) (Q : ForcingContext A.Model)
    (x : A.Model) : castContextEquiv h Q (Q.check x) = (castContext h Q).check (modelCast h x) := by
  subst h
  rfl

theorem castContext_P {A B : ForcingContext V} (h : A = B) (Q : ForcingContext A.Model) :
    (castContext h Q).P = modelCast h Q.P := by
  subst h
  rfl

theorem castContext_R {A B : ForcingContext V} (h : A = B) (Q : ForcingContext A.Model) :
    (castContext h Q).R = modelCast h Q.R := by
  subst h
  rfl

theorem castContext_one {A B : ForcingContext V} (h : A = B) (Q : ForcingContext A.Model) :
    (castContext h Q).one = modelCast h Q.one := by
  subst h
  rfl

theorem castContext_G {A B : ForcingContext V} (h : A = B) (Q : ForcingContext A.Model) :
    (castContext h Q).G = {y | ∃ x ∈ Q.G, y = modelCast h x} := by
  subst h
  ext y
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx

end ForcingContext

section

variable (C : ForcingContext V) {P₂ R₂ one₂ : V} (h₂ : IsForcingPreorder P₂ R₂)
  (t₂ : IsForcingTop P₂ R₂ one₂) (Q : ForcingContext C.Model)
  (hP : Q.P = C.check P₂) (hR : Q.R = C.check R₂) (hone : Q.one = C.check one₂)

include hP hR in
theorem firstFactorContext_combined :
    firstFactorContext C.order C.top h₂ (combinedGeneric_generic C Q hP hR) = C :=
  ForcingContext.ext rfl rfl rfl (firstProjection_combinedGeneric C Q hP hR)

include hP hR hone in
theorem secondFactorContext_combined :
    secondFactorContext C.order C.top h₂ t₂ (combinedGeneric_generic C Q hP hR) =
      ForcingContext.castContext (firstFactorContext_combined C h₂ Q hP hR).symm Q := by
  have h := (firstFactorContext_combined C h₂ Q hP hR).symm
  apply ForcingContext.ext
  · rw [ForcingContext.castContext_P, hP, ForcingContext.modelCast_check]
    rfl
  · rw [ForcingContext.castContext_R, hR, ForcingContext.modelCast_check]
    rfl
  · rw [ForcingContext.castContext_one, hone, ForcingContext.modelCast_check]
    rfl
  · rw [ForcingContext.castContext_G]
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [secondProjection_combinedGeneric C Q hP hR] at hq
      refine ⟨C.check q, hq, ?_⟩
      rw [ForcingContext.modelCast_check]
    · rintro ⟨x, hx, rfl⟩
      have := Q.generic.1.1 x hx
      rw [hP] at this
      obtain ⟨q, _, rfl⟩ := (C.mem_check_iff _ _).mp this
      refine ⟨q, ?_, ?_⟩
      · rw [secondProjection_combinedGeneric C Q hP hR]
        exact hx
      · rw [ForcingContext.modelCast_check]

/-- The two-step extension `V[G₁][H]` is the product extension. -/
noncomputable def twoStepEquiv :
    (productContext C.order C.top h₂ t₂ (combinedGeneric_generic C Q hP hR)).Model ≃ Q.Model :=
  ((productEquiv C.order C.top h₂ t₂ (combinedGeneric_generic C Q hP hR)).trans
    (ForcingContext.modelCast (secondFactorContext_combined C h₂ t₂ Q hP hR hone))).trans
    (ForcingContext.castContextEquiv (firstFactorContext_combined C h₂ Q hP hR).symm Q).symm

theorem twoStepEquiv_mem_iff (x y : (productContext C.order C.top h₂ t₂ (combinedGeneric_generic C Q hP hR)).Model) :
    twoStepEquiv C h₂ t₂ Q hP hR hone x ∈ twoStepEquiv C h₂ t₂ Q hP hR hone y ↔ x ∈ y := by
  unfold twoStepEquiv
  simp only [Equiv.trans_apply]
  rw [← ForcingContext.castContextEquiv_mem_iff (firstFactorContext_combined C h₂ Q hP hR).symm Q,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, ForcingContext.modelCast_mem_iff,
    productEquiv_mem_iff]

theorem twoStepEquiv_check (x : V) :
    twoStepEquiv C h₂ t₂ Q hP hR hone ((productContext C.order C.top h₂ t₂ (combinedGeneric_generic C Q hP hR)).check x) =
      Q.check (C.check x) := by
  unfold twoStepEquiv
  simp only [Equiv.trans_apply]
  rw [productEquiv_check, ForcingContext.modelCast_check]
  apply (ForcingContext.castContextEquiv (firstFactorContext_combined C h₂ Q hP hR).symm Q).injective
  rw [Equiv.apply_symm_apply, ForcingContext.castContextEquiv_check, ForcingContext.modelCast_check]

end

end ZFVP
