import ZFVP.ModelTheory.ProjectionQuotientTower
import ZFVP.ModelTheory.ForcedSequenceBounds
import ZFVP.SetTheory.ElementaryDependentChoice
import ZFVP.SetTheory.ForcingSeparativeOrder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingSeparativeOrderFormula : SetTheorySemisentence 3 :=
  f“S P R. ∀ z, z ∈ S ↔ ∃ p ∈ P, ∃ q ∈ P, z = !kpair.dfn p q ∧
    ∀ r ∈ P, !kpair.dfn r p ∈ R → ∃ s ∈ P,
      !kpair.dfn s r ∈ R ∧ !kpair.dfn s q ∈ R”

def forcingSeparativeClosedAtFormula : SetTheorySemisentence 3 :=
  “P R α. ∃ S, !forcingSeparativeOrderFormula S P R ∧ !forcingClosedAtFormula P S α”

def forcingSeparativeClosedBelowFormula : SetTheorySemisentence 3 :=
  “P R κ. ∀ α ∈ κ, !forcingSeparativeClosedAtFormula P R α”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingSeparativeOrderFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun S P R ↦ S = forcingSeparativeOrder P R)
      via forcingSeparativeOrderFormula :=
  ⟨fun v ↦ by
    have hev : forcingSeparativeOrderFormula.Evalb v ↔
        ∀ z, z ∈ v 0 ↔ ∃ p ∈ v 1, ∃ q ∈ v 1, z = ⟨p, q⟩ₖ ∧
          ∀ r ∈ v 1, ⟨r, p⟩ₖ ∈ v 2 → ForcingCompatible (v 1) (v 2) r q := by
      simp [forcingSeparativeOrderFormula, ForcingCompatible]
    dsimp only
    rw [hev, mem_ext_iff]
    apply forall_congr'
    intro z
    apply iff_congr Iff.rfl
    simp only [forcingSeparativeOrder, mem_sep_iff, mem_prod_iff]
    constructor
    · rintro ⟨p, hp, q, hq, rfl, h⟩
      exact ⟨⟨p, hp, q, hq, rfl⟩, by simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using h⟩
    · rintro ⟨⟨p, hp, q, hq, rfl⟩, h⟩
      exact ⟨p, hp, q, hq, rfl, by simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using h⟩⟩

instance forcingSeparativeClosedAtFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun P R α ↦ IsForcingClosedAt P (forcingSeparativeOrder P R) α)
      via forcingSeparativeClosedAtFormula :=
  ⟨fun v ↦ by simp [forcingSeparativeClosedAtFormula]⟩

instance forcingSeparativeClosedBelowFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun P R κ ↦ IsForcingClosedBelow P (forcingSeparativeOrder P R) κ)
      via forcingSeparativeClosedBelowFormula :=
  ⟨fun v ↦ by simp [forcingSeparativeClosedBelowFormula, IsForcingClosedBelow]⟩

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ElementaryMap.forcingSeparativeClosedAt_iff (j : ElementaryMap V W) (P R α : V) :
    IsForcingClosedAt P (forcingSeparativeOrder P R) α ↔
      IsForcingClosedAt (j P) (forcingSeparativeOrder (j P) (j R)) (j α) := by
  have h := j.evalb forcingSeparativeClosedAtFormula ![P, R, α]
  exact (Defined.eval_iff _).symm.trans (h.trans (Defined.eval_iff _))

theorem ElementaryMap.forcingSeparativeClosedBelow_iff (j : ElementaryMap V W) (P R κ : V) :
    IsForcingClosedBelow P (forcingSeparativeOrder P R) κ ↔
      IsForcingClosedBelow (j P) (forcingSeparativeOrder (j P) (j R)) (j κ) := by
  have h := j.evalb forcingSeparativeClosedBelowFormula ![P, R, κ]
  exact (Defined.eval_iff _).symm.trans (h.trans (Defined.eval_iff _))

namespace ForcingContext

theorem double_projectionQuotient_separative_closedAt_iff (A C : ForcingContext V)
    {Q S π τ ρ E : V}
    (hτ : IsForcingSplitProjection A.P A.R C.P C.R τ E)
    (hA : forcingProjectionGeneric A.P A.R τ C.G = A.G)
    (hπ : π ∈ A.P ^ Q) (hρ : ρ ∈ C.P ^ Q)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q) (γ : A.Model) :
    let B := A.projectionQuotientContext C hτ hA
    IsForcingClosedAt
      (B.projectionQuotient (A.projectionQuotient Q π) (A.projectionQuotientMap Q π ρ))
      (forcingSeparativeOrder
        (B.projectionQuotient (A.projectionQuotient Q π) (A.projectionQuotientMap Q π ρ))
        (B.projectionQuotientOrder (A.projectionQuotient Q π)
          (A.projectionQuotientOrder Q S π) (A.projectionQuotientMap Q π ρ)))
      (B.check γ) ↔
    IsForcingClosedAt (C.projectionQuotient Q ρ)
      (forcingSeparativeOrder (C.projectionQuotient Q ρ) (C.projectionQuotientOrder Q S ρ))
      (A.projectionInclusion C hτ hA γ) := by
  dsimp only
  let B := A.projectionQuotientContext C hτ hA
  let j := A.projectionFactorizationElementaryMap C hτ hA
  have h := j.forcingSeparativeClosedAt_iff
    (B.projectionQuotient (A.projectionQuotient Q π) (A.projectionQuotientMap Q π ρ))
    (B.projectionQuotientOrder (A.projectionQuotient Q π)
      (A.projectionQuotientOrder Q S π) (A.projectionQuotientMap Q π ρ)) (B.check γ)
  change _ ↔ IsForcingClosedAt
    (A.projectionFactorizationEquiv C hτ hA _)
    (forcingSeparativeOrder (A.projectionFactorizationEquiv C hτ hA _)
      (A.projectionFactorizationEquiv C hτ hA _))
    (A.projectionFactorizationEquiv C hτ hA (B.check γ)) at h
  rw [A.projectionFactorizationEquiv_quotient C hτ hA hπ hρ he,
    A.projectionFactorizationEquiv_quotientOrder C hτ hA hπ hρ he,
    A.projectionFactorizationEquiv_check C hτ hA] at h
  exact h

theorem double_projectionQuotient_separative_closedBelow_iff (A C : ForcingContext V)
    {Q S π τ ρ E : V}
    (hτ : IsForcingSplitProjection A.P A.R C.P C.R τ E)
    (hA : forcingProjectionGeneric A.P A.R τ C.G = A.G)
    (hπ : π ∈ A.P ^ Q) (hρ : ρ ∈ C.P ^ Q)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q) (κ : A.Model) :
    let B := A.projectionQuotientContext C hτ hA
    IsForcingClosedBelow
      (B.projectionQuotient (A.projectionQuotient Q π) (A.projectionQuotientMap Q π ρ))
      (forcingSeparativeOrder
        (B.projectionQuotient (A.projectionQuotient Q π) (A.projectionQuotientMap Q π ρ))
        (B.projectionQuotientOrder (A.projectionQuotient Q π)
          (A.projectionQuotientOrder Q S π) (A.projectionQuotientMap Q π ρ)))
      (B.check κ) ↔
    IsForcingClosedBelow (C.projectionQuotient Q ρ)
      (forcingSeparativeOrder (C.projectionQuotient Q ρ) (C.projectionQuotientOrder Q S ρ))
      (A.projectionInclusion C hτ hA κ) := by
  dsimp only
  let B := A.projectionQuotientContext C hτ hA
  let j := A.projectionFactorizationElementaryMap C hτ hA
  have h := j.forcingSeparativeClosedBelow_iff
    (B.projectionQuotient (A.projectionQuotient Q π) (A.projectionQuotientMap Q π ρ))
    (B.projectionQuotientOrder (A.projectionQuotient Q π)
      (A.projectionQuotientOrder Q S π) (A.projectionQuotientMap Q π ρ)) (B.check κ)
  change _ ↔ IsForcingClosedBelow
    (A.projectionFactorizationEquiv C hτ hA _)
    (forcingSeparativeOrder (A.projectionFactorizationEquiv C hτ hA _)
      (A.projectionFactorizationEquiv C hτ hA _))
    (A.projectionFactorizationEquiv C hτ hA (B.check κ)) at h
  rw [A.projectionFactorizationEquiv_quotient C hτ hA hπ hρ he,
    A.projectionFactorizationEquiv_quotientOrder C hτ hA hπ hρ he,
    A.projectionFactorizationEquiv_check C hτ hA] at h
  exact h

end ForcingContext
end ZFVP
