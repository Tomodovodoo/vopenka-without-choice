import ZFVP.SetTheory.GroundLikeFormulas
import ZFVP.SetTheory.GodelPairing

/-! The internal predicate that picks out a ground model from one parameter.

The parameter is a triple `r = ⟨δ, ⟨Pδδ, Pδ⟩⟩`: a regular cardinal `δ`, the ground's subsets of
`δ ×ˢ δ`, and the ground's subsets of `δ`. `IsGround x r` says that some ground-like `M` has
exactly those two collections of subsets and carries a code for `x`: a relation `E ∈ M` on `Λ ×ˢ Λ`
whose transitive collapse sends some `t` to `x`, together with the Gödel pairing `p ∈ M` of `Λ` and
the image `S` of `E` under `p`.

`groundFormula` is the same predicate as a first-order formula with no parameters from the model,
built from `groundLikeFormula`, `godelPairingFormula` and `isTransitiveCollapseFormula`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `x` lies in a ground model named by `r = ⟨δ, ⟨Pδδ, Pδ⟩⟩`. -/
def IsGround (x r : V) : Prop :=
  ∃ Θ M Λ p E S β t C f : V,
    IsOrdinal Θ ∧ IsGroundLike M (kpair.π₁ r) Θ ∧
    (∀ X : V, X ⊆ kpair.π₁ r ×ˢ kpair.π₁ r → (X ∈ M ↔ X ∈ kpair.π₁ (kpair.π₂ r))) ∧
    (∀ X : V, X ⊆ kpair.π₁ r → (X ∈ M ↔ X ∈ kpair.π₂ (kpair.π₂ r))) ∧
    IsOrdinal Λ ∧ p ∈ M ∧ IsGodelPairing Λ p ∧ range p ⊆ Θ ∧
    E ∈ M ∧ E ⊆ Λ ×ˢ Λ ∧
    (∀ z : V, z ∈ S ↔ ∃ q ∈ E, ⟨q, z⟩ₖ ∈ p) ∧
    IsOrdinal β ∧ t ∈ β ∧ IsTransitiveCollapse E β C f ∧ x = f ‘ t

/-- Build `IsGround x r` from the ten witnesses and the clauses they satisfy. -/
theorem isGround_of (x r Θ M Λ p E S β t C f : V) (hΘ : IsOrdinal Θ)
    (hM : IsGroundLike M (kpair.π₁ r) Θ)
    (hpar : ∀ X : V, X ⊆ kpair.π₁ r ×ˢ kpair.π₁ r → (X ∈ M ↔ X ∈ kpair.π₁ (kpair.π₂ r)))
    (hpar1 : ∀ X : V, X ⊆ kpair.π₁ r → (X ∈ M ↔ X ∈ kpair.π₂ (kpair.π₂ r)))
    (hΛ : IsOrdinal Λ) (hpM : p ∈ M) (hp : IsGodelPairing Λ p) (hrange : range p ⊆ Θ)
    (hEM : E ∈ M) (hE : E ⊆ Λ ×ˢ Λ) (hS : ∀ z : V, z ∈ S ↔ ∃ q ∈ E, ⟨q, z⟩ₖ ∈ p)
    (hβ : IsOrdinal β) (ht : t ∈ β) (hcol : IsTransitiveCollapse E β C f) (hx : x = f ‘ t) :
    IsGround x r :=
  ⟨Θ, M, Λ, p, E, S, β, t, C, f, hΘ, hM, hpar, hpar1, hΛ, hpM, hp, hrange, hEM, hE, hS, hβ, ht,
    hcol, hx⟩

/-- The witnesses of `IsGround x r`, in a shape an `obtain` can take apart. -/
theorem IsGround.exists {x r : V} (h : IsGround x r) :
    ∃ Θ M Λ p E S β t C f : V,
      IsOrdinal Θ ∧ IsGroundLike M (kpair.π₁ r) Θ ∧
      (∀ X : V, X ⊆ kpair.π₁ r ×ˢ kpair.π₁ r → (X ∈ M ↔ X ∈ kpair.π₁ (kpair.π₂ r))) ∧
      (∀ X : V, X ⊆ kpair.π₁ r → (X ∈ M ↔ X ∈ kpair.π₂ (kpair.π₂ r))) ∧
      IsOrdinal Λ ∧ p ∈ M ∧ IsGodelPairing Λ p ∧ range p ⊆ Θ ∧
      E ∈ M ∧ E ⊆ Λ ×ˢ Λ ∧
      (∀ z : V, z ∈ S ↔ ∃ q ∈ E, ⟨q, z⟩ₖ ∈ p) ∧
      IsOrdinal β ∧ t ∈ β ∧ IsTransitiveCollapse E β C f ∧ x = f ‘ t := h

/-- `IsGround` as a formula with no parameters, in the variables `x` and `r`. -/
def groundFormula : SetTheorySemisentence 2 :=
  f“x r. ∃ Th M L p E S b t C g,
    !IsOrdinal.dfn Th ∧ !groundLikeFormula M (!kpair.π₁.dfn r) Th ∧
    (∀ X, X ⊆ !prod.dfn (!kpair.π₁.dfn r) (!kpair.π₁.dfn r) →
      (X ∈ M ↔ X ∈ !kpair.π₁.dfn (!kpair.π₂.dfn r))) ∧
    (∀ X, X ⊆ !kpair.π₁.dfn r → (X ∈ M ↔ X ∈ !kpair.π₂.dfn (!kpair.π₂.dfn r))) ∧
    !IsOrdinal.dfn L ∧ p ∈ M ∧ !godelPairingFormula L p ∧ (!range.dfn p) ⊆ Th ∧
    E ∈ M ∧ E ⊆ !prod.dfn L L ∧
    (∀ z, z ∈ S ↔ ∃ q ∈ E, !kpair.dfn q z ∈ p) ∧
    !IsOrdinal.dfn b ∧ t ∈ b ∧ !isTransitiveCollapseFormula E b C g ∧ x = !value.dfn g t”

instance groundFormula_defined : ℒₛₑₜ-relation[V] IsGround via groundFormula :=
  ⟨fun v ↦ by simp [groundFormula, IsGround]⟩

theorem eval_groundFormula (x r : V) : groundFormula.Evalb ![x, r] ↔ IsGround x r :=
  Defined.eval_iff (φ := groundFormula) (R := fun v : Fin 2 → V ↦ IsGround (v 0) (v 1)) ![x, r]

end ZFVP
