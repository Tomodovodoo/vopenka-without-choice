import ZFVP.ModelTheory.ForcingModel
import ZFVP.SetTheory.PiOneRankCriterion
import ZFVP.SetTheory.InternalChoice

/-! # The endpoint rank model `M = (V[G])_Λ`

The paper's `thm:finite-restoration` ends at the model `M = (V[G])_Λ`: the rank `Λ` of the
generic extension of `V` by Woodin's forcing `Q_Λ`.  This module packages that endpoint as a
Lean type and proves that it models ZFC, from named hypotheses only.

Nothing about the Woodin iteration is proved here.  The facts the endpoint needs from W03 and
from Woodin's forcing theorem stay explicit:

* the ZF rank criterion at the endpoint height, as `IsRankCriterionHeight (A.check Λ)`;
* the paper's "M satisfies ZFC", as `InternalChoice (A.endpointRank Λ)`;
* rank agreement for the check map, as `checkRank`: a ground object of rank below `Λ` still has
  rank below `Λ` in the extension;
* "the forcing adds no ordinals below `Λ`", as `ordinals`.

`EndpointZFC` bundles the four.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- The paper's `M = (V[G])_Λ`: the elements of the generic extension of rank below the
image of `Λ`. -/
@[reducible] def endpointRank (A : ForcingContext V) (Λ : V) : Type _ :=
  SetDomain (hierarchy (A.check Λ))

instance endpointRankSetStructure (A : ForcingContext V) (Λ : V) :
    SetStructure (A.endpointRank Λ) :=
  inferInstanceAs (SetStructure (SetDomain (hierarchy (A.check Λ))))

/-- The endpoint rank is nonempty: the criterion puts `ω` below the height, so the rank of `ω`
computed in the extension is one of its elements. -/
theorem endpointRank_nonempty (A : ForcingContext V) {Λ : V}
    (h : IsRankCriterionHeight (A.check Λ)) : Nonempty (A.endpointRank Λ) := by
  let := h.1
  exact ⟨(⟨hierarchy (ω : A.Model), hierarchy_mem h.2.1⟩ : SetDomain _)⟩

/-- `M` models ZF.  This is the rank criterion applied inside the generic extension, which is a
ZF model by `ForcingContext.modelZF`. -/
theorem endpointRank_models_zf (A : ForcingContext V) {Λ : V}
    (h : IsRankCriterionHeight (A.check Λ)) :
    letI := A.endpointRank_nonempty h
    (A.endpointRank Λ)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  let := A.endpointRank_nonempty h
  exact h.models_zf

/-- `M` models AC once choice holds internally in it.  In the paper this comes from Woodin's
forcing theorem, which is not proved here. -/
theorem endpointRank_models_ac (A : ForcingContext V) {Λ : V}
    [Nonempty (A.endpointRank Λ)] [(A.endpointRank Λ)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hAC : InternalChoice (A.endpointRank Λ)) : (A.endpointRank Λ)↓[ℒₛₑₜ] ⊧* 𝗔𝗖 :=
  models_ac_of_internalChoice hAC

/-- The check map into the endpoint, on ground objects of rank below `Λ`.

The hypothesis `h` is the W03 rank agreement fact: the check map does not raise rank, so a
ground object of rank below `Λ` still has rank below `A.check Λ` in the extension.  There is no
lemma for it in the tree at this generality (the available one,
`ForcingContext.ofName_mem_checked_hierarchy`, wants a name of low rank, and the rank of the
check name of `x` is not bounded by the rank of `x` unless `Λ` is closed enough), so it stays a
hypothesis. -/
noncomputable def endpointCheck (A : ForcingContext V) (Λ : V)
    (h : ∀ x ∈ hierarchy Λ, A.check x ∈ hierarchy (A.check Λ)) (x : V) (hx : x ∈ hierarchy Λ) :
    A.endpointRank Λ := ⟨A.check x, h x hx⟩

theorem endpointCheck_injective (A : ForcingContext V) (Λ : V)
    (h : ∀ x ∈ hierarchy Λ, A.check x ∈ hierarchy (A.check Λ)) {x y : V}
    (hx : x ∈ hierarchy Λ) (hy : y ∈ hierarchy Λ)
    (hxy : A.endpointCheck Λ h x hx = A.endpointCheck Λ h y hy) : x = y :=
  (A.check_eq_iff x y).mp (congrArg Subtype.val hxy)

theorem endpointCheck_mem_iff (A : ForcingContext V) (Λ : V)
    (h : ∀ x ∈ hierarchy Λ, A.check x ∈ hierarchy (A.check Λ)) {x y : V}
    (hx : x ∈ hierarchy Λ) (hy : y ∈ hierarchy Λ) :
    A.endpointCheck Λ h x hx ∈ A.endpointCheck Λ h y hy ↔ x ∈ y :=
  A.check_mem_iff x y

/-- What W03 and Woodin's forcing theorem owe the endpoint of `thm:finite-restoration`.

`rankHeight` is the ZF criterion at the endpoint rank, `choice` is the paper's "`M` satisfies
ZFC", `checkRank` says the check map keeps rank below `Λ`, and `ordinals` says the forcing adds
no ordinals below `Λ`. -/
structure EndpointZFC (A : ForcingContext V) (Λ : V) : Prop where
  rankHeight : IsRankCriterionHeight (A.check Λ)
  choice :
    letI := A.endpointRank_nonempty rankHeight
    letI := A.endpointRank_models_zf rankHeight
    InternalChoice (A.endpointRank Λ)
  checkRank : ∀ x ∈ hierarchy Λ, A.check x ∈ hierarchy (A.check Λ)
  ordinals : ∀ β : A.Model, IsOrdinal β → β ∈ A.check Λ → ∃ b : V, b ∈ Λ ∧ β = A.check b

theorem EndpointZFC.nonempty {A : ForcingContext V} {Λ : V} (h : EndpointZFC A Λ) :
    Nonempty (A.endpointRank Λ) :=
  A.endpointRank_nonempty h.rankHeight

theorem EndpointZFC.models_zf {A : ForcingContext V} {Λ : V} (h : EndpointZFC A Λ) :
    letI := h.nonempty
    (A.endpointRank Λ)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  A.endpointRank_models_zf h.rankHeight

theorem EndpointZFC.models_ac {A : ForcingContext V} {Λ : V} (h : EndpointZFC A Λ) :
    letI := h.nonempty
    (A.endpointRank Λ)↓[ℒₛₑₜ] ⊧* 𝗔𝗖 := by
  let := h.nonempty
  let := h.models_zf
  exact A.endpointRank_models_ac h.choice

end ForcingContext
end ZFVP
