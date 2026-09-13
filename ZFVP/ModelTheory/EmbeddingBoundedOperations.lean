import ZFVP.ModelTheory.CodedMembershipEmbedding
import ZFVP.SetTheory.BoundedCodingSupport

/-! Bounded set operations commute with coded embeddings between transitive domains. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCodedMembershipEmbedding

variable {A B f : V} [IsTransitive A] [IsTransitive B]

theorem bounded_defined_iff (h : IsCodedMembershipEmbedding A B f)
    {n : ℕ} {φ : SetTheorySemisentence n} (hφ : IsBoundedSetFormula φ)
    (R : (Fin n → V) → Prop) [Defined R φ] (v : Fin n → V) (hv : ∀ i, v i ∈ A) :
    R v ↔ R (fun i ↦ f ‘ (v i)) := by
  let b : Fin n → SetDomain A := fun i ↦ ⟨v i, hv i⟩
  have hs := bounded_formula_absolute A hφ b
  have ht := bounded_formula_absolute B hφ (h.toFunction ∘ b)
  have he := h.eval_semisentence φ b
  exact (Defined.eval_iff v).symm.trans (hs.symm.trans
    (he.trans (ht.trans (Defined.eval_iff (fun i ↦ f ‘ (v i))))))

theorem value_empty (h : IsCodedMembershipEmbedding A B f) (h0 : (∅ : V) ∈ A) : f ‘ (∅ : V) = ∅ :=
  (h.bounded_defined_iff boundedEmptyFormula_bounded (fun v ↦ v 0 = ∅) ![∅] (by simp [h0])).mp rfl

theorem value_pair (h : IsCodedMembershipEmbedding A B f) {x y : V}
    (hx : x ∈ A) (hy : y ∈ A) (hp : ⟨x, y⟩ₖ ∈ A) :
    f ‘ ⟨x, y⟩ₖ = ⟨f ‘ x, f ‘ y⟩ₖ :=
  (h.bounded_defined_iff boundedKpairFormula_bounded
    (fun v ↦ v 0 = ⟨v 1, v 2⟩ₖ) ![⟨x, y⟩ₖ, x, y]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hx, hy, hp])).mp rfl

theorem value_doubleton (h : IsCodedMembershipEmbedding A B f) {x y : V}
    (hx : x ∈ A) (hy : y ∈ A) (hp : doubleton x y ∈ A) :
    f ‘ (doubleton x y) = doubleton (f ‘ x) (f ‘ y) :=
  (h.bounded_defined_iff boundedDoubletonFormula_bounded
    (fun v ↦ v 0 = doubleton (v 1) (v 2)) ![doubleton x y, x, y]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hx, hy, hp])).mp rfl

theorem value_succ (h : IsCodedMembershipEmbedding A B f) {x : V}
    (hx : x ∈ A) (hs : succ x ∈ A) : f ‘ (succ x) = succ (f ‘ x) :=
  (h.bounded_defined_iff boundedSuccFormula_bounded
    (fun v ↦ v 0 = succ (v 1)) ![succ x, x] (by simp [hx, hs])).mp rfl

theorem value_omega (h : IsCodedMembershipEmbedding A B f) (hω : (ω : V) ∈ A) : f ‘ (ω : V) = ω :=
  (h.bounded_defined_iff boundedOmegaFormula_bounded (fun v ↦ v 0 = ω) ![ω] (by simp [hω])).mp rfl

theorem value_function (h : IsCodedMembershipEmbedding A B f) {g X Y : V}
    (hg : g ∈ A) (hX : X ∈ A) (hY : Y ∈ A) (hf : g ∈ Y ^ X) :
    f ‘ g ∈ (f ‘ Y) ^ (f ‘ X) :=
  (h.bounded_defined_iff boundedFunctionFormula_bounded (fun v ↦ v 0 ∈ v 2 ^ v 1)
    ![g, X, Y] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hg, hX, hY])).mp hf

end IsCodedMembershipEmbedding

end ZFVP
