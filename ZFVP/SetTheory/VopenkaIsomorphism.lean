import ZFVP.SetTheory.VopenkaScheme
import ZFVP.SetTheory.MembershipIso

/-! The full Vopenka scheme transfers through membership isomorphisms. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem vopenkaInstance_of_membershipIso (e : V ≃ W)
    (hm : ∀ x y, e x ∈ e y ↔ x ∈ y) (φ : SetTheorySemisentence 2)
    (h : VopenkaInstance (V := V) φ) : VopenkaInstance (V := W) φ := by
  apply (eval_vopenkaSentence φ).mp
  have hs := (eval_vopenkaSentence φ).mpr h
  change (vopenkaSentence φ).Eval ![] Empty.elim at hs
  have he := (eval_membershipIso e hm (vopenkaSentence φ) ![] Empty.elim).mp hs
  have hf : (fun x : Empty ↦ e (Empty.elim x)) = Empty.elim := funext (fun x ↦ Empty.elim x)
  simpa only [models_iff, Semiformula.Realize, Function.comp_def, Matrix.empty_eq, hf] using he

end ZFVP
