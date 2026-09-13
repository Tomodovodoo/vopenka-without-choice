import ZFVP.ModelTheory.GeneratedZFVPTheory

/-! The finite equality basis entails Foundation's equality axioms, even before normalization. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem equalityBasisSentence_models_eq {M : Type*} [Structure ℒₛₑₜ M] [Nonempty M]
    (h : M↓[ℒₛₑₜ] ⊧ equalityBasisSentence) : M↓[ℒₛₑₜ] ⊧* 𝗘𝗤 ℒₛₑₜ := by
  have hh := h
  simp only [equalityBasisSentence, models_iff] at hh
  simp at hh
  obtain ⟨hr, hs, ht, hm⟩ := hh
  have hv (v : Fin 2 → M) : v = ![v 0, v 1] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  refine ⟨?_⟩
  intro φ hφ
  cases hφ with
  | refl => simpa [models_iff] using hr
  | symm => simpa [models_iff] using hs
  | trans => simpa [models_iff] using ht
  | funcExt f => exact Empty.elim f
  | relExt r =>
    cases r with
    | eq =>
      simp [models_iff, Theory.Eq.relExt]
      intro v hv0 hv1 he
      rw [hv (Semiterm.val v Empty.elim ∘ fun i ↦ #(Fin.addCast 2 i))] at he
      rw [hv (Semiterm.val v Empty.elim ∘ fun i ↦ #(Fin.addNat i 2))]
      exact ht _ _ _ (hs _ _ hv0) (ht _ _ _ he hv1)
    | mem =>
      simp [models_iff, Theory.Eq.relExt]
      intro v hv0 hv1 he
      rw [hv (Semiterm.val v Empty.elim ∘ fun i ↦ #(Fin.addCast 2 i))] at he
      rw [hv (Semiterm.val v Empty.elim ∘ fun i ↦ #(Fin.addNat i 2))]
      exact (hm _ _ _ _ hv0 hv1).mp he

theorem generatedZFVPTheory_models_eq (M : Type*) [Structure ℒₛₑₜ M] [Nonempty M]
    [M↓[ℒₛₑₜ] ⊧* generatedZFVPTheory] : M↓[ℒₛₑₜ] ⊧* 𝗘𝗤 ℒₛₑₜ :=
  equalityBasisSentence_models_eq (Theory.models M generatedZFVPTheory
    (GeneratedZFVPAxiom.fixed (by simp [fixedZFTheory])))

instance generatedZFVPTheory_eq_weaker : 𝗘𝗤 ℒₛₑₜ ⪯ generatedZFVPTheory := by
  apply Entailment.WeakerThan.ofAxm!
  intro φ hφ
  apply Theory.Proof.complete
  apply consequence_iff.{0, 0}.mpr
  intro M _ _ hM
  let := hM
  let := generatedZFVPTheory_models_eq M
  exact Theory.models M (𝗘𝗤 ℒₛₑₜ) hφ

end ZFVP
