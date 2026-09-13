import ZFVP.ModelTheory.RubinFiniteBlockUnion

/-! The source-model cofinal kernels of Rubin A.5. Every varying body is one
ordinary first-order formula. No theory consistency or model construction is
used, and the finite-set argument uses induction in the source model. -/

set_option autoImplicit false

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem rubin_inseparable_block_split
    (δ : ℕ → SetTheorySemiformula M 1) (ρ : ℕ → SetTheorySemiformula M 2)
    (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) {p : ℕ} (ks : Fin p → ℕ)
    {U W : M → Prop} (hUW : Inseparable M U W)
    (B : SetTheorySemiformula M p) (Aneg Apos : SetTheorySemiformula M (1 + p))
    (hcover : ∀ x s, B.Eval s id →
      Aneg.Eval (Fin.addCases ![x] s) id ∨ Apos.Eval (Fin.addCases ![x] s) id)
    (hB : BlockEx δ ρ p ks fun s ↦ B.Eval s id) :
    (∃ u, U u ∧ BlockEx δ ρ p ks fun s ↦ Aneg.Eval (Fin.addCases ![u] s) id) ∨
      ∃ w, W w ∧ BlockEx δ ρ p ks fun s ↦ Apos.Eval (Fin.addCases ![w] s) id := by
  classical
  by_contra hn
  have hUtail : ∀ u, U u → blockAllNot δ ρ ks Aneg u := by
    intro u hu
    exact (not_blockEx_iff δ ρ).mp (fun he ↦ hn (Or.inl ⟨u, hu, he⟩))
  have hWtail : ∀ w, W w → blockAllNot δ ρ ks Apos w := by
    intro w hw
    exact (not_blockEx_iff δ ρ).mp (fun he ↦ hn (Or.inr ⟨w, hw, he⟩))
  obtain ⟨w, hw, hneg⟩ := hUW.meets (blockAllNot δ ρ ks Aneg)
    (definable_blockAllNot δ ρ ks Aneg) hUtail
  apply blockAll_blockEx_contradiction δ ρ (BlockAll.and δ ρ hdir hneg (hWtail w hw)) hB
  intro s hs hBs
  exact (hcover w s hBs).elim hs.1 hs.2

theorem rubin_finite_block_split
    (δ : ℕ → SetTheorySemiformula M 1) (ρ : ℕ → SetTheorySemiformula M 2)
    (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) {p : ℕ} (ks : Fin p → ℕ)
    (B Outside : SetTheorySemiformula M p) (Member : SetTheorySemiformula M (1 + p))
    {a : M} (ha : IsInternallyFinite a)
    (hcover : ∀ s, B.Eval s id → Outside.Eval s id ∨ ∃ m ∈ a, Member.Eval (Fin.addCases ![m] s) id)
    (hB : BlockEx δ ρ p ks fun s ↦ B.Eval s id) :
    (BlockEx δ ρ p ks fun s ↦ Outside.Eval s id) ∨
      ∃ m ∈ a, BlockEx δ ρ p ks fun s ↦ Member.Eval (Fin.addCases ![m] s) id := by
  classical
  by_cases hOutside : BlockEx δ ρ p ks fun s ↦ Outside.Eval s id
  · exact Or.inl hOutside
  right
  by_contra hn
  have htail : ∀ m ∈ a, blockAllNot δ ρ ks Member m := by
    intro m hm
    exact (not_blockEx_iff δ ρ).mp (fun he ↦ hn ⟨m, hm, he⟩)
  have hfinite := internallyFinite_blockAllNot δ ρ hdir ks Member ha htail
  apply blockAll_blockEx_contradiction δ ρ
    (BlockAll.and δ ρ hdir ((not_blockEx_iff δ ρ).mp hOutside) hfinite) hB
  intro s hs hBs
  rcases hcover s hBs with hOut | ⟨m, hm, hMember⟩
  · exact hs.1 hOut
  · exact hs.2 m hm hMember

omit [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem rubin_inseparable_witness_split
    (δ : ℕ → SetTheorySemiformula M 1) (ρ : ℕ → SetTheorySemiformula M 2)
    (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) {p q : ℕ} (ks : Fin p → ℕ)
    {U W : M → Prop} (hUW : Inseparable M U W)
    (θ : SetTheorySemiformula M (p + q)) (ψ : SetTheorySemiformula M (1 + (p + q)))
    (Aneg Apos : SetTheorySemiformula M (1 + p))
    (hneg : ∀ x s, Aneg.Eval (Fin.addCases ![x] s) id ↔
      ∃ z : Fin q → M, θ.Eval (Matrix.appendr z s) id ∧ ¬ψ.Eval (Fin.addCases ![x] (Matrix.appendr z s)) id)
    (hpos : ∀ x s, Apos.Eval (Fin.addCases ![x] s) id ↔
      ∃ z : Fin q → M, θ.Eval (Matrix.appendr z s) id ∧ ψ.Eval (Fin.addCases ![x] (Matrix.appendr z s)) id)
    (hθ : BlockEx δ ρ p ks fun s ↦ ∃ z : Fin q → M, θ.Eval (Matrix.appendr z s) id) :
    (∃ u, U u ∧ BlockEx δ ρ p ks fun s ↦ ∃ z : Fin q → M,
      θ.Eval (Matrix.appendr z s) id ∧ ¬ψ.Eval (Fin.addCases ![u] (Matrix.appendr z s)) id) ∨
    ∃ w, W w ∧ BlockEx δ ρ p ks fun s ↦ ∃ z : Fin q → M,
      θ.Eval (Matrix.appendr z s) id ∧ ψ.Eval (Fin.addCases ![w] (Matrix.appendr z s)) id := by
  classical
  have hB : BlockEx δ ρ p ks fun s ↦ (∃¹^[q] θ).Eval s id := by
    simpa only [Semiformula.eval_exsItr] using hθ
  have hcover : ∀ x s, (∃¹^[q] θ).Eval s id →
      Aneg.Eval (Fin.addCases ![x] s) id ∨ Apos.Eval (Fin.addCases ![x] s) id := by
    intro x s hs
    obtain ⟨z, hz⟩ := Semiformula.eval_exsItr.mp hs
    by_cases hψ : ψ.Eval (Fin.addCases ![x] (Matrix.appendr z s)) id
    · exact Or.inr ((hpos x s).mpr ⟨z, hz, hψ⟩)
    · exact Or.inl ((hneg x s).mpr ⟨z, hz, hψ⟩)
  rcases rubin_inseparable_block_split δ ρ hdir ks hUW (∃¹^[q] θ) Aneg Apos hcover hB with
    ⟨u, hu, hU⟩ | ⟨w, hw, hW⟩
  · exact Or.inl ⟨u, hu, BlockEx.mono δ ρ (fun s hs ↦ (hneg u s).mp hs) hU⟩
  · exact Or.inr ⟨w, hw, BlockEx.mono δ ρ (fun s hs ↦ (hpos w s).mp hs) hW⟩

theorem rubin_finite_witness_split
    (δ : ℕ → SetTheorySemiformula M 1) (ρ : ℕ → SetTheorySemiformula M 2)
    (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) {p q : ℕ} (ks : Fin p → ℕ)
    (θ : SetTheorySemiformula M (p + q)) (i : Fin q) {a : M} (ha : IsInternallyFinite a)
    (Outside : SetTheorySemiformula M p) (Member : SetTheorySemiformula M (1 + p))
    (hout : ∀ s, Outside.Eval s id ↔ ∃ z : Fin q → M, θ.Eval (Matrix.appendr z s) id ∧ z i ∉ a)
    (hmember : ∀ m s, Member.Eval (Fin.addCases ![m] s) id ↔
      ∃ z : Fin q → M, θ.Eval (Matrix.appendr z s) id ∧ z i = m)
    (hθ : BlockEx δ ρ p ks fun s ↦ ∃ z : Fin q → M, θ.Eval (Matrix.appendr z s) id) :
    (BlockEx δ ρ p ks fun s ↦ ∃ z : Fin q → M, θ.Eval (Matrix.appendr z s) id ∧ z i ∉ a) ∨
      ∃ m ∈ a, BlockEx δ ρ p ks fun s ↦ ∃ z : Fin q → M, θ.Eval (Matrix.appendr z s) id ∧ z i = m := by
  classical
  have hB : BlockEx δ ρ p ks fun s ↦ (∃¹^[q] θ).Eval s id := by
    simpa only [Semiformula.eval_exsItr] using hθ
  have hcover : ∀ s, (∃¹^[q] θ).Eval s id →
      Outside.Eval s id ∨ ∃ m ∈ a, Member.Eval (Fin.addCases ![m] s) id := by
    intro s hs
    obtain ⟨z, hz⟩ := Semiformula.eval_exsItr.mp hs
    by_cases hza : z i ∈ a
    · exact Or.inr ⟨z i, hza, (hmember (z i) s).mpr ⟨z, hz, rfl⟩⟩
    · exact Or.inl ((hout s).mpr ⟨z, hz, hza⟩)
  rcases rubin_finite_block_split δ ρ hdir ks (∃¹^[q] θ) Outside Member ha hcover hB with hOut | ⟨m, hm, hMem⟩
  · exact Or.inl (BlockEx.mono δ ρ (fun s hs ↦ (hout s).mp hs) hOut)
  · exact Or.inr ⟨m, hm, BlockEx.mono δ ρ (fun s hs ↦ (hmember m s).mp hs) hMem⟩

end ZFVP
