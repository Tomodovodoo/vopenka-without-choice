import ZFVP.ModelTheory.RubinCofinalOmissionKernel

/-! The omission kernels for a directly finite family of definable orders.
Padding the family by tautologies allows the empty coordinate list as well. -/

set_option autoImplicit false

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def FiniteBlockEx {p : ℕ} (δ : Fin p → SetTheorySemiformula M 1)
    (ρ : Fin p → SetTheorySemiformula M 2) (B : (Fin p → M) → Prop) : Prop :=
  ∀ r : Fin p → M, (∀ t, (δ t).Eval ![r t] id) →
    ∃ s : Fin p → M, (∀ t, (δ t).Eval ![s t] id) ∧
      (∀ t, (ρ t).Eval ![r t, s t] id) ∧ B s

private def padFiniteFormulaFamily {p n : ℕ} (φ : Fin p → SetTheorySemiformula M n)
    (k : ℕ) : SetTheorySemiformula M n :=
  if hk : k < p then φ ⟨k, hk⟩ else ⊤

omit [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
@[simp] private theorem padFiniteFormulaFamily_at {p n : ℕ}
    (φ : Fin p → SetTheorySemiformula M n) (t : Fin p) :
    padFiniteFormulaFamily φ t.val = φ t := by
  simp [padFiniteFormulaFamily, t.isLt]

omit [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem padFiniteFormulaFamily_directed {p : ℕ}
    (δ : Fin p → SetTheorySemiformula M 1) (ρ : Fin p → SetTheorySemiformula M 2)
    (hdir : ∀ t, DirectedNoLast (fun x ↦ (δ t).Eval ![x] id)
      (fun x y ↦ (ρ t).Eval ![x, y] id)) :
    ∀ n, DirectedNoLast (dset (padFiniteFormulaFamily δ) n) (dlt (padFiniteFormulaFamily ρ) n) := by
  intro n
  change DirectedNoLast (fun x ↦ (padFiniteFormulaFamily δ n).Eval ![x] id)
    (fun x y ↦ (padFiniteFormulaFamily ρ n).Eval ![x, y] id)
  by_cases hn : n < p
  · simpa [dset, dlt, padFiniteFormulaFamily, hn] using hdir ⟨n, hn⟩
  · have htop : DirectedNoLast (fun _ : M ↦ True) (fun _ _ : M ↦ True) :=
      ⟨⟨Classical.choice ‹Nonempty M›, trivial⟩, fun _ _ _ _ _ _ _ _ ↦ trivial,
        fun x _ _ _ ↦ ⟨x, trivial, trivial, trivial⟩⟩
    simpa [dset, dlt, padFiniteFormulaFamily, hn] using htop

omit [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem finiteBlockEx_iff_padded {p : ℕ}
    (δ : Fin p → SetTheorySemiformula M 1) (ρ : Fin p → SetTheorySemiformula M 2)
    (B : (Fin p → M) → Prop) :
    FiniteBlockEx δ ρ B ↔ BlockEx (padFiniteFormulaFamily δ) (padFiniteFormulaFamily ρ) p Fin.val B := by
  simp only [FiniteBlockEx, BlockEx, dset, dlt, padFiniteFormulaFamily_at]

omit [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem rubin_finiteIndex_inseparable_split {p : ℕ}
    (δ : Fin p → SetTheorySemiformula M 1) (ρ : Fin p → SetTheorySemiformula M 2)
    (hdir : ∀ t, DirectedNoLast (fun x ↦ (δ t).Eval ![x] id)
      (fun x y ↦ (ρ t).Eval ![x, y] id))
    {U W : M → Prop} (hUW : Inseparable M U W)
    (B : SetTheorySemiformula M p) (Aneg Apos : SetTheorySemiformula M (1 + p))
    (hcover : ∀ x s, B.Eval s id →
      Aneg.Eval (Fin.addCases ![x] s) id ∨ Apos.Eval (Fin.addCases ![x] s) id)
    (hB : FiniteBlockEx δ ρ fun s ↦ B.Eval s id) :
    (∃ u, U u ∧ FiniteBlockEx δ ρ fun s ↦ Aneg.Eval (Fin.addCases ![u] s) id) ∨
      ∃ w, W w ∧ FiniteBlockEx δ ρ fun s ↦ Apos.Eval (Fin.addCases ![w] s) id := by
  have hh := rubin_inseparable_block_split (padFiniteFormulaFamily δ) (padFiniteFormulaFamily ρ)
    (padFiniteFormulaFamily_directed δ ρ hdir) Fin.val hUW B Aneg Apos hcover
    ((finiteBlockEx_iff_padded δ ρ _).mp hB)
  simpa only [← finiteBlockEx_iff_padded] using hh

theorem rubin_finiteIndex_finite_split {p : ℕ}
    (δ : Fin p → SetTheorySemiformula M 1) (ρ : Fin p → SetTheorySemiformula M 2)
    (hdir : ∀ t, DirectedNoLast (fun x ↦ (δ t).Eval ![x] id)
      (fun x y ↦ (ρ t).Eval ![x, y] id))
    (B Outside : SetTheorySemiformula M p) (Member : SetTheorySemiformula M (1 + p))
    {a : M} (ha : IsInternallyFinite a)
    (hcover : ∀ s, B.Eval s id →
      Outside.Eval s id ∨ ∃ m ∈ a, Member.Eval (Fin.addCases ![m] s) id)
    (hB : FiniteBlockEx δ ρ fun s ↦ B.Eval s id) :
    (FiniteBlockEx δ ρ fun s ↦ Outside.Eval s id) ∨
      ∃ m ∈ a, FiniteBlockEx δ ρ fun s ↦ Member.Eval (Fin.addCases ![m] s) id := by
  have hh := rubin_finite_block_split (padFiniteFormulaFamily δ) (padFiniteFormulaFamily ρ)
    (padFiniteFormulaFamily_directed δ ρ hdir) Fin.val B Outside Member ha hcover
    ((finiteBlockEx_iff_padded δ ρ _).mp hB)
  simpa only [← finiteBlockEx_iff_padded] using hh

omit [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem FiniteBlockEx.mono {p : ℕ}
    {δ : Fin p → SetTheorySemiformula M 1} {ρ : Fin p → SetTheorySemiformula M 2}
    {B C : (Fin p → M) → Prop} (h : ∀ s, B s → C s) (hB : FiniteBlockEx δ ρ B) :
    FiniteBlockEx δ ρ C := by
  intro r hr
  obtain ⟨s, hs, hrs, hBs⟩ := hB r hr
  exact ⟨s, hs, hrs, h s hBs⟩

private def consBlockBody {p : ℕ} (A : SetTheorySemiformula M (p + 1)) :
    SetTheorySemiformula M (1 + p) :=
  A ⇜ fun i ↦ #(Fin.cast (Nat.add_comm p 1) i)

omit [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_consBlockBody {p : ℕ} (A : SetTheorySemiformula M (p + 1))
    (x : M) (s : Fin p → M) :
    (consBlockBody A).Eval (Fin.addCases ![x] s) id ↔ A.Eval (x :> s) id := by
  rw [consBlockBody, Semiformula.eval_substs]
  have he : (Semiterm.val (Fin.addCases ![x] s) id ∘
      (fun i : Fin (p + 1) ↦ (#(Fin.cast (Nat.add_comm p 1) i) : Semiterm ℒₛₑₜ M (1 + p)))) =
      (x :> s) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · have hj : Fin.cast (Nat.add_comm p 1) j.succ = Fin.natAdd 1 j := by ext; simp; omega
      simp only [Function.comp_apply, Semiterm.val_bvar, hj, Fin.addCases_right, Matrix.cons_val_succ]
  rw [he]

omit [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem rubin_finiteIndex_inseparable_cons_split {p : ℕ}
    (δ : Fin p → SetTheorySemiformula M 1) (ρ : Fin p → SetTheorySemiformula M 2)
    (hdir : ∀ t, DirectedNoLast (fun x ↦ (δ t).Eval ![x] id)
      (fun x y ↦ (ρ t).Eval ![x, y] id))
    {U W : M → Prop} (hUW : Inseparable M U W)
    (B : SetTheorySemiformula M p) (Aneg Apos : SetTheorySemiformula M (p + 1))
    (hcover : ∀ x s, B.Eval s id → Aneg.Eval (x :> s) id ∨ Apos.Eval (x :> s) id)
    (hB : FiniteBlockEx δ ρ fun s ↦ B.Eval s id) :
    (∃ u, U u ∧ FiniteBlockEx δ ρ fun s ↦ Aneg.Eval (u :> s) id) ∨
      ∃ w, W w ∧ FiniteBlockEx δ ρ fun s ↦ Apos.Eval (w :> s) id := by
  have hc : ∀ x s, B.Eval s id →
      (consBlockBody Aneg).Eval (Fin.addCases ![x] s) id ∨
        (consBlockBody Apos).Eval (Fin.addCases ![x] s) id := by
    simpa only [eval_consBlockBody] using hcover
  rcases rubin_finiteIndex_inseparable_split δ ρ hdir hUW B
      (consBlockBody Aneg) (consBlockBody Apos) hc hB with ⟨u, hu, hn⟩ | ⟨w, hw, hp⟩
  · exact Or.inl ⟨u, hu, hn.mono (fun s hs ↦ (eval_consBlockBody Aneg u s).mp hs)⟩
  · exact Or.inr ⟨w, hw, hp.mono (fun s hs ↦ (eval_consBlockBody Apos w s).mp hs)⟩

theorem rubin_finiteIndex_finite_cons_split {p : ℕ}
    (δ : Fin p → SetTheorySemiformula M 1) (ρ : Fin p → SetTheorySemiformula M 2)
    (hdir : ∀ t, DirectedNoLast (fun x ↦ (δ t).Eval ![x] id)
      (fun x y ↦ (ρ t).Eval ![x, y] id))
    (B Outside : SetTheorySemiformula M p) (Member : SetTheorySemiformula M (p + 1))
    {a : M} (ha : IsInternallyFinite a)
    (hcover : ∀ s, B.Eval s id → Outside.Eval s id ∨ ∃ m ∈ a, Member.Eval (m :> s) id)
    (hB : FiniteBlockEx δ ρ fun s ↦ B.Eval s id) :
    (FiniteBlockEx δ ρ fun s ↦ Outside.Eval s id) ∨
      ∃ m ∈ a, FiniteBlockEx δ ρ fun s ↦ Member.Eval (m :> s) id := by
  have hc : ∀ s, B.Eval s id →
      Outside.Eval s id ∨ ∃ m ∈ a, (consBlockBody Member).Eval (Fin.addCases ![m] s) id := by
    simpa only [eval_consBlockBody] using hcover
  rcases rubin_finiteIndex_finite_split δ ρ hdir B Outside (consBlockBody Member) ha hc hB with ho | ⟨m, hm, hmem⟩
  · exact Or.inl ho
  · exact Or.inr ⟨m, hm, hmem.mono (fun s hs ↦ (eval_consBlockBody Member m s).mp hs)⟩

end ZFVP
