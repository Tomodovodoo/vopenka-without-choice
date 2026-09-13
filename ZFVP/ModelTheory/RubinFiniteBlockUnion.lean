import ZFVP.ModelTheory.RubinFiniteCofinalUnion
import ZFVP.ModelTheory.SeparatingTypesOmitted

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- In the block-body layout, quantify a member of the remaining parameter. -/
def finiteBlockExclusionBody {p : ℕ} (A : SetTheorySemiformula M (1 + p)) :
    SetTheorySemiformula M (1 + p) :=
  ∀¹ ((Semiformula.rel Language.Mem.mem ![#0, #(Fin.last (1 + p))]) 🡒
    ∼(A ⇜ fun i ↦ #(i.castSucc)))

theorem eval_finiteBlockExclusionBody {p : ℕ} (A : SetTheorySemiformula M (1 + p))
    (a : M) (s : Fin p → M) :
    (finiteBlockExclusionBody A).Eval (Matrix.appendr s ![a]) id ↔
      ∀ m ∈ a, ¬A.Eval (Fin.addCases ![m] s) id := by
  simp only [finiteBlockExclusionBody, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_neg,
    Semiformula.eval_substs]
  apply forall_congr'
  intro m
  have he : (Semiterm.val (m :> Matrix.appendr s ![a]) id ∘
      (fun i : Fin (1 + p) ↦ (#i.castSucc : Semiterm ℒₛₑₜ M ((1 + p) + 1)))) =
      Fin.addCases ![m] s := by
    funext i
    induction i using Fin.addCases with
    | left j =>
        simp only [Function.comp_apply, Semiterm.val_bvar, Fin.addCases_left, Matrix.cons_val_fin_one]
        rw [Fin.fin_one_eq_zero j]
        change (m :> Matrix.appendr s ![a]) 0 = m
        rfl
    | right j =>
        simp only [Function.comp_apply, Semiterm.val_bvar, Fin.addCases_right]
        have hi : (Fin.natAdd 1 j).castSucc = (j.addCast 1).succ := by ext; simp; omega
        rw [hi, Matrix.cons_val_succ, Matrix.appeendr_addCast]
  rw [he]
  have hi : Fin.last (1 + p) = ((0 : Fin 1).addNat p).succ := by ext; simp; omega
  simp [hi]

def finiteBlockAllNot (δ : ℕ → SetTheorySemiformula M 1)
    (ρ : ℕ → SetTheorySemiformula M 2) {p : ℕ} (ks : Fin p → ℕ)
    (A : SetTheorySemiformula M (1 + p)) (a : M) : Prop :=
  BlockAll δ ρ p ks fun s ↦ ∀ m ∈ a, ¬A.Eval (Fin.addCases ![m] s) id

theorem definable_finiteBlockAllNot (δ : ℕ → SetTheorySemiformula M 1)
    (ρ : ℕ → SetTheorySemiformula M 2) {p : ℕ} (ks : Fin p → ℕ)
    (A : SetTheorySemiformula M (1 + p)) :
    ℒₛₑₜ-predicate[M] (finiteBlockAllNot δ ρ ks A) := by
  refine ⟨⟨blockAllFormula δ ρ ks (finiteBlockExclusionBody A), ?_⟩⟩
  intro v
  have hv : (![v 0] : Fin 1 → M) = v := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  rw [← hv, eval_blockAllFormula]
  unfold finiteBlockAllNot
  apply iff_of_eq
  congr 1
  funext s
  exact propext (eval_finiteBlockExclusionBody A (v 0) s)

theorem internallyFinite_blockAllNot (δ : ℕ → SetTheorySemiformula M 1)
    (ρ : ℕ → SetTheorySemiformula M 2)
    (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) {p : ℕ} (ks : Fin p → ℕ)
    (A : SetTheorySemiformula M (1 + p)) {a : M} (ha : IsInternallyFinite a)
    (h : ∀ m ∈ a, blockAllNot δ ρ ks A m) : finiteBlockAllNot δ ρ ks A a := by
  have := definable_blockAllNot δ ρ ks A
  have := definable_finiteBlockAllNot δ ρ ks A
  apply internallyFinite_induction
    (fun a ↦ (∀ m ∈ a, blockAllNot δ ρ ks A m) → finiteBlockAllNot δ ρ ks A a)
    (by definability) ?_ ?_ a ha h
  · intro _
    choose r hr using fun i : Fin p ↦ (hdir (ks i)).nonempty
    exact ⟨r, hr, fun _ _ _ m hm ↦ False.elim (not_mem_empty hm)⟩
  · intro b m ih h'
    have hb := ih (fun x hx ↦ h' x (mem_insert.mpr (Or.inr hx)))
    have hm := h' m (mem_insert.mpr (Or.inl rfl))
    apply BlockAll.mono δ ρ ?_ (BlockAll.and δ ρ hdir hm hb)
    intro s hs x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hs.1
    · exact hs.2 x hx

/-- The cofinal-union lemma in the precise block language of Rubin A.4. -/
theorem internallyFinite_blockEx_union (δ : ℕ → SetTheorySemiformula M 1)
    (ρ : ℕ → SetTheorySemiformula M 2)
    (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) {p : ℕ} (ks : Fin p → ℕ)
    (A : SetTheorySemiformula M (1 + p)) {a : M} (ha : IsInternallyFinite a)
    (h : BlockEx δ ρ p ks fun s ↦ ∃ m ∈ a, A.Eval (Fin.addCases ![m] s) id) :
    ∃ m ∈ a, BlockEx δ ρ p ks fun s ↦ A.Eval (Fin.addCases ![m] s) id := by
  classical
  by_contra hn
  have hnot : ∀ m ∈ a, blockAllNot δ ρ ks A m := by
    intro m hm
    exact (not_blockEx_iff δ ρ).mp (fun he ↦ hn ⟨m, hm, he⟩)
  have hb := internallyFinite_blockAllNot δ ρ hdir ks A ha hnot
  exact blockAll_blockEx_contradiction δ ρ hb h (fun _ hn ⟨m, hm, he⟩ ↦ hn m hm he)

end ZFVP
