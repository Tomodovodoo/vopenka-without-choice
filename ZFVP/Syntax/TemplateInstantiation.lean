import ZFVP.Syntax.StandardPrefixRenaming
import ZFVP.Syntax.MembershipTailTemplates

/-! External formulas produced by the same templates as the internal schema compiler. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundIndexRew {n m : ℕ} (r : Fin n → Fin m) : Rew ℒₛₑₜ Empty n Empty m :=
  Rew.bind (fun i ↦ .bvar (r i)) Empty.elim

theorem eval_boundIndexRew {W : Type*} [SetStructure W] {n m : ℕ}
    (r : Fin n → Fin m) (φ : SetTheorySemisentence n) (b : Fin m → W) :
    (boundIndexRew r ▹ φ).Evalb b ↔ φ.Evalb (b ∘ r) := by
  simp [boundIndexRew, Semiformula.Evalb, Semiformula.eval_rew, Function.comp_def]
  apply Semiformula.eval_iff_of_funEqOn
  intro i
  exact Empty.elim i

namespace MembershipTemplate

def instantiate {a : ℕ} (φ : SetTheorySemisentence a) :
    {m : ℕ} → MembershipTemplate a m → SetTheorySemisentence m
  | _, .fixed ψ => ψ
  | _, .hole r => boundIndexRew r ▹ φ
  | _, .conj s t => s.instantiate φ ⋏ t.instantiate φ
  | _, .disj s t => s.instantiate φ ⋎ t.instantiate φ
  | _, .neg s => ∼s.instantiate φ
  | _, .all s => ∀¹ s.instantiate φ
  | _, .exs s => ∃¹ s.instantiate φ

theorem eval_instantiate {W : Type*} [SetStructure W] {a m : ℕ}
    (φ : SetTheorySemisentence a) (t : MembershipTemplate a m) (v : Fin m → W) :
    (t.instantiate φ).Evalb v ↔ t.Eval (fun w ↦ φ.Evalb w) v := by
  induction t with
  | fixed ψ => rfl
  | hole r => exact eval_boundIndexRew r φ v
  | conj s t ihs iht => exact and_congr (ihs v) (iht v)
  | disj s t ihs iht => exact or_congr (ihs v) (iht v)
  | neg s ih => simpa [instantiate, Eval, Semiformula.Evalb] using not_congr (ih v)
  | all s ih => exact forall_congr' (fun x ↦ ih (x :> v))
  | exs s ih => exact exists_congr (fun x ↦ ih (x :> v))

def instantiateTail {a : ℕ} (k : ℕ) (φ : SetTheorySemisentence (k + a)) :
    {m : ℕ} → MembershipTemplate a m → SetTheorySemisentence (k + m)
  | m, .fixed ψ => boundIndexRew (Fin.castLE (Nat.le_add_left m k)) ▹ ψ
  | _, .hole r => boundIndexRew (prefixIndexMap k r) ▹ φ
  | _, .conj s t => s.instantiateTail k φ ⋏ t.instantiateTail k φ
  | _, .disj s t => s.instantiateTail k φ ⋎ t.instantiateTail k φ
  | _, .neg s => ∼s.instantiateTail k φ
  | _, .all s => ∀¹ s.instantiateTail k φ
  | _, .exs s => ∃¹ s.instantiateTail k φ

theorem eval_instantiateTail {W : Type*} [SetStructure W] {a m k : ℕ}
    (φ : SetTheorySemisentence (k + a)) (t : MembershipTemplate a m)
    (v : Fin m → W) (b : Fin k → W) :
    (t.instantiateTail k φ).Evalb (prefixVector v b) ↔
      t.Eval (fun w ↦ φ.Evalb (prefixVector w b)) v := by
  induction t with
  | fixed ψ =>
    rw [instantiateTail, eval_boundIndexRew]
    have he : prefixVector v b ∘ Fin.castLE (Nat.le_add_left _ k) = v := by
      funext i; exact prefixVector_front v b i
    rw [he]
    rfl
  | hole r =>
    rw [instantiateTail, eval_boundIndexRew, prefixVector_comp_prefixIndexMap]
    rfl
  | conj s t ihs iht => exact and_congr (ihs v) (iht v)
  | disj s t ihs iht => exact or_congr (ihs v) (iht v)
  | neg s ih => simpa [instantiateTail, Eval, Semiformula.Evalb] using not_congr (ih v)
  | all s ih => exact forall_congr' (fun x ↦ ih (x :> v))
  | exs s ih => exact exists_congr (fun x ↦ ih (x :> v))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem compile_encode {a m : ℕ} (φ : SetTheorySemisentence a) (t : MembershipTemplate a m) :
    t.compile (V := V) (encodeMembershipFormula φ) = encodeMembershipFormula (t.instantiate φ) := by
  induction t with
  | fixed ψ => rfl
  | hole r =>
    exact renameMembershipFormula_encode
      (standardTuple_mem_function _ (fun i ↦ natCast_mem_of_lt (r i).isLt)) r
      (fun i ↦ value_standardTuple _ i) (boundIndexRew r) (fun _ ↦ rfl) φ
  | conj s t ihs iht => simp only [compile, instantiate, ihs, iht, encodeMembershipFormula_and]
  | disj s t ihs iht => simp only [compile, instantiate, ihs, iht, encodeMembershipFormula_or]
  | neg s ih => simp only [compile, instantiate, ih, encodeMembershipFormula_neg]
  | all s ih => simp only [compile, instantiate, ih, encodeMembershipFormula_all]
  | exs s ih => simp only [compile, instantiate, ih, encodeMembershipFormula_exs]

theorem compileTail_encode {a m k : ℕ} (φ : SetTheorySemisentence (k + a)) (t : MembershipTemplate a m) :
    t.compileTail (k : V) (encodeMembershipFormula φ) = encodeMembershipFormula (t.instantiateTail k φ) := by
  induction t with
  | @fixed m ψ =>
    simp only [compileTail, instantiateTail, prefixSize_natCast]
    apply renameMembershipFormula_encode
      (standardTuple_mem_function _ (fun i : Fin m ↦ natCast_mem_of_lt (lt_of_lt_of_le i.isLt (Nat.le_add_left m k))))
      (Fin.castLE (Nat.le_add_left m k)) (fun i ↦ value_standardTuple _ i) _ (fun _ ↦ rfl)
  | @hole m r =>
    simp only [compileTail, instantiateTail, prefixSize_natCast]
    have hr : prefixRenaming r (k : V) ∈ (((k + m : ℕ) : V)) ^ (((k + a : ℕ) : V)) := by
      simpa only [prefixSize_natCast] using prefixRenaming_function (V := V) r (n := (k : V)) (by simp)
    apply renameMembershipFormula_encode hr (prefixIndexMap k r) ?_ _ (fun _ ↦ rfl)
    intro i
    rw [prefixRenaming_natCast, value_standardTuple]
  | conj s t ihs iht => simp only [compileTail, instantiateTail, ihs, iht, encodeMembershipFormula_and]
  | disj s t ihs iht => simp only [compileTail, instantiateTail, ihs, iht, encodeMembershipFormula_or]
  | neg s ih => simp only [compileTail, instantiateTail, ih, encodeMembershipFormula_neg, prefixSize_natCast]
  | all s ih => simp only [compileTail, instantiateTail, ih, encodeMembershipFormula_all]
  | exs s ih => simp only [compileTail, instantiateTail, ih, encodeMembershipFormula_exs]

end MembershipTemplate
end ZFVP
