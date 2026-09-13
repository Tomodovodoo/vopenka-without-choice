import ZFVP.ModelTheory.InfinitaryGenericOldEmbedding

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.CoordinateTerm
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}

def EvalAt (p : H.FiniteCondition) {n} (φ : Formula (limit L) n)
    (ts : Fin n → CoordinateTerm (limit L)) : Prop :=
  ∃ hs : ∀ i, (ts i).1 ≤ 1 + p.1,
    ∀ b, Formula.WeakEval H.weakQuantifier p.2.formula b →
      Formula.WeakEval H.weakQuantifier φ
        (fun i ↦ (ts i).2.val (b ∘ Formula.rightEmbed (hs i)) Empty.elim)

theorem evalAt_persistent {p q : H.FiniteCondition} (hpq : Refines p q) {n}
    {φ : Formula (limit L) n} {ts : Fin n → CoordinateTerm (limit L)}
    (he : EvalAt p φ ts) : EvalAt q φ ts := by
  obtain ⟨h, hh⟩ := hpq
  obtain ⟨hs, he⟩ := he
  refine ⟨fun i ↦ (hs i).trans (Nat.add_le_add_left h 1), ?_⟩
  intro b hb
  have := he _ (hh b hb)
  simpa only [Function.comp_def, Formula.rightEmbed_trans] using this

theorem evalAt_congr {p : H.FiniteCondition} {n} {φ : Formula (limit L) n}
    {ss ts : Fin n → CoordinateTerm (limit L)}
    (he : ∀ i, EqualAt p (ss i) (ts i)) (hφ : EvalAt p φ ss) : EvalAt p φ ts := by
  classical
  choose hs ht he using he
  obtain ⟨hs', hh⟩ := hφ
  refine ⟨ht, ?_⟩
  intro b hb
  have hv : (fun i ↦ (ss i).2.val (b ∘ Formula.rightEmbed (hs' i)) Empty.elim) =
      (fun i ↦ (ts i).2.val (b ∘ Formula.rightEmbed (ht i)) Empty.elim) := by
    funext i
    exact he i b hb
  exact hv ▸ hh b hb

def Eval (c : ℕ → H.FiniteCondition) {n} (φ : Formula (limit L) n)
    (ts : Fin n → CoordinateTerm (limit L)) : Prop := ∃ k, EvalAt (c k) φ ts

theorem eval_congr (c : ℕ → H.FiniteCondition)
    (hc : ∀ {i j}, i ≤ j → Refines (c i) (c j)) {n} {φ : Formula (limit L) n}
    {ss ts : Fin n → CoordinateTerm (limit L)}
    (he : ∀ i, Rel c (ss i) (ts i)) (hφ : Eval c φ ss) : Eval c φ ts := by
  classical
  choose k hk using he
  obtain ⟨j, hj⟩ := hφ
  let m := max j (Finset.univ.sup k)
  have hjm : j ≤ m := Nat.le_max_left _ _
  have hkm (i : Fin n) : k i ≤ m :=
    (Finset.le_sup (f := k) (Finset.mem_univ i)).trans (Nat.le_max_right _ _)
  exact ⟨m, evalAt_congr (fun i ↦ equalAt_persistent (hc (hkm i)) (hk i))
    (evalAt_persistent (hc hjm) hj)⟩

theorem eval_congr_iff (c : ℕ → H.FiniteCondition)
    (hc : ∀ {i j}, i ≤ j → Refines (c i) (c j)) {n} {φ : Formula (limit L) n}
    {ss ts : Fin n → CoordinateTerm (limit L)} (he : ∀ i, Rel c (ss i) (ts i)) :
    Eval c φ ss ↔ Eval c φ ts :=
  ⟨eval_congr c hc he, eval_congr c hc (fun i ↦ rel_symm c (he i))⟩

end HenkinConstruction.FragmentExtension.CoordinateTerm
end ZFVP.Infinitary
