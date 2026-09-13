import ZFVP.ModelTheory.InfinitaryAdequateQuotient

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel.AdequateGenericChain
open AdequateFiniteCondition
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}
  {p₀ : AdequateFiniteCondition M S} (C : AdequateGenericChain M S p₀)

def NamesAt (p : AdequateFiniteCondition M S) (i : ℕ) (a : M.Domain) : Prop :=
  ∃ hi : i < 1 + p.1, ∀ b, p.2.formula.Eval b → b (RightCoordinate.index hi) = a

def Names (i : ℕ) (a : M.Domain) : Prop :=
  C.Eval (ParameterInstance.equalName (S := S) (0 : Fin 1) a) (i :> Fin.elim0)

theorem namesAt_persistent {p q : AdequateFiniteCondition M S} (hpq : Refines p q) {i a}
    (he : NamesAt p i a) : NamesAt q i a := by
  obtain ⟨g, hg⟩ := hpq
  obtain ⟨hi, he⟩ := he
  refine ⟨hi.trans_le (Nat.add_le_add_left g 1), ?_⟩
  intro b hb
  have ht := he _ (hg b hb)
  simpa only [Function.comp_apply, RightCoordinate.embed_index] using ht

theorem names_iff (i : ℕ) (a : M.Domain) : C.Names i a ↔ ∃ k, NamesAt (C.point k) i a := by
  constructor
  · rintro ⟨k, hk, hh⟩
    refine ⟨k, hk 0, ?_⟩
    intro b hb
    exact (ParameterInstance.eval_equalName (S := S) (0 : Fin 1) a
      (fun j ↦ b (RightCoordinate.index (hk j)))).mp (hh b hb)
  · rintro ⟨k, hk, hh⟩
    have hfit : ∀ j : Fin 1, (i :> Fin.elim0) j < 1 + (C.point k).1 := by
      intro j
      cases j using Fin.cases with
      | zero => exact hk
      | succ j => exact j.elim0
    refine ⟨k, hfit, ?_⟩
    intro b hb
    exact (ParameterInstance.eval_equalName _ _ _).mpr (hh b hb)

theorem exists_name (a : M.Domain) : ∃ i, C.Names i a := by
  let φ := ParameterInstance.equalName (S := S) (0 : Fin 1) a
  have h : C.Eval φ.exs Fin.elim0 := C.eval_of_valid _ _ (by
    intro b
    apply (ParameterInstance.eval_exs _ _).mpr
    exact ⟨a, (ParameterInstance.eval_equalName _ _ _).mpr rfl⟩)
  exact (C.eval_exs φ Fin.elim0).mp h

noncomputable def oldCoordinate (a : M.Domain) : ℕ := (C.exists_name a).choose

theorem oldCoordinate_names (a : M.Domain) : C.Names (C.oldCoordinate a) a := (C.exists_name a).choose_spec

noncomputable def oldEmbedding (a : M.Domain) : C.Domain := C.classOf (C.oldCoordinate a)

theorem names_unique {i a b} (ha : C.Names i a) (hb : C.Names i b) : a = b := by
  obtain ⟨k, hk⟩ := (C.names_iff i a).mp ha
  obtain ⟨l, hl⟩ := (C.names_iff i b).mp hb
  obtain ⟨hi, hh⟩ := namesAt_persistent (C.refines (Nat.le_max_left k l)) hk
  obtain ⟨hj, hg⟩ := namesAt_persistent (C.refines (Nat.le_max_right k l)) hl
  obtain ⟨e, he⟩ := (C.point (max k l)).2.nonempty C.adequate
  exact (hh e he).symm.trans (hg e he)

theorem names_of_equal {i j a} (he : C.Equal i j) (ha : C.Names i a) : C.Names j a := by
  apply C.eval_of_equal _ (ts := i :> Fin.elim0) (us := j :> Fin.elim0) ?_ ha
  intro k
  cases k using Fin.cases with
  | zero => exact he
  | succ k => exact k.elim0

theorem oldEmbedding_injective : Function.Injective C.oldEmbedding := by
  intro a b he
  have hr := C.classOf_eq_iff.mp he
  exact C.names_unique (C.names_of_equal hr (C.oldCoordinate_names a)) (C.oldCoordinate_names b)

/-- A finite tuple of names is simultaneously fixed at every sufficiently late condition. -/
theorem named_tuple_eventually {n} (ts : Fin n → ℕ) (b : Fin n → M.Domain)
    (hn : ∀ i, C.Names (ts i) (b i)) :
    ∃ k, ∀ l, k ≤ l → ∃ ht : ∀ i, ts i < 1 + (C.point l).1,
      ∀ a, (C.point l).2.formula.Eval a → (fun i ↦ a (RightCoordinate.index (ht i))) = b := by
  classical
  choose k hk using fun i ↦ (C.names_iff _ _).mp (hn i)
  refine ⟨Finset.univ.sup k, ?_⟩
  intro l hl
  have hkl (i : Fin n) : k i ≤ l := (Finset.le_sup (by simp)).trans hl
  have hname (i : Fin n) := namesAt_persistent (C.refines (hkl i)) (hk i)
  choose ht hh using hname
  exact ⟨ht, fun a ha ↦ funext fun i ↦ hh i a ha⟩

/-- Generic truth at a finite tuple of old names is exactly its original weak truth. -/
theorem eval_named_tuple {n} (φ : ParameterInstance M S n) (ts : Fin n → ℕ)
    (b : Fin n → M.Domain) (hn : ∀ i, C.Names (ts i) (b i)) :
    C.Eval φ ts ↔ φ.Eval b := by
  obtain ⟨k, hk⟩ := C.named_tuple_eventually ts b hn
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨ht, hh⟩ := hk (max k l) (Nat.le_max_left _ _)
    obtain ⟨hu, hu'⟩ := evalAt_persistent (C.refines (Nat.le_max_right k l)) hl
    obtain ⟨a, ha⟩ := (C.point (max k l)).2.nonempty C.adequate
    exact hh a ha ▸ hu' a ha
  · intro h
    obtain ⟨ht, hh⟩ := hk k (le_refl k)
    exact ⟨k, ht, fun a ha ↦ (hh a ha).symm ▸ h⟩

theorem quotientEval_oldEmbedding {n} (φ : ParameterInstance M S n) (b : Fin n → M.Domain) :
    C.QuotientEval φ (C.oldEmbedding ∘ b) ↔ φ.Eval b := by
  change C.QuotientEval φ (C.classOf ∘ (C.oldCoordinate ∘ b)) ↔ _
  rw [C.quotientEval_classOf]
  exact C.eval_named_tuple φ _ b (fun i ↦ C.oldCoordinate_names (b i))

theorem no_name_zero (a : M.Domain) : ¬C.Names 0 a := by
  intro hn
  obtain ⟨k, hk⟩ := (C.names_iff 0 a).mp hn
  obtain ⟨l, hl⟩ := C.avoids a
  obtain ⟨hi, hh⟩ := namesAt_persistent (C.refines (Nat.le_max_left k l)) hk
  obtain ⟨b, hb⟩ := (C.point (max k l)).2.nonempty C.adequate
  have he : RightCoordinate.index hi = Formula.lastCoordinate (C.point (max k l)).1 := by
    apply Fin.ext
    simp [RightCoordinate.index, Formula.lastCoordinate_val]
  exact hl (max k l) (Nat.le_max_right _ _) b hb (he ▸ hh b hb)

theorem newPoint_not_oldImage : C.classOf 0 ∉ Set.range C.oldEmbedding := by
  rintro ⟨a, ha⟩
  exact C.no_name_zero a (C.names_of_equal (C.classOf_eq_iff.mp ha) (C.oldCoordinate_names a))

end WeakModel.AdequateGenericChain
end ZFVP.Infinitary

