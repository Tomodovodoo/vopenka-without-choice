import ZFVP.ModelTheory.InfinitaryFiniteSupport

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace SequenceClosure
variable {L : Language}

def negMap : TaggedFormula L → TaggedFormula L
  | ⟨n, .conj f⟩ => ⟨n, .conj fun i ↦ .neg (f i)⟩
  | a => a

def exsMap : TaggedFormula L → TaggedFormula L
  | ⟨n + 1, .conj f⟩ => ⟨n, .conj fun i ↦ .exs (f i)⟩
  | a => a

def qMap : TaggedFormula L → TaggedFormula L
  | ⟨n + 1, .conj f⟩ => ⟨n, .conj fun i ↦ .q (f i)⟩
  | a => a

def andMap (a b : TaggedFormula L) : TaggedFormula L :=
  if h : b.1 = a.1 then
    match a.2 with
    | .conj f => ⟨a.1, .conj fun i ↦ Formula.and (h ▸ b.2) (f i)⟩
    | _ => a
  else a

def unary (a : TaggedFormula L) : Set (TaggedFormula L) := {negMap a, exsMap a, qMap a}

theorem unary_countable (a : TaggedFormula L) : (unary a).Countable :=
  ((Set.countable_singleton (qMap a)).insert (exsMap a)).insert (negMap a)

open HenkinLanguage

theorem negMap_supported {a : TaggedFormula (limit L)} (ha : FiniteSupport a.2) :
    FiniteSupport (negMap a).2 := by
  rcases a with ⟨n, φ⟩
  cases φ with
  | fo φ => exact ha
  | neg φ => exact ha
  | exs φ => exact ha
  | q φ => exact ha
  | conj f =>
    change FiniteSupport (.conj fun i ↦ .neg (f i))
    filter_upwards [ha] with k hk
    exact congrArg Formula.conj (funext fun i ↦ congrArg Formula.neg (congrFun (Formula.conj.inj hk) i))

theorem exsMap_supported {a : TaggedFormula (limit L)} (ha : FiniteSupport a.2) :
    FiniteSupport (exsMap a).2 := by
  rcases a with ⟨n, φ⟩
  cases n with
  | zero => exact ha
  | succ n =>
    cases φ with
    | fo φ => exact ha
    | neg φ => exact ha
    | exs φ => exact ha
    | q φ => exact ha
    | conj f =>
      change FiniteSupport (.conj fun i ↦ .exs (f i))
      filter_upwards [ha] with k hk
      exact congrArg Formula.conj (funext fun i ↦ congrArg Formula.exs (congrFun (Formula.conj.inj hk) i))

theorem qMap_supported {a : TaggedFormula (limit L)} (ha : FiniteSupport a.2) :
    FiniteSupport (qMap a).2 := by
  rcases a with ⟨n, φ⟩
  cases n with
  | zero => exact ha
  | succ n =>
    cases φ with
    | fo φ => exact ha
    | neg φ => exact ha
    | exs φ => exact ha
    | q φ => exact ha
    | conj f =>
      change FiniteSupport (.conj fun i ↦ .q (f i))
      filter_upwards [ha] with k hk
      exact congrArg Formula.conj (funext fun i ↦ congrArg Formula.q (congrFun (Formula.conj.inj hk) i))

theorem andMap_supported {a b : TaggedFormula (limit L)}
    (ha : FiniteSupport a.2) (hb : FiniteSupport b.2) : FiniteSupport (andMap a b).2 := by
  rcases a with ⟨n, φ⟩
  rcases b with ⟨m, ψ⟩
  by_cases h : m = n
  · subst m
    cases φ with
    | fo φ =>
      have he : andMap (⟨n, .fo φ⟩ : TaggedFormula (limit L)) ⟨n, ψ⟩ = ⟨n, .fo φ⟩ := by simp [andMap]
      rw [he]
      exact ha
    | neg φ =>
      have he : andMap (⟨n, .neg φ⟩ : TaggedFormula (limit L)) ⟨n, ψ⟩ = ⟨n, .neg φ⟩ := by simp [andMap]
      rw [he]
      exact ha
    | exs φ =>
      have he : andMap (⟨n, .exs φ⟩ : TaggedFormula (limit L)) ⟨n, ψ⟩ = ⟨n, .exs φ⟩ := by simp [andMap]
      rw [he]
      exact ha
    | q φ =>
      have he : andMap (⟨n, .q φ⟩ : TaggedFormula (limit L)) ⟨n, ψ⟩ = ⟨n, .q φ⟩ := by simp [andMap]
      rw [he]
      exact ha
    | conj f =>
      have he : andMap (⟨n, .conj f⟩ : TaggedFormula (limit L)) ⟨n, ψ⟩ =
          ⟨n, .conj fun i ↦ ψ.and (f i)⟩ := by simp [andMap]
      rw [he]
      filter_upwards [ha, hb] with k hk hp
      apply congrArg Formula.conj
      funext i
      rw [Formula.lMap_and, hp, congrFun (Formula.conj.inj hk) i]
  · have he : andMap (⟨n, φ⟩ : TaggedFormula (limit L)) ⟨m, ψ⟩ = ⟨n, φ⟩ := by simp [andMap, h]
    rw [he]
    exact ha

theorem unary_supported {a b : TaggedFormula (limit L)} (ha : FiniteSupport a.2)
    (hb : b ∈ unary a) : FiniteSupport b.2 := by
  rcases hb with rfl | rfl | rfl
  · exact negMap_supported ha
  · exact exsMap_supported ha
  · exact qMap_supported ha

end SequenceClosure
end ZFVP.Infinitary

