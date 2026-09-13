import ZFVP.ModelTheory.InfinitaryHenkinStep
import ZFVP.ModelTheory.InfinitaryLanguageComposition

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinLanguage
variable {L : Language}

instance withConstants_encodable [L.Encodable] {C : Type*} [Encodable C] :
    (WithConstants L C).Encodable :=
  ⟨fun k ↦ inferInstanceAs (Encodable (L.Func k ⊕ (Language.constant C).Func k)),
    fun k ↦ inferInstanceAs (Encodable (L.Rel k ⊕ (Language.constant C).Rel k))⟩

/-- Rename only the added constant symbols. -/
def constantsMap {C D : Type*} (ρ : C → D) : WithConstants L C →ᵥ WithConstants L D where
  func f := match f with
    | .inl f => .inl f
    | .inr (.const c) => .inr (.const (ρ c))
  rel r := match r with
    | .inl r => .inl r
    | .inr r => r.elim

abbrev stage (L : Language) (n : ℕ) := WithConstants L (Fin n)
abbrev limit (L : Language) := WithConstants L ℕ

def next (n : ℕ) : stage L n →ᵥ stage L (n + 1) := constantsMap Fin.castSucc

def intoLimit (n : ℕ) : stage L n →ᵥ limit L := constantsMap Fin.val

/-- Flatten the fresh Unit constant into the next numbered constant. -/
def flatten (n : ℕ) : WithConstants (stage L n) Unit →ᵥ stage L (n + 1) where
  func f := match f with
    | .inl (.inl f) => .inl f
    | .inl (.inr (.const c)) => .inr (.const c.castSucc)
    | .inr (.const _) => .inr (.const (Fin.last n))
  rel r := match r with
    | .inl (.inl r) => .inl r
    | .inl (.inr r) => r.elim
    | .inr r => r.elim

def unflatten (n : ℕ) : stage L (n + 1) →ᵥ WithConstants (stage L n) Unit where
  func f := match f with
    | .inl f => .inl (.inl f)
    | .inr (.const c) => Fin.lastCases (.inr (.const ())) (fun i ↦ .inl (.inr (.const i))) c
  rel r := match r with
    | .inl r => .inl (.inl r)
    | .inr r => r.elim

theorem unflatten_flatten_func (n : ℕ) {k} (f : (WithConstants (stage L n) Unit).Func k) :
    (unflatten n).func ((flatten n).func f) = f := by
  cases f with
  | inl f => cases f with
      | inl f => rfl
      | inr f => cases f; simp only [flatten, unflatten, WithConstants, Language.add, Language.constant, stage, Fin.lastCases_castSucc]
  | inr f => cases f with
      | const c => cases c; simp only [flatten, unflatten, WithConstants, Language.add, Language.constant, stage, Fin.lastCases_last]

theorem unflatten_flatten_rel (n : ℕ) {k} (r : (WithConstants (stage L n) Unit).Rel k) :
    (unflatten n).rel ((flatten n).rel r) = r := by
  cases r with
  | inl r => cases r with
      | inl r => rfl
      | inr r => exact r.elim
  | inr r => exact r.elim

/-- A refutation after flattening would give a refutation before flattening. -/
theorem consistent_flatten [L.Eq] (n : ℕ) {Γ : Set (Sentence (WithConstants (stage L n) Unit))}
    (hc : KeislerDerivation.Consistent Γ) :
    KeislerDerivation.Consistent (Formula.lMap (flatten n) '' Γ) :=
  LanguageMap.consistent_image (flatten n) (unflatten n) rfl
    (unflatten_flatten_func n) (unflatten_flatten_rel n) hc

/-- Send constants beyond a positive stage back to its first constant. -/
def fromLimit (n : ℕ) : limit L →ᵥ stage L (n + 1) :=
  constantsMap (fun i ↦ if h : i < n + 1 then ⟨i, h⟩ else 0)

theorem fromLimit_intoLimit_func (n : ℕ) {k} (f : (stage L (n + 1)).Func k) :
    (fromLimit n).func ((intoLimit (n + 1)).func f) = f := by
  cases f with
  | inl f => rfl
  | inr f => cases f with
      | const i => simp only [fromLimit, intoLimit, constantsMap, dite_eq_left i.isLt]; rfl

theorem fromLimit_intoLimit_rel (n : ℕ) {k} (r : (stage L (n + 1)).Rel k) :
    (fromLimit n).rel ((intoLimit (n + 1)).rel r) = r := by
  cases r with
  | inl r => rfl
  | inr r => exact r.elim

theorem consistent_intoLimit [L.Eq] (n : ℕ) {Γ : Set (Sentence (stage L (n + 1)))}
    (hc : KeislerDerivation.Consistent Γ) :
    KeislerDerivation.Consistent (Formula.lMap (intoLimit (n + 1)) '' Γ) :=
  LanguageMap.consistent_image (intoLimit (n + 1)) (fromLimit n) rfl
    (fromLimit_intoLimit_func n) (fromLimit_intoLimit_rel n) hc

def between {n m : ℕ} (h : n ≤ m) : stage L n →ᵥ stage L m := constantsMap (Fin.castLE h)

theorem constantsMap_comp {C D E : Type*} (ρ : C → D) (σ : D → E) :
    (constantsMap (L := L) σ).comp (constantsMap ρ) = constantsMap (σ ∘ ρ) := by
  apply LanguageMap.hom_ext
  · intro k f
    cases f with
    | inl f => rfl
    | inr f => cases f; rfl
  · intro k r
    cases r with
    | inl r => rfl
    | inr r => exact r.elim

theorem intoLimit_between {n m} (h : n ≤ m) :
    (intoLimit (L := L) m).comp (between h) = intoLimit n := by
  rw [intoLimit, between, constantsMap_comp]
  rfl

theorem intoLimit_next (n : ℕ) : (intoLimit (L := L) (n + 1)).comp (next n) = intoLimit n := by
  rw [intoLimit, next, constantsMap_comp]
  rfl

theorem flatten_add (n : ℕ) : (flatten (L := L) n).comp
    (Language.Hom.add₁ (stage L n) (Language.constant Unit)) = next n := by
  apply LanguageMap.hom_ext
  · intro k f
    cases f with
    | inl f => rfl
    | inr f => cases f; rfl
  · intro k r
    cases r with
    | inl r => rfl
    | inr r => exact r.elim

theorem intoLimit_original : (intoLimit (L := L) 0).comp
    (Language.Hom.add₁ L (Language.constant (Fin 0))) = Language.Hom.add₁ L (Language.constant ℕ) := by
  apply LanguageMap.hom_ext <;> intros <;> rfl

theorem formula_intoLimit_between {n m k} (h : n ≤ m) (φ : Formula (stage L n) k) :
    (φ.lMap (between h)).lMap (intoLimit m) = φ.lMap (intoLimit n) := by
  rw [LanguageMap.formula_comp, intoLimit_between]

theorem formula_intoLimit_next {n k} (φ : Formula (stage L n) k) :
    (φ.lMap (next n)).lMap (intoLimit (n + 1)) = φ.lMap (intoLimit n) := by
  rw [LanguageMap.formula_comp, intoLimit_next]

end HenkinLanguage
end ZFVP.Infinitary


