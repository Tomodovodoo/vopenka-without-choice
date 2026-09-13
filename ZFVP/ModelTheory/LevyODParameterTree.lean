import ZFVP.ModelTheory.LevyODLocalized
import ZFVP.ModelTheory.LevyStageDefinable

/-! The converse half of the Solovay model bridge: a set of the Levy extension that is ordinal
definable from a class of localized parameters is hereditarily definable from ground sets, reals
and ordinals.

Two ingredients. First, definability from allowed parameters is closed under substituting the
definitions of the parameters: a set defined by a formula from finitely many sets that are
themselves definable from ground sets, reals and ordinals is again so definable. The formula is
built by replacing the parameters one at a time with an existentially quantified variable pinned
down by the defining formula of that parameter, the new parameters being appended at the end of the
list.

Second, a parameter tree of finite depth over localized allowed parameters is localized, hence a
set of the extension that is ordinal definable through such a tree is definable from ground sets,
reals and ordinals, and hereditary ordinal definability gives hereditary definability.

The depth restriction is real: `IsParameterTree` only asks for a set `S` closed under taking the
components of the Kuratowski pairs it contains, and in a model of `ZF` whose membership is not
well founded from the outside such an `S` can carry a pair tree of nonstandard finite depth, which
has no external derivation as `IsFinitaryParameterTree`. The internal rank of `⟨a, b⟩ₖ` is above
those of `a` and `b`, so the descent is internally well founded, but that gives an induction only
for predicates definable in the model, and finite depth is not one. The statements below therefore
take either a tree of finite depth or the hypothesis that every parameter tree has finite depth. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ### Substituting the definition of the first parameter -/

/-- `∃ c, (∀ y, y ∈ c ↔ φ(y, w)) ∧ ψ(b, c, t)`, with free variables `b`, then `t`, then `w`. It
removes the first parameter of `ψ` and appends the parameters of `φ` at the end. -/
def definedFromFirst {N m : ℕ} (φ : SetTheorySemisentence (m + 1))
    (ψ : SetTheorySemisentence (N + 1 + 1)) : SetTheorySemisentence (N + m + 1) :=
  ∃¹ ((∀¹ (((∼(memAtom.subst ![#0, #1])) ⋎
        (φ.subst (#0 :> fun j ↦ #((Fin.natAdd N j).succ.succ.succ)))) ⋏
      ((∼(φ.subst (#0 :> fun j ↦ #((Fin.natAdd N j).succ.succ.succ)))) ⋎
        (memAtom.subst ![#0, #1])))) ⋏
    (ψ.subst (#1 :> #0 :> fun i ↦ #((Fin.castAdd m i).succ.succ))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_definedFromFirst {N m : ℕ} (φ : SetTheorySemisentence (m + 1))
    (ψ : SetTheorySemisentence (N + 1 + 1)) (b : V) (t : Fin N → V) (w : Fin m → V) :
    (definedFromFirst φ ψ).Evalb (b :> Fin.append t w) ↔
      ∃ c : V, (∀ y, y ∈ c ↔ φ.Evalb (y :> w)) ∧ ψ.Evalb (b :> c :> t) := by
  simp [definedFromFirst, memAtom, Semiformula.eval_substs, Matrix.comp_vecCons',
    Function.comp_def, Matrix.constant_eq_singleton]
  constructor
  · rintro ⟨c, hc, hψ⟩
    exact ⟨c, fun y ↦ ⟨fun hy ↦ (hc y).1.resolve_left (not_not.mpr hy),
      fun hφ ↦ (hc y).2.resolve_left (not_not.mpr hφ)⟩, hψ⟩
  · rintro ⟨c, hc, hψ⟩
    refine ⟨c, fun y ↦ ⟨?_, ?_⟩, hψ⟩
    · by_cases hy : y ∈ c
      · exact Or.inr ((hc y).mp hy)
      · exact Or.inl hy
    · by_cases hφ : φ.Evalb (y :> w)
      · exact Or.inr ((hc y).mpr hφ)
      · exact Or.inl hφ

namespace ForcingContext

variable {A : ForcingContext V}

/-- Definability from allowed parameters, with the first `n` parameters only assumed definable and
all later ones assumed allowed. Induction on `n` replaces the parameters one at a time. -/
theorem groundRealDefinable_of_definables_aux :
    ∀ (n N : ℕ) (ψ : SetTheorySemisentence (N + 1)) (v : Fin N → A.Model) (x : A.Model),
      (∀ i, A.IsGroundRealDefinable (v i)) →
      (∀ i : Fin N, n ≤ (i : ℕ) → A.IsSolovayParameter (v i)) →
      (∀ b, b ∈ x ↔ ψ.Evalb (b :> v)) → A.IsGroundRealDefinable x := by
  intro n
  induction n with
  | zero =>
    intro N ψ v x _ hs hx
    exact ⟨N, ψ, v, fun i ↦ hs i (Nat.zero_le _), hx⟩
  | succ n ih =>
    intro N
    cases N with
    | zero =>
      intro ψ v x _ _ hx
      exact ⟨0, ψ, v, fun i ↦ i.elim0, hx⟩
    | succ N =>
      intro ψ v x hv hs hx
      obtain ⟨m, φ, w, hw, hdefw⟩ := hv 0
      have hcons : (v 0 :> Fin.tail v) = v := Fin.cons_self_tail v
      have key : ∀ b : A.Model,
          b ∈ x ↔ (definedFromFirst φ ψ).Evalb (b :> Fin.append (Fin.tail v) w) := by
        intro b
        rw [eval_definedFromFirst]
        constructor
        · intro hb
          refine ⟨v 0, fun y ↦ hdefw y, ?_⟩
          rw [show (b :> v 0 :> Fin.tail v) = (b :> v) by rw [hcons]]
          exact (hx b).mp hb
        · rintro ⟨c, hc, hψ⟩
          have hcv : c = v 0 := mem_ext (fun y ↦ by rw [hc y, hdefw y])
          rw [hx b, ← hcons]
          rw [hcv] at hψ
          exact hψ
      refine ih (N + m) (definedFromFirst φ ψ) (Fin.append (Fin.tail v) w) x ?_ ?_ key
      · intro i
        refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
        · rw [Fin.append_left]
          exact hv j.succ
        · rw [Fin.append_right]
          exact groundRealDefinable_of_parameter (hw j)
      · intro i
        refine Fin.addCases
          (motive := fun i ↦ n ≤ (i : ℕ) → A.IsSolovayParameter (Fin.append (Fin.tail v) w i))
          (fun j hj ↦ ?_) (fun j _ ↦ ?_) i
        · rw [Fin.append_left]
          refine hs j.succ ?_
          simp only [Fin.val_castAdd] at hj
          simpa [Fin.val_succ] using Nat.succ_le_succ hj
        · rw [Fin.append_right]
          exact hw j

/-- A set defined by a formula from finitely many sets that are themselves definable from ground
sets, reals and ordinals is definable from ground sets, reals and ordinals. -/
theorem groundRealDefinable_of_definable_from_definables {n : ℕ} {x : A.Model}
    (v : Fin n → A.Model) (hv : ∀ i, A.IsGroundRealDefinable (v i))
    (ψ : SetTheorySemisentence (n + 1)) (hx : ∀ b, b ∈ x ↔ ψ.Evalb (b :> v)) :
    A.IsGroundRealDefinable x :=
  groundRealDefinable_of_definables_aux n n ψ v x hv
    (fun i hi ↦ absurd (i.isLt.trans_le hi) (Nat.lt_irrefl _)) hx

end ForcingContext

/-! ### Hereditary ordinal definability through parameter trees of finite depth -/

section

variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Hereditary ordinal definability from the parameter class, through parameter trees of finite
depth. -/
def IsHODFinitary (Pf : SetTheorySemisentence 2) (x p : M) : Prop :=
  IsODFinitary Pf x p ∧ ∀ y ∈ transitiveClosure x, IsODFinitary Pf y p

theorem isHOD_of_finitary {Pf : SetTheorySemisentence 2} {x p : M} (h : IsHODFinitary Pf x p) :
    IsHOD Pf x p :=
  ⟨isOD_of_finitary h.1, fun y hy ↦ isOD_of_finitary (h.2 y hy)⟩

/-- The transitive closure of a singleton is the set together with the transitive closure of the
set. -/
theorem transitiveClosure_singleton_subset (x : M) :
    transitiveClosure ({x} : M) ⊆ insert x (transitiveClosure x) := by
  refine transitiveClosure_minimal _ _ ?_ ⟨fun u hu z hz ↦ ?_⟩
  · rw [singleton_subset_iff_mem]
    exact mem_insert.mpr (Or.inl rfl)
  · rcases mem_insert.mp hu with rfl | hu
    · exact mem_insert.mpr (Or.inr (subset_transitiveClosure u z hz))
    · exact mem_insert.mpr (Or.inr ((transitiveClosure_transitive x).mem_trans hz hu))

end

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
  (Pf : SetTheorySemisentence 2) (p : (levyContext κ hG).Model)

include hG in
/-- A parameter tree of finite depth over a class of localized parameters is localized. -/
theorem isLocalized_finitaryParameterTree (hω : (ω : V) ∈ κ)
    (hPf : ∀ y : (levyContext κ hG).Model, Pf.Evalb ![y, p] → IsLocalized hG y)
    {P : (levyContext κ hG).Model} (h : IsFinitaryParameterTree Pf p P) : IsLocalized hG P :=
  isLocalized_of_finitaryParameterTree hG Pf p (isAllowed_localized hG Pf p hω hPf) h

include hG in
/-- If every parameter tree of the class has finite depth, then every parameter tree over a class
of localized parameters is localized. -/
theorem isLocalized_parameterTree_of_finitary_hypothesis (hω : (ω : V) ∈ κ)
    (hfin : ∀ P : (levyContext κ hG).Model, IsParameterTree Pf P p → IsFinitaryParameterTree Pf p P)
    (hPf : ∀ y : (levyContext κ hG).Model, Pf.Evalb ![y, p] → IsLocalized hG y)
    {P : (levyContext κ hG).Model} (h : IsParameterTree Pf P p) : IsLocalized hG P :=
  isLocalized_finitaryParameterTree hG Pf p hω hPf (hfin P h)

include hAC hU hc hω hG in
/-- A set of the Levy extension that is ordinal definable through a parameter tree of finite depth
over a class of localized parameters is definable from ground sets, reals and ordinals. -/
theorem groundRealDefinable_of_isODFinitary
    (hPf : ∀ y : (levyContext κ hG).Model, Pf.Evalb ![y, p] → IsLocalized hG y)
    {x : (levyContext κ hG).Model} (hx : IsODFinitary Pf x p) :
    (levyContext κ hG).IsGroundRealDefinable x := by
  obtain ⟨n, φ, v, hv, hdef⟩ :=
    isLocalized_isODFinitary_parameters hG Pf p hω (isAllowed_localized hG Pf p hω hPf) hx
  exact ForcingContext.groundRealDefinable_of_definable_from_definables v
    (fun i ↦ groundRealDefinable_of_isLocalized hAC hU hc hω hG (hv i)) φ hdef

include hAC hU hc hω hG in
/-- A hereditarily ordinal definable set of the Levy extension, through parameter trees of finite
depth over a class of localized parameters, is hereditarily definable from ground sets, reals and
ordinals. -/
theorem hereditarilyGroundRealDefinable_of_isHODFinitary
    (hPf : ∀ y : (levyContext κ hG).Model, Pf.Evalb ![y, p] → IsLocalized hG y)
    {x : (levyContext κ hG).Model} (hx : IsHODFinitary Pf x p) :
    (levyContext κ hG).IsHereditarilyGroundRealDefinable x := by
  intro y hy
  rcases mem_insert.mp (transitiveClosure_singleton_subset x y hy) with rfl | hy'
  · exact groundRealDefinable_of_isODFinitary hAC hU hc hω hG Pf p hPf hx.1
  · exact groundRealDefinable_of_isODFinitary hAC hU hc hω hG Pf p hPf (hx.2 y hy')

include hAC hU hc hω hG in
/-- If every parameter tree of the class has finite depth, an ordinal definable set of the Levy
extension is definable from ground sets, reals and ordinals. -/
theorem groundRealDefinable_of_isOD
    (hfin : ∀ P : (levyContext κ hG).Model, IsParameterTree Pf P p → IsFinitaryParameterTree Pf p P)
    (hPf : ∀ y : (levyContext κ hG).Model, Pf.Evalb ![y, p] → IsLocalized hG y)
    {x : (levyContext κ hG).Model} (hx : IsOD Pf x p) :
    (levyContext κ hG).IsGroundRealDefinable x := by
  obtain ⟨α, φ, P, hα, hcode, hP, hmem, he⟩ := hx
  exact groundRealDefinable_of_isODFinitary hAC hU hc hω hG Pf p hPf
    ⟨α, φ, P, hα, hcode, hfin P hP, hmem, he⟩

include hAC hU hc hω hG in
/-- If every parameter tree of the class has finite depth, a hereditarily ordinal definable set of
the Levy extension is hereditarily definable from ground sets, reals and ordinals. -/
theorem hereditarilyGroundRealDefinable_of_isHOD
    (hfin : ∀ P : (levyContext κ hG).Model, IsParameterTree Pf P p → IsFinitaryParameterTree Pf p P)
    (hPf : ∀ y : (levyContext κ hG).Model, Pf.Evalb ![y, p] → IsLocalized hG y)
    {x : (levyContext κ hG).Model} (hx : IsHOD Pf x p) :
    (levyContext κ hG).IsHereditarilyGroundRealDefinable x := by
  intro y hy
  rcases mem_insert.mp (transitiveClosure_singleton_subset x y hy) with rfl | hy'
  · exact groundRealDefinable_of_isOD hAC hU hc hω hG Pf p hfin hPf hx.1
  · exact groundRealDefinable_of_isOD hAC hU hc hω hG Pf p hfin hPf (hx.2 y hy')

end

end ZFVP
