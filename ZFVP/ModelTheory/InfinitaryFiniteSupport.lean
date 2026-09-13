import ZFVP.ModelTheory.InfinitaryHenkinLanguage
import ZFVP.ModelTheory.InfinitaryFragmentClosure
import Mathlib.Order.Filter.AtTopBot.Basic

namespace ZFVP.Infinitary
open LO LO.FirstOrder Filter
namespace HenkinLanguage
variable {L : Language}

/-- Retain the first `n + 1` constants and send later constants to zero. -/
def truncate (n : ℕ) : limit L →ᵥ limit L :=
  (intoLimit (n + 1)).comp (fromLimit n)

theorem truncate_rel (n : ℕ) {k} (r : (limit L).Rel k) :
    (truncate n).rel r = r := by
  cases r with
  | inl r => rfl
  | inr r => exact r.elim

theorem eventually_truncate_func {k} (f : (limit L).Func k) :
    ∀ᶠ n in atTop, (truncate n).func f = f := by
  cases f with
  | inl f => exact Eventually.of_forall fun _ ↦ rfl
  | inr f => cases f with
      | const i =>
        filter_upwards [eventually_ge_atTop i] with n hn
        have hi : i < n + 1 := Nat.lt_succ_of_le hn
        simp only [truncate, Language.Hom.comp, fromLimit, intoLimit, constantsMap,
          WithConstants, Language.add, Language.constant, limit, stage, Function.comp_apply, dite_eq_left hi]

theorem eventually_truncate_term {k} (t : Semiterm (limit L) Empty k) :
    ∀ᶠ n in atTop, t.lMap (truncate n) = t := by
  induction t with
  | bvar i => exact Eventually.of_forall fun _ ↦ rfl
  | fvar i => exact i.elim
  | func f ts ih =>
    have ht := (Filter.eventually_all.mpr ih)
    filter_upwards [eventually_truncate_func f, ht] with n hf hn
    change Semiterm.func ((truncate n).func f) (fun i ↦ (ts i).lMap (truncate n)) = _
    rw [hf]
    exact congrArg (Semiterm.func f) (funext hn)

theorem eventually_truncate_firstOrder {k} (φ : Semisentence (limit L) k) :
    ∀ᶠ n in atTop, φ.lMap (truncate n) = φ := by
  induction φ with
  | verum => exact Eventually.of_forall fun _ ↦ rfl
  | falsum => exact Eventually.of_forall fun _ ↦ rfl
  | rel r ts =>
    filter_upwards [Filter.eventually_all.mpr (fun i ↦ eventually_truncate_term (ts i))] with n hn
    change Semiformula.rel ((truncate n).rel r) (fun i ↦ (ts i).lMap (truncate n)) = _
    rw [truncate_rel]
    exact congrArg (Semiformula.rel r) (funext hn)
  | nrel r ts =>
    filter_upwards [Filter.eventually_all.mpr (fun i ↦ eventually_truncate_term (ts i))] with n hn
    change Semiformula.nrel ((truncate n).rel r) (fun i ↦ (ts i).lMap (truncate n)) = _
    rw [truncate_rel]
    exact congrArg (Semiformula.nrel r) (funext hn)
  | and φ ψ ihφ ihψ =>
    filter_upwards [ihφ, ihψ] with n hφ hψ
    exact congrArg₂ Semiformula.and hφ hψ
  | or φ ψ ihφ ihψ =>
    filter_upwards [ihφ, ihψ] with n hφ hψ
    exact congrArg₂ Semiformula.or hφ hψ
  | all φ ih =>
    filter_upwards [ih] with n hn
    exact congrArg Semiformula.all hn
  | exs φ ih =>
    filter_upwards [ih] with n hn
    exact congrArg Semiformula.exs hn

/-- A formula uses only a bounded initial segment of the new constants. -/
def FiniteSupport {k} (φ : Formula (limit L) k) : Prop :=
  ∀ᶠ n in atTop, φ.lMap (truncate n) = φ

theorem finiteSupport_fo {k} (φ : Semisentence (limit L) k) : FiniteSupport (.fo φ) := by
  filter_upwards [eventually_truncate_firstOrder φ] with n hn
  exact congrArg Formula.fo hn

theorem finiteSupport_expand {k} (φ : Semisentence (limit L) k) :
    FiniteSupport (Formula.expandFirstOrder φ) := by
  filter_upwards [eventually_truncate_firstOrder φ] with n hn
  rw [Formula.lMap_expandFirstOrder, hn]

theorem finiteSupport_neg {k} {φ : Formula (limit L) k} (hφ : FiniteSupport φ) :
    FiniteSupport (.neg φ) := by
  filter_upwards [hφ] with n hn
  exact congrArg Formula.neg hn

theorem finiteSupport_exs {k} {φ : Formula (limit L) (k + 1)} (hφ : FiniteSupport φ) :
    FiniteSupport (.exs φ) := by
  filter_upwards [hφ] with n hn
  exact congrArg Formula.exs hn

theorem finiteSupport_q {k} {φ : Formula (limit L) (k + 1)} (hφ : FiniteSupport φ) :
    FiniteSupport (.q φ) := by
  filter_upwards [hφ] with n hn
  exact congrArg Formula.q hn

theorem finiteSupport_and {k} {φ ψ : Formula (limit L) k}
    (hφ : FiniteSupport φ) (hψ : FiniteSupport ψ) : FiniteSupport (φ.and ψ) := by
  filter_upwards [hφ, hψ] with n hn hm
  rw [Formula.lMap_and, hn, hm]

theorem finiteSupport_subst {k m} {φ : Formula (limit L) k}
    (hφ : FiniteSupport φ) (σ : Fin k → Semiterm (limit L) Empty m) :
    FiniteSupport (φ.subst σ) := by
  filter_upwards [hφ, Filter.eventually_all.mpr (fun i ↦ eventually_truncate_term (σ i))]
    with n hn hs
  rw [Formula.lMap_subst, hn, funext hs]

theorem fixed_subformula (η : L →ᵥ L) {k m} {φ : Formula L k} {ψ : Formula L m}
    (hφ : φ.lMap η = φ) (hψ : ⟨m, ψ⟩ ∈ φ.subformulas) : ψ.lMap η = ψ := by
  induction φ with
  | fo φ =>
    have he : (⟨m, ψ⟩ : TaggedFormula L) = ⟨_, .fo φ⟩ := hψ
    cases he
    exact hφ
  | neg φ ih =>
    rcases hψ with he | hψ
    · cases he; exact hφ
    · exact ih (Formula.neg.inj hφ) hψ
  | conj φ ih =>
    rcases hψ with he | hψ
    · cases he; exact hφ
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hψ
      exact ih i (congrFun (Formula.conj.inj hφ) i) hi
  | exs φ ih =>
    rcases hψ with he | hψ
    · cases he; exact hφ
    · exact ih (Formula.exs.inj hφ) hψ
  | q φ ih =>
    rcases hψ with he | hψ
    · cases he; exact hφ
    · exact ih (Formula.q.inj hφ) hψ

theorem finiteSupport_subformula {k m} {φ : Formula (limit L) k}
    {ψ : Formula (limit L) m} (hφ : FiniteSupport φ) (hψ : ⟨m, ψ⟩ ∈ φ.subformulas) :
    FiniteSupport ψ := by
  filter_upwards [hφ] with n hn
  exact fixed_subformula _ hn hψ

theorem finiteSupport_has_stage {k} {φ : Formula (limit L) k} (hφ : FiniteSupport φ) :
    ∃ n, ∃ ψ : Formula (stage L (n + 1)) k, ψ.lMap (intoLimit (n + 1)) = φ := by
  obtain ⟨n, hn⟩ := hφ.exists
  refine ⟨n, φ.lMap (fromLimit n), ?_⟩
  rw [LanguageMap.formula_comp]
  exact hn

theorem finiteSupport_original {k} (φ : Formula L k) :
    FiniteSupport (φ.lMap (Language.Hom.add₁ L (Language.constant ℕ))) := by
  apply Eventually.of_forall
  intro n
  rw [LanguageMap.formula_comp]
  have he : (truncate n).comp (Language.Hom.add₁ L (Language.constant ℕ)) =
      Language.Hom.add₁ L (Language.constant ℕ) := by
    apply LanguageMap.hom_ext <;> intros <;> rfl
  rw [he]

theorem finiteSupport_firstOrder {a : TaggedFormula (limit L)}
    (ha : a ∈ FragmentClosure.firstOrder) : FiniteSupport a.2 := by
  rcases ha with ⟨⟨n, φ⟩, rfl⟩ | ⟨⟨n, φ⟩, rfl⟩
  · exact finiteSupport_fo φ
  · exact finiteSupport_expand φ

theorem finiteSupport_successors {a b : TaggedFormula (limit L)}
    (ha : FiniteSupport a.2) (hb : b ∈ FragmentClosure.successors a) :
    FiniteSupport b.2 := by
  rcases a with ⟨n, φ⟩
  rcases b with ⟨m, ψ⟩
  rcases hb with (hb | hb) | hb
  · exact finiteSupport_subformula ha hb
  · have he : (⟨m, ψ⟩ : TaggedFormula (limit L)) = ⟨n, .neg φ⟩ := hb
    cases he
    exact finiteSupport_neg ha
  · obtain ⟨k, σ, he⟩ := Set.mem_iUnion.mp hb
    cases he
    exact finiteSupport_subst ha σ

theorem finiteSupport_binders {a b : TaggedFormula (limit L)}
    (ha : FiniteSupport a.2) (hb : b ∈ FragmentClosure.binders a) :
    FiniteSupport b.2 := by
  rcases a with ⟨n, φ⟩
  cases n with
  | zero => exact False.elim hb
  | succ n =>
    rcases hb with he | he
    · cases he; exact finiteSupport_exs ha
    · cases he; exact finiteSupport_q ha

theorem finiteSupport_combine {a b : TaggedFormula (limit L)}
    (ha : FiniteSupport a.2) (hb : FiniteSupport b.2) :
    FiniteSupport (FragmentClosure.combine a b).2 := by
  rcases a with ⟨n, φ⟩
  rcases b with ⟨m, ψ⟩
  by_cases h : m = n
  · subst m
    have he : FragmentClosure.combine (⟨n, φ⟩ : TaggedFormula (limit L)) ⟨n, ψ⟩ =
        ⟨n, φ.and ψ⟩ := by simp [FragmentClosure.combine]
    rw [he]
    exact finiteSupport_and ha hb
  · have he : FragmentClosure.combine (⟨n, φ⟩ : TaggedFormula (limit L)) ⟨m, ψ⟩ =
        ⟨n, φ⟩ := by simp [FragmentClosure.combine, h]
    rw [he]
    exact ha

theorem finiteSupport_fragment [L.Encodable] {S : Set (TaggedFormula (limit L))}
    (hS : ∀ a ∈ S, FiniteSupport a.2) {a : TaggedFormula (limit L)}
    (ha : a ∈ FragmentClosure.carrier S) : FiniteSupport a.2 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
  clear ha
  induction n generalizing a with
  | zero => exact hn.elim (hS a) finiteSupport_firstOrder
  | succ n ih =>
    rcases hn with hn | (hn | hn) | hn
    · exact ih hn
    · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hn
      obtain ⟨hb, ha⟩ := Set.mem_iUnion.mp hb
      exact finiteSupport_successors (ih hb) ha
    · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hn
      obtain ⟨hb, ha⟩ := Set.mem_iUnion.mp hb
      exact finiteSupport_binders (ih hb) ha
    · obtain ⟨b, hbi⟩ := Set.mem_iUnion.mp hn
      obtain ⟨hbs, hai⟩ := Set.mem_iUnion.mp hbi
      obtain ⟨c, hci⟩ := Set.mem_iUnion.mp hai
      obtain ⟨hcs, he⟩ := Set.mem_iUnion.mp hci
      have he' : a = FragmentClosure.combine b c := he
      subst a
      exact finiteSupport_combine (ih hbs) (ih hcs)

end HenkinLanguage
end ZFVP.Infinitary



