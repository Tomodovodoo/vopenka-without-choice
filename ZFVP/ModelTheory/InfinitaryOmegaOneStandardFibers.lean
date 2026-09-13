import ZFVP.ModelTheory.InfinitaryOmegaOneWeakLimit

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakDirectedChain
open FragmentClosure

/-- The actual successor ordinal, still below omega-one. -/
noncomputable def omegaOneSucc (i : OmegaOne) : OmegaOne :=
  Ordinal.enum (α := OmegaOne) (· < ·)
    ⟨Order.succ (Ordinal.typein (α := OmegaOne) (· < ·) i), by
      have he : Ordinal.type (α := OmegaOne) (· < ·) = Ordinal.omega.{0} 1 := Ordinal.type_toType _
      rw [he]
      exact (Cardinal.isSuccLimit_omega 1).succ_lt
        (lt_of_lt_of_eq (Ordinal.typein_lt_type (α := OmegaOne) (· < ·) i) he)⟩

theorem typein_omegaOneSucc (i : OmegaOne) :
    Ordinal.typein (α := OmegaOne) (· < ·) (omegaOneSucc i) =
      Order.succ (Ordinal.typein (α := OmegaOne) (· < ·) i) := Ordinal.typein_enum _ _

theorem lt_omegaOneSucc (i : OmegaOne) : i < omegaOneSucc i := by
  apply (Ordinal.typein_lt_typein (α := OmegaOne) (· < ·)).mp
  rw [typein_omegaOneSucc]
  exact Order.lt_succ _

theorem le_omegaOneSucc (i : OmegaOne) : i ≤ omegaOneSucc i := (lt_omegaOneSucc i).le

theorem lt_omegaOneSucc_iff (i j : OmegaOne) : j < omegaOneSucc i ↔ j ≤ i := by
  rw [← Ordinal.typein_lt_typein (α := OmegaOne) (· < ·), typein_omegaOneSucc,
    Order.lt_succ_iff]
  exact Ordinal.typein_le_typein' _

variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}
  (C : WeakDirectedChain.{u,0,v} OmegaOne S)

/-- A large fiber receives a witness at every later successor, outside the
image of the immediately preceding stage. This is a condition on chain stages. -/
def LargeFiberSuccessorGrowth : Prop :=
  ∀ {n} (φ : Formula L (n + 1)), ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S →
    ∀ i (b : Fin n → (C.model i).Domain), Formula.WeakEval (C.model i).Q (.q φ) b →
      ∀ j (hij : i ≤ j), ∃ x : (C.model (omegaOneSucc j)).Domain,
        Formula.WeakEval (C.model (omegaOneSucc j)).Q φ
          (x :> C.map (hij.trans (le_omegaOneSucc j)) ∘ b) ∧
        x ∉ Set.range (C.map (le_omegaOneSucc j))

/-- A small fiber never acquires elements outside its original stage. -/
def PreservesSmallFibers : Prop :=
  ∀ {n} (φ : Formula L (n + 1)), ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S →
    ∀ i (b : Fin n → (C.model i).Domain), ¬Formula.WeakEval (C.model i).Q (.q φ) b →
      ∀ j (hij : i ≤ j) (x : (C.model j).Domain),
        Formula.WeakEval (C.model j).Q φ (x :> C.map hij ∘ b) →
          ∃ y : (C.model i).Domain, C.map hij y = x

theorem small_limitFiber_subset_stage (hsmall : C.PreservesSmallFibers)
    {n} {φ : Formula L (n + 1)} (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S)
    {i} (b : Fin n → (C.model i).Domain) (hq : ¬Formula.WeakEval (C.model i).Q (.q φ) b) :
    C.LimitFiber φ (C.fromStage i ∘ b) ⊆ Set.range (C.fromStage i) := by
  intro x hx
  obtain ⟨j, y, rfl⟩ := C.stage_cover x
  let k := max i j
  have hi : i ≤ k := le_max_left _ _
  have hj : j ≤ k := le_max_right _ _
  have hy : Formula.WeakEval (C.model k).Q φ (C.map hj y :> C.map hi ∘ b) := by
    apply (C.stageEval_fromStage φ hφ _).mp
    change C.StageEval φ (C.fromStage j y :> C.fromStage i ∘ b) at hx
    simpa only [C.fromStage_cons, ← Function.comp_assoc, C.fromStage_comp,
      C.fromStage_coherent] using hx
  obtain ⟨z, hz⟩ := hsmall φ hφ i b hq k hi (C.map hj y) hy
  refine ⟨z, ?_⟩
  exact (C.fromStage_coherent hi z).symm.trans
    ((congrArg (C.fromStage k) hz).trans (C.fromStage_coherent hj y))

theorem small_limitFiber_countable (hsmall : C.PreservesSmallFibers)
    {n} {φ : Formula L (n + 1)} (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S)
    {i} (b : Fin n → (C.model i).Domain) (hq : ¬Formula.WeakEval (C.model i).Q (.q φ) b) :
    (C.LimitFiber φ (C.fromStage i ∘ b)).Countable :=
  (Set.countable_range (C.fromStage i)).mono (C.small_limitFiber_subset_stage hsmall hφ b hq)

theorem large_limitFiber_fresh_after (hgrowth : C.LargeFiberSuccessorGrowth)
    {n} {φ : Formula L (n + 1)} (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S)
    {i} (b : Fin n → (C.model i).Domain) (hq : Formula.WeakEval (C.model i).Q (.q φ) b)
    (j : OmegaOne) (hij : i ≤ j) :
    ∃ x ∈ C.LimitFiber φ (C.fromStage i ∘ b), x ∉ Set.range (C.fromStage j) := by
  obtain ⟨x, hx, hnew⟩ := hgrowth φ hφ i b hq j hij
  refine ⟨C.fromStage (omegaOneSucc j) x, ?_, ?_⟩
  · change C.StageEval φ _
    have ht := (C.stageEval_fromStage φ hφ
      (x :> C.map (hij.trans (le_omegaOneSucc j)) ∘ b)).mpr hx
    simpa only [C.fromStage_cons, ← Function.comp_assoc, C.fromStage_comp] using ht
  · rintro ⟨y, hy⟩
    apply hnew
    refine ⟨y, ?_⟩
    have he := (C.fromStage_eq_iff y x (le_omegaOneSucc j) (le_refl _)).mp hy
    simpa only [C.identity] using he

/-- If the limit fiber were countable, all its elements would appear in one
stage. The next new witness contradicts that coverage. -/
theorem large_limitFiber_not_countable (hgrowth : C.LargeFiberSuccessorGrowth)
    {n} {φ : Formula L (n + 1)} (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S)
    {i} (b : Fin n → (C.model i).Domain) (hq : Formula.WeakEval (C.model i).Q (.q φ) b) :
    ¬(C.LimitFiber φ (C.fromStage i ∘ b)).Countable := by
  classical
  intro hc
  obtain ⟨x, hx, _⟩ := C.large_limitFiber_fresh_after hgrowth hφ b hq i (le_refl i)
  obtain ⟨f, hf⟩ := hc.exists_eq_range ⟨x, hx⟩
  obtain ⟨k, hk⟩ := C.countable_cover f
  obtain ⟨z, hz, hnew⟩ := C.large_limitFiber_fresh_after hgrowth hφ b hq (max i k) (le_max_left _ _)
  rw [hf] at hz
  obtain ⟨m, hm⟩ := hz
  obtain ⟨a, ha⟩ := hk m
  apply hnew
  exact ⟨C.map (le_max_right i k) a,
    (C.fromStage_coherent (le_max_right i k) a).trans (ha.trans hm)⟩

theorem stage_q_iff_uncountable_limitFiber (hgrowth : C.LargeFiberSuccessorGrowth)
    (hsmall : C.PreservesSmallFibers) {n} {φ : Formula L (n + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S) {i} (b : Fin n → (C.model i).Domain) :
    Formula.WeakEval (C.model i).Q (.q φ) b ↔
      ¬(C.LimitFiber φ (C.fromStage i ∘ b)).Countable := by
  classical
  constructor
  · exact C.large_limitFiber_not_countable hgrowth hφ b
  · intro h
    by_contra hq
    exact h (C.small_limitFiber_countable hsmall hφ b hq)

theorem limitQuantifier_fiber_iff_uncountable (hgrowth : C.LargeFiberSuccessorGrowth)
    (hsmall : C.PreservesSmallFibers) {n} {φ : Formula L (n + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S) (b : Fin n → C.Limit) :
    C.limitQuantifier (C.LimitFiber φ b) ↔ ¬(C.LimitFiber φ b).Countable := by
  obtain ⟨i, a, rfl⟩ := C.tuple_cover b
  rw [C.limitQuantifier_fiber hφ, C.stageEval_fromStage (.q φ) (q_closed hφ)]
  exact C.stage_q_iff_uncountable_limitFiber hgrowth hsmall hφ a

end WeakDirectedChain
end ZFVP.Infinitary
