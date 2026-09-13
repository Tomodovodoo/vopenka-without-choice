import ZFVP.ModelTheory.CountableCohenModel
import ZFVP.ModelTheory.CountableZFTransfer
import ZFVP.SetTheory.SymmetricSystemDictionary
import ZFVP.SetTheory.HartogsDictionary
import ZFVP.SetTheory.ElementaryForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The first variable is injective and contains the pair of the other two. -/
def injectivePairFormula : SetTheorySemisentence 3 := f“f x y. !Injective.dfn f ∧ !kpair.dfn x y ∈ f”

def countableCohenCarrierFormula : SetTheorySemisentence 3 :=
  f“P I J. ∀ p, p ∈ P ↔ p ⊆ !prod.dfn (!prod.dfn I J) (!(numeralFormula 2)) ∧
    !IsFunction.dfn p ∧ !internallyCountableFormula (!domain.dfn p)”

def countableCohenOrderFormula : SetTheorySemisentence 3 :=
  f“R I J. ∀ z, z ∈ R ↔ z ∈ !prod.dfn (!countableCohenCarrierFormula I J) (!countableCohenCarrierFormula I J) ∧
    !kpair.π₂.dfn z ⊆ !kpair.π₁.dfn z”

def countableCohenRowNameFormula : SetTheorySemisentence 4 :=
  f“t I J i. ∀ z, z ∈ t ↔ ∃ n ∈ J, ∃ p ∈ !countableCohenCarrierFormula I J,
    !kpair.dfn (!kpair.dfn i n) (!(numeralFormula 1)) ∈ p ∧
    z = !kpair.dfn (!checkNameFormula (!isEmpty) n) p”

def countableCohenInjectionCollisionFormula : SetTheorySemisentence 12 :=
  f“I P R Γ F t x y a i j p. I = !hartogsNumberFormula (!isω) ∧
    P = !countableCohenCarrierFormula I I ∧ R = !countableCohenOrderFormula I I ∧
    !symmetricGroupFormula P R Γ ∧ !symmetricNormalFilterFormula P Γ F ∧
    !hereditarilySymmetricNameFormula P Γ F t ∧
    !hereditarilySymmetricNameFormula P Γ F x ∧ !hereditarilySymmetricNameFormula P Γ F y ∧
    x = !countableCohenRowNameFormula I I i ∧ y = !countableCohenRowNameFormula I I j ∧
    i ∈ I ∧ j ∈ I ∧ i ≠ j ∧ p ∈ P ∧
    !(symmetricForcingTranslation injectivePairFormula) P R Γ F p (!assignmentPrependFormula (!(numeralFormula 2)) (!assignmentPrependFormula (!(numeralFormula 1)) (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) (!checkNameFormula (!isEmpty) a)) x) t) ∧ !(symmetricForcingTranslation injectivePairFormula) P R Γ F p (!assignmentPrependFormula (!(numeralFormula 2)) (!assignmentPrependFormula (!(numeralFormula 1)) (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) (!checkNameFormula (!isEmpty) a)) y) t) → ⊥”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_injectivePairFormula_assignment (v : Fin 3 → V) :
    injectivePairFormula.Evalb v ↔ Injective (v 0) ∧ ⟨v 1, v 2⟩ₖ ∈ v 0 := by
  simp [injectivePairFormula]

instance countableCohenCarrierFormula_defined :
    ℒₛₑₜ-function₂[V] countableCohenConditions via countableCohenCarrierFormula :=
  ⟨fun v ↦ by
    change countableCohenCarrierFormula.Evalb v ↔ v 0 = countableCohenConditions (v 1) (v 2)
    rw [mem_ext_iff]
    simp [countableCohenCarrierFormula, countableCohenConditions, mem_countablePartialFunctions]⟩
instance countableCohenOrderFormula_defined :
    ℒₛₑₜ-function₂[V] countableCohenOrder via countableCohenOrderFormula :=
  ⟨fun v ↦ by
    change countableCohenOrderFormula.Evalb v ↔ v 0 = countableCohenOrder (v 1) (v 2)
    rw [mem_ext_iff]
    simp [countableCohenOrderFormula, countableCohenOrder, reverseInclusionOrder]⟩
instance countableCohenRowNameFormula_defined :
    ℒₛₑₜ-function₃[V] countableCohenSubsetName via countableCohenRowNameFormula :=
  ⟨fun v ↦ by
    change countableCohenRowNameFormula.Evalb v ↔ v 0 = countableCohenSubsetName (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [countableCohenRowNameFormula, mem_countableCohenSubsetName]⟩

private theorem cohenCollision_forall_eq3 {α : Type*} (a₀ b₀ c₀ : α) (R : α → α → α → Prop) :
    (∀ a b c, a = a₀ → b = b₀ → c = c₀ → R a b c) ↔ R a₀ b₀ c₀ := by
  constructor
  · intro h; exact h a₀ b₀ c₀ rfl rfl rfl
  · rintro h a b c rfl rfl rfl; exact h

private theorem cohenCollision_forall_eq4 {α : Type*} (a₀ b₀ c₀ d₀ : α) (R : α → α → α → α → Prop) :
    (∀ a b c d, a = a₀ → b = b₀ → c = c₀ → d = d₀ → R a b c d) ↔ R a₀ b₀ c₀ d₀ := by
  constructor
  · intro h; exact h a₀ b₀ c₀ d₀ rfl rfl rfl rfl
  · rintro h a b c d rfl rfl rfl rfl; exact h

private theorem cohenCollision_forall_eq6 {α : Type*} (a₀ b₀ c₀ d₀ e₀ f₀ : α) (R : α → α → α → α → α → α → Prop) :
    (∀ a b c d e f, a = a₀ → b = b₀ → c = c₀ → d = d₀ → e = e₀ → f = f₀ → R a b c d e f) ↔ R a₀ b₀ c₀ d₀ e₀ f₀ := by
  constructor
  · intro h; exact h a₀ b₀ c₀ d₀ e₀ f₀ rfl rfl rfl rfl rfl rfl
  · rintro h a b c d e f rfl rfl rfl rfl rfl rfl; exact h

attribute [local simp] cohenCollision_forall_eq3 cohenCollision_forall_eq4 cohenCollision_forall_eq6

theorem eval_countableCohenInjectionCollisionFormula (v : Fin 12 → V) :
    countableCohenInjectionCollisionFormula.Evalb v ↔
    (v 0 = hartogsNumber (ω : V) → v 1 = countableCohenConditions (v 0) (v 0) →
    v 2 = countableCohenOrder (v 0) (v 0) →
    IsForcingAutomorphismGroup (v 1) (v 2) (v 3) → IsNormalSubgroupFilter (v 1) (v 3) (v 4) →
    IsHereditarilySymmetricName (v 1) (v 3) (v 4) (v 5) →
    IsHereditarilySymmetricName (v 1) (v 3) (v 4) (v 6) →
    IsHereditarilySymmetricName (v 1) (v 3) (v 4) (v 7) →
    v 6 = countableCohenSubsetName (v 0) (v 0) (v 9) →
    v 7 = countableCohenSubsetName (v 0) (v 0) (v 10) →
    v 9 ∈ v 0 → v 10 ∈ v 0 → v 9 ≠ v 10 → v 11 ∈ v 1 →
    v 11 ∈ symmetricForcingFormula (v 1) (v 2) (v 3) (v 4) injectivePairFormula
      (standardTuple ![v 5, v 6, checkName ∅ (v 8)]) →
    v 11 ∈ symmetricForcingFormula (v 1) (v 2) (v 3) (v 4) injectivePairFormula
      (standardTuple ![v 5, v 7, checkName ∅ (v 8)]) → False) := by
  simp [countableCohenInjectionCollisionFormula, standardTuple, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]

/-- Distinct rows cannot receive the same checked value under a forced injection, in any
symmetric system on this carrier containing the two row names. -/
theorem countableCohen_injection_collision {Γ F τ ξ ζ α p : V}
    (hΓ : IsForcingAutomorphismGroup (countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V)))
      (countableCohenOrder (hartogsNumber (ω : V)) (hartogsNumber (ω : V))) Γ)
    (hF : IsNormalSubgroupFilter (countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V))) Γ F)
    (hτ : IsHereditarilySymmetricName (countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V))) Γ F τ)
    (hξHS : IsHereditarilySymmetricName (countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V))) Γ F
      (countableCohenSubsetName (hartogsNumber (ω : V)) (hartogsNumber (ω : V)) ξ))
    (hζHS : IsHereditarilySymmetricName (countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V))) Γ F
      (countableCohenSubsetName (hartogsNumber (ω : V)) (hartogsNumber (ω : V)) ζ))
    (hξ : ξ ∈ hartogsNumber (ω : V)) (hζ : ζ ∈ hartogsNumber (ω : V)) (hne : ξ ≠ ζ)
    (hp : p ∈ countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V)))
    (hx : p ∈ symmetricForcingFormula (countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V)))
      (countableCohenOrder (hartogsNumber (ω : V)) (hartogsNumber (ω : V))) Γ F injectivePairFormula
      (standardTuple ![τ, countableCohenSubsetName (hartogsNumber (ω : V)) (hartogsNumber (ω : V)) ξ, checkName ∅ α]))
    (hy : p ∈ symmetricForcingFormula (countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V)))
      (countableCohenOrder (hartogsNumber (ω : V)) (hartogsNumber (ω : V))) Γ F injectivePairFormula
      (standardTuple ![τ, countableCohenSubsetName (hartogsNumber (ω : V)) (hartogsNumber (ω : V)) ζ, checkName ∅ α])) : False := by
  have hall := eval_of_countable_zf countableCohenInjectionCollisionFormula (by
    intro W _ _ _ _ v
    apply (eval_countableCohenInjectionCollisionFormula v).mpr
    intro hI hP hR hΓ hF hτ hX hY hxdef hydef hi hj hne hp hx hy
    simp only [hP, hR, hxdef, hydef, hI] at hΓ hF hτ hX hY hi hj hp hx hy
    let I := hartogsNumber (ω : W)
    obtain ⟨G, hG, hpG⟩ := exists_externalForcingGeneric (countableCohen_poset I I).1 hp
    let S : SymmetricContext W :=
      ⟨⟨countableCohenConditions I I, countableCohenOrder I I, ∅, G,
        (countableCohen_poset I I).1, countableCohen_top I I, hG⟩,
        v 3, v 4, countableCohen_poset I I, hΓ, hF⟩
    let t : S.Name := ⟨v 5, hτ⟩
    let x : S.Name := ⟨countableCohenSubsetName I I (v 9), hX⟩
    let y : S.Name := ⟨countableCohenSubsetName I I (v 10), hY⟩
    let a : S.Name := ⟨checkName ∅ (v 8), hereditarilySymmetric_checkName S.poset S.group S.normal S.top _⟩
    have hval (b : S.Name) : (fun i ↦ ((![t, b, a] : Fin 3 → S.Name) i).val) = ![t.val, b.val, a.val] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
    have h1 := (S.formula_truth injectivePairFormula ![t, x, a]).mpr ⟨v 11, hpG, by rw [hval]; exact hx⟩
    have h2 := (S.formula_truth injectivePairFormula ![t, y, a]).mpr ⟨v 11, hpG, by rw [hval]; exact hy⟩
    have h1' := (eval_injectivePairFormula_assignment _).mp h1
    have h2' := (eval_injectivePairFormula_assignment _).mp h2
    have heq : S.ofName x = S.ofName y := h1'.1 _ _ _ h1'.2 h2'.2
    apply OmegaOneCohenModel.subset_ne hG hi hj hne
    apply (omegaOneCohenContext G hG).toOrdinary_injective
    exact congrArg S.toOrdinary heq)
      ![hartogsNumber (ω : V), countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V)),
        countableCohenOrder (hartogsNumber (ω : V)) (hartogsNumber (ω : V)), Γ, F, τ,
        countableCohenSubsetName (hartogsNumber (ω : V)) (hartogsNumber (ω : V)) ξ,
        countableCohenSubsetName (hartogsNumber (ω : V)) (hartogsNumber (ω : V)) ζ, α, ξ, ζ, p]
  exact (eval_countableCohenInjectionCollisionFormula _).mp hall rfl rfl rfl hΓ hF hτ hξHS hζHS rfl rfl hξ hζ hne hp hx hy

end ZFVP
