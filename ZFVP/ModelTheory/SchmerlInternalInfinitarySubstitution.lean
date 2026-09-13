import ZFVP.ModelTheory.SchmerlInternalInfinitaryInduction
import ZFVP.Syntax.FormulaSubstitutionDefinability
import ZFVP.Syntax.FormulaSubstitutionSemantics

/-! Actual internal substitution of infinitary codes, including omega-indexed
conjunctions and lifted substitutions under Q. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def transformConjunction (q previous f : V) : V :=
  definableGraph (ω : V) (fun i ↦ previous ‘ (substitutionChild q (f ‘ i))) (by definability)

instance transformConjunction_definable : ℒₛₑₜ-function₃[V] transformConjunction := by
  have h : ℒₛₑₜ-relation₄[V] (fun z q previous f ↦ ∀ p, p ∈ z ↔
      ∃ i ∈ (ω : V), p = ⟨i, previous ‘ (substitutionChild q (f ‘ i))⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = transformConjunction (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [transformConjunction, mem_definableGraph_iff]

instance transformConjunction_isFunction (q previous f : V) : IsFunction (transformConjunction q previous f) :=
  inferInstanceAs (IsFunction (definableGraph _ _ _))

@[simp] theorem domain_transformConjunction (q previous f : V) :
    domain (transformConjunction q previous f) = (ω : V) := domain_definableGraph _ _ _

theorem value_transformConjunction (q previous f : V) {i : V} (hi : i ∈ (ω : V)) :
    (transformConjunction q previous f) ‘ i = previous ‘ (substitutionChild q (f ‘ i)) :=
  value_definableGraph _ _ _ hi

noncomputable def infinitarySubstitutionStep (L G q previous : V) : V := by
  classical
  let φ := kpair.π₂ (kpair.π₁ q)
  let tag := kpair.π₁ φ
  let data := kpair.π₂ φ
  exact if tag = 0 then foCode ((formulaSubstitutionGraph L ∅ G) ‘
      ⟨⟨kpair.π₁ (kpair.π₁ q), data⟩ₖ, kpair.π₂ q⟩ₖ)
    else if tag = 1 then negCode (previous ‘ (substitutionChild q data))
    else if tag = 2 then conjCode (transformConjunction q previous data)
    else if tag = 3 then exsCode (previous ‘ (substitutionBody q data))
    else qCode (previous ‘ (substitutionBody q data))

instance infinitarySubstitutionStep_definable : ℒₛₑₜ-function₄[V] infinitarySubstitutionStep := by
  have h : Language.DefinableRel₅ ℒₛₑₜ (fun z L G q p : V ↦
      let φ := kpair.π₂ (kpair.π₁ q)
      let t := kpair.π₁ φ
      let d := kpair.π₂ φ
      (t = 0 ∧ z = foCode ((formulaSubstitutionGraph L ∅ G) ‘ ⟨⟨kpair.π₁ (kpair.π₁ q), d⟩ₖ, kpair.π₂ q⟩ₖ)) ∨
      (t ≠ 0 ∧ t = 1 ∧ z = negCode (p ‘ (substitutionChild q d))) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t = 2 ∧ z = conjCode (transformConjunction q p d)) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 2 ∧ t = 3 ∧ z = exsCode (p ‘ (substitutionBody q d))) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ z = qCode (p ‘ (substitutionBody q d)))) := by
    dsimp
    repeat' apply Language.Definable.or
    all_goals definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = infinitarySubstitutionStep (v 1) (v 2) (v 3) (v 4) ↔ _
  unfold infinitarySubstitutionStep
  dsimp
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def infinitarySubstitutionGraph (L F G : V) : V :=
  depthRecursion F (infinitarySubstitutionStep L G) (by definability)

instance infinitarySubstitutionGraph_isFunction (L F G : V) : IsFunction (infinitarySubstitutionGraph L F G) :=
  depthRecursion_isFunction _ _ _

@[simp] theorem domain_infinitarySubstitutionGraph (L F G : V) :
    domain (infinitarySubstitutionGraph L F G) = depthDomain F := domain_depthRecursion _ _ _

instance infinitarySubstitutionGraph_definable : ℒₛₑₜ-function₃[V] infinitarySubstitutionGraph := by
  have h : ℒₛₑₜ-relation₄[V] (fun g L F G ↦
      IsRecursionAttempt (depthRelation (depthDomain F)) (depthDomain F)
        (infinitarySubstitutionStep L G) g ∧ domain g = depthDomain F) := by
    unfold IsRecursionAttempt
    definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (wellFoundedRecursion_eq_iff (depthRelation_wellFounded (depthDomain (v 2)))
    (infinitarySubstitutionStep (v 1) (v 3)) (by definability) (v 0))

theorem infinitarySubstitutionGraph_fo {L F G n φ k : V}
    (hφ : ⟨n, foCode φ⟩ₖ ∈ F) (hk : k ∈ (ω : V)) :
    (infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, foCode φ⟩ₖ, k⟩ₖ =
      foCode ((formulaSubstitutionGraph L ∅ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ) := by
  unfold infinitarySubstitutionGraph
  rw [depthRecursion_value F _ _ ((pair_mem_depthDomain _ _ _).mpr ⟨hφ, hk⟩)]
  simp only [infinitarySubstitutionStep, foCode, kpair.π₁_kpair, kpair.π₂_kpair, ite_true]

theorem infinitarySubstitutionGraph_neg {L F G n φ k : V} (hF : IsFragment L F)
    (hφ : ⟨n, negCode φ⟩ₖ ∈ F) (hk : k ∈ (ω : V)) :
    (infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, negCode φ⟩ₖ, k⟩ₖ =
      negCode ((infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ) := by
  unfold infinitarySubstitutionGraph
  rw [depthRecursion_value F _ _ ((pair_mem_depthDomain _ _ _).mpr ⟨hφ, hk⟩)]
  simp only [infinitarySubstitutionStep, negCode, kpair.π₁_kpair, kpair.π₂_kpair,
    OfNat.ofNat, internalNumeral_eq_iff, show ¬(1 : ℕ) = 0 from by decide, ite_false, ite_true, substitutionChild]
  exact congrArg (fun c ↦ ⟨(1 : V), c⟩ₖ)
    (depthRecursion_previous hF _ _ hφ hk hk ((immediate_neg_iff _ _ _).mpr rfl))

theorem infinitarySubstitutionGraph_conj {L F G n f k : V} (hF : IsFragment L F)
    (hφ : ⟨n, conjCode f⟩ₖ ∈ F) (hk : k ∈ (ω : V)) :
    (infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, conjCode f⟩ₖ, k⟩ₖ =
      conjCode (transformConjunction ⟨⟨n, conjCode f⟩ₖ, k⟩ₖ (infinitarySubstitutionGraph L F G) f) := by
  have hdata : IsFunction f ∧ domain f = (ω : V) ∧ ∀ i ∈ (ω : V), ⟨n, f ‘ i⟩ₖ ∈ F := by
    have hn := (hF.node hφ).2
    simpa [foCode, negCode, conjCode, exsCode, qCode, OfNat.ofNat, internalNumeral_eq_iff] using hn
  unfold infinitarySubstitutionGraph
  rw [depthRecursion_value F _ _ ((pair_mem_depthDomain _ _ _).mpr ⟨hφ, hk⟩)]
  simp only [infinitarySubstitutionStep, conjCode, kpair.π₁_kpair, kpair.π₂_kpair,
    OfNat.ofNat, internalNumeral_eq_iff, show ¬(2 : ℕ) = 0 from by decide,
    show ¬(2 : ℕ) = 1 from by decide, ite_false, ite_true]
  congr 1
  apply functions_eq_of_domain_values (by simp only [domain_transformConjunction])
  intro i hi
  rw [domain_transformConjunction] at hi
  rw [value_transformConjunction _ _ _ hi, value_transformConjunction _ _ _ hi]
  simp only [substitutionChild, kpair.π₁_kpair, kpair.π₂_kpair]
  exact depthRecursion_previous hF _ _ hφ hk hk
    ((immediate_conj_iff _ _ _).mpr ⟨hdata.1, i, hdata.2.1.symm ▸ hi, rfl⟩)

theorem infinitarySubstitutionGraph_exs {L F G n φ k : V} (hF : IsFragment L F)
    (hφ : ⟨n, exsCode φ⟩ₖ ∈ F) (hk : k ∈ (ω : V)) :
    (infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, exsCode φ⟩ₖ, k⟩ₖ =
      exsCode ((infinitarySubstitutionGraph L F G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ) := by
  unfold infinitarySubstitutionGraph
  rw [depthRecursion_value F _ _ ((pair_mem_depthDomain _ _ _).mpr ⟨hφ, hk⟩)]
  simp only [infinitarySubstitutionStep, exsCode, kpair.π₁_kpair, kpair.π₂_kpair,
    OfNat.ofNat, internalNumeral_eq_iff, show ¬(3 : ℕ) = 0 from by decide,
    show ¬(3 : ℕ) = 1 from by decide, show ¬(3 : ℕ) = 2 from by decide, ite_false, ite_true, substitutionBody]
  exact congrArg (fun c ↦ ⟨(3 : V), c⟩ₖ)
    (depthRecursion_previous hF _ _ hφ (ω_succ_closed hk) hk ((immediate_exs_iff _ _ _).mpr rfl))

theorem infinitarySubstitutionGraph_q {L F G n φ k : V} (hF : IsFragment L F)
    (hφ : ⟨n, qCode φ⟩ₖ ∈ F) (hk : k ∈ (ω : V)) :
    (infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, qCode φ⟩ₖ, k⟩ₖ =
      qCode ((infinitarySubstitutionGraph L F G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ) := by
  unfold infinitarySubstitutionGraph
  rw [depthRecursion_value F _ _ ((pair_mem_depthDomain _ _ _).mpr ⟨hφ, hk⟩)]
  simp only [infinitarySubstitutionStep, qCode, kpair.π₁_kpair, kpair.π₂_kpair,
    OfNat.ofNat, internalNumeral_eq_iff, show ¬(4 : ℕ) = 0 from by decide,
    show ¬(4 : ℕ) = 1 from by decide, show ¬(4 : ℕ) = 2 from by decide,
    show ¬(4 : ℕ) = 3 from by decide, ite_false, substitutionBody]
  exact congrArg (fun c ↦ ⟨(4 : V), c⟩ₖ)
    (depthRecursion_previous hF _ _ hφ (ω_succ_closed hk) hk ((immediate_q_iff _ _ _).mpr rfl))

end ZFVP.Infinitary.Internal
