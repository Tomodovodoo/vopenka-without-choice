import ZFVP.ModelTheory.InfinitaryHenkinLanguage

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction
open HenkinLanguage
variable {L : Language} [L.Eq]

open Classical in
noncomputable def rawStep {n} (Γ : Set (Sentence (stage L n))) (φ : Sentence (stage L n)) :
    Set (Sentence (WithConstants (stage L n) Unit)) :=
  if h : KeislerDerivation.Consistent Γ then (KeislerDerivation.exists_henkinStep Γ h φ).choose
    else Formula.lMap (Language.Hom.add₁ (stage L n) (Language.constant Unit)) '' Γ

theorem rawStep_spec {n} (Γ : Set (Sentence (stage L n))) (h : KeislerDerivation.Consistent Γ)
    (φ : Sentence (stage L n)) : KeislerDerivation.HenkinStep Γ φ (rawStep Γ φ) := by
  classical
  rw [rawStep, dite_eq_left h]
  exact (KeislerDerivation.exists_henkinStep Γ h φ).choose_spec

/-- At stage n there are exactly n available fresh constants. -/
noncomputable def theories (Γ : Set (Sentence L)) (e : (n : ℕ) → Sentence (stage L n)) :
    (n : ℕ) → Set (Sentence (stage L n))
  | 0 => Formula.lMap (Language.Hom.add₁ L (Language.constant (Fin 0))) '' Γ
  | n + 1 => Formula.lMap (flatten n) '' rawStep (theories Γ e n) (e n)

theorem theories_consistent (Γ : Set (Sentence L)) (hc : KeislerDerivation.Consistent Γ)
    (e : (n : ℕ) → Sentence (stage L n)) (n : ℕ) : KeislerDerivation.Consistent (theories Γ e n) := by
  induction n with
  | zero => exact ExistentialWitness.consistent_lMap hc
  | succ n ih => exact consistent_flatten n (rawStep_spec _ ih _).consistent

theorem theories_countable (Γ : Set (Sentence L)) (hc : KeislerDerivation.Consistent Γ)
    (hΓ : Γ.Countable) (e : (n : ℕ) → Sentence (stage L n)) (n : ℕ) : (theories Γ e n).Countable := by
  induction n with
  | zero => exact hΓ.image _
  | succ n ih => exact ((rawStep_spec _ (theories_consistent Γ hc e n) _).countable ih).image _

noncomputable def mapped (Γ : Set (Sentence L)) (e : (n : ℕ) → Sentence (stage L n))
    (n : ℕ) : Set (Sentence (limit L)) := Formula.lMap (intoLimit n) '' theories Γ e n

/-- The embeddings identify each old sentence with its image in the next stage. -/
theorem mapped_step_subset (Γ : Set (Sentence L)) (hc : KeislerDerivation.Consistent Γ)
    (e : (n : ℕ) → Sentence (stage L n)) (n : ℕ) : mapped Γ e n ⊆ mapped Γ e (n + 1) := by
  rintro _ ⟨φ, hφ, rfl⟩
  let η := Language.Hom.add₁ (stage L n) (Language.constant Unit)
  have hr : φ.lMap η ∈ rawStep (theories Γ e n) (e n) :=
    (rawStep_spec _ (theories_consistent Γ hc e n) _).includes ⟨φ, hφ, rfl⟩
  refine ⟨(φ.lMap η).lMap (flatten n), ⟨φ.lMap η, hr, rfl⟩, ?_⟩
  have he : (φ.lMap η).lMap (flatten n) = φ.lMap (next n) := by
    rw [LanguageMap.formula_comp, flatten_add]
  rw [he, formula_intoLimit_next]

theorem mapped_mono (Γ : Set (Sentence L)) (hc : KeislerDerivation.Consistent Γ)
    (e : (n : ℕ) → Sentence (stage L n)) : Monotone (mapped Γ e) :=
  monotone_nat_of_le_succ (mapped_step_subset Γ hc e)

theorem mapped_consistent (Γ : Set (Sentence L)) (hc : KeislerDerivation.Consistent Γ)
    (e : (n : ℕ) → Sentence (stage L n)) (n : ℕ) : KeislerDerivation.Consistent (mapped Γ e n) := by
  cases n with
  | zero =>
      exact KeislerDerivation.consistent_mono (mapped_step_subset Γ hc e 0)
        (consistent_intoLimit 0 (theories_consistent Γ hc e 1))
  | succ n => exact consistent_intoLimit n (theories_consistent Γ hc e (n + 1))

noncomputable def carrier (Γ : Set (Sentence L)) (e : (n : ℕ) → Sentence (stage L n)) :
    Set (Sentence (limit L)) := ⋃ n, mapped Γ e n

theorem carrier_countable (Γ : Set (Sentence L)) (hc : KeislerDerivation.Consistent Γ)
    (hΓ : Γ.Countable) (e : (n : ℕ) → Sentence (stage L n)) : (carrier Γ e).Countable :=
  Set.countable_iUnion (fun n ↦ (theories_countable Γ hc hΓ e n).image _)

theorem carrier_includes (Γ : Set (Sentence L)) (e : (n : ℕ) → Sentence (stage L n)) :
    Formula.lMap (Language.Hom.add₁ L (Language.constant ℕ)) '' Γ ⊆ carrier Γ e := by
  rintro _ ⟨φ, hφ, rfl⟩
  apply Set.mem_iUnion.mpr
  refine ⟨0, φ.lMap (Language.Hom.add₁ L (Language.constant (Fin 0))), ⟨φ, hφ, rfl⟩, ?_⟩
  rw [LanguageMap.formula_comp, intoLimit_original]

theorem finite_subset_stage (Γ : Set (Sentence L)) (hc : KeislerDerivation.Consistent Γ)
    (e : (n : ℕ) → Sentence (stage L n)) (s : Finset (Sentence (limit L)))
    (hs : ∀ φ ∈ s, φ ∈ carrier Γ e) : ∃ n, ∀ φ ∈ s, φ ∈ mapped Γ e n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert φ s hφ ih =>
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs φ (Finset.mem_insert_self _ _))
      obtain ⟨j, hj⟩ := ih (fun ψ hψ ↦ hs ψ (Finset.mem_insert_of_mem hψ))
      refine ⟨max i j, fun ψ hψ ↦ ?_⟩
      rcases Finset.mem_insert.mp hψ with rfl | hψ
      · exact mapped_mono Γ hc e (le_max_left _ _) hi
      · exact mapped_mono Γ hc e (le_max_right _ _) (hj ψ hψ)

theorem carrier_finite_consistent (Γ : Set (Sentence L)) (hc : KeislerDerivation.Consistent Γ)
    (e : (n : ℕ) → Sentence (stage L n)) (s : Finset (Sentence (limit L)))
    (hs : ∀ φ ∈ s, φ ∈ carrier Γ e) : KeislerDerivation.Consistent (s : Set (Sentence (limit L))) := by
  obtain ⟨n, hn⟩ := finite_subset_stage Γ hc e s hs
  exact KeislerDerivation.consistent_mono (fun φ hφ ↦ hn φ hφ) (mapped_consistent Γ hc e n)

def rawMap (n : ℕ) : WithConstants (stage L n) Unit →ᵥ limit L :=
  (intoLimit (n + 1)).comp (flatten n)

theorem rawMap_original (n : ℕ) : (rawMap (L := L) n).comp
    (Language.Hom.add₁ (stage L n) (Language.constant Unit)) = intoLimit n := by
  apply LanguageMap.hom_ext
  · intro k f
    cases f with
    | inl f => rfl
    | inr f => cases f; rfl
  · intro k r
    cases r with
    | inl r => rfl
    | inr r => exact r.elim

theorem raw_formula_original {n k} (φ : Formula (stage L n) k) :
    (φ.lMap (Language.Hom.add₁ (stage L n) (Language.constant Unit))).lMap (rawMap n) =
      φ.lMap (intoLimit n) := by rw [LanguageMap.formula_comp, rawMap_original]

theorem raw_mem_carrier (Γ : Set (Sentence L)) (e : (n : ℕ) → Sentence (stage L n)) {n}
    {φ : Sentence (WithConstants (stage L n) Unit)} (hφ : φ ∈ rawStep (theories Γ e n) (e n)) :
    φ.lMap (rawMap n) ∈ carrier Γ e := by
  apply Set.mem_iUnion.mpr
  refine ⟨n + 1, φ.lMap (flatten n), ⟨φ, hφ, rfl⟩, ?_⟩
  exact LanguageMap.formula_comp _ _ φ

theorem carrier_decides (Γ : Set (Sentence L)) (hc : KeislerDerivation.Consistent Γ)
    (e : (n : ℕ) → Sentence (stage L n)) (n : ℕ) :
    (e n).lMap (intoLimit n) ∈ carrier Γ e ∨ .neg ((e n).lMap (intoLimit n)) ∈ carrier Γ e := by
  rcases (rawStep_spec _ (theories_consistent Γ hc e n) _).decides with hp | hn
  · exact Or.inl (by simpa only [raw_formula_original] using raw_mem_carrier Γ e hp)
  · exact Or.inr (by simpa only [Formula.lMap_neg, raw_formula_original] using raw_mem_carrier Γ e hn)

theorem carrier_conjunction_witness (Γ : Set (Sentence L)) (hc : KeislerDerivation.Consistent Γ)
    (e : (n : ℕ) → Sentence (stage L n)) (n : ℕ) (f : ℕ → Sentence (stage L n)) (he : e n = .conj f) :
    .conj (fun i ↦ (f i).lMap (intoLimit n)) ∈ carrier Γ e ∨
      ∃ i, .neg ((f i).lMap (intoLimit n)) ∈ carrier Γ e := by
  rcases (rawStep_spec _ (theories_consistent Γ hc e n) _).conjunction_witness f he with hp | ⟨i, hi⟩
  · exact Or.inl (by simpa only [Formula.lMap_conj, raw_formula_original] using raw_mem_carrier Γ e hp)
  · exact Or.inr ⟨i, by simpa only [Formula.lMap_neg, raw_formula_original] using raw_mem_carrier Γ e hi⟩

def freshTerm (n : ℕ) : Semiterm (limit L) Empty 0 :=
  (ExistentialWitness.fresh (L := stage L n)).lMap (rawMap n)

theorem raw_witness (n : ℕ) (f : Formula (stage L n) 1) :
    (ExistentialWitness.sentence f).lMap (rawMap n) =
      (f.lMap (intoLimit n)).substFirst (freshTerm n) := by
  rw [ExistentialWitness.sentence, Formula.lMap_substFirst, raw_formula_original]
  rfl

theorem carrier_existential_witness (Γ : Set (Sentence L)) (hc : KeislerDerivation.Consistent Γ)
    (e : (n : ℕ) → Sentence (stage L n)) (n : ℕ) (f : Formula (stage L n) 1) (he : e n = .exs f) :
    .neg (.exs (f.lMap (intoLimit n))) ∈ carrier Γ e ∨
      (f.lMap (intoLimit n)).substFirst (freshTerm n) ∈ carrier Γ e := by
  rcases (rawStep_spec _ (theories_consistent Γ hc e n) _).existential_witness f he with hn | hp
  · exact Or.inl (by simpa only [Formula.lMap_neg, Formula.lMap_exs, raw_formula_original] using raw_mem_carrier Γ e hn)
  · exact Or.inr (by simpa only [raw_witness] using raw_mem_carrier Γ e hp)

end HenkinConstruction
end ZFVP.Infinitary

