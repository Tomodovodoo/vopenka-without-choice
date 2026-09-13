import ZFVP.SetTheory.UniquePiWitnessCodes
import ZFVP.SetTheory.WitnessCertificateBase
import ZFVP.SetTheory.BoundedSextupleBinding

/-! The least-rank family of Pi witnesses has a canonical code at the same positive Pi level.
Two Sigma assertions are replaced by their unique Pi certificates. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def noLowerWitnessFormula {n : ℕ} (ψ : SetTheorySemisentence (n + 1)) :
    SetTheorySemisentence (n + 4) := boundedSetAll (.bvar 1) (∼certificateWitnessFormula ψ)

def coversWitnessFormula {n : ℕ} (ψ : SetTheorySemisentence (n + 1)) :
    SetTheorySemisentence (n + 4) :=
  boundedSetAll (.bvar 2) ((∼(piOneRankFormula.subst ![.bvar 1, .bvar 0])).or
    ((∼certificateWitnessFormula ψ).or (.rel Language.Set.Rel.mem ![.bvar 0, .bvar 4])))

theorem noLowerWitnessFormula_sigma {n k : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    (hψ : IsPiFormula (k + 1) ψ) : IsSigmaFormula (k + 1) (noLowerWitnessFormula ψ) :=
  .boundedAll (.bvar 1) (hψ.subst _).neg

theorem coversWitnessFormula_sigma {n k : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    (hψ : IsPiFormula (k + 1) ψ) : IsSigmaFormula (k + 1) (coversWitnessFormula ψ) :=
  .boundedAll (.bvar 2) (.or ((piOneRankFormula_piOne.subst _).neg.mono (by omega))
    (.or (hψ.subst _).neg (.bounded (.rel _ _))))

def piWitnessCertificateFormula {n : ℕ} (k : ℕ) (ψ : SetTheorySemisentence (n + 1)) :
    SetTheorySemisentence (n + 6) :=
  (leastWitnessCertificateBaseFormula.subst ![.bvar 0, .bvar 1, .bvar 2, .bvar 3]).and
    ((boundedSetAll (.bvar 3) ((piOneRankFormula.subst ![.bvar 1, .bvar 0]).and
      (ψ.subst (.bvar 0 :> fun i : Fin n ↦ .bvar i.succ.succ.succ.succ.succ.succ.succ)))).and
      (((sigmaWitnessCodeFormula k (noLowerWitnessFormula ψ)).subst
        (.bvar 4 :> .bvar 0 :> .bvar 1 :> .bvar 2 :> .bvar 3 :>
          fun i : Fin n ↦ .bvar i.succ.succ.succ.succ.succ.succ)).and
        ((sigmaWitnessCodeFormula k (coversWitnessFormula ψ)).subst
          (.bvar 5 :> .bvar 0 :> .bvar 1 :> .bvar 2 :> .bvar 3 :>
            fun i : Fin n ↦ .bvar i.succ.succ.succ.succ.succ.succ))))

def piWitnessFamilyCodeFormula {n : ℕ} (k : ℕ) (ψ : SetTheorySemisentence (n + 1)) :
    SetTheorySemisentence (n + 1) :=
  boundedSextupleBind (.bvar 0) ((piWitnessCertificateFormula k ψ).subst
    (.bvar 0 :> .bvar 1 :> .bvar 2 :> .bvar 3 :> .bvar 4 :> .bvar 5 :>
      fun i : Fin n ↦ .bvar i.succ.succ.succ.succ.succ.succ.succ))

theorem piWitnessCertificateFormula_pi {n k : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    (hψ : IsPiFormula (k + 1) ψ) : IsPiFormula (k + 1) (piWitnessCertificateFormula k ψ) :=
  .and ((leastWitnessCertificateBaseFormula_piOne.subst _).mono (by omega))
    (.and (.boundedAll (.bvar 3) (.and ((piOneRankFormula_piOne.subst _).mono (by omega)) (hψ.subst _)))
      (.and ((sigmaWitnessCodeFormula_pi k _).subst _) ((sigmaWitnessCodeFormula_pi k _).subst _)))

theorem piWitnessFamilyCodeFormula_pi {n k : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    (hψ : IsPiFormula (k + 1) ψ) : IsPiFormula (k + 1) (piWitnessFamilyCodeFormula k ψ) :=
  boundedSextupleBind_levy _ ((piWitnessCertificateFormula_pi hψ).subst _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_or {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.or ψ).Evalb v ↔ φ.Evalb v ∨ ψ.Evalb v := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_noLowerWitnessFormula {n : ℕ} (ψ : SetTheorySemisentence (n + 1))
    (ξ U W C : V) (v : Fin n → V) :
    (noLowerWitnessFormula ψ).Evalb (ξ :> U :> W :> C :> v) ↔
      ∀ u ∈ U, ¬ψ.Evalb (u :> v) := by
  simp [noLowerWitnessFormula, eval_boundedSetAll, eval_certificateWitnessFormula]

theorem eval_coversWitnessFormula {n : ℕ} (ψ : SetTheorySemisentence (n + 1))
    (ξ U W C : V) (v : Fin n → V) :
    (coversWitnessFormula ψ).Evalb (ξ :> U :> W :> C :> v) ↔
      ∀ u ∈ W, ξ = rank u → ψ.Evalb (u :> v) → u ∈ C := by
  simp [coversWitnessFormula, eval_or, eval_boundedSetAll, eval_certificateWitnessFormula,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, Structure.rel, ← imp_iff_not_or]

private theorem eval_piWitnessCertificateFormula_raw {n k : ℕ}
    (ψ : SetTheorySemisentence (n + 1)) (ξ U W C d e : V) (v : Fin n → V) :
    (piWitnessCertificateFormula k ψ).Evalb (ξ :> U :> W :> C :> d :> e :> v) ↔
      (IsOrdinal ξ ∧ U = hierarchy ξ ∧ W = hierarchy (succ ξ) ∧ IsNonempty C ∧ C ⊆ W) ∧
      (∀ u ∈ C, ξ = rank u ∧ ψ.Evalb (u :> v)) ∧
      (sigmaWitnessCodeFormula k (noLowerWitnessFormula ψ)).Evalb (d :> ξ :> U :> W :> C :> v) ∧
      (sigmaWitnessCodeFormula k (coversWitnessFormula ψ)).Evalb (e :> ξ :> U :> W :> C :> v) := by
  simp [piWitnessCertificateFormula, eval_and, eval_boundedSetAll, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
    eval_leastWitnessCertificateBaseFormula]

theorem eval_piWitnessCertificateFormula {n k : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    (hψ : IsPiFormula (k + 1) ψ) (ξ U W C d e : V) (v : Fin n → V) :
    (piWitnessCertificateFormula k ψ).Evalb (ξ :> U :> W :> C :> d :> e :> v) ↔
      IsLeastWitnessCertificate (fun u ↦ ψ.Evalb (u :> v)) ξ U W C ∧
      (sigmaWitnessCodeFormula k (noLowerWitnessFormula ψ)).Evalb (d :> ξ :> U :> W :> C :> v) ∧
      (sigmaWitnessCodeFormula k (coversWitnessFormula ψ)).Evalb (e :> ξ :> U :> W :> C :> v) := by
  rw [eval_piWitnessCertificateFormula_raw]
  constructor
  · rintro ⟨⟨hξ, hU, hW, hC, hCW⟩, hm, hd, he⟩
    have hn := (eval_noLowerWitnessFormula ψ ξ U W C v).mp
      (sigmaWitnessCodeFormula_implies (noLowerWitnessFormula_sigma hψ) _ d hd)
    have ha := (eval_coversWitnessFormula ψ ξ U W C v).mp
      (sigmaWitnessCodeFormula_implies (coversWitnessFormula_sigma hψ) _ e he)
    exact ⟨⟨hξ, hU, hW, hC, hCW, hm, hn, ha⟩, hd, he⟩
  · rintro ⟨hc, hd, he⟩
    exact ⟨⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1⟩,
      hc.2.2.2.2.2.1, hd, he⟩

theorem piWitnessCertificate_exists {n k : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    (hψ : IsPiFormula (k + 1) ψ) (ξ U W C : V) (v : Fin n → V)
    (hc : IsLeastWitnessCertificate (fun u ↦ ψ.Evalb (u :> v)) ξ U W C) :
    ∃ d e : V, (piWitnessCertificateFormula k ψ).Evalb (ξ :> U :> W :> C :> d :> e :> v) := by
  obtain ⟨d, hd, _⟩ := (sigmaWitnessCodeFormula_existsUnique (noLowerWitnessFormula_sigma hψ)
    (ξ :> U :> W :> C :> v)).mp ((eval_noLowerWitnessFormula ψ ξ U W C v).mpr hc.2.2.2.2.2.2.1)
  obtain ⟨e, he, _⟩ := (sigmaWitnessCodeFormula_existsUnique (coversWitnessFormula_sigma hψ)
    (ξ :> U :> W :> C :> v)).mp ((eval_coversWitnessFormula ψ ξ U W C v).mpr hc.2.2.2.2.2.2.2)
  exact ⟨d, e, (eval_piWitnessCertificateFormula hψ ξ U W C d e v).mpr ⟨hc, hd, he⟩⟩

theorem eval_piWitnessFamilyCodeFormula {n k : ℕ} (ψ : SetTheorySemisentence (n + 1))
    (c : V) (v : Fin n → V) :
    (piWitnessFamilyCodeFormula k ψ).Evalb (c :> v) ↔ ∃ ξ U W C d e : V,
      c = ⟨ξ, ⟨U, ⟨W, ⟨C, ⟨d, e⟩ₖ⟩ₖ⟩ₖ⟩ₖ⟩ₖ ∧
      (piWitnessCertificateFormula k ψ).Evalb (ξ :> U :> W :> C :> d :> e :> v) := by
  simp [piWitnessFamilyCodeFormula, eval_boundedSextupleBind, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def]

theorem piWitnessFamilyCode_sound {n k : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    (hψ : IsPiFormula (k + 1) ψ) (c : V) (v : Fin n → V)
    (hc : (piWitnessFamilyCodeFormula k ψ).Evalb (c :> v)) : ∃ u : V, ψ.Evalb (u :> v) := by
  obtain ⟨ξ, U, W, C, d, e, _, ht⟩ := (eval_piWitnessFamilyCodeFormula ψ c v).mp hc
  have hcert := ((eval_piWitnessCertificateFormula hψ ξ U W C d e v).mp ht).1
  obtain ⟨u, hu⟩ := hcert.2.2.2.1
  exact ⟨u, (hcert.members u |>.mp hu).1⟩

theorem piWitnessFamilyCode_unique {n k : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    (hψ : IsPiFormula (k + 1) ψ) {c c' : V} (v : Fin n → V)
    (hc : (piWitnessFamilyCodeFormula k ψ).Evalb (c :> v))
    (hc' : (piWitnessFamilyCodeFormula k ψ).Evalb (c' :> v)) : c = c' := by
  obtain ⟨ξ, U, W, C, d, e, rfl, ht⟩ := (eval_piWitnessFamilyCodeFormula ψ c v).mp hc
  obtain ⟨ξ', U', W', C', d', e', rfl, ht'⟩ := (eval_piWitnessFamilyCodeFormula ψ c' v).mp hc'
  obtain ⟨hcert, hd, he⟩ := (eval_piWitnessCertificateFormula hψ ξ U W C d e v).mp ht
  obtain ⟨hcert', hd', he'⟩ := (eval_piWitnessCertificateFormula hψ ξ' U' W' C' d' e' v).mp ht'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hcert.unique hcert'
  have hde : d = d' := sigmaWitnessCodeFormula_unique (ξ :> U :> W :> C :> v) d d' hd hd'
  have hee : e = e' := sigmaWitnessCodeFormula_unique (ξ :> U :> W :> C :> v) e e' he he'
  subst d'
  subst e'
  rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem semisentence_witness_section_definable {n : ℕ}
    (ψ : SetTheorySemisentence (n + 1)) (v : Fin n → V) :
    ℒₛₑₜ-predicate (fun u ↦ ψ.Evalb (u :> v)) := by
  have hψ : Language.Definable ℒₛₑₜ (fun w : Fin (n + 1) → V ↦ ψ.Evalb w) :=
    (show Defined (fun w : Fin (n + 1) → V ↦ ψ.Evalb w) ψ from ⟨fun _ ↦ Iff.rfl⟩).to_definable
  apply Language.Definable.substitution hψ (f := fun i w ↦ (w 0 :> v) i)
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change Language.DefinableFunction ℒₛₑₜ (fun w : Fin 1 → V ↦ w 0)
    definability
  · change Language.DefinableFunction ℒₛₑₜ (fun (_ : Fin 1 → V) ↦ v j)
    definability

theorem piWitnessFamilyCode_existsUnique {n k : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    (hψ : IsPiFormula (k + 1) ψ) (v : Fin n → V) (hex : ∃ u : V, ψ.Evalb (u :> v)) :
    ∃! c : V, (piWitnessFamilyCodeFormula k ψ).Evalb (c :> v) := by
  obtain ⟨ξ, U, W, C, hc⟩ := leastWitnessCertificate_exists
    (fun u ↦ ψ.Evalb (u :> v)) (semisentence_witness_section_definable ψ v) hex
  obtain ⟨d, e, ht⟩ := piWitnessCertificate_exists hψ ξ U W C v hc
  let c := ⟨ξ, ⟨U, ⟨W, ⟨C, ⟨d, e⟩ₖ⟩ₖ⟩ₖ⟩ₖ⟩ₖ
  have hcode : (piWitnessFamilyCodeFormula k ψ).Evalb (c :> v) :=
    (eval_piWitnessFamilyCodeFormula ψ c v).mpr ⟨ξ, U, W, C, d, e, rfl, ht⟩
  exact ⟨c, hcode, fun c' hc' ↦ piWitnessFamilyCode_unique hψ v hc' hcode⟩

theorem piWitnessFamilyCode_existsUnique_iff {n k : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    (hψ : IsPiFormula (k + 1) ψ) (v : Fin n → V) :
    (∃! c : V, (piWitnessFamilyCodeFormula k ψ).Evalb (c :> v)) ↔ ∃ u : V, ψ.Evalb (u :> v) := by
  constructor
  · rintro ⟨c, hc, _⟩
    exact piWitnessFamilyCode_sound hψ c v hc
  · exact piWitnessFamilyCode_existsUnique hψ v

end ZFVP
