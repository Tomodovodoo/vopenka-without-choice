import ZFVP.SetTheory.UniquePiWitnessCodes
import ZFVP.SetTheory.VopenkaZFRanks
import ZFVP.SetTheory.BoundedRankCriterionWitnesses

/-! A Pi_1 code for the least rank-criterion height above a given ordinal. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def noEarlierRankCriterionFormula : SetTheorySemisentence 2 :=
  “θ b. ∀ η ∈ θ, b ∈ η → ¬!rankCriterionFormula η”

theorem noEarlierRankCriterionFormula_sigmaOne : IsSigmaFormula 1 noEarlierRankCriterionFormula :=
  .boundedAll (.bvar 0) (.or (.bounded (.nrel _ _)) (rankCriterionFormula_piOne.subst _).neg)

def leastRankCriterionCertificateFormula : SetTheorySemisentence 3 :=
  “θ d b. !rankCriterionFormula θ ∧ b ∈ θ ∧
    !(leastWitnessCodeFormula boundedNoEarlierRankCriterionMatrix) d θ b”

theorem leastRankCriterionCertificateFormula_piOne : IsPiFormula 1 leastRankCriterionCertificateFormula :=
  .and (rankCriterionFormula_piOne.subst _) (.and (.bounded (.rel _ _))
    ((leastWitnessCodeFormula_pi (IsLevyFormula.bounded boundedNoEarlierRankCriterionMatrix_bounded)).subst _))

def leastRankCriterionCodeFormula : SetTheorySemisentence 2 :=
  boundedPairBind (.bvar 0) (leastRankCriterionCertificateFormula.subst ![.bvar 0, .bvar 1, .bvar 3])

theorem leastRankCriterionCodeFormula_piOne : IsPiFormula 1 leastRankCriterionCodeFormula :=
  boundedPairBind_levy _ (leastRankCriterionCertificateFormula_piOne.subst _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsLeastRankCriterionAbove (b θ : V) : Prop :=
  IsLeastOrdinal (fun η ↦ b ∈ η ∧ IsRankCriterionHeight η) θ

instance isLeastRankCriterionAbove_definable : ℒₛₑₜ-relation[V] IsLeastRankCriterionAbove := by
  unfold IsLeastRankCriterionAbove IsLeastOrdinal
  definability

theorem leastRankCriterionAbove_existsUnique
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (b : V) [IsOrdinal b] : ∃! θ : V, IsLeastRankCriterionAbove b θ := by
  apply leastOrdinal_existsUnique _ (by definability)
  obtain ⟨θ, hb, hθ⟩ := vopenka_rankCriterion_unbounded hVP b
  exact ⟨θ, hθ.1, hb, hθ⟩

theorem IsLeastRankCriterionAbove.unique {b θ η : V}
    (h : IsLeastRankCriterionAbove b θ) (h' : IsLeastRankCriterionAbove b η) : θ = η :=
  subset_antisymm (h.2.2 η h'.1 h'.2.1) (h'.2.2 θ h.1 h.2.1)

theorem eval_noEarlierRankCriterionFormula (θ b : V) :
    noEarlierRankCriterionFormula.Evalb ![θ, b] ↔
      ∀ η ∈ θ, b ∈ η → ¬IsRankCriterionHeight η := by
  simp [noEarlierRankCriterionFormula]

theorem leastRankCriterionAbove_iff (b θ : V) :
    IsLeastRankCriterionAbove b θ ↔ IsRankCriterionHeight θ ∧ b ∈ θ ∧
      ∀ η ∈ θ, b ∈ η → ¬IsRankCriterionHeight η := by
  constructor
  · intro h
    refine ⟨h.2.1.2, h.2.1.1, ?_⟩
    intro η hη hb hcrit
    exact mem_irrefl η (h.2.2 η hcrit.1 ⟨hb, hcrit⟩ η hη)
  · rintro ⟨hθ, hb, hn⟩
    let := hθ.1
    refine ⟨hθ.1, ⟨hb, hθ⟩, ?_⟩
    rintro η hη ⟨hbη, hcη⟩
    let := hη
    rcases IsOrdinal.mem_trichotomy θ η with hl | he | hg
    · exact IsOrdinal.toIsTransitive.transitive _ hl
    · exact subset_of_eq he
    · exact False.elim (hn η hg hbη hcη)

theorem eval_leastRankCriterionCertificateFormula (θ d b : V) :
    leastRankCriterionCertificateFormula.Evalb ![θ, d, b] ↔
      IsRankCriterionHeight θ ∧ b ∈ θ ∧
        (leastWitnessCodeFormula boundedNoEarlierRankCriterionMatrix).Evalb ![d, θ, b] := by
  simp [leastRankCriterionCertificateFormula]

theorem leastRankCriterionCertificate_sound {θ d b : V}
    (h : leastRankCriterionCertificateFormula.Evalb ![θ, d, b]) : IsLeastRankCriterionAbove b θ := by
  obtain ⟨hθ, hb, hd⟩ := (eval_leastRankCriterionCertificateFormula θ d b).mp h
  apply (leastRankCriterionAbove_iff b θ).mpr
  obtain ⟨W, hW⟩ := ((eval_leastWitnessCodeFormula boundedNoEarlierRankCriterionMatrix ![θ, b] d).mp hd).witness
  exact ⟨hθ, hb, boundedNoEarlierRankCriterionMatrix_sound hW⟩

theorem leastRankCriterionCertificate_exists {θ b : V} (h : IsLeastRankCriterionAbove b θ) :
    ∃! d : V, leastRankCriterionCertificateFormula.Evalb ![θ, d, b] := by
  obtain ⟨hθ, hb, hn⟩ := (leastRankCriterionAbove_iff b θ).mp h
  let := hθ.1
  obtain ⟨d, hd, hu⟩ := leastWitnessCode_existsUnique boundedNoEarlierRankCriterionMatrix ![θ, b]
    ⟨hierarchy θ, boundedNoEarlierRankCriterionMatrix_complete hθ.2.2.1 hn⟩
  refine ⟨d, (eval_leastRankCriterionCertificateFormula θ d b).mpr
    ⟨hθ, hb, (eval_leastWitnessCodeFormula _ _ _).mpr hd⟩, ?_⟩
  intro e he
  exact hu e ((eval_leastWitnessCodeFormula _ _ _).mp
    ((eval_leastRankCriterionCertificateFormula θ e b).mp he).2.2)

theorem eval_leastRankCriterionCodeFormula (c b : V) :
    leastRankCriterionCodeFormula.Evalb ![c, b] ↔ ∃ θ d : V,
      c = ⟨θ, d⟩ₖ ∧ leastRankCriterionCertificateFormula.Evalb ![θ, d, b] := by
  simp [leastRankCriterionCodeFormula, eval_boundedPairBind, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

theorem leastRankCriterionCode_unique {c c' b : V}
    (h : leastRankCriterionCodeFormula.Evalb ![c, b])
    (h' : leastRankCriterionCodeFormula.Evalb ![c', b]) : c = c' := by
  obtain ⟨θ, d, rfl, hd⟩ := (eval_leastRankCriterionCodeFormula c b).mp h
  obtain ⟨η, e, rfl, he⟩ := (eval_leastRankCriterionCodeFormula c' b).mp h'
  have hθη := (leastRankCriterionCertificate_sound hd).unique (leastRankCriterionCertificate_sound he)
  subst η
  have hde : d = e := ((eval_leastWitnessCodeFormula _ _ _).mp
    ((eval_leastRankCriterionCertificateFormula θ d b).mp hd).2.2).unique
      ((eval_leastWitnessCodeFormula _ _ _).mp ((eval_leastRankCriterionCertificateFormula θ e b).mp he).2.2)
  rw [hde]

theorem leastRankCriterionCode_existsUnique
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (b : V) [IsOrdinal b] : ∃! c : V, leastRankCriterionCodeFormula.Evalb ![c, b] := by
  obtain ⟨θ, hθ, _⟩ := leastRankCriterionAbove_existsUnique hVP b
  obtain ⟨d, hd, _⟩ := leastRankCriterionCertificate_exists hθ
  have hc := (eval_leastRankCriterionCodeFormula ⟨θ, d⟩ₖ b).mpr ⟨θ, d, rfl, hd⟩
  exact ⟨⟨θ, d⟩ₖ, hc, fun c hc' ↦ leastRankCriterionCode_unique hc' hc⟩

theorem leastRankCriterionCode_internalZF {c b : V}
    (h : leastRankCriterionCodeFormula.Evalb ![c, b]) :
    ∃ θ d : V, c = ⟨θ, d⟩ₖ ∧ IsLeastRankCriterionAbove b θ ∧
      IsInternalZFModel (hierarchy θ) := by
  obtain ⟨θ, d, he, hd⟩ := (eval_leastRankCriterionCodeFormula c b).mp h
  have hθ := leastRankCriterionCertificate_sound hd
  exact ⟨θ, d, he, hθ, hθ.2.1.2.internalZFModel⟩

end ZFVP
