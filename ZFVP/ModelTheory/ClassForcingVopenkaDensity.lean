import ZFVP.ModelTheory.ClassForcingDensitySemantics
import ZFVP.SetTheory.CnExtendibleVopenka
import ZFVP.SetTheory.PiVopenkaCnExtendible
import ZFVP.SetTheory.MagidorSupercompactMeasure

/-! Class-forcing density for the Vopenka scheme.

This module proves the full first-order-scheme criterion using all positive
standard levels and proves the single higher-fragment converse under explicit
syntax bounds. `ClassForcingVopenkaDensitySharp` removes those bounds, and
`ClassForcingVopenkaDensityComplete` proves the equivalence at every positive
standard level. Its level-one case uses
`pi_one_vopenka_iff_unbounded_supercompact_measure` from
`ZFVP.SetTheory.SupercompactPiOneVopenka`, with ordinary normal-fine-measure
supercompactness and no auxiliary strengthening premise.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- A fixed formula for the normal-fine-measure definition of supercompactness. -/
def densitySupercompactFormula : SetTheorySemisentence 1 :=
  f“κ. !initialOrdinalFormula κ ∧ !isω ∈ κ ∧
    ∀ lam, !IsOrdinal.dfn lam → κ ⊆ lam → ∃ U, !normalFineMeasureFormula κ lam U”

/-- The property's formula at the paper's standard fragment level. The unused
level zero is false; level one uses supercompactness in the measure sense. -/
def densityCardinalFormula : ℕ → SetTheorySemisentence 1
  | 0 => ⊥
  | 1 => densitySupercompactFormula
  | n + 2 => cnExtendibleFormula (n + 1)

variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_densitySupercompactFormula (κ : M) :
    densitySupercompactFormula.Evalb ![κ] ↔ IsSupercompact κ := by
  simp [densitySupercompactFormula, IsSupercompact, eval_normalFineMeasureFormula]

universe u v w

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    {I : Type w} {W : I → Type v}
    [∀ i, SetStructure (W i)] [∀ i, Nonempty (W i)]
    [∀ i, (W i)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ClassForcingDensitySemantics

variable (S : ClassForcingDensitySemantics V I W)

/-- Every coded instance in the indicated standard Pi fragment is forced. -/
def forcesPiVopenka (m : ℕ) : Prop :=
  ∀ φ : SetTheorySemisentence 2, IsPiFormula m φ →
    S.Forces S.top (vopenkaSentence φ) ![]

/-- The entire first-order Vopenka scheme is forced. -/
def forcesVopenka : Prop :=
  ∀ φ : SetTheorySemisentence 2, S.Forces S.top (vopenkaSentence φ) ![]

theorem top_forces_vopenkaInstance_iff (φ : SetTheorySemisentence 2) :
    S.Forces S.top (vopenkaSentence φ) ![] ↔
      ∀ i, VopenkaInstance (V := W i) φ := by
  rw [S.top_forces_iff]
  apply forall_congr'
  intro i
  have he : (fun j : Fin 0 ↦ S.eval i ((![] : Fin 0 → {τ : V // τ ∈ S.Names}) j)) =
      (![] : Fin 0 → W i) := by funext j; exact Fin.elim0 j
  rw [he]
  exact eval_vopenkaSentence φ

theorem forcesPiVopenka_iff (m : ℕ) :
    S.forcesPiVopenka m ↔
      ∀ i, ∀ φ : SetTheorySemisentence 2, IsPiFormula m φ →
        VopenkaInstance (V := W i) φ := by
  constructor
  · intro h i φ hφ
    exact (S.top_forces_vopenkaInstance_iff φ).mp (h φ hφ) i
  · intro h φ hφ
    exact (S.top_forces_vopenkaInstance_iff φ).mpr (fun i ↦ h i φ hφ)

theorem forcesVopenka_iff :
    S.forcesVopenka ↔ ∀ i, ∀ φ : SetTheorySemisentence 2,
      VopenkaInstance (V := W i) φ := by
  constructor
  · intro h i φ
    exact (S.top_forces_vopenkaInstance_iff φ).mp (h φ) i
  · intro h φ
    exact (S.top_forces_vopenkaInstance_iff φ).mpr (fun i ↦ h i φ)

theorem cn_extensionsUnbounded_iff (n : ℕ) :
    S.extensionsUnbounded (cnExtendibleFormula n) ↔
      ∀ i, ∀ η : W i, IsOrdinal η →
        ∃ κ : W i, η ∈ κ ∧ IsCnExtendible n κ := by
  constructor
  · intro h i η hη
    obtain ⟨κ, hκ, hηκ, hK⟩ := h i η hη
    exact ⟨κ, hηκ, (eval_cnExtendibleFormula n κ).mp hK⟩
  · intro h i η hη
    obtain ⟨κ, hηκ, hK⟩ := h i η hη
    exact ⟨κ, hK.1.1, hηκ, (eval_cnExtendibleFormula n κ).mpr hK⟩

theorem supercompact_extensionsUnbounded_iff :
    S.extensionsUnbounded densitySupercompactFormula ↔
      ∀ i, ∀ η : W i, IsOrdinal η →
        ∃ κ : W i, η ∈ κ ∧ IsSupercompact κ := by
  constructor
  · intro h i η hη
    obtain ⟨κ, hκ, hηκ, hK⟩ := h i η hη
    exact ⟨κ, hηκ, (eval_densitySupercompactFormula κ).mp hK⟩
  · intro h i η hη
    obtain ⟨κ, hηκ, hK⟩ := h i η hη
    exact ⟨κ, hK.isOrdinal, hηκ, (eval_densitySupercompactFormula κ).mpr hK⟩

/-- The forward direction of the paper's criterion at every positive standard
level, with supercompactness at level one in the normal-measure sense. -/
theorem denselyUnbounded_of_forcesPiVopenka (hAC : ∀ i, InternalChoice (W i))
    {m : ℕ} (hm : 0 < m) (hVP : S.forcesPiVopenka m) :
    S.denselyUnbounded (densityCardinalFormula m) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  cases n with
  | zero =>
    apply (S.denselyUnbounded_iff _).mpr
    apply S.supercompact_extensionsUnbounded_iff.mpr
    intro i
    exact supercompact_unbounded_of_pi_one_vopenka (hAC i)
      ((S.forcesPiVopenka_iff 1).mp hVP i)
  | succ k =>
    apply (S.denselyUnbounded_iff _).mpr
    apply (S.cn_extensionsUnbounded_iff (k + 1)).mpr
    intro i
    exact pi_vopenka_implies_cnExtendible_unbounded (hAC i)
      ((S.forcesPiVopenka_iff (k + 2)).mp hVP i)

/-- The reverse single-fragment implication at levels covering the two explicit
syntax bounds of the existing C(n)-extendibility proof. -/
theorem forcesPiVopenka_of_denselyUnbounded {k : ℕ}
    (hsyntax : coreSyntaxDictionaryBound ≤ k + 1)
    (hemb : codedElementaryEmbeddingBound ≤ k + 1)
    (hd : S.denselyUnbounded (densityCardinalFormula (k + 2))) :
    S.forcesPiVopenka (k + 2) := by
  apply (S.forcesPiVopenka_iff (k + 2)).mpr
  intro i φ hφ
  have hE := (S.cn_extensionsUnbounded_iff (k + 1)).mp
    ((S.denselyUnbounded_iff _).mp hd) i
  exact cnExtendible_unbounded_implies_pi_vopenka hsyntax hemb hE φ hφ

theorem forcesPiVopenka_iff_denselyUnbounded (hAC : ∀ i, InternalChoice (W i))
    {k : ℕ} (hsyntax : coreSyntaxDictionaryBound ≤ k + 1)
    (hemb : codedElementaryEmbeddingBound ≤ k + 1) :
    S.forcesPiVopenka (k + 2) ↔ S.denselyUnbounded (densityCardinalFormula (k + 2)) :=
  ⟨S.denselyUnbounded_of_forcesPiVopenka hAC (by omega),
    S.forcesPiVopenka_of_denselyUnbounded hsyntax hemb⟩

/-- The full first-order scheme criterion, with precisely the density properties
at all positive standard levels. This uses arbitrarily high levels in the
reverse direction and therefore needs neither of the open low-level converse
bridges. The extension-choice hypothesis is the paper's ZFC-extension assumption. -/
theorem forcesVopenka_iff_all_denselyUnbounded (hAC : ∀ i, InternalChoice (W i)) :
    S.forcesVopenka ↔
      ∀ m : ℕ, 0 < m → S.denselyUnbounded (densityCardinalFormula m) := by
  constructor
  · intro h m hm
    exact S.denselyUnbounded_of_forcesPiVopenka hAC hm (fun φ _ ↦ h φ)
  · intro hd
    apply S.forcesVopenka_iff.mpr
    intro i φ
    obtain ⟨k, hsyntax, hemb, hbound⟩ : ∃ k : ℕ,
        coreSyntaxDictionaryBound ≤ k + 1 ∧
        codedElementaryEmbeddingBound ≤ k + 1 ∧ levySyntacticBound φ ≤ k := by
      refine ⟨max coreSyntaxDictionaryBound
        (max codedElementaryEmbeddingBound (levySyntacticBound φ)), ?_, ?_, ?_⟩
      · exact le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
      · exact le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (Nat.le_succ _)
      · exact le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    have hφ : IsPiFormula (k + 2) φ :=
      (isLevyFormula_syntacticBound φ .pi).mono
        (le_trans hbound (Nat.le_add_right k 2))
    have hE := (S.cn_extensionsUnbounded_iff (k + 1)).mp
      ((S.denselyUnbounded_iff _).mp (hd (k + 2) (Nat.zero_lt_succ (k + 1)))) i
    exact cnExtendible_unbounded_implies_pi_vopenka hsyntax hemb hE φ hφ

end ClassForcingDensitySemantics
end ZFVP
