import ZFVP.ModelTheory.LevyCollapseSubmodel
import ZFVP.SetTheory.LevyCollapseRowPermutations
import ZFVP.SetTheory.ForcingFormulaNameAction
import ZFVP.ModelTheory.ForcingFunctionValues

/-! Localization for the Levy collapse (lem:Solovay-localization, the homogeneity step): a
condition forcing a statement about names for the subcollapse below `β` can be cut below `β`,
because a row permutation fixing the subcollapse moves the condition onto any extension of its
cut. Hence a set of checks of ordinals defined in `V[G]` from subcollapse names has a name for
the subcollapse, so it belongs to `V[G_β]`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `q` forces `φ(x, v)`. -/
def ForcesAt (P R : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) (x q : V) : Prop :=
  q ∈ forcingFormula P R φ (standardTuple (x :> v))

instance forcesAt_definable (P R : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) :
    ℒₛₑₜ-relation[V] (ForcesAt P R φ v) := by
  unfold ForcesAt
  simp only [standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ]
  definability

/-- The subcollapse name of `{α ∈ θ : φ(α̌, v)}`. -/
noncomputable def localizedName (κ β θ : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → V) : V :=
  {z ∈ (repl (checkName ∅) (by definability) θ) ×ˢ levyCollapse β ;
    ForcesAt (levyCollapse κ) (levyOrder κ) φ v (kpair.π₁ z) (kpair.π₂ z)}

theorem kpair_mem_localizedName_iff (κ β θ : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → V) (σ q : V) :
    ⟨σ, q⟩ₖ ∈ localizedName κ β θ φ v ↔ (∃ α ∈ θ, σ = checkName ∅ α) ∧ q ∈ levyCollapse β ∧
      q ∈ forcingFormula (levyCollapse κ) (levyOrder κ) φ (standardTuple (σ :> v)) := by
  unfold localizedName
  simp only [mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, repl_spec, and_assoc]
  exact Iff.rfl

theorem localizedName_isName (κ β θ : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → V) : IsForcingName (levyCollapse β) (localizedName κ β θ φ v) := by
  rw [forcingName_iff]
  intro z hz
  obtain ⟨x, hx, q, hq, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨α, _, rfl⟩ := (repl_spec _).mp hx
  exact ⟨checkName ∅ α, q, hq, rfl, checkName_isName (empty_mem_levyCollapse β) α⟩

section

variable {κ : V} (β : V) [IsOrdinal β] (hβ : β ⊆ κ)

include hβ in
/-- Names over the subcollapse are fixed by row permutations above `β`. -/
theorem nameAction_levyPermutation_fixed {σ τ : V} (hσ : IsInternalPermutation (ω : V) σ)
    (hτ : IsForcingName (levyCollapse β) τ) : nameAction (levyPermutation κ β σ) τ = τ :=
  nameAction_eq_self_of_fixed (hτ.mono (levyCollapse_mono hβ)) (fun ρ hρ _ p hp ↦
    levyPermutation_fixed hσ (forcingName_condition (forcingName_mem_closure hτ hρ) hp) hβ)

include hβ in
/-- Homogeneity: the cut below `β` of a condition forcing a statement about subcollapse names
forces the same statement. -/
theorem levyCut_forces {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V)
    (hv : ∀ i, IsForcingName (levyCollapse β) (v i)) {p : V} (hp : p ∈ levyCollapse κ)
    (hforce : p ∈ forcingFormula (levyCollapse κ) (levyOrder κ) φ (standardTuple v)) :
    levyCut β p ∈ forcingFormula (levyCollapse κ) (levyOrder κ) φ (standardTuple v) := by
  have hR := (levyCollapse_poset κ).1
  have hreg := forcingFormula_regular hR φ (standardTuple v)
  have hq : levyCut β p ∈ levyCollapse κ := levyCollapse_subset hp (levyCut_subset β p)
  by_contra hno
  have h3 := hreg.2.2 _ hq
  have hex : ∃ q' ∈ levyCollapse κ, ⟨q', levyCut β p⟩ₖ ∈ levyOrder κ ∧
      ∀ r ∈ forcingFormula (levyCollapse κ) (levyOrder κ) φ (standardTuple v), ⟨r, q'⟩ₖ ∉ levyOrder κ := by
    by_contra h
    apply hno
    apply h3
    intro q' hq' hle
    by_contra hnone
    apply h
    exact ⟨q', hq', hle, fun r hr hle' ↦ hnone ⟨r, hr, hle'⟩⟩
  obtain ⟨q', hq'P, hq'le, hneg⟩ := hex
  obtain ⟨σ, hσ, hmove⟩ := exists_permutation_moving (levyRows_finite (β := β) hp) (levyRows_subset β p)
    (levyRows_finite (β := β) hq'P) (levyRows_subset β q')
  have hπ := levyPermutation_automorphism (κ := κ) (β := β) hσ
  have hcutq' : levyCut β p ⊆ q' := ((pair_mem_reverseInclusionOrder _ _ _).mp hq'le).2.2
  have hcompat := levyPermutation_compatible hσ hp hq'P hcutq' hmove
  have hπp : (levyPermutation κ β σ) ‘ p ∈ forcingFormula (levyCollapse κ) (levyOrder κ) φ (standardTuple v) := by
    have h := (forcingFormula_nameAction_iff hR hπ φ v
      (fun i ↦ (hv i).mono (levyCollapse_mono hβ)) hp).mpr hforce
    have hfix : (fun i ↦ nameAction (levyPermutation κ β σ) (v i)) = v :=
      funext (fun i ↦ nameAction_levyPermutation_fixed β hβ hσ (hv i))
    rwa [hfix] at h
  rw [levyPermutation_value hp] at hπp
  have hπpP := permutedGraph_levy_mem (levyRowPermutation_permutation (κ := κ) (β := β) hσ)
    (levyRowPermutation_preservesColumns (κ := κ) (β := β) hσ) hp
  have hr := levyCollapse_union hπpP hq'P hcompat
  have hrle : ⟨permutedGraph (levyRowPermutation κ β σ) p ∪ q', permutedGraph (levyRowPermutation κ β σ) p⟩ₖ ∈
      levyOrder κ := (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hr, hπpP, subset_union_left _ _⟩
  have hrA := hreg.2.1 _ hπp _ hr hrle
  exact hneg _ hrA ((pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hr, hq'P, subset_union_right _ _⟩)

variable {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- The value of the localized name is the set of checks of ordinals below `θ` satisfying `φ`
with the subcollapse-name parameters. -/
theorem mem_ofName_localizedName_iff (θ : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → ForcingName (levyCollapse β)) (x : (levyContext κ hG).Model) :
    x ∈ (levyContext κ hG).ofName ⟨localizedName κ β θ φ (fun i ↦ (v i).val),
        (localizedName_isName κ β θ φ _).mono (levyCollapse_mono hβ)⟩ ↔
      ∃ α ∈ θ, x = (levyContext κ hG).check α ∧
        φ.Evalb ((levyContext κ hG).check α :>
          fun i ↦ (levyContext κ hG).ofName ⟨(v i).val, (v i).property.mono (levyCollapse_mono hβ)⟩) := by
  let A := levyContext κ hG
  have htruth : ∀ α : V, φ.Evalb (A.check α :>
      fun i ↦ A.ofName ⟨(v i).val, (v i).property.mono (levyCollapse_mono hβ)⟩) ↔
      GenericMeets G (forcingFormula (levyCollapse κ) (levyOrder κ) φ
        (standardTuple (checkName ∅ α :> fun i ↦ (v i).val))) := by
    intro α
    have h := A.formula_truth φ (⟨checkName ∅ α, checkName_isName (levyCollapse_top κ).1 α⟩ :>
      fun i ↦ ⟨(v i).val, (v i).property.mono (levyCollapse_mono hβ)⟩)
    have e1 : (fun i ↦ A.ofName ((⟨checkName ∅ α, checkName_isName (levyCollapse_top κ).1 α⟩ :>
        fun i ↦ (⟨(v i).val, (v i).property.mono (levyCollapse_mono hβ)⟩ : ForcingName A.P)) i)) =
        (A.check α :> fun i ↦ A.ofName ⟨(v i).val, (v i).property.mono (levyCollapse_mono hβ)⟩) := by
      funext i
      refine Fin.cases rfl (fun j ↦ rfl) i
    have e2 : (fun i ↦ ((⟨checkName ∅ α, checkName_isName (levyCollapse_top κ).1 α⟩ :>
        fun i ↦ (⟨(v i).val, (v i).property.mono (levyCollapse_mono hβ)⟩ : ForcingName A.P)) i).val) =
        (checkName ∅ α :> fun i ↦ (v i).val) := by
      funext i
      refine Fin.cases rfl (fun j ↦ rfl) i
    rw [e1, e2] at h
    exact h
  constructor
  · intro hx
    obtain ⟨ν, q, hqG, hνq, rfl⟩ := (A.mem_ofName_iff _ x).mp hx
    obtain ⟨⟨α, hα, hν⟩, _, hforce⟩ := (kpair_mem_localizedName_iff κ β θ φ _ ν.val q).mp hνq
    refine ⟨α, hα, ?_, ?_⟩
    · exact congrArg A.ofName (Subtype.ext hν)
    · rw [htruth]
      rw [hν] at hforce
      exact ⟨q, hqG, hforce⟩
  · rintro ⟨α, hα, rfl, hφ⟩
    obtain ⟨p, hpG, hforce⟩ := (htruth α).mp hφ
    have hpP : p ∈ levyCollapse κ := hG.1.1 p hpG
    have hcut := levyCut_forces β hβ φ (checkName ∅ α :> fun i ↦ (v i).val)
      (fun i ↦ Fin.cases (checkName_isName (empty_mem_levyCollapse β) α) (fun j ↦ (v j).property) i)
      hpP hforce
    have hcutG : levyCut β p ∈ G :=
      hG.1.2.2.1 p hpG _ (levyCollapse_subset hpP (levyCut_subset β p)) (levyCut_le hpP)
    refine (A.mem_ofName_iff _ _).mpr ⟨⟨checkName ∅ α, checkName_isName (levyCollapse_top κ).1 α⟩,
      levyCut β p, hcutG, ?_, rfl⟩
    exact (kpair_mem_localizedName_iff κ β θ φ _ _ _).mpr ⟨⟨α, hα, rfl⟩, levyCut_mem hpP, hcut⟩

/-- Localization: a set of checks of ordinals defined from subcollapse-name parameters lies in
`V[G_β]`. -/
theorem inLevySubmodel_localized (θ : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → ForcingName (levyCollapse β)) :
    InLevySubmodel β hβ hG ((levyContext κ hG).ofName ⟨localizedName κ β θ φ (fun i ↦ (v i).val),
      (localizedName_isName κ β θ φ _).mono (levyCollapse_mono hβ)⟩) :=
  inLevySubmodel_ofName β hβ hG ⟨localizedName κ β θ φ (fun i ↦ (v i).val), localizedName_isName κ β θ φ _⟩

end

end ZFVP
