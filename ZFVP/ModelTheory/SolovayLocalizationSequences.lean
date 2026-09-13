import ZFVP.ModelTheory.SolovayLocalization
import ZFVP.ModelTheory.GroundRealsHODClosure
import ZFVP.SetTheory.EndExtensionReplacement
import ZFVP.SetTheory.EndExtensionSets

/-! Lemma Solovay-localization, second clause: a definable sequence `⟨A_ξ : ξ < δ⟩` of subsets of
`κ` with `δ < κ` lies in one bounded-stage extension. The sequence is coded by the set of pairs
`{⟨ξ, α⟩ : α ∈ A_ξ}`, which is a definable set of ground pairs and hence localized; the sequence
is recovered from the code inside the bounded-stage extension. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- `z` is a pair `⟨ξ, α⟩` with `α` in the value of the function `g` at `ξ`. -/
def sequenceCodeFormula : SetTheorySemisentence 2 :=
  f“z g. ∃ ξ α w, z = !kpair.dfn ξ α ∧ !kpair.dfn ξ w ∈ g ∧ α ∈ w”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sequenceCodeFormula (v : Fin 2 → V) :
    sequenceCodeFormula.Evalb v ↔ ∃ ξ α w : V, v 0 = ⟨ξ, α⟩ₖ ∧ ⟨ξ, w⟩ₖ ∈ v 1 ∧ α ∈ w := by
  simp [sequenceCodeFormula]

/-- The code of a sequence of sets as a set of pairs. -/
noncomputable def sequenceCode (D K g : V) : V :=
  sep (D ×ˢ K) (fun z ↦ ∃ ξ α w, z = ⟨ξ, α⟩ₖ ∧ ⟨ξ, w⟩ₖ ∈ g ∧ α ∈ w) (by definability)

theorem mem_sequenceCode_iff (D K g z : V) :
    z ∈ sequenceCode D K g ↔ z ∈ D ×ˢ K ∧ ∃ ξ α w, z = ⟨ξ, α⟩ₖ ∧ ⟨ξ, w⟩ₖ ∈ g ∧ α ∈ w :=
  mem_sep_iff

/-- For a function `g : D → ℘ K`, membership of a pair in the code is membership in the value. -/
theorem kpair_mem_sequenceCode_iff {D K g : V} (hg : g ∈ ℘ K ^ D) {ξ α : V} (hξ : ξ ∈ D) :
    ⟨ξ, α⟩ₖ ∈ sequenceCode D K g ↔ α ∈ g ‘ ξ := by
  haveI : IsFunction g := IsFunction.of_mem hg
  have hdom : domain g = D := domain_eq_of_mem_function hg
  have hval : g ‘ ξ ∈ ℘ K := function_value_mem hg hξ
  rw [mem_sequenceCode_iff]
  constructor
  · rintro ⟨_, ξ', α', w, hz, hw, hαw⟩
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hz
    rw [value_eq_of_kpair_mem hw]
    exact hαw
  · intro hα
    refine ⟨kpair_mem_iff.mpr ⟨hξ, mem_power_iff.mp hval α hα⟩, ξ, α, g ‘ ξ, rfl,
      kpair_value_mem (by rw [hdom]; exact hξ), hα⟩

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- The code of a definable sequence is definable. -/
theorem sequenceCode_groundRealDefinable {δ : V} {g : (levyContext κ hG).Model}
    (hg : g ∈ ℘ ((levyContext κ hG).check κ) ^ ((levyContext κ hG).check δ))
    (hgd : (levyContext κ hG).IsGroundRealDefinable g) :
    (levyContext κ hG).IsGroundRealDefinable
      (sequenceCode ((levyContext κ hG).check δ) ((levyContext κ hG).check κ) g) := by
  haveI : IsFunction g := IsFunction.of_mem hg
  have hdom : domain g = (levyContext κ hG).check δ := domain_eq_of_mem_function hg
  refine ForcingContext.groundRealDefinable_of_definable_from hgd sequenceCodeFormula (fun b ↦ ?_)
  rw [mem_sequenceCode_iff, eval_sequenceCodeFormula]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨ξ, α, w, rfl, hw, hαw⟩
    refine ⟨?_, ξ, α, w, rfl, hw, hαw⟩
    have hξ : ξ ∈ (levyContext κ hG).check δ := by rw [← hdom]; exact mem_domain_of_kpair_mem hw
    have hwval : w = g ‘ ξ := (value_eq_of_kpair_mem hw).symm
    have hval : g ‘ ξ ∈ ℘ ((levyContext κ hG).check κ) := function_value_mem hg hξ
    rw [hwval] at hαw
    exact kpair_mem_iff.mpr ⟨hξ, mem_power_iff.mp hval α hαw⟩

set_option maxHeartbeats 1000000 in
/-- A sequence is recovered from its code inside a bounded-stage extension containing the code. -/
theorem inLevySubmodel_of_sequenceCode {β : V} [IsOrdinal β] (hβ : β ⊆ κ) {δ : V}
    {g : (levyContext κ hG).Model}
    (hg : g ∈ ℘ ((levyContext κ hG).check κ) ^ ((levyContext κ hG).check δ))
    (hC : InLevySubmodel β hβ hG
      (sequenceCode ((levyContext κ hG).check δ) ((levyContext κ hG).check κ) g)) :
    InLevySubmodel β hβ hG g := by
  let A := levyContext κ hG
  let C := levySubContext β hβ hG
  let L := levySubRealization β hβ hG
  haveI : IsFunction g := IsFunction.of_mem hg
  have hdom : domain g = A.check δ := domain_eq_of_mem_function hg
  obtain ⟨C', hC'⟩ := hC
  have hS : ℒₛₑₜ-function₁ (fun ξ : C.Model ↦ ({α ∈ C.check κ ; ⟨ξ, α⟩ₖ ∈ C'} : C.Model)) := by
    have h : ℒₛₑₜ-relation (fun s ξ : C.Model ↦ ∀ α, α ∈ s ↔ α ∈ C.check κ ∧ ⟨ξ, α⟩ₖ ∈ C') := by
      definability
    apply Language.Definable.of_iff h
    intro v
    change v 0 = {α ∈ C.check κ ; ⟨v 1, α⟩ₖ ∈ C'} ↔ _
    rw [mem_ext_iff]
    simp only [mem_sep_iff]
  let F : C.Model → C.Model := fun ξ ↦ ⟨ξ, {α ∈ C.check κ ; ⟨ξ, α⟩ₖ ∈ C'}⟩ₖ
  have hF : ℒₛₑₜ-function₁ F := by
    unfold F
    have := hS
    definability
  have hT : ℒₛₑₜ-function₁ (fun ξ : A.Model ↦ ({α ∈ A.check κ ; ⟨ξ, α⟩ₖ ∈
      sequenceCode (A.check δ) (A.check κ) g} : A.Model)) := by
    have h : ℒₛₑₜ-relation (fun s ξ : A.Model ↦ ∀ α, α ∈ s ↔ α ∈ A.check κ ∧ ⟨ξ, α⟩ₖ ∈
        sequenceCode (A.check δ) (A.check κ) g) := by
      definability
    apply Language.Definable.of_iff h
    intro v
    change v 0 = {α ∈ A.check κ ; ⟨v 1, α⟩ₖ ∈ sequenceCode (A.check δ) (A.check κ) g} ↔ _
    rw [mem_ext_iff]
    simp only [mem_sep_iff]
  let Q : A.Model → A.Model := fun ξ ↦ ⟨ξ, {α ∈ A.check κ ; ⟨ξ, α⟩ₖ ∈
    sequenceCode (A.check δ) (A.check κ) g}⟩ₖ
  have hQ : ℒₛₑₜ-function₁ Q := by
    unfold Q
    have := hT
    definability
  refine ⟨repl F hF (C.check δ), ?_⟩
  have h1 : L.embedding (C.check κ) = A.check κ :=
    (L.value_check κ).trans (levySubRealization_ground β hβ hG κ)
  have h2 : L.embedding C' = sequenceCode (A.check δ) (A.check κ) g := hC'
  have hmap : ∀ x ∈ C.check δ, L.embedding (F x) = Q (L.embedding x) := by
    intro x _
    show L.embedding ⟨x, {α ∈ C.check κ ; ⟨x, α⟩ₖ ∈ C'}⟩ₖ =
      ⟨L.embedding x, {α ∈ A.check κ ; ⟨L.embedding x, α⟩ₖ ∈ sequenceCode (A.check δ) (A.check κ) g}⟩ₖ
    rw [L.embedding.map_kpair]
    congr 1
    rw [L.embedding.map_separation _ (fun α ↦ ⟨x, α⟩ₖ ∈ C')
      (fun α ↦ ⟨L.embedding x, α⟩ₖ ∈ L.embedding C') (by definability) (by definability)
      (fun α _ ↦ by rw [← L.embedding.map_kpair, L.embedding.mem_iff]), h1]
    apply mem_ext
    intro α
    rw [mem_sep_iff, mem_sep_iff, h2]
  have hrepl : L.value (repl F hF (C.check δ)) = repl Q hQ (A.check δ) := by
    have h := L.embedding.map_repl (C.check δ) F Q hF hQ hmap
    change L.value (repl F hF (C.check δ)) = repl Q hQ (L.value (C.check δ)) at h
    rw [L.value_check] at h
    exact h
  rw [hrepl]
  have hval : ∀ ξ ∈ A.check δ, g ‘ ξ =
      {α ∈ A.check κ ; ⟨ξ, α⟩ₖ ∈ sequenceCode (A.check δ) (A.check κ) g} := by
    intro ξ hξ
    apply mem_ext
    intro α
    rw [mem_sep_iff, kpair_mem_sequenceCode_iff hg hξ]
    exact ⟨fun h ↦ ⟨mem_power_iff.mp (function_value_mem hg hξ) α h, h⟩, fun h ↦ h.2⟩
  apply mem_ext
  intro z
  rw [repl_spec]
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    show ⟨ξ, {α ∈ A.check κ ; ⟨ξ, α⟩ₖ ∈ sequenceCode (A.check δ) (A.check κ) g}⟩ₖ ∈ g
    rw [← hval ξ hξ]
    exact kpair_value_mem (by rw [hdom]; exact hξ)
  · intro hz
    have hz' := (mem_function_iff.mp hg).1 z hz
    obtain ⟨ξ, hξ, y, _, rfl⟩ := mem_prod_iff.mp hz'
    refine ⟨ξ, hξ, ?_⟩
    have hy : y = g ‘ ξ := (value_eq_of_kpair_mem hz).symm
    show ⟨ξ, y⟩ₖ = ⟨ξ, {α ∈ A.check κ ; ⟨ξ, α⟩ₖ ∈ sequenceCode (A.check δ) (A.check κ) g}⟩ₖ
    exact congrArg (fun s ↦ ⟨ξ, s⟩ₖ) (hy.trans (hval ξ hξ))

include hAC hU hc hω hκ in
/-- Lemma Solovay-localization, second clause: a definable sequence of subsets of `κ` indexed by
`δ` lies in a single bounded-stage extension. -/
theorem sequence_localized {δ : V} {g : (levyContext κ hG).Model}
    (hg : g ∈ ℘ ((levyContext κ hG).check κ) ^ ((levyContext κ hG).check δ))
    (hgd : (levyContext κ hG).IsGroundRealDefinable g) : IsLocalized hG g := by
  have hcode := sequenceCode_groundRealDefinable hG hg hgd
  have hsub : sequenceCode ((levyContext κ hG).check δ) ((levyContext κ hG).check κ) g ⊆
      (levyContext κ hG).check (δ ×ˢ κ) := by
    intro z hz
    have hp : (levyContext κ hG).check (δ ×ˢ κ) =
        (levyContext κ hG).check δ ×ˢ (levyContext κ hG).check κ :=
      (levyContext κ hG).checkEmbedding.map_prod δ κ
    rw [hp]
    exact ((mem_sequenceCode_iff _ _ _ _).mp hz).1
  obtain ⟨ξ, hξ, hloc⟩ := groundRealDefinable_localized hAC hU hc hω hκ hG hcode hsub
  haveI : IsOrdinal ξ := IsOrdinal.of_mem hξ
  exact ⟨ξ, hξ, inLevySubmodel_of_sequenceCode hG _ hg hloc⟩

end

end ZFVP
