import ZFVP.ModelTheory.SolovayLocalization
import ZFVP.SetTheory.OrdinalDefinability
import ZFVP.Syntax.EndExtensionMembershipSyntax
import ZFVP.ModelTheory.EndExtensionLanguage
import ZFVP.ModelTheory.ConstantStructure

/-! Ordinal definability in the Levy extension and localization. A bounded stage `V[G_ξ]` is the
range of an end extension, so it is closed downwards under membership and closed under pairing:
that gives the two closure lemmas for `IsLocalized`. Two-variable membership formula codes of the
extension are checks of ground codes, so they are localized. Putting the pieces together, a set
that is ordinal definable from a parameter tree which is localized is the set defined by a single
formula from three localized parameters, so the Solovay localization lemma applies to it. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory



variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The two-variable membership formula codes of an extension are the checks of the ground ones. -/
theorem ForcingContext.check_membershipFormulaCode (A : ForcingContext V)
    {y : A.Model} (hy : IsMembershipFormulaCode ((2 : ℕ) : A.Model) y) : ∃ c : V, y = A.check c := by
  have hfam : (formulaFamily membershipLanguageCode ∅ : A.Model) =
      A.checkEmbedding (formulaFamily membershipLanguageCode ∅ : V) := by
    rw [A.checkEmbedding.map_formulaFamily membershipLanguageCode_valid ∅,
      A.checkEmbedding.map_membershipLanguageCode, A.checkEmbedding.map_empty]
  rw [IsMembershipFormulaCode, hfam] at hy
  obtain ⟨_, c, _, _, rfl⟩ := (A.checkEmbedding.pair_mem_image_iff _ _ _).mp hy
  exact ⟨c, rfl⟩

section

variable {κ : V} [IsOrdinal κ] {G : Set V}
  (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- A bounded stage is transitive, so members of a localized set are localized. -/
theorem isLocalized_of_mem {S y : (levyContext κ hG).Model} (hS : IsLocalized hG S) (hy : y ∈ S) :
    IsLocalized hG y := by
  obtain ⟨ξ, hξ, z, hz⟩ := hS
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  refine ⟨ξ, hξ, ?_⟩
  rw [← hz] at hy
  obtain ⟨w, _, rfl⟩ := (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value_endExtension z hy
  exact ⟨w, rfl⟩

/-- A bounded stage is closed under pairing. -/
theorem isLocalized_kpair {a b : (levyContext κ hG).Model} (ha : IsLocalized hG a)
    (hb : IsLocalized hG b) : IsLocalized hG ⟨a, b⟩ₖ := by
  obtain ⟨ξ₁, hξ₁, h₁⟩ := ha
  obtain ⟨ξ₂, hξ₂, h₂⟩ := hb
  obtain ⟨ξ, hξ, hs₁, hs₂⟩ := exists_stage_ge hξ₁ hξ₂
  have : IsOrdinal ξ₁ := IsOrdinal.of_mem hξ₁
  have : IsOrdinal ξ₂ := IsOrdinal.of_mem hξ₂
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  obtain ⟨u, hu⟩ := inLevySubmodel_mono hG _ _ hs₁ h₁
  obtain ⟨v, hv⟩ := inLevySubmodel_mono hG _ _ hs₂ h₂
  have hk : ∀ u v, (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value ⟨u, v⟩ₖ =
      ⟨(levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value u,
        (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value v⟩ₖ :=
    fun u v ↦ (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).embedding.map_kpair u v
  exact ⟨ξ, hξ, ⟨u, v⟩ₖ, by rw [hk u v, hu, hv]⟩

include hG in
/-- Every two-variable membership formula code of the extension is localized. -/
theorem isLocalized_membershipFormulaCode (hom : (ω : V) ∈ κ) (y : (levyContext κ hG).Model)
    (hy : IsMembershipFormulaCode ((2 : ℕ) : (levyContext κ hG).Model) y) : IsLocalized hG y := by
  obtain ⟨c, rfl⟩ := (levyContext κ hG).check_membershipFormulaCode hy
  exact isLocalized_check hG hom c

end

section

variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Parameter trees of externally finite depth: allowed parameters, closed under pairing. -/
inductive IsFinitaryParameterTree (Pf : SetTheorySemisentence 2) (p : M) : M → Prop
  | allowed {y : M} (h : IsAllowed Pf y p) : IsFinitaryParameterTree Pf p y
  | kpair {a b : M} : IsFinitaryParameterTree Pf p a → IsFinitaryParameterTree Pf p b →
      IsFinitaryParameterTree Pf p ⟨a, b⟩ₖ

/-- A tree of finite depth is a parameter tree. -/
theorem isParameterTree_of_finitary {Pf : SetTheorySemisentence 2} {p P : M}
    (h : IsFinitaryParameterTree Pf p P) : IsParameterTree Pf P p := by
  induction h with
  | allowed h => exact isParameterTree_of_allowed Pf h
  | kpair _ _ iha ihb => exact isParameterTree_kpair Pf iha ihb

/-- Ordinal definability from the parameter class through a parameter tree of finite depth. -/
def IsODFinitary (Pf : SetTheorySemisentence 2) (x p : M) : Prop :=
  ∃ α φ P : M, IsOrdinal α ∧ IsMembershipFormulaCode ((2 : ℕ) : M) φ ∧
    IsFinitaryParameterTree Pf p P ∧ P ∈ hierarchy α ∧ x = decode α φ P

theorem isOD_of_finitary {Pf : SetTheorySemisentence 2} {x p : M} (h : IsODFinitary Pf x p) :
    IsOD Pf x p := by
  obtain ⟨α, φ, P, hα, hφ, hP, hmem, he⟩ := h
  exact ⟨α, φ, P, hα, hφ, isParameterTree_of_finitary hP, hmem, he⟩

end

section

variable {κ : V} [IsOrdinal κ] {G : Set V}
  (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
  (Pf : SetTheorySemisentence 2) (p : (levyContext κ hG).Model)

include hG in
/-- Reduction of "every allowed parameter is localized" to its class case: ordinals of the
extension are checks and formula codes are checks, so only the members of the class are left. -/
theorem isAllowed_localized (hom : (ω : V) ∈ κ)
    (hPf : ∀ y : (levyContext κ hG).Model, Pf.Evalb ![y, p] → IsLocalized hG y)
    (y : (levyContext κ hG).Model) (hy : IsAllowed Pf y p) : IsLocalized hG y := by
  rcases hy with hord | hcode | hclass
  · have := hord
    obtain ⟨β, _, rfl⟩ := (levyContext κ hG).ordinal_eq_check y
    exact isLocalized_check hG hom β
  · exact isLocalized_membershipFormulaCode hG hom y hcode
  · exact hPf y hclass

include hG in
/-- A parameter tree of finite depth over localized allowed parameters is localized. -/
theorem isLocalized_of_finitaryParameterTree
    (hall : ∀ y : (levyContext κ hG).Model, IsAllowed Pf y p → IsLocalized hG y)
    {P : (levyContext κ hG).Model} (h : IsFinitaryParameterTree Pf p P) : IsLocalized hG P := by
  induction h with
  | allowed h => exact hall _ h
  | kpair _ _ iha ihb => exact isLocalized_kpair hG iha ihb

end

/-- Membership in the set defined over `V_α` by the code `φ` with the parameter `P`. -/
def odMemFormula : SetTheorySemisentence 4 := f“b α φ P. b ∈ !decodeFormula α φ P”

theorem odMemFormula_evalb (b α φ P : V) :
    odMemFormula.Evalb ![b, α, φ, P] ↔ b ∈ decode α φ P := by
  simp [odMemFormula]

section

variable {κ : V} [IsOrdinal κ] {G : Set V}
  (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
  (Pf : SetTheorySemisentence 2) (p : (levyContext κ hG).Model)

include hG in
/-- The set defined over `V_α` by a code and a localized parameter is defined by a single formula
from three localized parameters. -/
theorem exists_localized_parameters_of_decode (hom : (ω : V) ∈ κ)
    {α φ₀ P : (levyContext κ hG).Model} (hα : IsOrdinal α)
    (hcode : IsMembershipFormulaCode ((2 : ℕ) : (levyContext κ hG).Model) φ₀)
    (hPloc : IsLocalized hG P) :
    ∃ (n : ℕ) (φ : SetTheorySemisentence (n + 1)) (v : Fin n → (levyContext κ hG).Model),
      (∀ i, IsLocalized hG (v i)) ∧ ∀ b, b ∈ decode α φ₀ P ↔ φ.Evalb (b :> v) := by
  refine ⟨3, odMemFormula, ![α, φ₀, P], ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · have := hα
      obtain ⟨β, _, hβ⟩ := (levyContext κ hG).ordinal_eq_check α
      simpa only [Matrix.cons_val_zero, hβ] using isLocalized_check hG hom β
    · refine Fin.cases ?_ (fun k ↦ ?_) j
      · simpa using isLocalized_membershipFormulaCode hG hom φ₀ hcode
      · refine Fin.cases ?_ (fun t ↦ t.elim0) k
        simpa using hPloc
  · intro b
    exact (odMemFormula_evalb b α φ₀ P).symm

include hG in
/-- A set ordinal definable from a parameter class whose parameter trees are localized is defined
by a single formula from three localized parameters. -/
theorem isLocalized_isOD_parameters (hom : (ω : V) ∈ κ)
    (htree : ∀ P : (levyContext κ hG).Model, IsParameterTree Pf P p → IsLocalized hG P)
    {x : (levyContext κ hG).Model} (hx : IsOD Pf x p) :
    ∃ (n : ℕ) (φ : SetTheorySemisentence (n + 1)) (v : Fin n → (levyContext κ hG).Model),
      (∀ i, IsLocalized hG (v i)) ∧ ∀ b, b ∈ x ↔ φ.Evalb (b :> v) := by
  obtain ⟨α, φ₀, P, hα, hcode, hP, -, rfl⟩ := hx
  exact exists_localized_parameters_of_decode hG hom hα hcode (htree P hP)

include hG in
/-- A set ordinal definable through a parameter tree of finite depth, over allowed parameters that
are localized, is defined by a single formula from three localized parameters. -/
theorem isLocalized_isODFinitary_parameters (hom : (ω : V) ∈ κ)
    (hall : ∀ y : (levyContext κ hG).Model, IsAllowed Pf y p → IsLocalized hG y)
    {x : (levyContext κ hG).Model} (hx : IsODFinitary Pf x p) :
    ∃ (n : ℕ) (φ : SetTheorySemisentence (n + 1)) (v : Fin n → (levyContext κ hG).Model),
      (∀ i, IsLocalized hG (v i)) ∧ ∀ b, b ∈ x ↔ φ.Evalb (b :> v) := by
  obtain ⟨α, φ₀, P, hα, hcode, hP, -, rfl⟩ := hx
  exact exists_localized_parameters_of_decode hG hom hα hcode
    (isLocalized_of_finitaryParameterTree hG Pf p hall hP)

end

end ZFVP
