import ZFVP.ModelTheory.ClassForcingVopenkaDensity
import ZFVP.SetTheory.CnExtendibleVopenkaSharp

/-! The class-forcing density criterion at every standard fragment m >= 2.
The sharp transitive-ZF proof removes both numerical dictionary bounds.
`ClassForcingVopenkaDensityComplete` adds the m = 1 case and proves the
equivalence at every positive standard level, using the ordinary
normal-fine-measure theorem `pi_one_vopenka_iff_unbounded_supercompact_measure`
from `ZFVP.SetTheory.SupercompactPiOneVopenka`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The arbitrary-language Pi(k+2) fragment is equivalent over ZFC to unbounded
C(k+1)-extendibles, for every natural k. -/
theorem pi_vopenka_iff_unbounded_cnExtendible_sharp (hAC : InternalChoice M) (k : ℕ) :
    (∀ φ : SetTheorySemisentence 2, IsPiFormula (k + 2) φ → VopenkaInstance (V := M) φ) ↔
      ∀ α : M, IsOrdinal α → ∃ κ : M, α ∈ κ ∧ IsCnExtendible (k + 1) κ :=
  ⟨pi_vopenka_implies_cnExtendible_unbounded hAC,
    fun h φ hφ ↦ cnExtendible_unbounded_implies_pi_vopenka_sharp h φ hφ⟩

universe u v w

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    {I : Type w} {W : I → Type v}
    [∀ i, SetStructure (W i)] [∀ i, Nonempty (W i)]
    [∀ i, (W i)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ClassForcingDensitySemantics

variable (S : ClassForcingDensitySemantics V I W)

/-- The converse density implication at every standard level at least two. -/
theorem forcesPiVopenka_of_denselyUnbounded_sharp {k : ℕ}
    (hd : S.denselyUnbounded (densityCardinalFormula (k + 2))) :
    S.forcesPiVopenka (k + 2) := by
  apply (S.forcesPiVopenka_iff (k + 2)).mpr
  intro i φ hφ
  have hE := (S.cn_extensionsUnbounded_iff (k + 1)).mp
    ((S.denselyUnbounded_iff _).mp hd) i
  exact cnExtendible_unbounded_implies_pi_vopenka_sharp hE φ hφ

/-- Proposition `prop:class-forcing-criteria` for every standard m >= 2, under
the paper's explicit forcing-theorem and ZFC-extension hypotheses. -/
theorem forcesPiVopenka_iff_denselyUnbounded_sharp (hAC : ∀ i, InternalChoice (W i))
    {m : ℕ} (hm : 2 ≤ m) :
    S.forcesPiVopenka m ↔ S.denselyUnbounded (densityCardinalFormula m) := by
  cases m with
  | zero => omega
  | succ m =>
    cases m with
    | zero => omega
    | succ k =>
      exact ⟨S.denselyUnbounded_of_forcesPiVopenka hAC (by omega),
        S.forcesPiVopenka_of_denselyUnbounded_sharp⟩

end ClassForcingDensitySemantics
end ZFVP
