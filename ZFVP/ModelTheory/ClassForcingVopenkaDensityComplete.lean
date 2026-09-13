import ZFVP.ModelTheory.ClassForcingVopenkaDensitySharp
import ZFVP.SetTheory.SupercompactPiOneVopenka

/-! The class-forcing density criterion at every positive standard fragment. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u v w
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    {I : Type w} {W : I → Type v}
    [∀ i, SetStructure (W i)] [∀ i, Nonempty (W i)]
    [∀ i, (W i)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ClassForcingDensitySemantics
variable (S : ClassForcingDensitySemantics V I W)

theorem forcesPiOneVopenka_of_denselyUnbounded (hAC : ∀ i, InternalChoice (W i))
    (hd : S.denselyUnbounded (densityCardinalFormula 1)) : S.forcesPiVopenka 1 := by
  apply (S.forcesPiVopenka_iff 1).mpr
  intro i φ hφ
  have hSC := S.supercompact_extensionsUnbounded_iff.mp ((S.denselyUnbounded_iff _).mp hd) i
  exact supercompact_unbounded_implies_pi_one_vopenka (hAC i) hSC φ hφ

theorem forcesPiVopenka_iff_denselyUnbounded_all_positive (hAC : ∀ i, InternalChoice (W i))
    {m : ℕ} (hm : 0 < m) :
    S.forcesPiVopenka m ↔ S.denselyUnbounded (densityCardinalFormula m) := by
  by_cases hone : m = 1
  · subst m
    exact ⟨S.denselyUnbounded_of_forcesPiVopenka hAC (by omega),
      S.forcesPiOneVopenka_of_denselyUnbounded hAC⟩
  · exact S.forcesPiVopenka_iff_denselyUnbounded_sharp hAC (by omega)

end ClassForcingDensitySemantics
end ZFVP
