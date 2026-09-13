import ZFVP.Syntax.SigmaOneInternalForcing
import ZFVP.Syntax.SigmaOneInternalNonforcing
import ZFVP.Syntax.EndExtensionMembershipSyntax

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Resident forcing computations agree in ZF membership end extensions. -/
theorem internalForces_iff (j : MembershipEndExtension V W) {P R D n φ b p : V}
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ D ^ n) (hp : p ∈ P) :
    InternalForces P R D n φ b p ↔
      InternalForces (j P) (j R) (j D) (j n) (j φ) (j b) (j p) := by
  have hφ' := (j.membershipFormulaCode_iff n φ).mpr hφ
  have hb' := (j.function_iff b n D).mpr hb
  have hp' := (j.mem_iff p P).mpr hp
  have he (ψ : SetTheorySemisentence 7) :
      ψ.Evalb (fun i ↦ j (![P, R, D, n, φ, b, p] i)) ↔
        ψ.Evalb ![j P, j R, j D, j n, j φ, j b, j p] := by
    simp [Matrix.comp_vecCons', Matrix.constant_eq_singleton]
  constructor
  · intro h
    apply (eval_sigmaOneInternalForcingFormula hφ' hb' hp').mp
    exact (he _).mp (j.sigma_one_upward sigmaOneInternalForcingFormula_sigmaOne _
      ((eval_sigmaOneInternalForcingFormula hφ hb hp).mpr h))
  · intro h
    by_contra hn
    have hn' := j.sigma_one_upward sigmaOneInternalNonforcingFormula_sigmaOne _
      ((eval_sigmaOneInternalNonforcingFormula hφ hb hp).mpr hn)
    exact ((eval_sigmaOneInternalNonforcingFormula hφ' hb' hp').mp ((he _).mp hn')) h

end MembershipEndExtension
end ZFVP



