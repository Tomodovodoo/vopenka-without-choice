import ZFVP.ModelTheory.ForcingHartogsName
import ZFVP.SetTheory.HartogsLimitRegular
import ZFVP.ModelTheory.WoodinCollapseForcesRestoration
import ZFVP.ModelTheory.ForcingCheckedBounded

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem hartogsNumberName_forces_dependentChoiceBelow {P R one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P) (τ : ForcingName P)
    (hord : p ∈ forcingFormula P R IsOrdinal.dfn (standardTuple ![τ.val]))
    (hDC : p ∈ forcingFormula P R dependentChoiceAtFormula (standardTuple ![τ.val])) :
    p ∈ forcingFormula P R dependentChoiceBelowFormula
      (standardTuple ![hartogsNumberName P R τ.val]) := by
  let κ : ForcingName P := ⟨hartogsNumberName P R τ.val, hartogsNumberName_isName _ _ _⟩
  let φ : SetTheorySemisentence 2 := hartogsNumberFormula.and
    ((IsOrdinal.dfn.subst (fun i ↦ .bvar ((![1] : Fin 1 → Fin 2) i))).and
      (dependentChoiceAtFormula.subst (fun i ↦ .bvar ((![1] : Fin 1 → Fin 2) i))))
  let ψ : SetTheorySemisentence 2 := dependentChoiceBelowFormula.subst
    (fun i ↦ .bvar ((![0] : Fin 1 → Fin 2) i))
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![κ.val, τ.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_rename, forcingFormula_rename]
    exact ⟨hartogsNumberName_forces hR htop hp τ, hord, hDC⟩
  have hh := forcingFormula_entailment φ ψ (by
    intro W _ _ _ v hv
    change hartogsNumberFormula.Evalb v ∧
      (IsOrdinal.dfn.subst (fun i ↦ .bvar ((![1] : Fin 1 → Fin 2) i))).Evalb v ∧
      (dependentChoiceAtFormula.subst (fun i ↦ .bvar ((![1] : Fin 1 → Fin 2) i))).Evalb v at hv
    have hs : v 0 = hartogsNumber (v 1) ∧ IsOrdinal (v 1) ∧ InternalDependentChoiceAt (v 1) := by
      simpa [Semiformula.eval_substs] using hv
    let := hs.2.1
    have hd : ∀ α ∈ v 0, InternalDependentChoiceAt α := by
      rw [hs.1]
      exact dependentChoiceBelow_hartogsNumber hs.2.2
    simpa [ψ, Semiformula.eval_substs] using hd) hR htop hp ![κ, τ] hφ
  change p ∈ forcingFormula P R (dependentChoiceBelowFormula.subst
    (fun i ↦ .bvar ((![0] : Fin 1 → Fin 2) i))) (standardTuple ![κ.val, τ.val]) at hh
  rw [forcingFormula_rename] at hh
  exact hh

theorem hartogsNumberName_checked_lower_choice {P R one p γ I : V} [IsOrdinal γ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P) (hI : I ∈ γ)
    (hDC : p ∈ forcingFormula P R dependentChoiceAtFormula (standardTuple ![checkName one γ])) :
    p ∈ forcingFormula P R dependentChoiceAtFormula (standardTuple ![checkName one I]) ∧
    p ∈ forcingFormula P R nameMemberFormula
      (standardTuple ![checkName one I, hartogsNumberName P R (checkName one γ)]) := by
  let τ : ForcingName P := ⟨checkName one γ, checkName_isName htop.1 _⟩
  let α : ForcingName P := ⟨checkName one I, checkName_isName htop.1 _⟩
  let κ : ForcingName P := ⟨hartogsNumberName P R τ.val, hartogsNumberName_isName _ _ _⟩
  let φ : SetTheorySemisentence 3 :=
    (hartogsNumberFormula.subst (fun i ↦ .bvar ((![0, 1] : Fin 2 → Fin 3) i))).and
    ((IsOrdinal.dfn.subst (fun i ↦ .bvar ((![1] : Fin 1 → Fin 3) i))).and
      ((dependentChoiceAtFormula.subst (fun i ↦ .bvar ((![1] : Fin 1 → Fin 3) i))).and
        (nameMemberFormula.subst (fun i ↦ .bvar ((![2, 1] : Fin 2 → Fin 3) i)))))
  let ψ : SetTheorySemisentence 3 :=
    (dependentChoiceAtFormula.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 3) i))).and
      (nameMemberFormula.subst (fun i ↦ .bvar ((![2, 0] : Fin 2 → Fin 3) i)))
  have hm : p ∈ forcingFormula P R nameMemberFormula (standardTuple ![α.val, τ.val]) := by
    rw [forcingFormula_nameMember]
    exact (mem_atomicMembership_checkName_iff hR htop _ _ _).mpr ⟨hp, hI⟩
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![κ.val, τ.val, α.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_and, mem_inter_iff, forcingFormula_rename, forcingFormula_rename,
      forcingFormula_rename, forcingFormula_rename]
    exact ⟨hartogsNumberName_forces hR htop hp τ, forces_checked_ordinal hR htop inferInstance hp, hDC, hm⟩
  have hh := forcingFormula_entailment φ ψ (by
    intro W _ _ _ v hv
    change (hartogsNumberFormula.subst (fun i ↦ .bvar ((![0, 1] : Fin 2 → Fin 3) i))).Evalb v ∧
      (IsOrdinal.dfn.subst (fun i ↦ .bvar ((![1] : Fin 1 → Fin 3) i))).Evalb v ∧
      (dependentChoiceAtFormula.subst (fun i ↦ .bvar ((![1] : Fin 1 → Fin 3) i))).Evalb v ∧
      (nameMemberFormula.subst (fun i ↦ .bvar ((![2, 1] : Fin 2 → Fin 3) i))).Evalb v at hv
    have hs : v 0 = hartogsNumber (v 1) ∧ IsOrdinal (v 1) ∧
        InternalDependentChoiceAt (v 1) ∧ v 2 ∈ v 1 := by
      simpa [Semiformula.eval_substs, nameMemberFormula] using hv
    let := hs.2.1
    let := IsOrdinal.of_mem hs.2.2.2
    have hsub : v 2 ⊆ v 1 := IsOrdinal.toIsTransitive.transitive _ hs.2.2.2
    have hc : InternalDependentChoiceAt (v 2) := hs.2.2.1.downward hsub
    have hm : v 2 ∈ v 0 := by
      rw [hs.1]
      exact ordinal_cardLE_iff_mem_hartogsNumber.mp (cardLE_of_subset hsub)
    change (dependentChoiceAtFormula.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 3) i))).Evalb v ∧
      (nameMemberFormula.subst (fun i ↦ .bvar ((![2, 0] : Fin 2 → Fin 3) i))).Evalb v
    simpa [Semiformula.eval_substs, nameMemberFormula] using And.intro hc hm)
    hR htop hp ![κ, τ, α] hφ
  dsimp only [ψ] at hh
  rw [forcingFormula_and, mem_inter_iff, forcingFormula_rename, forcingFormula_rename] at hh
  exact hh

end ZFVP
