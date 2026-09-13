import ZFVP.ModelTheory.ForcingEntailment
import ZFVP.SetTheory.ForcingRenaming

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

set_option maxHeartbeats 1000000

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def nameMemberFormula : SetTheorySemisentence 2 := “x Q. x ∈ Q”

theorem forcingFormula_nameMember (P R σ τ : V) :
    forcingFormula P R nameMemberFormula (standardTuple ![σ, τ]) = atomicMembership P R σ τ := by
  change atomicMembership P R ((standardTuple ![σ, τ]) ‘ (0 : V))
    ((standardTuple ![σ, τ]) ‘ (1 : V)) = _
  have h0 := value_standardTuple ![σ, τ] (0 : Fin 2)
  have h1 := value_standardTuple ![σ, τ] (1 : Fin 2)
  exact congrArg₂ (atomicMembership P R) h0 h1

theorem forcedPreorder_refl {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (Q S x : ForcingName P)
    (hpre : p ∈ forcingFormula P R forcingPreorderFormula (standardTuple ![Q.val, S.val]))
    (hx : p ∈ atomicMembership P R x.val Q.val) :
    p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val, x.val, x.val]) := by
  let φ : SetTheorySemisentence 3 :=
    (forcingPreorderFormula.subst (fun i ↦ .bvar ((![0, 1] : Fin 2 → Fin 3) i))).and
      (nameMemberFormula.subst (fun i ↦ .bvar ((![2, 0] : Fin 2 → Fin 3) i)))
  let ψ : SetTheorySemisentence 3 := boundedPairMemberFormula.subst (fun i ↦ .bvar ((![1, 2, 2] : Fin 3 → Fin 3) i))
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![Q.val, S.val, x.val]) := by
    rw [show φ = (forcingPreorderFormula.subst (fun i ↦ .bvar ((![0, 1] : Fin 2 → Fin 3) i))).and
      (nameMemberFormula.subst (fun i ↦ .bvar ((![2, 0] : Fin 2 → Fin 3) i))) from rfl,
      forcingFormula_and, mem_inter_iff, forcingFormula_rename, forcingFormula_rename]
    constructor
    · exact hpre
    · change p ∈ forcingFormula P R nameMemberFormula (standardTuple ![x.val, Q.val])
      rwa [forcingFormula_nameMember]
  have hψ := forcingFormula_entailment φ ψ (by
    intro W _ _ _ v hv
    change ((forcingPreorderFormula.subst (fun i ↦ .bvar ((![0, 1] : Fin 2 → Fin 3) i))).Evalb v ∧
      (nameMemberFormula.subst (fun i ↦ .bvar ((![2, 0] : Fin 2 → Fin 3) i))).Evalb v) at hv
    have hpre : IsForcingPreorder (v 0) (v 1) := by simpa [Semiformula.eval_substs] using hv.1
    have hx : v 2 ∈ v 0 := by simpa [Semiformula.eval_substs, nameMemberFormula] using hv.2
    simpa [ψ, Semiformula.eval_substs] using hpre.2.1 (v 2) hx)
    hR htop hp ![Q, S, x] hφ
  change p ∈ forcingFormula P R ψ (standardTuple ![Q.val, S.val, x.val]) at hψ
  rw [show ψ = boundedPairMemberFormula.subst (fun i ↦ .bvar ((![1, 2, 2] : Fin 3 → Fin 3) i)) from rfl,
    forcingFormula_rename] at hψ
  exact hψ

theorem forcedPreorder_trans {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (Q S x y z : ForcingName P)
    (hpre : p ∈ forcingFormula P R forcingPreorderFormula (standardTuple ![Q.val, S.val]))
    (hxy : p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val, x.val, y.val]))
    (hyz : p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val, y.val, z.val])) :
    p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val, x.val, z.val]) := by
  let φ : SetTheorySemisentence 5 :=
    (forcingPreorderFormula.subst (fun i ↦ .bvar ((![0, 1] : Fin 2 → Fin 5) i))).and
      ((boundedPairMemberFormula.subst (fun i ↦ .bvar ((![1, 2, 3] : Fin 3 → Fin 5) i))).and
        (boundedPairMemberFormula.subst (fun i ↦ .bvar ((![1, 3, 4] : Fin 3 → Fin 5) i))))
  let ψ : SetTheorySemisentence 5 :=
    boundedPairMemberFormula.subst (fun i ↦ .bvar ((![1, 2, 4] : Fin 3 → Fin 5) i))
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![Q.val, S.val, x.val, y.val, z.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_rename, forcingFormula_rename, forcingFormula_rename]
    exact ⟨hpre, hxy, hyz⟩
  have hψ := forcingFormula_entailment φ ψ (by
    intro W _ _ _ v hv
    change (_ ∧ _ ∧ _) at hv
    have hp := hv.1
    have hxy' := hv.2.1
    have hyz' := hv.2.2
    change (forcingPreorderFormula.subst (fun i ↦ .bvar ((![0, 1] : Fin 2 → Fin 5) i))).Evalb v at hp
    change (boundedPairMemberFormula.subst (fun i ↦ .bvar ((![1, 2, 3] : Fin 3 → Fin 5) i))).Evalb v at hxy'
    change (boundedPairMemberFormula.subst (fun i ↦ .bvar ((![1, 3, 4] : Fin 3 → Fin 5) i))).Evalb v at hyz'
    have hpre : IsForcingPreorder (v 0) (v 1) := by simpa [Semiformula.eval_substs] using hp
    have hxy : ⟨v 2, v 3⟩ₖ ∈ v 1 := by simpa [Semiformula.eval_substs] using hxy'
    have hyz : ⟨v 3, v 4⟩ₖ ∈ v 1 := by simpa [Semiformula.eval_substs] using hyz'
    have hxyQ := kpair_mem_iff.mp (hpre.1 _ hxy)
    have hyzQ := kpair_mem_iff.mp (hpre.1 _ hyz)
    simpa [ψ, Semiformula.eval_substs] using
      hpre.2.2 (v 2) hxyQ.1 (v 3) hxyQ.2 (v 4) hyzQ.2 hxy hyz)
    hR htop hp ![Q, S, x, y, z] hφ
  change p ∈ forcingFormula P R ψ (standardTuple ![Q.val, S.val, x.val, y.val, z.val]) at hψ
  dsimp only [ψ] at hψ
  rw [forcingFormula_rename] at hψ
  exact hψ

theorem forcedTop_mem {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (Q S t : ForcingName P)
    (ht : p ∈ forcingFormula P R forcingTopFormula (standardTuple ![Q.val, S.val, t.val])) :
    p ∈ atomicMembership P R t.val Q.val := by
  let ψ : SetTheorySemisentence 3 := nameMemberFormula.subst (fun i ↦ .bvar ((![2, 0] : Fin 2 → Fin 3) i))
  have hψ := forcingFormula_entailment forcingTopFormula ψ (by
    intro W _ _ _ v hv
    have ht : IsForcingTop (v 0) (v 1) (v 2) := (Defined.eval_iff _).mp hv
    simpa [ψ, nameMemberFormula, Semiformula.eval_substs] using ht.1)
    hR htop hp ![Q, S, t] ht
  change p ∈ forcingFormula P R ψ (standardTuple ![Q.val, S.val, t.val]) at hψ
  dsimp only [ψ] at hψ
  rw [forcingFormula_rename] at hψ
  change p ∈ forcingFormula P R nameMemberFormula (standardTuple ![t.val, Q.val]) at hψ
  rwa [forcingFormula_nameMember] at hψ

theorem forcedTop_above {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (Q S t x : ForcingName P)
    (ht : p ∈ forcingFormula P R forcingTopFormula (standardTuple ![Q.val, S.val, t.val]))
    (hx : p ∈ atomicMembership P R x.val Q.val) :
    p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val, x.val, t.val]) := by
  let φ : SetTheorySemisentence 4 :=
    (forcingTopFormula.subst (fun i ↦ .bvar ((![0, 1, 2] : Fin 3 → Fin 4) i))).and
      (nameMemberFormula.subst (fun i ↦ .bvar ((![3, 0] : Fin 2 → Fin 4) i)))
  let ψ : SetTheorySemisentence 4 :=
    boundedPairMemberFormula.subst (fun i ↦ .bvar ((![1, 3, 2] : Fin 3 → Fin 4) i))
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![Q.val, S.val, t.val, x.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_rename, forcingFormula_rename]
    refine ⟨ht, ?_⟩
    change p ∈ forcingFormula P R nameMemberFormula (standardTuple ![x.val, Q.val])
    rwa [forcingFormula_nameMember]
  have hψ := forcingFormula_entailment φ ψ (by
    intro W _ _ _ v hv
    change (_ ∧ _) at hv
    have ht' := hv.1
    have hx' := hv.2
    change (forcingTopFormula.subst (fun i ↦ .bvar ((![0, 1, 2] : Fin 3 → Fin 4) i))).Evalb v at ht'
    change (nameMemberFormula.subst (fun i ↦ .bvar ((![3, 0] : Fin 2 → Fin 4) i))).Evalb v at hx'
    have ht : IsForcingTop (v 0) (v 1) (v 2) := by simpa [Semiformula.eval_substs] using ht'
    have hx : v 3 ∈ v 0 := by simpa [Semiformula.eval_substs, nameMemberFormula] using hx'
    simpa [ψ, Semiformula.eval_substs] using ht.2 (v 3) hx)
    hR htop hp ![Q, S, t, x] hφ
  change p ∈ forcingFormula P R ψ (standardTuple ![Q.val, S.val, t.val, x.val]) at hψ
  dsimp only [ψ] at hψ
  rw [forcingFormula_rename] at hψ
  exact hψ

end ZFVP
