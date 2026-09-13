import ZFVP.ModelTheory.SymmetricModel
import ZFVP.SetTheory.SymmetricImageName
import ZFVP.SetTheory.SymmetricImageWitnesses

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricContext

theorem definableImage (S : SymmetricContext V) (τ : S.Name) (H : V) (hH : H ∈ S.F)
    (hfix : ∀ π ∈ H, nameAction π τ.val = τ.val)
    (A : V → V → V) (hA : ℒₛₑₜ-function₂ A)
    (he : ∀ π ∈ H, ∀ σ ν, IsHereditarilySymmetricName S.P S.Γ S.F σ →
      IsHereditarilySymmetricName S.P S.Γ S.F ν → ∀ p ∈ S.P,
        π ‘ p ∈ A (nameAction π σ) (nameAction π ν) ↔ p ∈ A σ ν)
    (hd : ∀ σ ν, IsForcingDownwardClosed S.P S.R (A σ ν))
    (Q : S.Model → S.Model → Prop)
    (htruth : ∀ σ ν : S.Name, GenericMeets S.G (A σ.val ν.val) ↔ Q (S.ofName σ) (S.ofName ν))
    (huniq : ∀ a, a ∈ S.ofName τ → ∀ b c, Q a b → Q a c → b = c) :
    ∃ b : S.Model, ∀ x, x ∈ b ↔ ∃ a, a ∈ S.ofName τ ∧ Q a x := by
  obtain ⟨B, hB, hstable, hbound⟩ := symmetricImageWitnessBound S.group S.normal hH τ.val A hA
  have hn := hereditarilySymmetric_forcingImageName S.group S.normal hH τ.property hfix hB hstable A hA he
  let ζ : S.Name := ⟨forcingImageName S.P S.R τ.val B A hA, hn⟩
  refine ⟨S.ofName ζ, ?_⟩
  intro x
  obtain ⟨ξ, rfl⟩ := S.ofName_surjective x
  constructor
  · intro hx
    obtain ⟨ν, p, hpG, hp, heν⟩ := (S.mem_ofName_iff ζ _).mp hx
    obtain ⟨_, _, _, σ, s, hσs, hps, hpA⟩ := (mem_forcingImageName_iff S.P S.R τ.val B A hA _ _).mp hp
    let σ' : S.Name := ⟨σ, (hereditarilySymmetric_iff _ _ _ _).mp τ.property |>.2 σ s hσs⟩
    have hsG := S.generic.1.2.2.1 p hpG s (forcingOrder_right_mem S.order hps) hps
    refine ⟨S.ofName σ', (S.mem_ofName_iff τ _).mpr ⟨σ', s, hsG, hσs, rfl⟩, ?_⟩
    rw [heν]
    exact (htruth σ' ν).mp ⟨p, hpG, hpA⟩
  · rintro ⟨a, ha, hQ⟩
    obtain ⟨σ, s, hsG, hσs, heσ⟩ := (S.mem_ofName_iff τ a).mp ha
    rw [heσ] at hQ ha
    obtain ⟨p, hpG, hpA⟩ := (htruth σ ξ).mpr hQ
    obtain ⟨q, hqG, hqs, hqp⟩ := S.generic.1.2.2.2 s hsG p hpG
    have hqA := hd σ.val ξ.val p hpA q (S.generic.1.1 q hqG) hqp
    obtain ⟨ν, hνB, hνA⟩ := hbound σ.val (mem_domain_of_kpair_mem hσs) q (S.generic.1.1 q hqG)
      ⟨ξ.val, ξ.property, hqA⟩
    let ν' : S.Name := ⟨ν, hB ν hνB⟩
    have heν : S.ofName ξ = S.ofName ν' := huniq _ ha _ _ hQ ((htruth σ ν').mp ⟨q, hqG, hνA⟩)
    exact (S.mem_ofName_iff ζ _).mpr
      ⟨ν', q, hqG, (mem_forcingImageName_iff S.P S.R τ.val B A hA _ _).mpr
        ⟨hνB, S.generic.1.1 q hqG, (hB ν hνB).1, σ.val, s, hσs, hqs, hνA⟩, heν⟩

end SymmetricContext
end ZFVP
