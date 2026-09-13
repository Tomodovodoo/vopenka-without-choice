import ZFVP.ModelTheory.SymmetricModelZF
import ZFVP.SetTheory.NameMapGraph

/-! Interpret a symmetric graph name as a graph inside the symmetric model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricContext

theorem of_pair (S : SymmetricContext V) (σ τ : S.Name) :
    S.ofName (S.pairName σ τ) = {S.ofName σ, S.ofName τ} := by
  apply SetTheory.mem_ext_iff.mpr
  intro x
  simpa only [mem_insert, mem_singleton_iff] using S.mem_pairName_iff σ τ x

theorem of_orderedPairName (S : SymmetricContext V) (σ τ : S.Name) :
    S.ofName ⟨orderedPairName S.one σ.val τ.val,
      hereditarilySymmetric_orderedPairName S.poset S.group S.normal S.top σ.property τ.property⟩ =
        ⟨S.ofName σ, S.ofName τ⟩ₖ := by
  change S.ofName (S.pairName (S.pairName σ σ) (S.pairName σ τ)) = _
  rw [S.of_pair, S.of_pair, S.of_pair]
  simp [kpair]

noncomputable def mapGraph (S : SymmetricContext V) (D f : V)
    (hs : IsHereditarilySymmetricName S.P S.Γ S.F (nameMapGraph S.one D f)) : S.Model :=
  S.ofName ⟨nameMapGraph S.one D f, hs⟩

theorem mem_mapGraph_iff (S : SymmetricContext V) (D f : V)
    (hs : IsHereditarilySymmetricName S.P S.Γ S.F (nameMapGraph S.one D f))
    (hD : ∀ σ ∈ D, IsHereditarilySymmetricName S.P S.Γ S.F σ)
    (hf : ∀ σ ∈ D, IsHereditarilySymmetricName S.P S.Γ S.F (f ‘ σ)) (z : S.Model) :
    z ∈ S.mapGraph D f hs ↔ ∃ σ, ∃ hσ : σ ∈ D,
      z = ⟨S.ofName ⟨σ, hD σ hσ⟩, S.ofName ⟨f ‘ σ, hf σ hσ⟩⟩ₖ := by
  change z ∈ S.ofName ⟨nameMapGraph S.one D f, hs⟩ ↔ _
  rw [S.mem_ofName_iff]
  constructor
  · rintro ⟨ν, p, _, hp, he⟩
    obtain ⟨σ, hσ, hpair⟩ := (mem_nameMapGraph_iff _ _ _ _).mp hp
    let σ' : S.Name := ⟨σ, hD σ hσ⟩
    let τ' : S.Name := ⟨f ‘ σ, hf σ hσ⟩
    have hν : ν = (⟨orderedPairName S.one σ'.val τ'.val,
        hereditarilySymmetric_orderedPairName S.poset S.group S.normal S.top σ'.property τ'.property⟩ : S.Name) :=
      Subtype.ext (kpair_iff.mp hpair).1
    exact ⟨σ, hσ, he.trans ((congrArg S.ofName hν).trans (S.of_orderedPairName σ' τ'))⟩
  · rintro ⟨σ, hσ, he⟩
    let σ' : S.Name := ⟨σ, hD σ hσ⟩
    let τ' : S.Name := ⟨f ‘ σ, hf σ hσ⟩
    let ν : S.Name := ⟨orderedPairName S.one σ'.val τ'.val,
      hereditarilySymmetric_orderedPairName S.poset S.group S.normal S.top σ'.property τ'.property⟩
    exact ⟨ν, S.one, externalForcingFilter_top S.generic.1 S.top,
      (mem_nameMapGraph_iff _ _ _ _).mpr ⟨σ, hσ, rfl⟩, he.trans (S.of_orderedPairName σ' τ').symm⟩

theorem mapGraph_isFunction (S : SymmetricContext V) (D f : V)
    (hs : IsHereditarilySymmetricName S.P S.Γ S.F (nameMapGraph S.one D f))
    (hD : ∀ σ ∈ D, IsHereditarilySymmetricName S.P S.Γ S.F σ)
    (hf : ∀ σ ∈ D, IsHereditarilySymmetricName S.P S.Γ S.F (f ‘ σ))
    (huniq : ∀ σ (hσ : σ ∈ D) τ (hτ : τ ∈ D),
      S.ofName ⟨σ, hD σ hσ⟩ = S.ofName ⟨τ, hD τ hτ⟩ →
        S.ofName ⟨f ‘ σ, hf σ hσ⟩ = S.ofName ⟨f ‘ τ, hf τ hτ⟩) :
    IsFunction (S.mapGraph D f hs) := by
  apply isFunction_iff.mpr
  apply mem_function.intro
  · intro z hz
    obtain ⟨σ, hσ, rfl⟩ := (S.mem_mapGraph_iff D f hs hD hf z).mp hz
    exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hz, mem_range_of_kpair_mem hz⟩
  · intro x hx
    obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
    refine ⟨y, hy, ?_⟩
    intro z hz
    obtain ⟨σ, hσ, heσ⟩ := (S.mem_mapGraph_iff D f hs hD hf _).mp hy
    obtain ⟨τ, hτ, heτ⟩ := (S.mem_mapGraph_iff D f hs hD hf _).mp hz
    obtain ⟨hxσ, rfl⟩ := kpair_iff.mp heσ
    obtain ⟨hxτ, rfl⟩ := kpair_iff.mp heτ
    exact (huniq σ hσ τ hτ (hxσ.symm.trans hxτ)).symm

theorem mem_domain_mapGraph_iff (S : SymmetricContext V) (D f : V)
    (hs : IsHereditarilySymmetricName S.P S.Γ S.F (nameMapGraph S.one D f))
    (hD : ∀ σ ∈ D, IsHereditarilySymmetricName S.P S.Γ S.F σ)
    (hf : ∀ σ ∈ D, IsHereditarilySymmetricName S.P S.Γ S.F (f ‘ σ)) (x : S.Model) :
    x ∈ domain (S.mapGraph D f hs) ↔ ∃ σ, ∃ hσ : σ ∈ D, x = S.ofName ⟨σ, hD σ hσ⟩ := by
  rw [mem_domain_iff]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨σ, hσ, he⟩ := (S.mem_mapGraph_iff D f hs hD hf _).mp hy
    exact ⟨σ, hσ, (kpair_iff.mp he).1⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨S.ofName ⟨f ‘ σ, hf σ hσ⟩, (S.mem_mapGraph_iff D f hs hD hf _).mpr ⟨σ, hσ, rfl⟩⟩

theorem mapGraph_value (S : SymmetricContext V) (D f : V)
    (hs : IsHereditarilySymmetricName S.P S.Γ S.F (nameMapGraph S.one D f))
    (hD : ∀ σ ∈ D, IsHereditarilySymmetricName S.P S.Γ S.F σ)
    (hf : ∀ σ ∈ D, IsHereditarilySymmetricName S.P S.Γ S.F (f ‘ σ))
    [IsFunction (S.mapGraph D f hs)] {σ : V} (hσ : σ ∈ D) :
    (S.mapGraph D f hs) ‘ (S.ofName ⟨σ, hD σ hσ⟩) = S.ofName ⟨f ‘ σ, hf σ hσ⟩ :=
  value_eq_of_kpair_mem ((S.mem_mapGraph_iff D f hs hD hf _).mpr ⟨σ, hσ, rfl⟩)

end SymmetricContext
end ZFVP
