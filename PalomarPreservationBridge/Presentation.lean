import PalomarPreservationBridge.Dictionary
import ZFVP.ModelTheory.SymmetricModelZF
import ZFVP.SetTheory.VopenkaIsomorphism

namespace PalomarPreservationBridge
open PalomarBridge LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {M : Type u} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "mem" => (fun x y : M => x ∈ y)

/-- The two name domains differ only in their proved equivalent predicates. -/
def nameEquiv (d : SymmetricData mem) :
    {t : M // HereditarilySymmetric mem d.P d.group d.filter t} ≃ (toContext d).Name where
  toFun t := ⟨t.val, (hereditarilySymmetric_iff _ _ _ _).mp t.property⟩
  invFun t := ⟨t.val, (hereditarilySymmetric_iff _ _ _ _).mpr t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def evaluation (d : SymmetricData mem) :
    {t : M // HereditarilySymmetric mem d.P d.group d.filter t} → (toContext d).Model :=
  (toContext d).ofName ∘ nameEquiv d

theorem evaluation_surjective (d : SymmetricData mem) : Function.Surjective (evaluation d) :=
  (toContext d).ofName_surjective.comp (nameEquiv d).surjective

theorem evaluation_eq_iff (d : SymmetricData mem)
    (s t : {t : M // HereditarilySymmetric mem d.P d.group d.filter t}) :
    evaluation d s = evaluation d t ↔ ∃ p ∈ d.G, p ∈ equality mem d.P d.R s.val t.val := by
  simp only [equality_eq]
  exact ZFVP.ClassForcingQuotient.ofName_eq_iff _ _ _ _ _ _ _ (nameEquiv d s) (nameEquiv d t)

theorem evaluation_mem_iff (d : SymmetricData mem)
    (s t : {t : M // HereditarilySymmetric mem d.P d.group d.filter t}) :
    evaluation d s ∈ evaluation d t ↔ ∃ p ∈ d.G, p ∈ membership mem d.P d.R s.val t.val := by
  simp only [membership_eq]
  rfl

/-- The existing symmetric-model construction supplies the specified quotient. -/
theorem canonical_presentation (d : SymmetricData mem) :
    Presentation mem d (toContext d).Model (fun x y => x ∈ y) :=
  ⟨evaluation d, evaluation_surjective d, fun s t =>
    ⟨evaluation_eq_iff d s t, evaluation_mem_iff d s t⟩⟩

/-- Every presentation of the explicitly specified quotient is isomorphic to the
constructed symmetric model. Neither well-foundedness nor a valuation recursion
on the external ground is assumed. -/
theorem presentation_isomorphic (d : SymmetricData mem) {W : Type u}
    (wmem : W → W → Prop) (h : Presentation mem d W wmem) :
    ∃ e : (toContext d).Model ≃ W, ∀ x y, wmem (e x) (e y) ↔ x ∈ y := by
  classical
  obtain ⟨val, hsurj, hval⟩ := h
  let chooseName := Function.surjInv (evaluation_surjective d)
  have hchoose (x : (toContext d).Model) : evaluation d (chooseName x) = x :=
    Function.surjInv_eq (evaluation_surjective d) x
  let f : (toContext d).Model → W := fun x => val (chooseName x)
  have hmap (t : {t : M // HereditarilySymmetric mem d.P d.group d.filter t}) :
      f (evaluation d t) = val t := by
    exact (hval _ _).1.mpr ((evaluation_eq_iff d _ _).mp (hchoose (evaluation d t)))
  have hinj : Function.Injective f := by
    intro x y he
    have he' := (evaluation_eq_iff d _ _).mpr ((hval _ _).1.mp he)
    simpa only [hchoose] using he'
  have honto : Function.Surjective f := by
    intro x
    obtain ⟨t, rfl⟩ := hsurj x
    exact ⟨evaluation d t, hmap t⟩
  refine ⟨Equiv.ofBijective f ⟨hinj, honto⟩, ?_⟩
  intro x y
  obtain ⟨s, rfl⟩ := evaluation_surjective d x
  obtain ⟨t, rfl⟩ := evaluation_surjective d y
  change wmem (f (evaluation d s)) (f (evaluation d t)) ↔ _
  rw [hmap, hmap]
  exact (hval s t).2.trans (evaluation_mem_iff d s t).symm

end PalomarPreservationBridge
