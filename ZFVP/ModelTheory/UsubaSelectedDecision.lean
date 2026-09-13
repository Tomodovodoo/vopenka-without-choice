import ZFVP.ModelTheory.UsubaBoundCoordinates
import ZFVP.ModelTheory.WoodinSelectedThreadDecision

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

def IsUsubaSelectedDecision (θ i f c d : V) : Prop :=
  ∀ (A : ForcingContext V),
    A.P = (T).P i →
    A.R = (T).R i →
    A.one = (T).top i → d ∈ A.G →
    ∀ g : ForcingName A.P, g.val = f →
      ∃ X a : A.Model, A.ofName g ∈ A.check ((T).P θ) ^ X ∧
        a ∈ X ∧ (A.ofName g) ‘ a = A.check c

theorem ForcingContext.usubaCoordinate_function {θ i j : V} [IsOrdinal θ] [IsOrdinal j]
    (A : ForcingContext V) (hjθ : j ⊆ θ)
    (hP : A.P = (T).P i) (hR : A.R = (T).R i) (ho : A.one = (T).top i)
    (f : ForcingName A.P) {X : A.Model}
    (hf : A.ofName f ∈ A.check ((T).P θ) ^ X) :
    A.ofName ⟨usubaBoundCoordinateName θ i f.val j,
      by simpa only [← hP] using usubaBoundCoordinateName_isName θ i f.val j⟩ ∈
      A.check ((T).P j) ^ X := by
  have hρ := (T).projection_function j θ inferInstance inferInstance hjθ
  have hv := A.forcingCompositionName_value f
    ⟨checkName A.one ((T).projection j θ), checkName_isName A.top.1 _⟩
  change A.ofName ⟨forcingCompositionName A.P A.R f.val
    (checkName A.one ((T).projection j θ)), _⟩ =
      compose (A.ofName f) (A.check ((T).projection j θ)) at hv
  simpa only [usubaBoundCoordinateName, ← hP, ← hR, ← ho, hv] using
    compose_function hf ((A.check_function_iff _ _ _).mpr hρ)

theorem ForcingContext.usubaCoordinate_selected {θ i f c d j : V} [IsOrdinal θ] [IsOrdinal j]
    (A : ForcingContext V) (hjθ : j ⊆ θ)
    (hP : A.P = (T).P i) (hR : A.R = (T).R i) (ho : A.one = (T).top i)
    (hc : c ∈ (T).P θ) (hselected : IsUsubaSelectedDecision θ i f c d) (hdG : d ∈ A.G)
    (g : ForcingName A.P) (hg : g.val = f) :
    let μ : ForcingName A.P := ⟨usubaBoundCoordinateName θ i g.val j,
      by simpa only [← hP] using usubaBoundCoordinateName_isName θ i g.val j⟩
    ∃ X a : A.Model, A.ofName μ ∈ A.check ((T).P j) ^ X ∧
      a ∈ X ∧ (A.ofName μ) ‘ a = A.check (((T).projection j θ) ‘ c) := by
  obtain ⟨X, a, hf, ha, hac⟩ := hselected A hP hR ho hdG g hg
  refine ⟨X, a, A.usubaCoordinate_function hjθ hP hR ho g hf, ha, ?_⟩
  have hρ := (T).projection_function j θ inferInstance inferInstance hjθ
  let := IsFunction.of_mem hρ
  have hv := A.forcingCompositionName_value g
    ⟨checkName A.one ((T).projection j θ), checkName_isName A.top.1 _⟩
  change A.ofName ⟨forcingCompositionName A.P A.R g.val
    (checkName A.one ((T).projection j θ)), _⟩ =
      compose (A.ofName g) (A.check ((T).projection j θ)) at hv
  simp only [usubaBoundCoordinateName, ← hP, ← hR, ← ho, hv]
  rw [value_compose_of_mem_function hf ((A.check_function_iff _ _ _).mpr hρ) ha, hac,
    A.check_value ((domain_eq_of_mem_function hρ).symm ▸ hc)]

theorem usubaSelectedDecision_of_forced {θ i f c d : V}
    (hf : d ∈ forcingFormula ((T).P i)
      ((T).R i) selectedFunctionRangeFormula
      (standardTuple ![checkName ((T).top i)
        ((T).P θ), f,
        checkName ((T).top i) c])) :
    IsUsubaSelectedDecision θ i f c d := by
  intro A hP hR ho hdG g hg
  have hforce := hf
  rw [← hP, ← hR, ← ho, ← hg] at hforce
  exact (Defined.eval_iff _).mp ((A.formula_truth selectedFunctionRangeFormula
    ![⟨checkName A.one ((T).P θ), checkName_isName A.top.1 _⟩,
      g, ⟨checkName A.one c, checkName_isName A.top.1 _⟩]).mpr ⟨d, hdG, hforce⟩)

theorem ForcingContext.exists_usubaSelectedDecision_below {θ i c e : V}
    (A : ForcingContext V)
    (hP : A.P = (T).P i)
    (hR : A.R = (T).R i)
    (ho : A.one = (T).top i)
    (f : ForcingName A.P) {X a : A.Model}
    (hf : A.ofName f ∈ A.check ((T).P θ) ^ X)
    (ha : a ∈ X) (hac : (A.ofName f) ‘ a = A.check c) (he : e ∈ A.G) :
    ∃ d ∈ A.G, ⟨d, e⟩ₖ ∈ A.R ∧ IsUsubaSelectedDecision θ i f.val c d := by
  have htruth : selectedFunctionRangeFormula.Evalb
      (fun k ↦ A.ofName ((![⟨checkName A.one ((T).P θ),
        checkName_isName A.top.1 _⟩, f, ⟨checkName A.one c, checkName_isName A.top.1 _⟩] :
          Fin 3 → ForcingName A.P) k)) :=
    (Defined.eval_iff _).mpr ⟨X, a, hf, ha, hac⟩
  obtain ⟨q, hqG, hq⟩ := (A.formula_truth selectedFunctionRangeFormula _).mp htruth
  obtain ⟨d, hdG, hdq, hde⟩ := A.generic.1.2.2.2 q hqG e he
  refine ⟨d, hdG, hde, usubaSelectedDecision_of_forced ?_⟩
  have hd := (forcingFormula_regular A.order selectedFunctionRangeFormula _).2.1
    q hq d (A.generic.1.1 d hdG) hdq
  change d ∈ forcingFormula A.P A.R selectedFunctionRangeFormula
    (standardTuple ![checkName A.one ((T).P θ), f.val,
      checkName A.one c]) at hd
  simpa only [hP, hR, ho] using hd

end ZFVP
