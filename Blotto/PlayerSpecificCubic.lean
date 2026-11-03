import Blotto.PlayerSpecificEquilibrium

/-! The four interval sums and literal cubic of the player-specific parameter
search. Equality breakpoints may be assigned to either side: the identities
hold for both choices, so grouping coincident ratios loses no candidate. -/
namespace Blotto.PlayerSpecificCubic
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure Coefficients (𝕂 : Type*) where
  A1 : 𝕂
  A2 : 𝕂
  B1 : 𝕂
  B2 : 𝕂

def coefficients {𝕂 : Type*} [Field 𝕂] {n : ℕ} (v w : Fin n → 𝕂) (high : Fin n → Bool) : Coefficients 𝕂 where
  A1 := ∑ j,if high j then w j else 0
  A2 := ∑ j,if high j then 0 else (v j)^2/w j
  B1 := ∑ j,if high j then (w j)^2/v j else 0
  B2 := ∑ j,if high j then 0 else v j

def cubic {𝕂 : Type*} [Field 𝕂] (c : Coefficients 𝕂) (b gamma : 𝕂) : 𝕂 :=
  c.B1*gamma^3-b*c.A1*gamma^2+c.B2*gamma-b*c.A2

def candidateScale {𝕂 : Type*} [Field 𝕂] (c : Coefficients 𝕂) (b gamma : 𝕂) : 𝕂 :=
  (gamma^2*c.B1+c.B2)/(2*b)

def Respects {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂] {n : ℕ}
    (v w : Fin n → 𝕂) (high : Fin n → Bool) (gamma : 𝕂) : Prop :=
  ∀ j,if high j then gamma*w j≤v j else v j≤gamma*w j

variable {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂] [IsStrictOrderedRing 𝕂]

theorem columnA (v w gamma scale : 𝕂) (high : Bool) (hv : 0<v) (hw : 0<w)
    (hg : 0<gamma) (hs : 0<scale) (h : if high then gamma*w≤v else v≤gamma*w) :
    PlayerSpecificMarginals.probA v w gamma*PlayerSpecificMarginals.length v w gamma scale=
      (gamma*(if high then w else 0)+(if high then 0 else v^2/w)/gamma)/scale := by
  cases high with
  | false =>
    obtain ⟨hl,hp,_⟩ := PlayerSpecificMarginals.low_formulas hv hw hg h scale
    rw [hl,hp]
    simp only [Bool.false_eq_true,ite_false,mul_zero,zero_add]
    field_simp [hg.ne',hw.ne',hs.ne']
  | true =>
    obtain ⟨hl,hp,_⟩ := PlayerSpecificMarginals.high_formulas hv hw hg h scale
    rw [hl,hp]
    simp only [ite_true,one_mul,zero_div,add_zero]

theorem columnB (v w gamma scale : 𝕂) (high : Bool) (hv : 0<v) (hw : 0<w)
    (hg : 0<gamma) (hs : 0<scale) (h : if high then gamma*w≤v else v≤gamma*w) :
    PlayerSpecificMarginals.probB v w gamma*PlayerSpecificMarginals.length v w gamma scale=
      (gamma^2*(if high then w^2/v else 0)+(if high then 0 else v))/scale := by
  cases high with
  | false =>
    obtain ⟨hl,_,hp⟩ := PlayerSpecificMarginals.low_formulas hv hw hg h scale
    rw [hl,hp]
    simp only [Bool.false_eq_true,ite_false,mul_zero,zero_add,one_mul]
  | true =>
    obtain ⟨hl,_,hp⟩ := PlayerSpecificMarginals.high_formulas hv hw hg h scale
    rw [hl,hp]
    simp only [ite_true,add_zero]
    field_simp [hv.ne',hs.ne']

theorem sumA {n : ℕ} (v w : Fin n → 𝕂) (high : Fin n → Bool) (gamma scale : 𝕂)
    (hv : ∀ j,0<v j) (hw : ∀ j,0<w j) (hg : 0<gamma) (hs : 0<scale)
    (h : Respects v w high gamma) :
    (∑ j,PlayerSpecificMarginals.probA (v j) (w j) gamma*PlayerSpecificMarginals.length (v j) (w j) gamma scale)=
      (gamma*(coefficients v w high).A1+(coefficients v w high).A2/gamma)/scale := by
  calc
    _ = ∑ j,(gamma*(if high j then w j else 0)+(if high j then 0 else (v j)^2/w j)/gamma)/scale :=
      Finset.sum_congr rfl (fun j _ => columnA _ _ _ _ _ (hv j) (hw j) hg hs (h j))
    _ = _ := by
      rw [← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_div]
      rfl

theorem sumB {n : ℕ} (v w : Fin n → 𝕂) (high : Fin n → Bool) (gamma scale : 𝕂)
    (hv : ∀ j,0<v j) (hw : ∀ j,0<w j) (hg : 0<gamma) (hs : 0<scale)
    (h : Respects v w high gamma) :
    (∑ j,PlayerSpecificMarginals.probB (v j) (w j) gamma*PlayerSpecificMarginals.length (v j) (w j) gamma scale)=
      (gamma^2*(coefficients v w high).B1+(coefficients v w high).B2)/scale := by
  calc
    _ = ∑ j,(gamma^2*(if high j then (w j)^2/v j else 0)+(if high j then 0 else v j))/scale :=
      Finset.sum_congr rfl (fun j _ => columnB _ _ _ _ _ (hv j) (hw j) hg hs (h j))
    _ = _ := by
      rw [← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum]
      rfl

theorem mean_equations {n : ℕ} (v w : Fin n → 𝕂) (high : Fin n → Bool) (b gamma scale : 𝕂)
    (hv : ∀ j,0<v j) (hw : ∀ j,0<w j) (hg : 0<gamma) (hs : 0<scale)
    (h : Respects v w high gamma) :
    ((∑ j,PlayerSpecificMarginals.probA (v j) (w j) gamma*PlayerSpecificMarginals.length (v j) (w j) gamma scale)=2 ∧
      (∑ j,PlayerSpecificMarginals.probB (v j) (w j) gamma*PlayerSpecificMarginals.length (v j) (w j) gamma scale)=2*b) ↔
      (2*scale=gamma*(coefficients v w high).A1+(coefficients v w high).A2/gamma ∧
        2*b*scale=gamma^2*(coefficients v w high).B1+(coefficients v w high).B2) := by
  rw [sumA v w high gamma scale hv hw hg hs h,sumB v w high gamma scale hv hw hg hs h]
  constructor
  · rintro ⟨hA,hB⟩
    exact ⟨((div_eq_iff hs.ne').mp hA).symm,((div_eq_iff hs.ne').mp hB).symm⟩
  · rintro ⟨hA,hB⟩
    exact ⟨(div_eq_iff hs.ne').mpr hA.symm,(div_eq_iff hs.ne').mpr hB.symm⟩

end Blotto.PlayerSpecificCubic
