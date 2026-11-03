import Blotto.GeneralPaperSelectionStorage

/-! The constant-size selection phase: original input, prepared cell points,
optional root/value, casts, arithmetic temporaries and returned branch. All
primitive scratch is bounded by the actual complete selection price. -/
namespace Blotto.GeneralPaperSelectionConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperSelectionStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def rootValue (r : Option Farey.Fraction) : ℕ := match r with
  | none => 0
  | some f => rationalWordWidth f.value

theorem root_value (Q B : ℕ) (r : Option Farey.Fraction)
    (hr : ∀ f,r=some f → f.num≤2*Q ∧ f.den≤2*Q) :
    rootValue r≤GeneralPaperSelectionPoints.width Q B := by
  cases he : r with
  | none => exact Nat.zero_le _
  | some f =>
    have hf := hr f he
    exact (GeneralPaperSelectionPoints.root_words Q B f hf.1 hf.2).2.2

def casts (W Q j : ℕ) : ℕ :=
  fields W [j,Q,j+1,2*j,2*j+1,2*Q]+
    rationalWordWidth (j:ℚ)+rationalWordWidth (Q:ℚ)+rationalWordWidth ((j+1:ℕ):ℚ)+
      rationalWordWidth ((2*j+1:ℕ):ℚ)+rationalWordWidth ((2*Q:ℕ):ℚ)

theorem casts_bound (W Q j B : ℕ) (hQ : 0<Q) (hj : j<Q) :
    casts W Q j≤11*GeneralPaperSelectionPoints.width Q B+38*W := by
  have hn := GeneralPaperSelectionPoints.natural_words Q j B hQ hj
  have rat (x : ℕ) (hx : x≤2*Q) : rationalWordWidth (x:ℚ)≤GeneralPaperSelectionPoints.width Q B := by
    have h := rationalWordWidth_of_height (GeneralPaperSelectionPoints.cast_height Q x hx)
    unfold GeneralPaperSelectionPoints.width
    omega
  have h0 := rat j (by omega)
  have h1 := rat Q (by omega)
  have h2 := rat (j+1) (by omega)
  have h3 := rat (2*j+1) (by omega)
  have h4 := rat (2*Q) (by omega)
  have hF := fields_bound W (GeneralPaperSelectionPoints.width Q B) [j,Q,j+1,2*j,2*j+1,2*Q] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hn.2.2.1
    · exact hn.2.2.2.1
    · exact hn.2.2.2.2.1
    · exact hn.2.2.2.2.2.1
    · exact hn.2.2.2.2.2.2.1
    · exact hn.2.2.2.2.2.2.2)
  change _≤6*(GeneralPaperSelectionPoints.width Q B+W)+32*W at hF
  unfold casts
  omega

def window (model : RationalCostModel) (W Q j : ℕ) (hQ : 0<Q) (b : ℚ) (r : Option Farey.Fraction) : ℕ :=
  rationalWordWidth b+points W (GeneralPaperSelectionPointsPrice.run model W Q j).1+
    root W r+rootValue r+casts W Q j+
    selected W (GeneralPaperSelectionBits.run model W Q j hQ b r).1+
      (GeneralPaperSelectionBits.run model W Q j hQ b r).2+256*W

def profile (model : RationalCostModel) (W Q B : ℕ) : ℕ :=
  25*GeneralPaperSelectionPoints.width Q B+625*W+
    512*(W+model.rat (GeneralPaperSelectionPoints.width Q B))

theorem bounded (model : RationalCostModel) (W Q j B : ℕ) (hQ : 0<Q) (b : ℚ) (r : Option Farey.Fraction)
    (hj : j<Q) (hB : RationalHeight b B)
    (hr : ∀ f,r=some f → f.num≤2*Q ∧ f.den≤2*Q) :
    window model W Q j hQ b r≤profile model W Q B := by
  have hb : rationalWordWidth b≤GeneralPaperSelectionPoints.width Q B :=
    (GeneralPaperSelectionPoints.rational_words Q j B b hQ hj hB).1
  have hp := point_record W Q j hQ hj
  have hroot := root_bound W Q r hr
  have hv := root_value Q B r hr
  have hc := casts_bound W Q j B hQ hj
  have hs := selected_bound W Q j hQ hj (b:ℝ) r hr
  have hw := GeneralPaperSelectionBits.work model W Q j B hQ b r hj hB hr
  have hwidth : GeneralPaperSelectionPoints.width Q 0≤GeneralPaperSelectionPoints.width Q B := by
    unfold GeneralPaperSelectionPoints.width
    omega
  unfold window profile
  rw [GeneralPaperSelectionPointsPrice.data,GeneralPaperSelectionBits.data]
  omega

end Blotto.GeneralPaperSelectionConstructionStorage
