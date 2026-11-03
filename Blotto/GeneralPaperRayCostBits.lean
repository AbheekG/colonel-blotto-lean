import Blotto.GeneralPaperCommonLatticeMinimumBits

/-! Construct the actual fixed-probe ray costs with operand-sensitive bit
prices. Inputs, multiplication, addition and results share one lattice-size
envelope; no artificial history of denominator products is charged.
-/
namespace Blotto.GeneralPaperRayCostBits
open RationalOrderCell GeneralPaperRayRationalBound GeneralPaperRayAnchorCosts
set_option autoImplicit false
set_option maxHeartbeats 3500000

def multiplyPrice (model : RationalCostModel) (a b : ℚ) : ℕ :=
  model.rat (RationalExpression.pairWidth a b)+rationalWordWidth (a*b)

theorem multiplyPrice_le (model : RationalCostModel) (a b : ℚ) (H : ℕ)
    (ha : rationalWordWidth a≤H) (hb : rationalWordWidth b≤H) (hc : rationalWordWidth (a*b)≤H) :
    multiplyPrice model a b≤2*model.rat H := by
  have hp := model.monotone (max_le ha hb)
  have ho := hc.trans (model.word_le H)
  unfold multiplyPrice RationalExpression.pairWidth at *
  omega

def run {m K : ℕ} (model : RationalCostModel) (W : ℕ) (x w : Variable m K → ℚ)
    (t : ℚ) (j : Fin m) (l : Fin K) : ℚ × ℕ :=
  let a := anchorQ x j l
  let b := anchorQ w j l
  let product := t*b
  (a+product,24*W+multiplyPrice model t b+GeneralPaperScoreBitPrimitive.additionPrice model a product)

theorem data {m K : ℕ} (model : RationalCostModel) (W : ℕ) (x w : Variable m K → ℚ)
    (t : ℚ) (j : Fin m) (l : Fin K) : (run model W x w t j l).1=costs x w t j l := rfl

theorem operands {m K : ℕ} (D E X V : ℕ) (hED : E∣D) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a))
    (t : ℚ) (ht : 0≤t ∧ t≤1) (j : Fin m) (l : Fin K) :
    Bounded (D*t.den) (X+V+1) (anchorQ x j l) ∧
    Bounded (D*t.den) (X+V+1) (anchorQ w j l) ∧
    Bounded (D*t.den) (X+V+1) t ∧
    Bounded (D*t.den) (X+V+1) (t*anchorQ w j l) ∧
    Bounded (D*t.den) (X+V+1) (costs x w t j l) := by
  have hA := (GeneralPaperRayAnchorBound.anchor D X x hx j l).enlarge (Nat.dvd_mul_right D t.den)
  have hB := (GeneralPaperRayAnchorBound.anchor E V w hw j l).enlarge hED
  have hT : Bounded t.den 1 t := ⟨dvd_refl _,by rw [abs_of_nonneg ht.1]; exact ht.2⟩
  have hProduct : Bounded (D*t.den) V (t*anchorQ w j l) := by
    simpa only [Nat.mul_comm t.den D,Nat.one_mul] using hT.mul hB
  have hB' := hB.enlarge (Nat.dvd_mul_right D t.den)
  have hT' := hT.enlarge (show t.den∣D*t.den from ⟨D,by ring⟩)
  exact ⟨hA.mono (by omega),hB'.mono (by omega),hT'.mono (by omega),
    hProduct.mono (by omega),(GeneralPaperRayFixedQuerySize.cost D E X V hED x w hx hw t ht j l).mono (by omega)⟩

theorem work {m K : ℕ} (model : RationalCostModel) (W D E X V : ℕ) (hD : 0<D) (hED : E∣D)
    (x w : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a))
    (t : ℚ) (ht : 0≤t ∧ t≤1) (j : Fin m) (l : Fin K) :
    (run model W x w t j l).2≤24*W+
      4*model.rat (GeneralPaperCommonLatticeDPBits.width (D*t.den) (X+V+1) m) := by
  have ho := operands D E X V hED x w hx hw t ht j l
  have hPos := Nat.mul_pos hD t.den_pos
  have hWidth (q : ℚ) (hq : Bounded (D*t.den) (X+V+1) q) :=
    GeneralPaperCommonLatticeDPBits.input_width (D*t.den) (X+V+1) m hPos q hq
  have hm := multiplyPrice_le model t (anchorQ w j l) _
    (hWidth _ ho.2.2.1) (hWidth _ ho.2.1) (hWidth _ ho.2.2.2.1)
  have ha := GeneralPaperScoreBitPrimitive.additionPrice_le model (anchorQ x j l) (t*anchorQ w j l) _
    (hWidth _ ho.1) (hWidth _ ho.2.2.2.1) (hWidth _ ho.2.2.2.2)
  change 24*W+multiplyPrice model t (anchorQ w j l)+
    GeneralPaperScoreBitPrimitive.additionPrice model (anchorQ x j l) (t*anchorQ w j l)≤_
  omega

end Blotto.GeneralPaperRayCostBits
