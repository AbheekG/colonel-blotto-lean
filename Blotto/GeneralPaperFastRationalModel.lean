import Blotto.GeneralPaperPreparedReferenceCapacity

/-! The paper's fast-rational primitive convention as an explicit logarithmic
majorant. These are mathematical prices for the declared bit model; they do
not assert a generated-C or library implementation bound. The class is
nonempty for every logarithmic exponent and preserves all Rat model laws. -/
namespace Blotto.GeneralPaperFastRationalModel
set_option autoImplicit false
set_option maxHeartbeats 800000

def logFactor (d w : ℕ) : ℕ := (binaryWordWidth (w+1)+1)^d

theorem factor_positive (d w : ℕ) : 1≤logFactor d w := by
  unfold logFactor
  exact Nat.one_le_pow _ _ (by omega)

theorem factor_monotone (d : ℕ) : Monotone (logFactor d) := by
  intro a b hab
  exact Nat.pow_le_pow_left (Nat.add_le_add_right (binaryWordWidth_mono (by omega : a+1≤b+1)) 1) d

def charge (C d w : ℕ) : ℕ := C*w*logFactor d w

theorem charge_monotone (C d : ℕ) : Monotone (charge C d) := by
  intro a b hab
  exact Nat.mul_le_mul (Nat.mul_le_mul_left C hab) (factor_monotone d hab)

def fast (d : ℕ) : RationalCostModel where
  rat := charge 1 d
  monotone := charge_monotone 1 d
  word_le := by
    intro w
    simpa only [charge,Nat.one_mul,Nat.mul_one] using Nat.mul_le_mul_left w (factor_positive d w)
  superadditive := by
    intro a b
    have ha := Nat.mul_le_mul_left a (factor_monotone d (show a≤a+b by omega))
    have hb := Nat.mul_le_mul_left b (factor_monotone d (show b≤a+b by omega))
    simp only [charge,Nat.one_mul]
    nlinarith only [ha,hb]

def Growth (model : RationalCostModel) (C d : ℕ) : Prop := ∀ w,model.rat w≤charge C d w

def IsFast (model : RationalCostModel) : Prop := ∃ C d,Growth model C d

theorem fast_growth (d : ℕ) : Growth (fast d) 1 d := fun _ => Nat.le_refl _

theorem fast_is_fast (d : ℕ) : IsFast (fast d) := ⟨1,d,fast_growth d⟩

theorem degree_zero (w : ℕ) : (fast 0).rat w=w := by
  simp only [fast,charge,logFactor,pow_zero,Nat.one_mul,Nat.mul_one]

theorem price_zero (model : RationalCostModel) : model.rat 0=0 := by
  have h := model.superadditive 0 0
  simp only [Nat.zero_add] at h
  omega

theorem growth_coefficient_positive {model : RationalCostModel} {C d : ℕ} (h : Growth model C d) : 1≤C := by
  have hw := model.word_le 1
  have hp := h 1
  by_contra hn
  have hz : C=0 := by omega
  simp only [charge,hz,Nat.zero_mul] at hp
  omega

theorem charge_superadditive (C d a b : ℕ) : charge C d a+charge C d b≤charge C d (a+b) := by
  have h := (fast d).superadditive a b
  simp only [fast,charge,Nat.one_mul] at h
  have hc := Nat.mul_le_mul_left C h
  dsimp only [charge]
  nlinarith only [hc]

end Blotto.GeneralPaperFastRationalModel
