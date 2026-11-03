import Blotto.GeneralPaperRayFieldsBits

/-! Complete bit-priced native fixed-point minimum: actual cost arrays,
the existing stored exact-score DP, and its strict high-score scan. One
common lattice supplies the actual operand-width premises of every phase.
-/
namespace Blotto.GeneralPaperRayMinimumBits
open RationalOrderCell GeneralPaperExactScoreDP GeneralPaperRayRationalBound
set_option autoImplicit false
set_option maxHeartbeats 4500000

def run {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ) (S h : ℕ) : Option (GeneralPaperMinimum.Selection K) × ℕ :=
  let inputs := GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t
  let minimum := GeneralPaperCommonLatticeMinimumBits.run model W S h inputs.1
  (minimum.1,inputs.2+minimum.2+8*W)

theorem data {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ) (S h : ℕ) :
    (run model W matrix x w t S h).1=(GeneralPaperRayQueryWork.minimumRun matrix x w t S h).1 := by
  simp only [run,GeneralPaperRayFieldsBits.fields_data,GeneralPaperCommonLatticeMinimumBits.native_data,
    GeneralPaperRayQueryWork.minimum_data]

def profile (m K S W P : ℕ) : ℕ :=
  512*(m+1)*(K+1)*(W+P)+GeneralPaperCommonLatticeMinimumBits.profile m K S W P+8*W

theorem work {m K : ℕ} (model : RationalCostModel) (W D E X V : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a)) (t : ℚ) (ht : 0≤t ∧ t≤1) (S h : ℕ)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) :
    (run model W matrix x w t S h).2≤
      profile m K S W (model.rat (GeneralPaperCommonLatticeDPBits.width (D*t.den) (X+V+1) m)) := by
  have hf := GeneralPaperRayFieldsBits.fields_work model W D E X V hD hED matrix x w hx hw t ht hW hK hM
  have hb := GeneralPaperRayFieldsBits.fields_bounded model W D E X V hED matrix x w hx hw t ht
  have hLen : (GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t).1.length=m := by
    rw [GeneralPaperRayFieldsBits.fields_data]
    simp only [fields,List.length_ofFn]
  have hm := GeneralPaperCommonLatticeMinimumBits.work model W (D*t.den) (X+V+1) m S h
    (Nat.mul_pos hD t.den_pos) (GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t).1 hb
    hLen.le hW hIndex
  rw [hLen] at hm
  change (GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t).2+
    (GeneralPaperCommonLatticeMinimumBits.run model W S h
      (GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t).1).2+8*W≤_
  unfold profile
  omega

theorem profile_mono (m K S W : ℕ) {P Q : ℕ} (h : P≤Q) : profile m K S W P≤profile m K S W Q := by
  unfold profile GeneralPaperCommonLatticeMinimumBits.profile GeneralPaperScoreDPBits.profile
    GeneralPaperScoreDPBits.stepProfile
  gcongr

theorem profile_bound (m K S W P : ℕ) (hW : 1≤W) :
    profile m K S W P≤2048*(m+1)*(K+1)*(S+1)*(W+P) := by
  have hi : GeneralPaperScoreDPBits.initialProfile S W≤93*(S+1)*W := by
    unfold GeneralPaperScoreDPBits.initialProfile
    nlinarith only [Nat.mul_le_mul_left (S+1) (show 3≤3*W by omega)]
  have he : GeneralPaperScoreDPBits.stepProfile K S W P≤
      (S+1)*(K+1)*(166*W+3*P) := by
    unfold GeneralPaperScoreDPBits.stepProfile
    nlinarith only [Nat.zero_le ((S+1)*K*W),Nat.zero_le ((S+1)*P)]
  have h01 : 1≤(m+1)*(K+1)*(S+1) := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hM : m≤(m+1)*(K+1)*(S+1) := by
    have hK : 1≤K+1 := by omega
    have hS : 1≤S+1 := by omega
    nlinarith only [Nat.mul_le_mul_left (m+1) hK,
      Nat.mul_le_mul_left ((m+1)*(K+1)) hS]
  have hA : (m+1)*(K+1)≤(m+1)*(K+1)*(S+1) := by
    have hh := Nat.mul_le_mul_left ((m+1)*(K+1)) (show 1≤S+1 by omega)
    simpa only [Nat.mul_one] using hh
  have hB : S+1≤(m+1)*(K+1)*(S+1) := by
    have hh := Nat.mul_le_mul_right (S+1) (show 1≤(m+1)*(K+1) from Nat.mul_pos (by omega) (by omega))
    simpa only [Nat.one_mul] using hh
  have hStep := Nat.mul_le_mul_left m he
  have hC : m*(S+1)*(K+1)≤(m+1)*(K+1)*(S+1) := by nlinarith
  have hStep' := Nat.mul_le_mul_right (166*W+3*P) hC
  have hInit := Nat.mul_le_mul_right (93*W) hB
  have hFinal := Nat.mul_le_mul_right (28*W+P) hB
  have hSmall := Nat.mul_le_mul_right (18*W) h01
  have hControl := Nat.mul_le_mul_right (4*W) hM
  have hFields := Nat.mul_le_mul_right (512*(W+P)) hA
  unfold profile GeneralPaperCommonLatticeMinimumBits.profile GeneralPaperScoreDPBits.profile
  nlinarith only [hi,hStep,hStep',hInit,hFinal,hSmall,hControl,hFields,
    Nat.zero_le ((m+1)*(K+1)*(S+1)*W),Nat.zero_le ((m+1)*(K+1)*(S+1)*P)]

end Blotto.GeneralPaperRayMinimumBits
