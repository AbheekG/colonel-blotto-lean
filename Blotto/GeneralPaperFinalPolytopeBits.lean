import Blotto.GeneralPaperFinalStaticBits
import Blotto.GeneralPaperRayPredicateBits

/-! The bit-priced final polytope check shares the prepared score matrix.
It executes every static row and the complete strict-score DP, preserving
the original feasibility decision even for a rejected candidate point. -/
namespace Blotto.GeneralPaperFinalPolytopeBits
open RationalOrderCell GeneralPaperExactScoreDP GeneralPaperRayRationalBound
set_option autoImplicit false
set_option maxHeartbeats 4500000

def run {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (Field K)) (S h : ℕ) (beta : ℚ) (x : Variable m K → ℚ) :
    GeneralPaperFinalPolytopeCheck.Result :=
  let static := GeneralPaperFinalStaticBits.run model.rat W labels x
  let high := GeneralPaperRayPredicateBits.run model W matrix x (fun _ => 0) S h beta 0
  ⟨static.accepted && high.1,static.work+high.2+8*W⟩

theorem data {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (Field K)) (S h : ℕ) (beta : ℚ) (x : Variable m K → ℚ) :
    (run model W labels matrix S h beta x).accepted=
      (GeneralPaperFinalPolytopeCheck.run labels matrix S h beta x).accepted := by
  simp only [run,GeneralPaperFinalPolytopeCheck.run,GeneralPaperFinalStaticBits.data,GeneralPaperRayPredicateBits.data]

theorem correct {T m K : ℕ} (model : RationalCostModel) (W depth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (S h : ℕ)
    (hK : 0<K) (hCap : S<2^depth) (beta : ℚ) (x : Variable m K → ℚ) :
    (run model W dict.label (GeneralPaperScoreMatrixWork.matrixRun depth dict v S).1 S h beta x).accepted=true ↔
      GeneralPaperAffineConstraintRows.Feasible dict.label (GeneralPaperStrictScore.score v S) h (beta:ℝ) (fun a => (x a:ℝ)) := by
  rw [data]
  exact GeneralPaperFinalPolytopeCheck.correct depth dict v S h hK hCap beta x

def profile (T m K S W Q : ℕ) : ℕ :=
  GeneralPaperStaticScanPrice.profile T m K W Q+4096*(m+1)*(K+1)*(S+1)*(W+Q)+8*W

theorem work {T m K : ℕ} (model : RationalCostModel) (W D X P : ℕ) (hm : 0<m) (hD : 0<D)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (Field K)) (S h : ℕ)
    (beta : ℚ) (hb : Bounded D P beta) (x : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a))
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) :
    (run model W labels matrix S h beta x).work≤profile T m K S W
      (model.rat (1+2*(GeneralPaperRayUniformSize.width D 1 m X 0 P+1))) := by
  let Q := model.rat (1+2*(GeneralPaperRayUniformSize.width D 1 m X 0 P+1))
  have hs := GeneralPaperFinalStaticBits.work model.rat model.monotone W D X P hm hD labels x hx
  have hp := model.monotone (show 1+2*GeneralPaperRayUniformSize.width D 1 m X 0 P≤
    1+2*(GeneralPaperRayUniformSize.width D 1 m X 0 P+1) by omega)
  have hs' : (GeneralPaperFinalStaticBits.run model.rat W labels x).work≤
      GeneralPaperStaticScanPrice.profile T m K W Q := by
    apply hs.trans
    unfold GeneralPaperStaticScanPrice.profile
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hp W)
  have hh := GeneralPaperRayPredicateBits.work model W D 1 X 0 P 1 hD (one_dvd D) matrix x (fun _ => 0)
    hx (fun _ => Bounded.zero 1) beta hb 0 (by norm_num)
    (GeneralPaperQuantizedHeight.zero_height 1 (by decide)) S h hW hK hM hIndex
  change (GeneralPaperFinalStaticBits.run model.rat W labels x).work+
    (GeneralPaperRayPredicateBits.run model W matrix x (fun _ => 0) S h beta 0).2+8*W≤_
  unfold profile
  exact Nat.add_le_add_right (Nat.add_le_add hs' hh) _

end Blotto.GeneralPaperFinalPolytopeBits
