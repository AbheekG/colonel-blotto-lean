import Blotto.GeneralPaperStaticRowPrice

/-! Complete native static scan, including literal row-index enumeration,
sparse constructors/residuals, positive-slope roots and earliest-row ties.
The family-sensitive sum preserves the paper's O(d+mT) arithmetic count.
-/
namespace Blotto.GeneralPaperStaticScanPrice
open RationalOrderCell GeneralPaperStaticRayRows GeneralPaperRayUniformSize GeneralPaperRayRationalBound
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run {T m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (x w : Variable m K → ℚ) : GeneralPaperRayMinimum.Result (StaticIndex T m K) :=
  let indices := GeneralPaperStaticEnumerationPrice.run W T m K
  let chosen := GeneralPaperStaticMinimumScanPrice.scan primitive W
    (GeneralPaperStaticRowPrice.evaluate primitive W labels x w) indices.1
  ⟨chosen.choice,indices.2+chosen.work+8*W⟩

theorem data {T m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (x w : Variable m K → ℚ) :
    (run primitive W labels x w).choice=(GeneralPaperStaticRayScan.scan labels x w).choice := by
  simp only [run,GeneralPaperStaticEnumerationPrice.data]
  exact GeneralPaperStaticMinimumScanPrice.data primitive W _ _
    (GeneralPaperStaticRowPrice.data primitive W labels x w) _

def profile (T m K W Q : ℕ) : ℕ := 4096*(m*(K-1)+m+m*T+T+1)*(W+Q)

theorem work {T m K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E X V P : ℕ) (hm : 0<m) (hD : 0<D) (hE : 0<E) (labels : Fin T → Fin m → Fin K)
    (x w : Variable m K → ℚ) (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j)) :
    (run primitive W labels x w).work≤profile T m K W (primitive (1+2*width D E m X V P)) := by
  let A := interceptCap m X P
  let B := slopeCap m V
  let R := width D E m X V P
  let Q := primitive (1+2*R)
  let rows := GeneralPaperStaticEnumerationPrice.run W T m K
  let evaluate := GeneralPaperStaticRowPrice.evaluate primitive W labels x w
  have hRoot : GeneralPaperRayAffineBound.rootWidth D E A B≤R :=
    GeneralPaperRayAffineBound.rootWidth_mono D E A B (A+A) (B+B) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hScan := GeneralPaperStaticMinimumScanPrice.work primitive hMono W D E A B R hD hE hRoot evaluate rows.1
    (fun i _ => GeneralPaperStaticRowPrice.bounded primitive W D E X V P hm labels x w hx hw i)
  have hSum : (rows.1.map (fun i => (evaluate i).2+56*W+6*Q)).sum≤
      (rows.1.map (GeneralPaperStaticRowPrice.charge W Q)).sum :=
    List.sum_le_sum (fun i _ => GeneralPaperStaticRowPrice.work primitive hMono W D E X V P hm hD hE labels x w hx hw i)
  have hCharges : (rows.1.map (GeneralPaperStaticRowPrice.charge W Q)).sum=
      (m*(K-1))*(502*W+63*Q)+T*((64*m+114)*W+(9*m+9)*Q) := by
    rw [GeneralPaperStaticEnumerationPrice.data,GeneralPaperStaticRowPrice.charge_sum]
  rw [hCharges] at hSum
  change (GeneralPaperStaticMinimumScanPrice.scan primitive W evaluate rows.1).work≤
    (rows.1.map (fun i => (evaluate i).2+56*W+6*Q)).sum+2*W at hScan
  have hEnum := GeneralPaperStaticEnumerationPrice.work W T m K
  let d := m*(K-1)
  let slack := (2570*d+3072*m+4032*m*T+2958*T+3062)*W+
    (4033*d+4096*m+4087*m*T+4087*T+4096)*Q
  have hIdentity : d*(502*W+63*Q)+T*((64*m+114)*W+(9*m+9)*Q)+
      1024*(d+m+T+1)*W+10*W+slack=profile T m K W Q := by
    dsimp only [d,slack,profile]
    ring
  change rows.2+(GeneralPaperStaticMinimumScanPrice.scan primitive W evaluate rows.1).work+8*W≤profile T m K W Q
  change rows.2≤_ at hEnum
  change _≤d*(502*W+63*Q)+T*((64*m+114)*W+(9*m+9)*Q) at hSum
  change rows.2≤1024*(d+m+T+1)*W at hEnum
  omega

theorem work_linear {T m K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E X V P : ℕ) (hm : 0<m) (hK : 2≤K) (hD : 0<D) (hE : 0<E) (labels : Fin T → Fin m → Fin K)
    (x w : Variable m K → ℚ) (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j)) :
    (run primitive W labels x w).work≤8192*(m*(K-1)+m*T+1)*(W+primitive (1+2*width D E m X V P)) := by
  have hh := work primitive hMono W D E X V P hm hD hE labels x w hx hw
  have hd : m≤m*(K-1) := by nlinarith only [show 1≤K-1 by omega]
  have ht : T≤m*T := by nlinarith only [show 1≤m by omega]
  have hs : m*(K-1)+m+m*T+T+1≤2*(m*(K-1)+m*T+1) := by omega
  have hp := Nat.mul_le_mul_right (W+primitive (1+2*width D E m X V P)) (Nat.mul_le_mul_left 4096 hs)
  apply hh.trans
  unfold profile
  convert hp using 1
  ring

end Blotto.GeneralPaperStaticScanPrice
