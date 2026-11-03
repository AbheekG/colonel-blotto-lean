import Blotto.GeneralPaperStaticScanPrice
import Blotto.GeneralPaperFinalPolytopeCheck

/-! A bit-priced final scan of every original static row. Sparse row
evaluation, the literal index list, rational comparisons and control are
included. No crossing is computed and no early rejection skips a row. -/
namespace Blotto.GeneralPaperFinalStaticBits
open RationalOrderCell GeneralPaperStaticRayRows GeneralPaperRayRationalBound GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 6000000

def loop {T m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (x : Variable m K → ℚ) : List (StaticIndex T m K) → Bool → ℕ → GeneralPaperFinalStaticCheck.Result
  | [],accepted,spent => ⟨accepted,spent+2*W⟩
  | i::rest,accepted,spent =>
    let evaluated := GeneralPaperStaticRowPrice.evaluate primitive W labels x (fun _ => 0) i
    loop primitive W labels x rest (accepted && decide (evaluated.1.intercept≤0))
      (spent+evaluated.2+primitive (RationalExpression.pairWidth evaluated.1.intercept 0)+8*W)

def run {T m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (x : Variable m K → ℚ) : GeneralPaperFinalStaticCheck.Result :=
  let rows := GeneralPaperStaticEnumerationPrice.run W T m K
  let checked := loop primitive W labels x rows.1 true 0
  ⟨checked.accepted,rows.2+checked.work+8*W⟩

theorem loop_data {T m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (x : Variable m K → ℚ) (rows : List (StaticIndex T m K)) (accepted : Bool) (spent oldSpent : ℕ) :
    (loop primitive W labels x rows accepted spent).accepted=
      (GeneralPaperFinalStaticCheck.loop labels x rows accepted oldSpent).accepted := by
  induction rows generalizing accepted spent oldSpent with
  | nil => rfl
  | cons i rest ih =>
    simp only [loop,GeneralPaperFinalStaticCheck.loop,GeneralPaperStaticRowPrice.data]
    exact ih _ _ _

theorem data {T m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (x : Variable m K → ℚ) :
    (run primitive W labels x).accepted=(GeneralPaperFinalStaticCheck.run labels x).accepted := by
  simp only [run,GeneralPaperFinalStaticCheck.run,GeneralPaperStaticEnumerationPrice.data]
  exact loop_data primitive W labels x _ true 0 0

theorem loop_work {T m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (x : Variable m K → ℚ) (rows : List (StaticIndex T m K)) (accepted : Bool) (spent : ℕ) :
    (loop primitive W labels x rows accepted spent).work=spent+
      (rows.map (fun i => (GeneralPaperStaticRowPrice.evaluate primitive W labels x (fun _ => 0) i).2+
        primitive (RationalExpression.pairWidth
          (GeneralPaperStaticRowPrice.evaluate primitive W labels x (fun _ => 0) i).1.intercept 0)+8*W)).sum+2*W := by
  induction rows generalizing accepted spent with
  | nil => simp only [loop,List.map_nil,List.sum_nil,Nat.add_zero]
  | cons i rest ih => rw [loop,ih,List.map_cons,List.sum_cons]; omega

theorem compare_work {T m K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D X P : ℕ) (hm : 0<m) (hD : 0<D) (labels : Fin T → Fin m → Fin K)
    (x : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a)) (i : StaticIndex T m K) :
    primitive (RationalExpression.pairWidth
      (GeneralPaperStaticRowPrice.evaluate primitive W labels x (fun _ => 0) i).1.intercept 0)≤
        primitive (1+2*width D 1 m X 0 P) := by
  let R := width D 1 m X 0 P
  have hb := GeneralPaperStaticRowPrice.bounded primitive W D 1 X 0 P hm labels x (fun _ => 0)
    hx (fun _ => Bounded.zero 1) i
  have hc := GeneralPaperAffineValuePrice.coefficients hD (by decide : 0<1) _ hb
  have hr : GeneralPaperRayAffineBound.rootWidth D 1 (interceptCap m X P) (slopeCap m 0)≤R :=
    GeneralPaperRayAffineBound.rootWidth_mono D 1 _ _ _ _ (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hi := hc.1.mono hr
  have hp : 0<R := by
    have hd := binaryWordWidth_pos D
    dsimp only [R,width,GeneralPaperRayAffineBound.rootWidth]
    omega
  have hz := GeneralPaperQuantizedHeight.zero_height R hp
  exact hMono (max_le (rationalWordWidth_of_height hi) (rationalWordWidth_of_height hz))

theorem work {T m K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D X P : ℕ) (hm : 0<m) (hD : 0<D) (labels : Fin T → Fin m → Fin K)
    (x : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a)) :
    (run primitive W labels x).work≤GeneralPaperStaticScanPrice.profile T m K W
      (primitive (1+2*width D 1 m X 0 P)) := by
  let Q := primitive (1+2*width D 1 m X 0 P)
  let rows := GeneralPaperStaticEnumerationPrice.run W T m K
  have hEach (i : StaticIndex T m K) :
      (GeneralPaperStaticRowPrice.evaluate primitive W labels x (fun _ => 0) i).2+
        primitive (RationalExpression.pairWidth
          (GeneralPaperStaticRowPrice.evaluate primitive W labels x (fun _ => 0) i).1.intercept 0)+8*W≤
          GeneralPaperStaticRowPrice.charge W Q i := by
    have he := GeneralPaperStaticRowPrice.work primitive hMono W D 1 X 0 P hm hD (by decide) labels x (fun _ => 0)
      hx (fun _ => Bounded.zero 1) i
    have hc := compare_work primitive hMono W D X P hm hD labels x hx i
    change _≤GeneralPaperStaticRowPrice.charge W Q i at he
    change _≤Q at hc
    omega
  have hSum := List.sum_le_sum (fun i (_ : i∈rows.1) => hEach i)
  have hCharges : (rows.1.map (GeneralPaperStaticRowPrice.charge W Q)).sum=
      (m*(K-1))*(502*W+63*Q)+T*((64*m+114)*W+(9*m+9)*Q) := by
    rw [GeneralPaperStaticEnumerationPrice.data,GeneralPaperStaticRowPrice.charge_sum]
  rw [hCharges] at hSum
  have hLoop := loop_work primitive W labels x rows.1 true 0
  have hEnum := GeneralPaperStaticEnumerationPrice.work W T m K
  let d := m*(K-1)
  let slack := (2570*d+3072*m+4032*m*T+2958*T+3062)*W+
    (4033*d+4096*m+4087*m*T+4087*T+4096)*Q
  have hIdentity : d*(502*W+63*Q)+T*((64*m+114)*W+(9*m+9)*Q)+
      1024*(d+m+T+1)*W+10*W+slack=GeneralPaperStaticScanPrice.profile T m K W Q := by
    dsimp only [d,slack,GeneralPaperStaticScanPrice.profile]
    ring
  change rows.2+(loop primitive W labels x rows.1 true 0).work+8*W≤
    GeneralPaperStaticScanPrice.profile T m K W Q
  change rows.2≤1024*(d+m+T+1)*W at hEnum
  change _≤d*(502*W+63*Q)+T*((64*m+114)*W+(9*m+9)*Q) at hSum
  omega

end Blotto.GeneralPaperFinalStaticBits
