import Blotto.GeneralPaperFinalStaticStorage

/-! Complete final polytope check: all static enumeration/row/Boolean-scan
and strict-score DP phases, plus native Boolean/phase/partial-return fields.
The point need not be feasible or accepted. Original input owners remain
with the enclosing raw endpoint caller. -/
namespace Blotto.GeneralPaperFinalPolytopeStorage
open RationalOrderCell GeneralPaperExactScoreDP GeneralPaperRayRationalBound GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (W T m K S R : ℕ) : ℕ := GeneralPaperFinalPolytopeBits.profile T m K S W (model.rat (1+2*R))
def metadataCap (model : RationalCostModel) (W T m K S R : ℕ) : ℕ := S+2+3*price model W T m K S R
def caller {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (Field K)) (S h : ℕ) (beta : ℚ) (x : Variable m K → ℚ) : ℕ :=
  let static := GeneralPaperFinalStaticBits.run model.rat W labels x
  let high := GeneralPaperRayPredicateBits.run model W matrix x (fun _ => 0) S h beta 0
  let result := GeneralPaperFinalPolytopeBits.run model W labels matrix S h beta x
  fields W [S,h,static.work,high.2,result.work,8*W,static.work+high.2,GeneralPaperFinalStaticLoopStorage.bit static.accepted,
    GeneralPaperFinalStaticLoopStorage.bit high.1,GeneralPaperFinalStaticLoopStorage.bit result.accepted]+128*W
def callerProfile (model : RationalCostModel) (W T m K S R : ℕ) : ℕ := 10*(natBits (metadataCap model W T m K S R)+W)+160*W

inductive Phase {m K : ℕ} (T : ℕ) (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (Field K)) (x : Variable m K → ℚ) (S : ℕ) where
  | static (phase : GeneralPaperFinalStaticStorage.Phase T m K)
  | high (phase : GeneralPaperRayQueryStorage.Phase model W matrix x (fun _ => 0) 0 S)
  | returned

def window {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (Field K)) (S h : ℕ) (beta : ℚ) (x : Variable m K → ℚ)
    (phase : Phase T model W matrix x S) : ℕ :=
  caller model W labels matrix S h beta x+match phase with
  | .static p => GeneralPaperFinalStaticStorage.window model W labels x p
  | .high p => GeneralPaperRayPredicateStorage.window model W matrix x (fun _ => 0) S h beta 0 p
  | .returned => 0
def profile (model : RationalCostModel) (W T m K S R : ℕ) : ℕ := callerProfile model W T m K S R+
  GeneralPaperFinalStaticStorage.profile model W T m K R+GeneralPaperRayPredicateStorage.profile model W m K S R

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W D X P R : ℕ) (hm : 0<m) (hD : 0<D)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (Field K)) (S h : ℕ)
    (hs : ∀ j l,((matrix.read j).read l).1≤S) (hh : h≤S) (beta : ℚ) (hb : Bounded D P beta)
    (x : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a))
    (hRoot : GeneralPaperRayUniformSize.width D 1 m X 0 P+1≤R)
    (hCommon : GeneralPaperCommonLatticeDPBits.width D (X+1) m≤R)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) (hIndex : binaryWordWidth (S+2)≤W)
    (phase : Phase T model W matrix x S) : window model W labels matrix S h beta x phase≤profile model W T m K S R := by
  let static := GeneralPaperFinalStaticBits.run model.rat W labels x
  let high := GeneralPaperRayPredicateBits.run model W matrix x (fun _ => 0) S h beta 0
  let result := GeneralPaperFinalPolytopeBits.run model W labels matrix S h beta x
  have hWork := (GeneralPaperFinalPolytopeBits.work model W D X P hm hD labels matrix S h beta hb x hx hW hK hM hIndex).trans
    (show GeneralPaperFinalPolytopeBits.profile T m K S W (model.rat (1+2*(GeneralPaperRayUniformSize.width D 1 m X 0 P+1)))≤price model W T m K S R by
      unfold price GeneralPaperFinalPolytopeBits.profile GeneralPaperStaticScanPrice.profile
      gcongr <;> exact model.monotone (by omega))
  change result.work≤price model W T m K S R at hWork
  have hShape : result.work=static.work+high.2+8*W := rfl
  have hbStatic := GeneralPaperFinalStaticLoopStorage.bit_bound static.accepted
  have hbHigh := GeneralPaperFinalStaticLoopStorage.bit_bound high.1
  have hbResult := GeneralPaperFinalStaticLoopStorage.bit_bound result.accepted
  have hf := fields_bound W (natBits (metadataCap model W T m K S R))
    [S,h,static.work,high.2,result.work,8*W,static.work+high.2,GeneralPaperFinalStaticLoopStorage.bit static.accepted,
      GeneralPaperFinalStaticLoopStorage.bit high.1,GeneralPaperFinalStaticLoopStorage.bit result.accepted] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      unfold metadataCap
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤10*(natBits (metadataCap model W T m K S R)+W)+32*W at hf
  have hCaller : caller model W labels matrix S h beta x≤callerProfile model W T m K S R := by
    change GeneralPaperEncodedScalarStorage.fields W [S,h,static.work,high.2,result.work,8*W,static.work+high.2,
      GeneralPaperFinalStaticLoopStorage.bit static.accepted,GeneralPaperFinalStaticLoopStorage.bit high.1,
      GeneralPaperFinalStaticLoopStorage.bit result.accepted]+128*W≤_
    unfold callerProfile
    omega
  cases phase with
  | static p =>
    have hStatic := GeneralPaperFinalStaticStorage.bounded model W D X P R hm hD labels x hx (by omega) p
    unfold window profile
    dsimp only
    omega
  | high p =>
    have hQuery := GeneralPaperRayPredicateStorage.bounded model W D 1 X 0 P 1 S h R hD (one_dvd D)
      matrix hs x (fun _ => 0) hx (fun _ => Bounded.zero 1) beta hb 0 (by norm_num)
      (GeneralPaperQuantizedHeight.zero_height 1 (by decide))
      (by simpa only [Rat.den_zero,Nat.mul_one,Nat.add_zero] using hCommon) hRoot hh hW hK hM hIndex p
    unfold window profile
    dsimp only
    omega
  | returned =>
    unfold window profile
    dsimp only
    omega

end Blotto.GeneralPaperFinalPolytopeStorage
