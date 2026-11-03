import Blotto.GeneralPaperRawAffineEvaluate
import Blotto.GeneralPaperBasisAffineBits

/-! Complete bit prices and output bounds for the already executed raw
affine evaluator. Bounds include unreduced integer products and casts.
They hold before either final acceptance test, without box feasibility. -/
namespace Blotto.GeneralPaperRawAffineBits
open GeneralPaperBasisAffineData GeneralPaperIntegerPrimitivePrice GeneralPaperRayRationalBound
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6000000

def cap (H B N : ℕ) : ℕ := 1+N+B+H+(N+B)*H
def width (H B N : ℕ) : ℕ := 1+4*binaryWordWidth (cap H B N)

theorem cache_congr {d : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (left right : Data d)
    (hc : left.constant=right.constant) (hs : left.slope=right.slope) (hd : left.determinant=right.determinant)
    (numerator : ℤ) (denominator : ℕ) :
    GeneralPaperRawAffineEvaluate.run bits model W left numerator denominator=
      GeneralPaperRawAffineEvaluate.run bits model W right numerator denominator := by
  have he (primitive : ℕ → ℕ) (A : ℕ) :
      GeneralPaperRawAffineEvaluate.entry primitive A left numerator denominator=
        GeneralPaperRawAffineEvaluate.entry primitive A right numerator denominator := by
    funext k
    simp only [GeneralPaperRawAffineEvaluate.entry,hc,hs,hd]
  simp only [GeneralPaperRawAffineEvaluate.run,he]

theorem top_bound (c s numerator : ℤ) (denominator H B N : ℕ)
    (hc : c.natAbs≤H) (hs : s.natAbs≤H) (hb : numerator.natAbs≤B) (hn : denominator≤N) :
    ((denominator:ℤ)*c+numerator*s).natAbs≤(N+B)*H := by
  have ha : ((denominator:ℤ)*c).natAbs≤N*H := by
    rw [Int.natAbs_mul,Int.natAbs_natCast]; exact Nat.mul_le_mul hn hc
  have hd : (numerator*s).natAbs≤B*H := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul hb hs
  have ht := (Int.natAbs_add_le ((denominator:ℤ)*c) (numerator*s)).trans (Nat.add_le_add ha hd)
  nlinarith only [ht]

theorem bottom_bound (determinant : ℤ) (denominator H N : ℕ)
    (hd : determinant.natAbs≤H) (hn : denominator≤N) :
    ((denominator:ℤ)*determinant).natAbs≤N*H := by
  rw [Int.natAbs_mul,Int.natAbs_natCast]
  exact Nat.mul_le_mul hn hd

theorem entry_height {d : ℕ} (primitive : ℕ → ℕ) (W H B N : ℕ) (cache : Data d)
    (numerator : ℤ) (denominator : ℕ) (hb : numerator.natAbs≤B) (hn : denominator≤N)
    (hd : cache.determinant.natAbs≤H) (hc : ∀ k,(cache.constant.read k).natAbs≤H)
    (hs : ∀ k,(cache.slope.read k).natAbs≤H) (k : Fin d) :
    RationalHeight (GeneralPaperRawAffineEvaluate.entry primitive W cache numerator denominator k).1
      (2*binaryWordWidth (cap H B N)) := by
  have ht := top_bound _ _ numerator denominator H B N (hc k) (hs k) hb hn
  have hBot := bottom_bound cache.determinant denominator H N hd hn
  have hTop : ((denominator:ℤ)*cache.constant.read k+numerator*cache.slope.read k).natAbs≤cap H B N := by
    unfold cap; omega
  have hBottom : ((denominator:ℤ)*cache.determinant).natAbs≤cap H B N := by
    have hh : N*H≤(N+B)*H := Nat.mul_le_mul_right H (Nat.le_add_right _ _)
    unfold cap; omega
  have hh := (GeneralPaperBasisStageSize.int_height _ _ hTop).div
    (GeneralPaperBasisStageSize.int_height _ _ hBottom)
  simpa only [GeneralPaperRawAffineEvaluate.entry,two_mul] using hh

theorem entry_work {d : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W H B N : ℕ)
    (cache : Data d) (numerator : ℤ) (denominator : ℕ) (hb : numerator.natAbs≤B) (hn : denominator≤N)
    (hd : cache.determinant.natAbs≤H) (hc : ∀ k,(cache.constant.read k).natAbs≤H)
    (hs : ∀ k,(cache.slope.read k).natAbs≤H) (k : Fin d) :
    (GeneralPaperRawAffineEvaluate.entry primitive W cache numerator denominator k).2≤
      32*(W+primitive (width H B N)) := by
  let M := cap H B N
  let Q := primitive (width H B N)
  let c := cache.constant.read k
  let s := cache.slope.read k
  let a := (denominator:ℤ)*c
  let b := numerator*s
  let top := a+b
  let bottom := (denominator:ℤ)*cache.determinant
  have hCaps : N≤M ∧ B≤M ∧ H≤M ∧ (N+B)*H≤M := by dsimp only [M,cap]; omega
  have hN : (denominator:ℤ).natAbs≤M := by simpa only [Int.natAbs_natCast] using hn.trans hCaps.1
  have hB := hb.trans hCaps.2.1
  have hC := (hc k).trans hCaps.2.2.1
  have hS := (hs k).trans hCaps.2.2.1
  have hDet := hd.trans hCaps.2.2.1
  have hA : a.natAbs≤M := by
    have hh := bottom_bound c denominator H N (hc k) hn
    have hm := Nat.mul_le_mul_right H (Nat.le_add_right N B)
    exact hh.trans (hm.trans hCaps.2.2.2)
  have hBS : b.natAbs≤M := by
    have hh : b.natAbs≤B*H := by dsimp only [b]; rw [Int.natAbs_mul]; exact Nat.mul_le_mul hb (hs k)
    have hm := Nat.mul_le_mul_right H (Nat.le_add_left B N)
    exact hh.trans (hm.trans hCaps.2.2.2)
  have hTop : top.natAbs≤M := (top_bound c s numerator denominator H B N (hc k) (hs k) hb hn).trans hCaps.2.2.2
  have hBottom : bottom.natAbs≤M := by
    have hm := Nat.mul_le_mul_right H (Nat.le_add_right N B)
    exact (bottom_bound _ _ _ _ hd hn).trans (hm.trans hCaps.2.2.2)
  have hPromote := hMono (show 1+binaryWordWidth M≤width H B N by dsimp only [width,M]; omega)
  have hMulA := binary_le primitive hMono (fun x y => x*y) (denominator:ℤ) c M hN hC hA
  have hMulB := binary_le primitive hMono (fun x y => x*y) numerator s M hB hS hBS
  have hAdd := binary_le primitive hMono (fun x y => x+y) a b M hA hBS hTop
  have hMulD := binary_le primitive hMono (fun x y => x*y) (denominator:ℤ) cache.determinant M hN hDet hBottom
  have hCastN := hMono (word_bound _ M hN)
  have hCastTop := hMono (word_bound _ M hTop)
  have hCastBottom := hMono (word_bound _ M hBottom)
  have hRatTop : rationalWordWidth (top:ℚ)≤width H B N := by
    exact (rationalWordWidth_of_height (GeneralPaperBasisStageSize.int_height top M hTop)).trans (by dsimp only [width,M]; omega)
  have hRatBottom : rationalWordWidth (bottom:ℚ)≤width H B N := by
    exact (rationalWordWidth_of_height (GeneralPaperBasisStageSize.int_height bottom M hBottom)).trans (by dsimp only [width,M]; omega)
  have hRatResult : rationalWordWidth ((top:ℚ)/(bottom:ℚ))≤width H B N := by
    have hh := rationalWordWidth_of_height (entry_height primitive W H B N cache numerator denominator hb hn hd hc hs k)
    change rationalWordWidth ((top:ℚ)/(bottom:ℚ))≤1+2*(2*binaryWordWidth (cap H B N)) at hh
    dsimp only [width]
    omega
  have hWriteTop := hMono hRatTop
  have hWriteBottom := hMono hRatBottom
  have hDiv := GeneralPaperRationalPrimitivePrice.binary_le primitive hMono (fun x y => x/y)
    (top:ℚ) (bottom:ℚ) (width H B N) hRatTop hRatBottom hRatResult
  change _≤32*(W+Q)
  change binary primitive (fun x y => x*y) (denominator:ℤ) c+
    binary primitive (fun x y => x*y) numerator s+binary primitive (fun x y => x+y) a b+
    binary primitive (fun x y => x*y) (denominator:ℤ) cache.determinant+
    primitive (word (denominator:ℤ))+primitive (word top)+primitive (word bottom)+
    primitive (rationalWordWidth (top:ℚ))+primitive (rationalWordWidth (bottom:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary primitive (fun x y => x/y) (top:ℚ) (bottom:ℚ)+16*W≤_
  omega

theorem work {d : ℕ} (model : RationalCostModel) (W H B N : ℕ) (hW : 1≤W)
    (hD : binaryWordWidth (d+1)≤W) (cache : Data d) (numerator : ℤ) (denominator : ℕ)
    (hb : numerator.natAbs≤B) (hn : denominator≤N) (hd : cache.determinant.natAbs≤H)
    (hc : ∀ k,(cache.constant.read k).natAbs≤H) (hs : ∀ k,(cache.slope.read k).natAbs≤H) :
    (GeneralPaperRawAffineEvaluate.run true model W cache numerator denominator).2≤
      256*(d+1)*(W+model.rat (width H B N)) := by
  let Q := model.rat (width H B N)
  have hEach := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) =>
    entry_work model.rat model.monotone W H B N cache numerator denominator hb hn hd hc hs k)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hEach
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (GeneralPaperRawAffineEvaluate.entry model.rat W cache numerator denominator)
  have ho : 6*W+10*1*binaryWordWidth (d+1)+28≤44*W := by omega
  have hO := Nat.mul_le_mul_left (d+1) ho
  have hN : denominator≤cap H B N := by unfold cap; omega
  have hp := model.monotone (show 1+binaryWordWidth denominator≤width H B N from
    (Nat.add_le_add_left (binaryWordWidth_mono hN) 1).trans (by unfold width; omega))
  change (PaperIndexedArrayConstruction.run (fun w => w) W
    (GeneralPaperRawAffineEvaluate.entry model.rat W cache numerator denominator)).2+
      model.rat (1+binaryWordWidth denominator)+16*W≤256*(d+1)*(W+Q)
  change _≤d*(32*(W+Q)) at hEach
  nlinarith only [hEach,hh,hO,hp,Nat.zero_le (d*W),Nat.zero_le (d*Q)]

theorem bounded {d : ℕ} (model : RationalCostModel) (W H B N : ℕ) (cache : Data d)
    (numerator : ℤ) (denominator : ℕ) (hDen : 0<denominator) (hDet : cache.determinant≠0)
    (hb : numerator.natAbs≤B) (hn : denominator≤N) (hc : ∀ k,(cache.constant.read k).natAbs≤H)
    (hs : ∀ k,(cache.slope.read k).natAbs≤H) (k : Fin d) :
    Bounded (denominator*cache.determinant.natAbs) ((N+B)*H)
      ((GeneralPaperRawAffineEvaluate.run true model W cache numerator denominator).1.read k) := by
  rw [GeneralPaperRawAffineEvaluate.data]
  refine ⟨GeneralPaperBasisAffineEvaluate.lattice cache hDet numerator denominator hDen k,?_⟩
  rw [GeneralPaperBasisAffineEvaluate.read]
  have hnz : (denominator:ℤ)≠0 := by exact_mod_cast hDen.ne'
  exact abs_int_fraction _ _ (mul_ne_zero hnz hDet) _
    (top_bound _ _ _ _ _ _ _ (hc k) (hs k) hb hn)

theorem threshold_bounded (numerator : ℤ) (denominator : ℕ) (hDen : 0<denominator)
    (D B : ℕ) (hb : numerator.natAbs≤B) :
    Bounded (denominator*D) B ((numerator:ℚ)/(denominator:ℚ)) := by
  have hnz : (denominator:ℤ)≠0 := by exact_mod_cast hDen.ne'
  have hLat : OnRationalLattice denominator ((numerator:ℚ)/(denominator:ℚ)) := by
    have hh := FinitePolytopeRationalWitness.denominator_divInt (numerator:=numerator) (denominator:=(denominator:ℤ)) hnz
    simpa only [OnRationalLattice,Int.natAbs_natCast,Int.cast_natCast] using hh
  refine ⟨hLat.enlarge (dvd_mul_right denominator D),?_⟩
  simpa only [Int.cast_natCast] using abs_int_fraction numerator (denominator:ℤ) hnz B hb

end Blotto.GeneralPaperRawAffineBits
