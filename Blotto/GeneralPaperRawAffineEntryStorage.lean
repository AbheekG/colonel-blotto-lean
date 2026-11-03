import Blotto.GeneralPaperSourceBasisAffineStorageReachedRates

/-! Literal raw affine scalar storage before any acceptance check.
All integer inputs/products/sum/denominator, casts/division/result and
primitive scratch are retained. Every primitive charge and prefix partial
price is counted, without reduction, feasibility or nonzero assumptions. -/
namespace Blotto.GeneralPaperRawAffineEntryStorage
open GeneralPaperBasisAffineData GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits)
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def operands {d : ℕ} (cache : Data d) (numerator : ℤ) (denominator : ℕ) (k : Fin d) : List ℤ :=
  let n : ℤ := denominator
  let c := cache.constant.read k
  let s := cache.slope.read k
  [n,c,s,numerator,cache.determinant,n*c,numerator*s,n*c+numerator*s,n*cache.determinant]

theorem operands_bound {d : ℕ} (H B N : ℕ) (cache : Data d) (numerator : ℤ) (denominator : ℕ)
    (hb : numerator.natAbs≤B) (hn : denominator≤N) (hd : cache.determinant.natAbs≤H)
    (hc : ∀ k,(cache.constant.read k).natAbs≤H) (hs : ∀ k,(cache.slope.read k).natAbs≤H) (k : Fin d) :
    ∀ z∈operands cache numerator denominator k,z.natAbs≤GeneralPaperRawAffineBits.cap H B N := by
  let M := GeneralPaperRawAffineBits.cap H B N
  have hN : (denominator:ℤ).natAbs≤M := by rw [Int.natAbs_natCast]; unfold M GeneralPaperRawAffineBits.cap; omega
  have hB : numerator.natAbs≤M := by unfold M GeneralPaperRawAffineBits.cap; omega
  have hDet : cache.determinant.natAbs≤M := by unfold M GeneralPaperRawAffineBits.cap; omega
  have hC : (cache.constant.read k).natAbs≤M := by have h:=hc k; unfold M GeneralPaperRawAffineBits.cap; omega
  have hS : (cache.slope.read k).natAbs≤M := by have h:=hs k; unfold M GeneralPaperRawAffineBits.cap; omega
  have hNH := GeneralPaperRawAffineBits.bottom_bound (cache.constant.read k) denominator H N (hc k) hn
  have hBH : (numerator*cache.slope.read k).natAbs≤B*H := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul hb (hs k)
  have hNH' := Nat.mul_le_mul_right H (Nat.le_add_right N B)
  have hBH' := Nat.mul_le_mul_right H (Nat.le_add_left B N)
  have hTop := GeneralPaperRawAffineBits.top_bound (cache.constant.read k) (cache.slope.read k) numerator denominator H B N (hc k) (hs k) hb hn
  have hBottom := GeneralPaperRawAffineBits.bottom_bound cache.determinant denominator H N hd hn
  intro z hz
  simp only [operands,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals unfold M GeneralPaperRawAffineBits.cap at *; omega

def charges {d : ℕ} (model : RationalCostModel) (cache : Data d) (numerator : ℤ) (denominator : ℕ) (k : Fin d) : List ℕ :=
  let n : ℤ := denominator
  let c := cache.constant.read k
  let s := cache.slope.read k
  let a := n*c
  let b := numerator*s
  let top := a+b
  let bottom := n*cache.determinant
  [GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x*y) n c,
    GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x*y) numerator s,
    GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x+y) a b,
    GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x*y) n cache.determinant,
    model.rat (GeneralPaperIntegerPrimitivePrice.word n),model.rat (GeneralPaperIntegerPrimitivePrice.word top),
    model.rat (GeneralPaperIntegerPrimitivePrice.word bottom),model.rat (rationalWordWidth (top:ℚ)),
    model.rat (rationalWordWidth (bottom:ℚ)),GeneralPaperRationalPrimitivePrice.binary model.rat (fun x y => x/y) (top:ℚ) (bottom:ℚ)]
def primitiveScratch {d : ℕ} (model : RationalCostModel) (cache : Data d) (numerator : ℤ) (denominator : ℕ) (k : Fin d) : ℕ :=
  (charges model cache numerator denominator k).sum

theorem work_eq {d : ℕ} (model : RationalCostModel) (W : ℕ) (cache : Data d) (numerator : ℤ) (denominator : ℕ) (k : Fin d) :
    (GeneralPaperRawAffineEvaluate.entry model.rat W cache numerator denominator k).2=
      primitiveScratch model cache numerator denominator k+16*W := by
  simp only [GeneralPaperRawAffineEvaluate.entry,primitiveScratch,charges,List.sum_cons,List.sum_nil,Nat.add_zero]
  omega

theorem member_sum (xs : List ℕ) (a : ℕ) (ha : a∈xs) : a≤xs.sum := by
  induction xs with
  | nil => cases ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with rfl|h
    · exact Nat.le_add_right _ _
    · exact (ih h).trans (Nat.le_add_left _ _)

theorem take_sum (xs : List ℕ) (k : ℕ) : (xs.take k).sum≤xs.sum := by
  induction xs generalizing k with
  | nil => simp only [List.take_nil,List.sum_nil,le_refl]
  | cons a xs ih =>
    cases k with
    | zero => simp only [List.take_zero,List.sum_nil]; exact Nat.zero_le _
    | succ k => simpa only [List.take_succ_cons,List.sum_cons] using Nat.add_le_add_left (ih k) a

def controls {d : ℕ} (model : RationalCostModel) (W : ℕ) (cache : Data d) (numerator : ℤ) (denominator : ℕ) (k : Fin d) : List ℕ :=
  let cs := charges model cache numerator denominator k
  [d,k.val,16*W,(GeneralPaperRawAffineEvaluate.entry model.rat W cache numerator denominator k).2]++cs++
    (List.range 11).map (fun i => (cs.take i).sum)
def price (model : RationalCostModel) (W R : ℕ) : ℕ := 32*(W+model.rat R)
def metadataCap (model : RationalCostModel) (W d R : ℕ) : ℕ := d+2+3*price model W R+16*W
def window {d : ℕ} (model : RationalCostModel) (W : ℕ) (cache : Data d) (numerator : ℤ) (denominator : ℕ) (k : Fin d) : ℕ :=
  let top := (denominator:ℤ)*cache.constant.read k+numerator*cache.slope.read k
  let bottom := (denominator:ℤ)*cache.determinant
  let result := GeneralPaperRawAffineEvaluate.entry model.rat W cache numerator denominator k
  listFootprint W integerBits (operands cache numerator denominator k)+natBits denominator+
    listFootprint W rationalWordWidth [(top:ℚ),(bottom:ℚ),result.1]+primitiveScratch model cache numerator denominator k+
    fields W (controls model W cache numerator denominator k)+256*W
def profile (model : RationalCostModel) (W d R : ℕ) : ℕ :=
  9*(R+2*W)+32*W+R+3*(R+2*W)+32*W+32*model.rat R+25*(natBits (metadataCap model W d R)+W)+288*W

theorem bounded {d : ℕ} (model : RationalCostModel) (W H B N R : ℕ) (cache : Data d) (numerator : ℤ) (denominator : ℕ)
    (hb : numerator.natAbs≤B) (hn : denominator≤N) (hd : cache.determinant.natAbs≤H)
    (hc : ∀ k,(cache.constant.read k).natAbs≤H) (hs : ∀ k,(cache.slope.read k).natAbs≤H)
    (hR : GeneralPaperRawAffineBits.width H B N≤R) (k : Fin d) : window model W cache numerator denominator k≤profile model W d R := by
  let M := GeneralPaperRawAffineBits.cap H B N
  let cs := charges model cache numerator denominator k
  let result := GeneralPaperRawAffineEvaluate.entry model.rat W cache numerator denominator k
  let top := (denominator:ℤ)*cache.constant.read k+numerator*cache.slope.read k
  let bottom := (denominator:ℤ)*cache.determinant
  have hSmall : 1+binaryWordWidth M≤R := by dsimp only [M]; unfold GeneralPaperRawAffineBits.width at hR; omega
  have hInt (z) (hz : z∈operands cache numerator denominator k) : integerBits z≤R :=
    (Nat.add_le_add_left (binaryWordWidth_mono (operands_bound H B N cache numerator denominator hb hn hd hc hs k z hz)) 1).trans hSmall
  have hOperands := list_bound W R integerBits (operands cache numerator denominator k) hInt
  have hLength : (operands cache numerator denominator k).length=9 := rfl
  rw [hLength] at hOperands
  have hRawN : natBits denominator≤R := by
    have hN : denominator≤M := by dsimp only [M]; unfold GeneralPaperRawAffineBits.cap; omega
    exact (Nat.add_le_add_left (binaryWordWidth_mono hN) 1).trans hSmall
  have hTop : top∈operands cache numerator denominator k := by simp only [operands,top,List.mem_cons,List.not_mem_nil,or_false]; tauto
  have hBottom : bottom∈operands cache numerator denominator k := by simp only [operands,bottom,List.mem_cons,List.not_mem_nil,or_false]; tauto
  have hRat (z : ℤ) (hz : z∈operands cache numerator denominator k) : rationalWordWidth (z:ℚ)≤R := by
    have hh := GeneralPaperBasisStageSize.int_height z M (operands_bound H B N cache numerator denominator hb hn hd hc hs k z hz)
    exact (rationalWordWidth_of_height hh).trans (by dsimp only [M]; unfold GeneralPaperRawAffineBits.width at hR; omega)
  have hResult := (rationalWordWidth_of_height (GeneralPaperRawAffineBits.entry_height model.rat W H B N cache numerator denominator hb hn hd hc hs k)).trans
    (show 1+2*(2*binaryWordWidth (GeneralPaperRawAffineBits.cap H B N))≤R by unfold GeneralPaperRawAffineBits.width at hR; omega)
  have hRationals := list_bound W R rationalWordWidth [(top:ℚ),(bottom:ℚ),result.1] (by
    intro q hq; simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl
    · exact hRat top hTop
    · exact hRat bottom hBottom
    · exact hResult)
  change listFootprint W rationalWordWidth _≤3*(R+2*W)+32*W at hRationals
  have hScratch : primitiveScratch model cache numerator denominator k≤32*model.rat R := by
    have h := GeneralPaperRawAffineBits.entry_work model.rat model.monotone 0 H B N cache numerator denominator hb hn hd hc hs k
    rw [work_eq] at h
    simp only [Nat.mul_zero,Nat.add_zero,Nat.zero_add] at h
    exact h.trans (Nat.mul_le_mul_left 32 (model.monotone hR))
  have hWork : result.2≤price model W R :=
    (GeneralPaperRawAffineBits.entry_work model.rat model.monotone W H B N cache numerator denominator hb hn hd hc hs k).trans
      (Nat.mul_le_mul_left 32 (Nat.add_le_add_left (model.monotone hR) W))
  have hShape : result.2=cs.sum+16*W := work_eq model W cache numerator denominator k
  dsimp only [result,cs] at hWork hShape
  have hCount : (controls model W cache numerator denominator k).length=25 := by
    simp only [controls,List.length_append,List.length_cons,List.length_nil,List.length_map,List.length_range,charges]
  have hf := fields_bound W (natBits (metadataCap model W d R)) (controls model W cache numerator denominator k) (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    unfold controls at ha
    dsimp only at ha
    rcases List.mem_append.mp ha with ha|ha
    · rcases List.mem_append.mp ha with ha|ha
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        unfold metadataCap
        rcases ha with rfl|rfl|rfl|rfl <;> omega
      · have h := member_sum (charges model cache numerator denominator k) a ha
        unfold metadataCap; omega
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
      have h := take_sum (charges model cache numerator denominator k) i
      unfold metadataCap; omega)
  rw [hCount] at hf
  unfold window profile
  dsimp only
  dsimp only [top,bottom,result] at hRationals hf
  omega

end Blotto.GeneralPaperRawAffineEntryStorage
