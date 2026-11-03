import Blotto.GeneralPaperRawAffineEntryStorage

/-! Complete native raw affine evaluation. Original unreduced fraction,
full rational output/fill buffers, all scalar windows and six outer partial
fields coexist. The existing affine-cache owner remains with the caller.
No feasibility, denominator reduction or nonzero premise is used. -/
namespace Blotto.GeneralPaperRawAffineStorage
open GeneralPaperBasisAffineData GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (W d R : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.workCap W d (GeneralPaperRawAffineEntryStorage.price model W R)+model.rat R+16*W
def metadataCap (model : RationalCostModel) (W d R : ℕ) : ℕ := d+1+3*price model W d R+16*W
def window {d : ℕ} (model : RationalCostModel) (W copied : ℕ) (cache : Data d) (numerator : ℤ) (denominator : ℕ) : ℕ :=
  let callback := GeneralPaperRawAffineEvaluate.entry model.rat W cache numerator denominator
  let filled := PaperIndexedArrayConstruction.run (fun w => w) W callback
  let result := GeneralPaperRawAffineEvaluate.run true model W cache numerator denominator
  let copy := model.rat (1+binaryWordWidth denominator)
  integerBits numerator+natBits denominator+arrayFootprint W rationalWordWidth result.1+
    GeneralPaperNativePayloadFillStorage.window W rationalWordWidth callback
      (GeneralPaperRawAffineEntryStorage.window model W cache numerator denominator) (min copied d) (Nat.min_le_right _ _)+
    copy+fields W [d,filled.2,copy,16*W,result.2,filled.2+copy]+128*W
def profile (model : RationalCostModel) (W d R : ℕ) : ℕ :=
  2*R+arrayProfile W d R+GeneralPaperNativePayloadFillStorage.profile W R d (GeneralPaperRawAffineEntryStorage.price model W R)
    (GeneralPaperRawAffineEntryStorage.profile model W d R)+model.rat R+6*(natBits (metadataCap model W d R)+W)+160*W

theorem entry_word {d : ℕ} (model : RationalCostModel) (W H B N R : ℕ) (cache : Data d) (numerator : ℤ) (denominator : ℕ)
    (hb : numerator.natAbs≤B) (hn : denominator≤N) (hd : cache.determinant.natAbs≤H)
    (hc : ∀ k,(cache.constant.read k).natAbs≤H) (hs : ∀ k,(cache.slope.read k).natAbs≤H)
    (hR : GeneralPaperRawAffineBits.width H B N≤R) (k : Fin d) :
    rationalWordWidth (GeneralPaperRawAffineEvaluate.entry model.rat W cache numerator denominator k).1≤R :=
  (rationalWordWidth_of_height (GeneralPaperRawAffineBits.entry_height model.rat W H B N cache numerator denominator hb hn hd hc hs k)).trans
    (by unfold GeneralPaperRawAffineBits.width at hR; omega)

theorem bounded {d : ℕ} (model : RationalCostModel) (W copied H B N R : ℕ) (cache : Data d) (numerator : ℤ) (denominator : ℕ)
    (hb : numerator.natAbs≤B) (hn : denominator≤N) (hd : cache.determinant.natAbs≤H)
    (hc : ∀ k,(cache.constant.read k).natAbs≤H) (hs : ∀ k,(cache.slope.read k).natAbs≤H)
    (hR : GeneralPaperRawAffineBits.width H B N≤R) (hW : 1≤W) (hD : binaryWordWidth (d+1)≤W) :
    window model W copied cache numerator denominator≤profile model W d R := by
  let callback := GeneralPaperRawAffineEvaluate.entry model.rat W cache numerator denominator
  let filled := PaperIndexedArrayConstruction.run (fun w => w) W callback
  let result := GeneralPaperRawAffineEvaluate.run true model W cache numerator denominator
  let copy := model.rat (1+binaryWordWidth denominator)
  let M := GeneralPaperRawAffineBits.cap H B N
  have hSmall : 1+binaryWordWidth M≤R := by dsimp only [M]; unfold GeneralPaperRawAffineBits.width at hR; omega
  have hNum : integerBits numerator≤R :=
    (Nat.add_le_add_left (binaryWordWidth_mono (show numerator.natAbs≤M by dsimp only [M]; unfold GeneralPaperRawAffineBits.cap; omega)) 1).trans hSmall
  have hDen : natBits denominator≤R :=
    (Nat.add_le_add_left (binaryWordWidth_mono (show denominator≤M by dsimp only [M]; unfold GeneralPaperRawAffineBits.cap; omega)) 1).trans hSmall
  have hCopy : copy≤model.rat R := model.monotone hDen
  have hC (i) : (callback i).2≤GeneralPaperRawAffineEntryStorage.price model W R :=
    (GeneralPaperRawAffineBits.entry_work model.rat model.monotone W H B N cache numerator denominator hb hn hd hc hs i).trans
      (Nat.mul_le_mul_left 32 (Nat.add_le_add_left (model.monotone hR) W))
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W R (GeneralPaperRawAffineEntryStorage.price model W R)
    (GeneralPaperRawAffineEntryStorage.profile model W d R) rationalWordWidth callback
    (GeneralPaperRawAffineEntryStorage.window model W cache numerator denominator)
    (entry_word model W H B N R cache numerator denominator hb hn hd hc hs hR) hC
    (GeneralPaperRawAffineEntryStorage.bounded model W H B N R cache numerator denominator hb hn hd hc hs hR)
    hW hD (min copied d) (Nat.min_le_right _ _)
  have hFilled := GeneralPaperNativePayloadFillStorage.prefix_work W (GeneralPaperRawAffineEntryStorage.price model W R) callback hC hW hD d le_rfl
  change filled.2≤GeneralPaperNativePayloadFillStorage.workCap W d (GeneralPaperRawAffineEntryStorage.price model W R) at hFilled
  have hShape : result.2=filled.2+copy+16*W := rfl
  have hWork : result.2≤price model W d R := by unfold price; omega
  have hReturned := GeneralPaperEncodedBasisStorage.array_bound W R rationalWordWidth result.1 (by
    intro i
    change rationalWordWidth (filled.1.read i)≤R
    rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact entry_word model W H B N R cache numerator denominator hb hn hd hc hs hR i)
  have hf := fields_bound W (natBits (metadataCap model W d R)) [d,filled.2,copy,16*W,result.2,filled.2+copy] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    unfold metadataCap
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (metadataCap model W d R)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [callback,filled,result,copy] at hFill hReturned hCopy hf
  omega

end Blotto.GeneralPaperRawAffineStorage
