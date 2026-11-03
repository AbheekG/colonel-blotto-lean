import Blotto.GeneralPaperNativeGrowingQuotientStorage

/-! Literal occurrence-block division, also called once to compute the
block size. The native adaptive quotient peak, increment primitive, result
label, constructed fuel and all wrapper price prefixes coexist. Bounds
use an operand magnitude cap and actual depth, with no division oracle. -/
namespace Blotto.GeneralPaperNativeBlockLabelStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def magnitude (N B : ℕ) : ℕ := 2*(N+B+1)
def price (model : RationalCostModel) (W N B : ℕ) : ℕ :=
  GeneralPaperNativeGrowingQuotientStorage.workCap model W (magnitude N B) (binaryWordWidth N)+
    2*model.rat (1+binaryWordWidth (N+1))+32*W
def metadataCap (model : RationalCostModel) (W N B : ℕ) : ℕ := N+B+price model W N B+32*W+1
def window {K B : ℕ} (model : RationalCostModel) (W : ℕ) (hB : 0<B) (r : Fin (K*B)) : ℕ :=
  let divided := GeneralPaperGrowingQuotientBits.run model.rat W r.val B (r.val+1)
  let inc := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) r.val 1
  let result := GeneralPaperNativeBlockLabel.run model.rat W hB r
  GeneralPaperNativeGrowingQuotientStorage.peak model W r.val B (r.val+1)+
    natBits (r.val+1)+natBits result.1.val+inc+
    fields W [r.val,B,r.val+1,result.1.val,divided.2,inc,result.2,divided.2+inc,32*W]+128*W
def profile (model : RationalCostModel) (W N B : ℕ) : ℕ :=
  GeneralPaperNativeGrowingQuotientStorage.profile model W (magnitude N B) (N+1) (binaryWordWidth N)+
    2*natBits (N+1)+2*model.rat (1+binaryWordWidth (N+1))+
    9*(natBits (metadataCap model W N B)+W)+160*W

theorem work {K B : ℕ} (model : RationalCostModel) (W N : ℕ) (hB : 0<B) (r : Fin (K*B)) (hr : r.val≤N) :
    (GeneralPaperNativeBlockLabel.run model.rat W hB r).2≤price model W N B := by
  have hDepth := (GeneralPaperNativeBlockLabel.depth model.rat W r.val B hB).trans (binaryWordWidth_mono hr)
  have hDiv := GeneralPaperNativeGrowingQuotientStorage.work_bound model W r.val B (r.val+1)
    (magnitude N B) (binaryWordWidth N) hB (by unfold magnitude; omega) (by unfold magnitude; omega) hDepth
  have hInc := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b) r.val 1 (N+1)
    (by omega) (by omega) (by omega)
  change (GeneralPaperGrowingQuotientBits.run model.rat W r.val B (r.val+1)).2+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) r.val 1+32*W≤_
  unfold price
  omega

theorem bounded {K B : ℕ} (model : RationalCostModel) (W N : ℕ) (hB : 0<B) (r : Fin (K*B)) (hr : r.val≤N) :
    window model W hB r≤profile model W N B := by
  let divided := GeneralPaperGrowingQuotientBits.run model.rat W r.val B (r.val+1)
  let inc := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) r.val 1
  let result := GeneralPaperNativeBlockLabel.run model.rat W hB r
  have hDepth := (GeneralPaperNativeBlockLabel.depth model.rat W r.val B hB).trans (binaryWordWidth_mono hr)
  have hPeak := GeneralPaperNativeGrowingQuotientStorage.bounded model W r.val B (r.val+1)
    (magnitude N B) (N+1) (binaryWordWidth N) hB (by unfold magnitude; omega) (by unfold magnitude; omega) (by omega) hDepth
  have hInc := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b) r.val 1 (N+1)
    (by omega) (by omega) (by omega)
  change inc≤2*model.rat (1+binaryWordWidth (N+1)) at hInc
  have hResult := work model W N hB r hr
  change result.2≤price model W N B at hResult
  have hShape : result.2=divided.2+inc+32*W := rfl
  have hLabel : result.1.val≤N :=
    (GeneralPaperNativeGrowingQuotientStorage.result_bounds model W r.val B (r.val+1) hB).1.trans hr
  have hn : natBits (r.val+1)≤natBits (N+1) := Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
  have hq : natBits result.1.val≤natBits (N+1) := Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
  have hf := fields_bound W (natBits (metadataCap model W N B))
    [r.val,B,r.val+1,result.1.val,divided.2,inc,result.2,divided.2+inc,32*W] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change fields W _≤9*(natBits (metadataCap model W N B)+W)+32*W at hf
  change GeneralPaperNativeGrowingQuotientStorage.peak model W r.val B (r.val+1)+
    natBits (r.val+1)+natBits result.1.val+inc+
    fields W [r.val,B,r.val+1,result.1.val,divided.2,inc,result.2,divided.2+inc,32*W]+128*W≤_
  unfold profile
  omega

theorem profile_mono (model : RationalCostModel) (W n N b B : ℕ) (hn : n≤N) (hb : b≤B) :
    profile model W n b≤profile model W N B := by
  unfold profile metadataCap price magnitude GeneralPaperNativeGrowingQuotientStorage.profile
    GeneralPaperNativeGrowingQuotientStorage.frameProfile GeneralPaperNativeGrowingQuotientStorage.metadataCap
    GeneralPaperNativeGrowingQuotientStorage.workCap natBits
  gcongr <;> (apply model.monotone; gcongr)

theorem price_mono (model : RationalCostModel) (W n N b B : ℕ) (hn : n≤N) (hb : b≤B) :
    price model W n b≤price model W N B := by
  unfold price magnitude GeneralPaperNativeGrowingQuotientStorage.workCap
  gcongr <;> (apply model.monotone; gcongr)

end Blotto.GeneralPaperNativeBlockLabelStorage
