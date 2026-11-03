import Blotto.GeneralPaperSourceQuantizationParentReachedRates

/-! Actual unit-source caller: retained rational rows and own budget,
physical quantized/normalized columns and native child/partial/return
counters coexist. Child work caps are erased proof parameters; no cost
oracle is supplied to the native routine, and no whole-child scratch is used. -/
namespace Blotto.GeneralPaperUnitSourceCallerStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEnclosingSourceOwners
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def price (W P Q : ℕ) : ℕ := P+Q+64*W
def metadataCap (W T m K P Q : ℕ) : ℕ := T+m+K+price W P Q+64*W+1
def window {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (budget : ℚ) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) : ℕ :=
  let quantized := GeneralPaperNativeDivisibleColumns.run model.rat (fun w => w) W hT hK hDiv rows
  let normalized := GeneralPaperNativeDictionaryNormalize.run model.rat (fun w => w) W budget quantized.1
  let result := GeneralPaperNativeUnitSourceJoin.run model.rat (fun w => w) W hT hK hDiv budget rows
  rowsFoot W rows+rationalWordWidth budget+columnsFoot W quantized.1+columnsFoot W normalized.1+
    fields W [T,m,K,quantized.2,normalized.2,result.2,quantized.2+normalized.2,64*W]+128*W
def profile (W T m K R P Q : ℕ) : ℕ :=
  rowsProfile W T m R+R+2*columnsProfile W T m K R+8*(natBits (metadataCap W T m K P Q)+W)+160*W

theorem work {T m K : ℕ} (model : RationalCostModel) (W P Q : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (budget : ℚ) (rows : FixedArrayTable T (FixedArrayTable m ℚ))
    (hP : (GeneralPaperNativeDivisibleColumns.run model.rat (fun w => w) W hT hK hDiv rows).2≤P)
    (hQ : (GeneralPaperNativeDictionaryNormalize.run model.rat (fun w => w) W budget
      (GeneralPaperNativeDivisibleColumns.run model.rat (fun w => w) W hT hK hDiv rows).1).2≤Q) :
    (GeneralPaperNativeUnitSourceJoin.run model.rat (fun w => w) W hT hK hDiv budget rows).2≤price W P Q :=
  Nat.add_le_add_right (Nat.add_le_add hP hQ) _

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W R P Q : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (budget : ℚ) (rows : FixedArrayTable T (FixedArrayTable m ℚ))
    (hb : rationalWordWidth budget≤R) (hv : ∀ i j,rationalWordWidth ((rows.read i).read j)≤R)
    (hOld : columnsFoot W (GeneralPaperNativeDivisibleColumns.run model.rat (fun w => w) W hT hK hDiv rows).1≤columnsProfile W T m K R)
    (hNew : columnsFoot W (GeneralPaperNativeUnitSourceJoin.run model.rat (fun w => w) W hT hK hDiv budget rows).1≤columnsProfile W T m K R)
    (hP : (GeneralPaperNativeDivisibleColumns.run model.rat (fun w => w) W hT hK hDiv rows).2≤P)
    (hQ : (GeneralPaperNativeDictionaryNormalize.run model.rat (fun w => w) W budget
      (GeneralPaperNativeDivisibleColumns.run model.rat (fun w => w) W hT hK hDiv rows).1).2≤Q) :
    window model W hT hK hDiv budget rows≤profile W T m K R P Q := by
  let quantized := GeneralPaperNativeDivisibleColumns.run model.rat (fun w => w) W hT hK hDiv rows
  let normalized := GeneralPaperNativeDictionaryNormalize.run model.rat (fun w => w) W budget quantized.1
  let result := GeneralPaperNativeUnitSourceJoin.run model.rat (fun w => w) W hT hK hDiv budget rows
  have hRows := rows_bound W R rows hv
  change columnsFoot W quantized.1≤columnsProfile W T m K R at hOld
  change columnsFoot W normalized.1≤columnsProfile W T m K R at hNew
  change quantized.2≤P at hP
  change normalized.2≤Q at hQ
  have hShape : result.2=quantized.2+normalized.2+64*W := rfl
  have hf := fields_bound W (natBits (metadataCap W T m K P Q))
    [T,m,K,quantized.2,normalized.2,result.2,quantized.2+normalized.2,64*W] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap price; omega)
  change fields W _≤8*(natBits (metadataCap W T m K P Q)+W)+32*W at hf
  change rowsFoot W rows+rationalWordWidth budget+columnsFoot W quantized.1+columnsFoot W normalized.1+
    fields W [T,m,K,quantized.2,normalized.2,result.2,quantized.2+normalized.2,64*W]+128*W≤_
  unfold profile
  omega

end Blotto.GeneralPaperUnitSourceCallerStorage
