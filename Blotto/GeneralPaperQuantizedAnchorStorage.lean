import Blotto.GeneralPaperSourceDictionaryNormalizationReachedRates

/-! Literal native K-anchor construction from retained sorted references.
The zero branch and predecessor branch share a conservative constant scalar
reservation. Original order/value arrays, full native fill/return buffers,
recursive payload/work fields and one active scalar window coexist. -/
namespace Blotto.GeneralPaperQuantizedAnchorStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

def operandWord (T K : ℕ) : ℕ := 1+binaryWordWidth (2*T+K+2)
def callbackPrice (model : RationalCostModel) (W T K : ℕ) : ℕ := 5*model.rat (operandWord T K)+64*W
def price (model : RationalCostModel) (W T K : ℕ) : ℕ := GeneralPaperNativePayloadFillStorage.workCap W K (callbackPrice model W T K)
def scalarCap (model : RationalCostModel) (W T K : ℕ) : ℕ := 2*T+K+2+callbackPrice model W T K
def scalarControls {K B : ℕ} (model : RationalCostModel) (W : ℕ) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (value : FixedArrayTable (K*B) ℚ) (l : Fin K) : List ℕ :=
  let test := GeneralPaperIntegerWordPrice.compare model.rat l.val 0
  let mul := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) l.val B
  let sub := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a-b) (l.val*B) 1
  let target := if l.val=0 then 0 else (order.read (GeneralPaperBlockQuantization.predecessor hB l)).val
  [K,B,l.val,l.val*B,l.val*B-1,target,test,mul,sub,
    (GeneralPaperNativeQuantizedAnchors.entry model.rat W hB order value l).2,64*W,test+mul,test+mul+sub,
    GeneralPaperFinalStaticLoopStorage.bit (decide (l.val=0))]
def scalarWindow {K B : ℕ} (model : RationalCostModel) (W : ℕ) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (value : FixedArrayTable (K*B) ℚ) (l : Fin K) : ℕ :=
  rationalWordWidth (GeneralPaperNativeQuantizedAnchors.entry model.rat W hB order value l).1+
    GeneralPaperIntegerWordPrice.compare model.rat l.val 0+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) l.val B+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a-b) (l.val*B) 1+
    fields W (scalarControls model W hB order value l)+128*W
def scalarProfile (model : RationalCostModel) (W T K R : ℕ) : ℕ :=
  R+5*model.rat (operandWord T K)+14*(natBits (scalarCap model W T K)+W)+160*W
def metadataCap (model : RationalCostModel) (W T K : ℕ) : ℕ := T+K+price model W T K+64*W+1
def window {K B : ℕ} (model : RationalCostModel) (W : ℕ) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (value : FixedArrayTable (K*B) ℚ) (count : ℕ) (hc : count≤K) : ℕ :=
  arrayFootprint W (fun i : Fin (K*B) => natBits i.val) order+arrayFootprint W rationalWordWidth value+natBits B+
    GeneralPaperNativePayloadFillStorage.window W rationalWordWidth (GeneralPaperNativeQuantizedAnchors.entry model.rat W hB order value)
      (scalarWindow model W hB order value) count hc+
    fields W [K,B,(GeneralPaperNativeQuantizedAnchors.run model.rat (fun w => w) W hB order value).2,64*W]+128*W
def profile (model : RationalCostModel) (W T K R : ℕ) : ℕ :=
  arrayProfile W T (natBits T)+arrayProfile W T R+operandWord T K+
    GeneralPaperNativePayloadFillStorage.profile W R K (callbackPrice model W T K) (scalarProfile model W T K R)+
    4*(natBits (metadataCap model W T K)+W)+160*W

theorem entry_word {K B : ℕ} (model : RationalCostModel) (W R : ℕ) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (value : FixedArrayTable (K*B) ℚ)
    (hR : 3≤R) (hv : ∀ i,rationalWordWidth (value.read i)≤R) (l : Fin K) :
    rationalWordWidth (GeneralPaperNativeQuantizedAnchors.entry model.rat W hB order value l).1≤R := by
  unfold GeneralPaperNativeQuantizedAnchors.entry
  split
  · exact (show rationalWordWidth (0:ℚ)=3 by decide).le.trans hR
  · exact hv _

theorem scalar_bound {K B : ℕ} (model : RationalCostModel) (W R : ℕ) (hK : 0<K) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (value : FixedArrayTable (K*B) ℚ)
    (hR : 3≤R) (hv : ∀ i,rationalWordWidth (value.read i)≤R) (l : Fin K) :
    scalarWindow model W hB order value l≤scalarProfile model W (K*B) K R := by
  let N := 2*(K*B)+K+2
  have hBcap : B≤K*B := by nlinarith only [hK]
  have hMul : l.val*B≤K*B := Nat.mul_le_mul_right B l.isLt.le
  have hL : l.val≤N := by unfold N; omega
  have hBW : B≤N := by unfold N; omega
  have h1 : 1≤N := by unfold N; omega
  have hQ : 1+binaryWordWidth N=operandWord (K*B) K := rfl
  have hTest := GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone l.val 0 (operandWord (K*B) K)
    ((Nat.add_le_add_left (binaryWordWidth_mono hL) 1).trans_eq hQ)
    ((Nat.add_le_add_left (binaryWordWidth_mono (Nat.zero_le N)) 1).trans_eq hQ)
  have hP := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b) l.val B N hL hBW (by unfold N; omega)
  have hS := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a-b) (l.val*B) 1 N (by unfold N; omega) h1 (by unfold N; omega)
  rw [hQ] at hP hS
  have hEntry := GeneralPaperNativeQuantizedAnchors.entry_work model.rat model.monotone W hB order value l
  have hWidth : 1+binaryWordWidth (K*B+B+1)≤operandWord (K*B) K := Nat.add_le_add_left (binaryWordWidth_mono (show K*B+B+1≤2*(K*B)+K+2 by omega)) 1
  have hEntry' := hEntry.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 5 (model.monotone hWidth)) _)
  have hValue := entry_word model W R hB order value hR hv l
  have hTarget : (if l.val=0 then 0 else (order.read (GeneralPaperBlockQuantization.predecessor hB l)).val)≤K*B := by
    split
    · exact Nat.zero_le _
    · exact (order.read _).isLt.le
  have hBit := GeneralPaperFinalStaticLoopStorage.bit_bound (decide (l.val=0))
  have hf := fields_bound W (natBits (scalarCap model W (K*B) K)) (scalarControls model W hB order value l) (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    unfold scalarControls at hz
    dsimp only at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold scalarCap callbackPrice
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤14*(natBits (scalarCap model W (K*B) K)+W)+32*W at hf
  unfold scalarWindow scalarProfile
  omega

theorem callback_work {K B : ℕ} (model : RationalCostModel) (W : ℕ) (hK : 0<K) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (value : FixedArrayTable (K*B) ℚ) (l : Fin K) :
    (GeneralPaperNativeQuantizedAnchors.entry model.rat W hB order value l).2≤callbackPrice model W (K*B) K := by
  have h := GeneralPaperNativeQuantizedAnchors.entry_work model.rat model.monotone W hB order value l
  have hBcap : B≤K*B := by nlinarith only [hK]
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 5 (model.monotone
    (Nat.add_le_add_left (binaryWordWidth_mono (show K*B+B+1≤2*(K*B)+K+2 by omega)) 1))) _)

theorem work {K B : ℕ} (model : RationalCostModel) (W : ℕ) (hK : 0<K) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (value : FixedArrayTable (K*B) ℚ)
    (hW : 1≤W) (hIndex : binaryWordWidth (K+1)≤W) :
    (GeneralPaperNativeQuantizedAnchors.run model.rat (fun w => w) W hB order value).2≤price model W (K*B) K :=
  GeneralPaperNativePayloadFillStorage.prefix_work W _ (GeneralPaperNativeQuantizedAnchors.entry model.rat W hB order value)
    (callback_work model W hK hB order value) hW hIndex K le_rfl

theorem bounded {K B : ℕ} (model : RationalCostModel) (W R : ℕ) (hK : 0<K) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (value : FixedArrayTable (K*B) ℚ)
    (hR : 3≤R) (hv : ∀ i,rationalWordWidth (value.read i)≤R)
    (hW : 1≤W) (hIndex : binaryWordWidth (K+1)≤W) (count : ℕ) (hc : count≤K) :
    window model W hB order value count hc≤profile model W (K*B) K R := by
  have hOrder := array_bound W (natBits (K*B)) (fun i : Fin (K*B) => natBits i.val) order
    (fun i => Nat.add_le_add_left (binaryWordWidth_mono (order.read i).isLt.le) 1)
  have hValue := array_bound W R rationalWordWidth value hv
  have hBcap : B≤K*B := by nlinarith only [hK]
  have hBword : natBits B≤operandWord (K*B) K := Nat.add_le_add_left (binaryWordWidth_mono (by omega : B≤2*(K*B)+K+2)) 1
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W R (callbackPrice model W (K*B) K) (scalarProfile model W (K*B) K R)
    rationalWordWidth (GeneralPaperNativeQuantizedAnchors.entry model.rat W hB order value) (scalarWindow model W hB order value)
    (entry_word model W R hB order value hR hv) (callback_work model W hK hB order value)
    (scalar_bound model W R hK hB order value hR hv) hW hIndex count hc
  have hWork := work model W hK hB order value hW hIndex
  have hf := fields_bound W (natBits (metadataCap model W (K*B) K))
    [K,B,(GeneralPaperNativeQuantizedAnchors.run model.rat (fun w => w) W hB order value).2,64*W] (by
      intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold metadataCap
      rcases hz with rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤4*(natBits (metadataCap model W (K*B) K)+W)+32*W at hf
  unfold window profile
  omega

end Blotto.GeneralPaperQuantizedAnchorStorage
