import Blotto.GeneralPaperRankArrayData

/-! The actual fill derives its annotation bound at every prefix. These
analytical caps price the two annotation additions without a second pass.
The value word includes the full code bound V, independent of index depth.
-/
namespace Blotto.GeneralPaperRankArrayOperands
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperRankArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def entryBound (depth : ℕ) : ℕ := depth*(12*depth+34)+66
def magnitude (m depth : ℕ) : ℕ := 128*(m+1)*(depth+1)^2+256
def width (m depth V : ℕ) : ℕ :=
  GeneralPaperRankOperands.width depth V+128+16*binaryWordWidth (m+1)

theorem fill_annotation {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k depth : ℕ)
    (values : Summary k) (cuts : FixedArrayTable m ℕ) (hDepth : depth=35+k)
    (count : ℕ) (hCount : count≤m) :
    (fill bits index primitive W k depth values cuts count hCount).1.2≤count*entryBound depth+18 := by
  induction count with
  | zero => simp only [fill,Nat.zero_mul,Nat.zero_add]; exact le_refl _
  | succ count ih =>
    have hEarlier := ih (by omega)
    have hLookup := GeneralPaperSelectedRank.lookup_work k values (cuts.read ⟨count,by omega⟩)
    rw [←hDepth] at hLookup
    rw [fill]
    dsimp only
    rw [GeneralPaperSelectedRankPrice.data bits primitive W k depth values _ hDepth]
    unfold entryBound at *
    nlinarith only [hEarlier,hLookup]

theorem annotation_cap (m depth count : ℕ) (hCount : count≤m) :
    count*entryBound depth+18≤magnitude m depth := by
  have hEntry : entryBound depth≤128*(depth+1)^2 := by
    unfold entryBound
    nlinarith only [Nat.zero_le depth]
  have h := Nat.mul_le_mul hCount hEntry
  unfold magnitude
  nlinarith only [h,Nat.zero_le ((depth+1)^2)]

theorem word_bound (m depth V : ℕ) : 1+binaryWordWidth (magnitude m depth)≤width m depth V := by
  have ha := binaryWordWidth_mul 128 (m+1)
  have hb := binaryWordWidth_mul (128*(m+1)) ((depth+1)^2)
  have hs := binaryWordWidth_mul (depth+1) (depth+1)
  rw [←pow_two] at hs
  have hd := GeneralPaperInitializerControlCounters.word_le_self (depth+1)
  have hc := GeneralPaperRayOperandWidthEnvelope.word_add (128*(m+1)*(depth+1)^2) 256
  have h128 : binaryWordWidth 128=8 := by decide
  have h256 : binaryWordWidth 256=9 := by decide
  unfold magnitude width GeneralPaperRankOperands.width
  omega

theorem additions_work {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W k depth V : ℕ) (values : Summary k) (cuts : FixedArrayTable m ℕ) (hDepth : depth=35+k)
    (count : ℕ) (hCount : count+1≤m) :
    let earlier := fill bits index primitive W k depth values cuts count (by omega)
    let found := GeneralPaperSelectedRankPrice.run bits primitive W k depth values (cuts.read ⟨count,by omega⟩)
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) earlier.1.2 found.1.work+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (earlier.1.2+found.1.work) 50≤
        4*primitive (width m depth V) := by
  have hFull := (fill_annotation bits index primitive W k depth values cuts hDepth (count+1) hCount).trans
    (annotation_cap m depth (count+1) hCount)
  rw [fill] at hFull
  dsimp only at hFull ⊢
  have hWord := word_bound m depth V
  have price (a b : ℕ) (ha : a≤magnitude m depth) (hb : b≤magnitude m depth) (hc : a+b≤magnitude m depth) :
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) a b≤2*primitive (width m depth V) :=
    (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono _ a b (magnitude m depth) ha hb hc).trans
      (Nat.mul_le_mul_left 2 (hMono hWord))
  let earlier := fill bits index primitive W k depth values cuts count (by omega)
  let found := GeneralPaperSelectedRankPrice.run bits primitive W k depth values (cuts.read ⟨count,by omega⟩)
  change earlier.1.2+found.1.work+50≤magnitude m depth at hFull
  change GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) earlier.1.2 found.1.work+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (earlier.1.2+found.1.work) 50≤_
  have ha := price earlier.1.2 found.1.work (by omega) (by omega) (by omega)
  have hb := price (earlier.1.2+found.1.work) 50 (by omega) (by omega) hFull
  omega

theorem depth_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (m k V : ℕ) :
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) 35 k≤2*primitive (width m (35+k) V) := by
  have hDepth : 35+k≤magnitude m (35+k) := by
    have h := annotation_cap m (35+k) 0 (Nat.zero_le _)
    unfold magnitude at *
    nlinarith only [Nat.zero_le m,Nat.zero_le k]
  exact (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono _ 35 k (magnitude m (35+k))
    (by omega) (by omega) hDepth).trans (Nat.mul_le_mul_left 2 (hMono (word_bound m (35+k) V)))

end Blotto.GeneralPaperRankArrayOperands
