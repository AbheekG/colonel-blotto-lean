import Blotto.GeneralPaperPricedNaturalRange

/-! Generate every fixed-grid point, sharing the range of within-band
indices and each band's constructed dyadic factor. Append copies only the
current band. No alphabet or allocation product is enumerated.
-/
namespace Blotto.GeneralPaperProfitPointPrice
open GeneralPaperProfitGridPoints
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def width (w B : ℕ) : ℕ := 64+8*(B+binaryWordWidth (w+1)+1)

def point (primitive : ℕ → ℕ) (W w factor r : ℕ) : ℕ × ℕ :=
  let a := w+r
  (a*factor,GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) w r+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) a factor+32*W)

theorem point_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W w B h r : ℕ)
    (hh : h≤B) (hr : r<w) :
    (point primitive W w (2^h) r).2≤4*primitive (width w B)+32*W := by
  have hw := binaryWordWidth_mono (show w≤w+1 by omega)
  have hR := binaryWordWidth_mono (show r≤w+1 by omega)
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add w r
  have hp := GeneralPaperNatPowerOperands.power_width 2 h
  have hm := binaryWordWidth_mul (w+r) (2^h)
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hp
  have hAdd := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) w r (width w B)
    (by unfold width; omega) (by unfold width; omega) (by unfold width; omega)
  have hMul := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) (w+r) (2^h) (width w B)
    (by unfold width; omega) (by unfold width; omega) (by unfold width; omega)
  change GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) w r+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) (w+r) (2^h)+32*W≤_
  omega

def band (primitive : ℕ → ℕ) (W w h : ℕ) (indices : List ℕ) : List ℕ × ℕ :=
  let factor := GeneralPaperDyadicPowerBits.run primitive W h
  let mapped := GeneralPaperPricedListMap.run W (point primitive W w factor.1.power) indices
  (mapped.1,factor.2+mapped.2+32*W)

theorem band_data (primitive : ℕ → ℕ) (W w h : ℕ) :
    (band primitive W w h (List.range w)).1=GeneralPaperProfitGridPoints.band w h := by
  simp only [band,GeneralPaperPricedListMap.data,point,GeneralPaperDyadicPowerBits.data,
    (GeneralPaperScoreScaleParameters.power_data h).1,GeneralPaperProfitGridPoints.band]

def bandProfile (primitive : ℕ → ℕ) (W w B : ℕ) : ℕ :=
  64*(B+1)*(W+primitive (width w B))+(4*primitive (width w B)+40*W)*w+34*W

theorem band_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W w B h : ℕ) (hh : h≤B) :
    (band primitive W w h (List.range w)).2≤bandProfile primitive W w B := by
  have hPow := GeneralPaperDyadicPowerBits.work primitive hMono W h
  have hWidth : 8+2*h≤width w B := by unfold width; omega
  have hFactor : (GeneralPaperDyadicPowerBits.run primitive W h).1.power=2^h := by
    rw [GeneralPaperDyadicPowerBits.data,(GeneralPaperScoreScaleParameters.power_data h).1]
  have hMap := GeneralPaperPricedListMap.work W (4*primitive (width w B)+32*W)
    (point primitive W w (GeneralPaperDyadicPowerBits.run primitive W h).1.power) (List.range w) (by
      intro r hr
      rw [hFactor]
      exact point_work primitive hMono W w B h r hh (List.mem_range.mp hr))
  rw [List.length_range] at hMap
  have hP := Nat.mul_le_mul
    (Nat.mul_le_mul_left 64 (Nat.add_le_add_right hh 1))
    (Nat.add_le_add_left (hMono hWidth) W)
  change (GeneralPaperDyadicPowerBits.run primitive W h).2+
    (GeneralPaperPricedListMap.run W (point primitive W w (GeneralPaperDyadicPowerBits.run primitive W h).1.power) (List.range w)).2+32*W≤_
  unfold bandProfile
  nlinarith only [hPow,hP,hMap]

def run (primitive : ℕ → ℕ) (W w B : ℕ) : List ℕ × ℕ :=
  let indices := GeneralPaperPricedNaturalRange.run W w
  let heights := GeneralPaperPricedNaturalRange.run W (B+1)
  let generated := GeneralPaperPricedListStream.flatMap W (fun h => band primitive W w h indices.1) heights.1
  (generated.1,indices.2+heights.2+generated.2+32*W)

theorem data (primitive : ℕ → ℕ) (W w B : ℕ) :
    (run primitive W w B).1=points w B := by
  simp only [run,GeneralPaperPricedNaturalRange.data,GeneralPaperPricedListStream.flatMap_data,
    band_data,points]

def profile (primitive : ℕ → ℕ) (W w B : ℕ) : ℕ :=
  (bandProfile primitive W w B+(8*w+8)*W)*(B+1)+32*(w+B+1)*W+38*W

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W w B : ℕ) :
    (run primitive W w B).2≤profile primitive W w B := by
  have hf := GeneralPaperPricedListStream.flatMap_work W w (bandProfile primitive W w B)
    (fun h => band primitive W w h (List.range w)) (List.range (B+1))
    (by intro h _; rw [band_data,band_length])
    (by intro h hh; exact band_work primitive hMono W w B h (by have := List.mem_range.mp hh; omega))
  rw [List.length_range] at hf
  change (GeneralPaperPricedNaturalRange.run W w).2+(GeneralPaperPricedNaturalRange.run W (B+1)).2+
    (GeneralPaperPricedListStream.flatMap W (fun h => band primitive W w h (GeneralPaperPricedNaturalRange.run W w).1)
      (GeneralPaperPricedNaturalRange.run W (B+1)).1).2+32*W≤_
  rw [GeneralPaperPricedNaturalRange.data,GeneralPaperPricedNaturalRange.data,
    GeneralPaperPricedNaturalRange.work,GeneralPaperPricedNaturalRange.work]
  unfold profile
  nlinarith only [hf]

theorem arithmetic_work (w B : ℕ) :
    (run (fun _ => 1) 1 w B).2≤256*(w+B+1)*(B+1) := by
  have h := work (fun _ => 1) (fun _ _ _ => Nat.le_refl 1) 1 w B
  unfold profile bandProfile at h
  dsimp only at h
  nlinarith only [h,Nat.zero_le (B*B),Nat.zero_le (w*B)]

end Blotto.GeneralPaperProfitPointPrice
