import Blotto.GeneralPaperSelectionPoints

/-! All literal selection-point arithmetic, casts and writes. The common
scale is cast once and reused by both endpoint divisions. Midpoint fraction
components are retained for the eventual selected proxy record.
-/
namespace Blotto.GeneralPaperSelectionPointsPrice
set_option autoImplicit false
set_option maxHeartbeats 6000000

def naturalWork (model : RationalCostModel) (Q j : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) j 1+
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 j+
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (2*j) 1+
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 Q

def casts (model : RationalCostModel) (Q j : ℕ) (p : GeneralPaperSelectionPoints.Points) : ℕ :=
  model.rat (rationalWordWidth (j:ℚ))+model.rat (rationalWordWidth (Q:ℚ))+
  model.rat (rationalWordWidth (p.upperNum:ℚ))+model.rat (rationalWordWidth (p.midNum:ℚ))+
  model.rat (rationalWordWidth (p.midDen:ℚ))

def rationalWork (model : RationalCostModel) (Q j : ℕ) (p : GeneralPaperSelectionPoints.Points) : ℕ :=
  GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (j:ℚ) (Q:ℚ)+
  GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (p.upperNum:ℚ) (Q:ℚ)+
  GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (p.midNum:ℚ) (p.midDen:ℚ)

theorem natural_work (model : RationalCostModel) (Q j B : ℕ) (hQ : 0<Q) (hj : j<Q) :
    naturalWork model Q j≤8*model.rat (GeneralPaperSelectionPoints.width Q B) := by
  obtain ⟨h1,h2,hjW,hQW,huW,htW,hnW,hdW⟩ := GeneralPaperSelectionPoints.natural_words Q j B hQ hj
  let L := GeneralPaperSelectionPoints.width Q B
  have c1 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b) j 1 L hjW h1 huW
  have c2 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) 2 j L h2 hjW htW
  have c3 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b) (2*j) 1 L htW h1 hnW
  have c4 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) 2 Q L h2 hQW hdW
  change naturalWork model Q j≤8*model.rat L
  unfold naturalWork
  omega

theorem arithmetic_work (model : RationalCostModel) (Q j B : ℕ) (b : ℚ) (hQ : 0<Q) (hj : j<Q)
    (hB : RationalHeight b B) :
    casts model Q j (GeneralPaperSelectionPoints.prepare Q j)+
      rationalWork model Q j (GeneralPaperSelectionPoints.prepare Q j)≤11*model.rat (GeneralPaperSelectionPoints.width Q B) := by
  obtain ⟨_,hjW,hQW,huW,hnW,hdW,hlW,hhW,hmW⟩ := GeneralPaperSelectionPoints.rational_words Q j B b hQ hj hB
  let p := GeneralPaperSelectionPoints.prepare Q j
  let L := GeneralPaperSelectionPoints.width Q B
  have c1 := model.monotone hjW
  have c2 := model.monotone hQW
  have c3 := model.monotone huW
  have c4 := model.monotone hnW
  have c5 := model.monotone hdW
  have c6 := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) (j:ℚ) (Q:ℚ) L hjW hQW hlW
  have c7 := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) (p.upperNum:ℚ) (Q:ℚ) L huW hQW hhW
  have c8 := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) (p.midNum:ℚ) (p.midDen:ℚ) L hnW hdW hmW
  change casts model Q j p+rationalWork model Q j p≤11*model.rat L
  unfold casts rationalWork
  dsimp only [p,L] at *
  omega

def run (model : RationalCostModel) (W Q j : ℕ) : GeneralPaperSelectionPoints.Points × ℕ :=
  let p := GeneralPaperSelectionPoints.prepare Q j
  (p,naturalWork model Q j+casts model Q j p+rationalWork model Q j p+128*W)

theorem data (model : RationalCostModel) (W Q j : ℕ) :
    (run model W Q j).1=GeneralPaperSelectionPoints.prepare Q j := rfl

theorem work (model : RationalCostModel) (W Q j B : ℕ) (b : ℚ) (hQ : 0<Q) (hj : j<Q)
    (hB : RationalHeight b B) :
    (run model W Q j).2≤19*model.rat (GeneralPaperSelectionPoints.width Q B)+128*W := by
  have hn := natural_work model Q j B hQ hj
  have hr := arithmetic_work model Q j B b hQ hj hB
  change naturalWork model Q j+casts model Q j (GeneralPaperSelectionPoints.prepare Q j)+
    rationalWork model Q j (GeneralPaperSelectionPoints.prepare Q j)+128*W≤_
  omega

end Blotto.GeneralPaperSelectionPointsPrice
