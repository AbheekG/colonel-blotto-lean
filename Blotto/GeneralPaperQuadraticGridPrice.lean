import Blotto.GeneralPaperScoreScalePrice

/-! Shared price for constructing a root/alphabet scale above 4*a*a.
Both literal products precede the one native doubling ceiling. The entire
native result is returned; no numerical logarithm is executed.
-/
namespace Blotto.GeneralPaperQuadraticGridPrice
set_option autoImplicit false

def width (a : ℕ) : ℕ := 16+4*binaryWordWidth a

def run (primitive : ℕ → ℕ) (W a : ℕ) : GeneralPaperPowerCeiling.Result × ℕ :=
  let first := 4*a
  let target := first*a
  let scale := GeneralPaperPowerCeilingBits.run primitive W target
  (scale.1,scale.2+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 4 a+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) first a+64*W)

theorem data (primitive : ℕ → ℕ) (W a : ℕ) :
    (run primitive W a).1=GeneralPaperPowerCeiling.ceiling (4*a*a) :=
  GeneralPaperPowerCeilingBits.data primitive W (4*a*a)

theorem operand_words (a : ℕ) :
    let L := width a
    1+binaryWordWidth 4≤L ∧ 1+binaryWordWidth a≤L ∧ 1+binaryWordWidth (4*a)≤L ∧
    1+binaryWordWidth (4*a*a)≤L ∧ 1+binaryWordWidth (2*(4*a*a+1))≤L := by
  have h4 : binaryWordWidth 4=3 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  have h1 : binaryWordWidth 1=1 := by decide
  have hFirst := binaryWordWidth_mul 4 a
  have hTarget := binaryWordWidth_mul (4*a) a
  have hPlus := GeneralPaperRayOperandWidthEnvelope.word_add (4*a*a) 1
  have hDouble := binaryWordWidth_mul 2 (4*a*a+1)
  dsimp only
  unfold width
  omega

def profile (primitive : ℕ → ℕ) (W a : ℕ) : ℕ :=
  128*(binaryWordWidth (4*a*a)+1)*(W+primitive (width a))

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W a : ℕ) :
    (run primitive W a).2≤profile primitive W a := by
  let L := width a
  let F := W+primitive L
  obtain ⟨h4,ha,hFirst,hTarget,hCeil⟩ := operand_words a
  have hA := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 4 a L h4 ha hFirst
  have hB := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) (4*a) a L hFirst ha hTarget
  have hC := GeneralPaperPowerCeilingBits.work primitive hMono W (4*a*a)
  have hP := hMono hCeil
  have hCeilCost := hC.trans (Nat.mul_le_mul_left (64*(binaryWordWidth (4*a*a)+1)) (Nat.add_le_add_left hP W))
  change (GeneralPaperPowerCeilingBits.run primitive W (4*a*a)).2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 4 a+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) (4*a) a+64*W≤
    128*(binaryWordWidth (4*a*a)+1)*F
  change _≤64*(binaryWordWidth (4*a*a)+1)*F at hCeilCost
  have hF : W≤F := Nat.le_add_right _ _
  have hQ : primitive L≤F := Nat.le_add_left _ _
  have hWord := binaryWordWidth_pos (4*a*a)
  nlinarith only [hA,hB,hCeilCost,hF,hQ,hWord]

theorem scale_width (a : ℕ) (ha : 0<a) :
    binaryWordWidth (GeneralPaperPowerCeiling.ceiling (4*a*a)).power≤4+2*binaryWordWidth a := by
  have hUpper := GeneralPaperPowerCeiling.ceiling_upper (4*a*a) (by positivity)
  have hM := binaryWordWidth_mono hUpper.le
  have hEq : 2*(4*a*a)=8*a*a := by ring
  rw [hEq] at hM
  have hD := binaryWordWidth_mul (8*a) a
  have hE := binaryWordWidth_mul 8 a
  have h8 : binaryWordWidth 8=4 := by decide
  omega

end Blotto.GeneralPaperQuadraticGridPrice
