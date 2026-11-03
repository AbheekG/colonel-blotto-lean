import Blotto.GeneralPaperDyadicPowerBits
import Blotto.GeneralPaperPowerCeilingBits

/-! Construct K, S and the score depth once, retaining the native work
annotation. Charge the accuracy-index addition, product m*K, both power
constructors and the cached record/control writes. No size premise is used.
-/
namespace Blotto.GeneralPaperScoreScalePrice
set_option autoImplicit false
set_option maxHeartbeats 4000000

def width (m k : ℕ) : ℕ :=
  32+4*binaryWordWidth m+4*binaryWordWidth k+4*(7+k)

def run (primitive : ℕ → ℕ) (W m k : ℕ) : GeneralPaperScoreScaleParameters.Parameters × ℕ :=
  let labels := GeneralPaperDyadicPowerBits.run primitive W (7+k)
  let scale := GeneralPaperPowerCeilingBits.run primitive W (m*labels.1.power)
  (⟨labels.1.power,scale.1.power,scale.1.doublings+1,labels.1.work+scale.1.work+16⟩,
    labels.2+scale.2+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) 7 k+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) m labels.1.power+64*W)

theorem data (primitive : ℕ → ℕ) (W m k : ℕ) :
    (run primitive W m k).1=GeneralPaperScoreScaleParameters.prepare m k := by
  simp only [run,GeneralPaperDyadicPowerBits.data,GeneralPaperPowerCeilingBits.data,
    GeneralPaperScoreScaleParameters.prepare]

theorem operand_words (m k : ℕ) :
    let K := (GeneralPaperScoreScaleParameters.prepare m k).K
    let L := width m k
    8+2*(7+k)≤L ∧ 1+binaryWordWidth 7≤L ∧ 1+binaryWordWidth k≤L ∧
    1+binaryWordWidth (7+k)≤L ∧ 1+binaryWordWidth m≤L ∧
    1+binaryWordWidth K≤L ∧ 1+binaryWordWidth (m*K)≤L ∧
    1+binaryWordWidth (2*(m*K+1))≤L := by
  have hk : binaryWordWidth (GeneralPaperScoreScaleParameters.prepare m k).K≤1+2*(7+k) := by
    rw [GeneralPaperScoreScaleParameters.label_power]
    simpa only [show binaryWordWidth 2=2 by decide,Nat.mul_comm] using GeneralPaperNatPowerOperands.power_width 2 (7+k)
  have ht := binaryWordWidth_mul m (GeneralPaperScoreScaleParameters.prepare m k).K
  have hPlus := GeneralPaperRayOperandWidthEnvelope.word_add (m*(GeneralPaperScoreScaleParameters.prepare m k).K) 1
  have hDouble := binaryWordWidth_mul 2 (m*(GeneralPaperScoreScaleParameters.prepare m k).K+1)
  have he := GeneralPaperRayOperandWidthEnvelope.word_add 7 k
  have h1 : binaryWordWidth 1=1 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  have h7 : binaryWordWidth 7=3 := by decide
  dsimp only
  unfold width
  omega

def profile (primitive : ℕ → ℕ) (W m k : ℕ) : ℕ :=
  128*((7+k)+binaryWordWidth (m*(GeneralPaperScoreScaleParameters.prepare m k).K)+2)*
    (W+primitive (width m k))

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m k : ℕ) :
    (run primitive W m k).2≤profile primitive W m k := by
  let K := (GeneralPaperScoreScaleParameters.prepare m k).K
  let L := width m k
  let F := W+primitive L
  obtain ⟨hD,h7,hk,he,hm,hK,ht,hCeil⟩ := operand_words m k
  have hl := GeneralPaperDyadicPowerBits.work primitive hMono W (7+k)
  have hc := GeneralPaperPowerCeilingBits.work primitive hMono W (m*K)
  have heCost := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) 7 k L h7 hk he
  have hmCost := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) m K L hm hK ht
  have hLP := hMono hD
  have hCP := hMono hCeil
  have hlCost := hl.trans (Nat.mul_le_mul_left (64*((7+k)+1)) (Nat.add_le_add_left hLP W))
  have hcCost := hc.trans (Nat.mul_le_mul_left (64*(binaryWordWidth (m*K)+1)) (Nat.add_le_add_left hCP W))
  unfold run profile
  dsimp only
  rw [GeneralPaperDyadicPowerBits.data]
  change (GeneralPaperDyadicPowerBits.run primitive W (7+k)).2+
    (GeneralPaperPowerCeilingBits.run primitive W (m*K)).2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) 7 k+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) m K+64*W≤
      128*((7+k)+binaryWordWidth (m*K)+2)*F
  change _≤64*((7+k)+1)*F at hlCost
  change _≤64*(binaryWordWidth (m*K)+1)*F at hcCost
  have hF : W≤F := Nat.le_add_right _ _
  have hP : primitive L≤F := Nat.le_add_left _ _
  nlinarith only [hlCost,hcCost,heCost,hmCost,hF,hP]

end Blotto.GeneralPaperScoreScalePrice
