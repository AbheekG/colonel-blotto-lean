import Blotto.GeneralPaperClassifierCFWords

/-! Complete constructor/classifier operand price at the now-constructed
shared local control word. This wrapper requires no capacity/width oracle.
Original rational precision B remains explicit; CF temporary memory and
global source/address/space joins remain separate paper obligations.
-/
namespace Blotto.GeneralPaperCalibratedClassifier
open GeneralPaperPrecallControlWord
set_option autoImplicit false
set_option maxHeartbeats 6000000

def prepare (model : RationalCostModel) (m k : ℕ) (b : ℚ) :=
  GeneralPaperPreparedClassifierBits.prepare model (word m k) m k b

theorem data (model : RationalCostModel) (m k : ℕ) (b : ℚ) :
    (prepare model m k b).1=((GeneralPaperPrecallCachePrice.specification m k,GeneralPaperProxyParameters.alphabet m k),
      GeneralPaperProxyClassifier.classify m k (b:ℝ)) :=
  GeneralPaperPreparedClassifierBits.data model (word m k) m k b

def profile (model : RationalCostModel) (m k B : ℕ) : ℕ :=
  let g := (GeneralPaperProxyParameters.prepare m k).gridBits
  GeneralPaperPrecallCachePrice.profile model.rat (word m k) m k+
    4194304*(g+6)*(word m k+model.rat (512+8*B+64*g))+56*word m k

theorem work (model : RationalCostModel) (m k : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) :
    (prepare model m k b).2≤profile model m k B := by
  have hp := GeneralPaperPreparedClassifierBits.work model (word m k) m k b hb B hB
  have hc := GeneralPaperClassifierEnvelope.profile_bound model (word m k)
    (GeneralPaperPrecallCachePrice.specification m k) B
  have hWidth := GeneralPaperClassifierEnvelope.actual_width m k B
  have hP := model.monotone hWidth
  have hProfile := hc.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hP (word m k)))
  change _≤GeneralPaperPrecallCachePrice.profile model.rat (word m k) m k+
    GeneralPaperClassifierBits.profile model (word m k) (GeneralPaperPrecallCachePrice.specification m k) B+56*word m k at hp
  exact hp.trans (Nat.add_le_add_right (Nat.add_le_add_left hProfile _) _)

theorem unit_data (model : RationalCostModel) (m k : ℕ) (b : ℚ) :
    (prepare model m k b).1=(GeneralPaperCachedClassifier.prepare m k (b:ℝ)).1 :=
  GeneralPaperPreparedClassifierBits.unit_data model (word m k) m k b

theorem metadata (model : RationalCostModel) (m k : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) :
    binaryWordWidth ((prepare model m k b).1.2.work+128)≤word m k :=
  GeneralPaperClassifierControlWords.returned_metadata model m k b hb

end Blotto.GeneralPaperCalibratedClassifier
