import Blotto.GeneralPaperCachedSharedPreparation

/-! Real-arithmetic classifier and source controls, using the native real
quotient rather than assigning unit cost to the bit integer division.
The classifier's returned alphabet feeds source parameter construction once.
-/
namespace Blotto.GeneralPaperArithmeticSourcePrecall
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def prepare (m k Qv : ℕ) (b : ℝ) :=
  let front := GeneralPaperCachedClassifier.prepare m k b
  let source := GeneralPaperSourcePreparationCache.prepare (fun _ => 1) 1 m front.1.1.2.lambda k Qv
  ((front.1,source.1),front.2+source.2+64)

theorem data (m k Qv : ℕ) (b : ℝ) :
    (prepare m k Qv b).1=
      (((GeneralPaperPrecallCachePrice.specification m k,GeneralPaperProxyParameters.alphabet m k),
        GeneralPaperProxyClassifier.classify m k b),GeneralPaperSourcePreparationCache.specification m
          (GeneralPaperProxyParameters.alphabet m k).lambda k Qv) := by
  simp only [prepare,GeneralPaperCachedClassifier.prepare_data,GeneralPaperSourcePreparationCache.data]

def profile (m k Qv : ℕ) : ℕ :=
  GeneralPaperPrecallCachePrice.profile (fun _ => 1) 1 m k+
    182*(GeneralPaperProxyParameters.prepare m k).gridBits+1118+
    524288*GeneralPaperSourcePreparationSizes.measure m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv

theorem work (m k Qv : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    (prepare m k Qv b).2≤profile m k Qv := by
  have hf := GeneralPaperCachedClassifier.prepare_work m k b hb
  have hs := GeneralPaperSourcePreparationEnvelope.unit_work m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv
  change (GeneralPaperCachedClassifier.prepare m k b).2+
    (GeneralPaperSourcePreparationCache.prepare (fun _ => 1) 1 m
      (GeneralPaperCachedClassifier.prepare m k b).1.1.2.lambda k Qv).2+64≤_
  rw [GeneralPaperCachedClassifier.prepare_data]
  dsimp only
  unfold profile
  omega

theorem bit_data (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) :
    (GeneralPaperSourcePrecallPreparation.prepare model W m k Qv b).1=(prepare m k Qv (b:ℝ)).1 := by
  rw [GeneralPaperSourcePrecallPreparation.data,data]

end Blotto.GeneralPaperArithmeticSourcePrecall
