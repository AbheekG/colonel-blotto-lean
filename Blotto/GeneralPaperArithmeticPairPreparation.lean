import Blotto.GeneralPaperCachedSourcePairLaw

/-! Construct the actual arithmetic classifier/control/grid caches once
and retain their returned records for the two-player source/compiler.
The real-RAM front end uses its existing arithmetic quotient/root routine.
It does not charge unit cost to bit integer division on original encodings. -/
namespace Blotto.GeneralPaperArithmeticPairPreparation
open GeneralPaperProxyParameters GeneralPaperCachedSourcePair
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4096

noncomputable def run (m k Qv : ℕ) (b : ℝ) : Input m k Qv b×ℕ :=
  let front := GeneralPaperArithmeticSourcePrecall.prepare m k Qv b
  let grid := GeneralPaperMaterializationFromControls.arithmetic k front.1.2
  let hFront := GeneralPaperArithmeticSourcePrecall.data m k Qv b
  let hA : front.1.1.1.2=alphabet m k := congrArg (fun r => r.1.1.2) hFront
  let hControls : front.1.2=GeneralPaperSourcePreparationCache.specification m front.1.1.1.2.lambda k Qv := by
    rw [hA]
    exact congrArg Prod.snd hFront
  let hGrid := GeneralPaperMaterializationFromControls.arithmetic_data m front.1.1.1.2.lambda k Qv front.1.2 hControls
  (⟨front.1.1.1.1,front.1.1.1.2,grid.1,front.1.1.2,
    congrArg (fun r => r.1.1.1) hFront,hA,hGrid,congrArg (fun r => r.1.2) hFront⟩,
    front.2+grid.2+128)

def profile (m k Qv : ℕ) : ℕ :=
  GeneralPaperArithmeticSourcePrecall.profile m k Qv+
    524288*(GeneralPaperSourcePreparationSizes.measure m (alphabet m k).lambda k Qv+1)^2+
    GeneralPaperProfitGridProfile.bound (GeneralPaperProfitParameters.parameters m (alphabet m k).lambda k Qv).width
      (GeneralPaperProfitParameters.parameters m (alphabet m k).lambda k Qv).exponent+128

theorem arithmetic_work (m k Qv : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    (run m k Qv b).2≤profile m k Qv := by
  let front := GeneralPaperArithmeticSourcePrecall.prepare m k Qv b
  have hFront := GeneralPaperArithmeticSourcePrecall.data m k Qv b
  have hA : front.1.1.1.2=alphabet m k := congrArg (fun r => r.1.1.2) hFront
  have hControls : front.1.2=GeneralPaperSourcePreparationCache.specification m front.1.1.1.2.lambda k Qv := by
    rw [hA]
    exact congrArg Prod.snd hFront
  have hf := GeneralPaperArithmeticSourcePrecall.work m k Qv b hb
  have hg := GeneralPaperMaterializationFromControls.arithmetic_work m front.1.1.1.2.lambda k Qv front.1.2 hControls
  rw [hA] at hg
  change front.2≤GeneralPaperArithmeticSourcePrecall.profile m k Qv at hf
  change (GeneralPaperMaterializationFromControls.arithmetic k front.1.2).2≤
    524288*(GeneralPaperSourcePreparationSizes.measure m (alphabet m k).lambda k Qv+1)^2+
      GeneralPaperProfitGridProfile.bound (GeneralPaperProfitParameters.parameters m (alphabet m k).lambda k Qv).width
        (GeneralPaperProfitParameters.parameters m (alphabet m k).lambda k Qv).exponent at hg
  change front.2+(GeneralPaperMaterializationFromControls.arithmetic k front.1.2).2+128≤_
  unfold profile
  omega

theorem returned_controls (m k Qv : ℕ) (b : ℝ) :
    (run m k Qv b).1.control=GeneralPaperPrecallCachePrice.specification m k :=
  (run m k Qv b).1.control_data

end Blotto.GeneralPaperArithmeticPairPreparation
