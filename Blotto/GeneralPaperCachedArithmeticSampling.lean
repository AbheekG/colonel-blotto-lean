import Blotto.GeneralPaperRealPreparationHeadline

/-! Actual cached arithmetic draws include only selected-row extraction,
one old checked evaluator and one fresh-bit decode. No T-row materializing
pass is substituted in either the algorithm or its work bound. -/
namespace Blotto.GeneralPaperCachedArithmeticSampling
open GeneralPaperCachedCircleRows
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

theorem draw_work {n T K S : ℕ} (model : RationalCostModel) (price index : ℕ → ℕ) (Ap : ℕ)
    (o : GeneralPaperReducedValuesDriver.Output n) (hm : o.m=o.classified.heavy.size+o.representatives)
    (hR : 0<o.representatives) (hW : 0<o.classified.lightWeight) (hS : 0<S) (c : ℚ)
    (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (hBijective : Function.Bijective (GeneralPaperLightFieldIndexEquiv.mapping o.classified))
    (reciprocal : Bool) (i : Fin T) (l : Fin S) :
    (GeneralPaperCachedCircleSampler.draw false model 1 o hR c (pair price index Ap o hm columns).1 reciprocal i l).2≤
      GeneralPaperCachedCircleWork.selectedProfile o.classified.heavy.size 1+
        (1024*(binaryWordWidth (o.representatives*o.classified.lightWeight)+1)+24*o.representatives+816*(n+1)+64) := by
  let prepared := (pair price index Ap o hm columns).1
  let selected := materialize (fun _ => 1) 1 o.classified (if reciprocal then prepared.poor else prepared.rich) prepared.common i
  have hSelected := GeneralPaperCachedCircleWork.selected_work (fun _ => 1) 1 (by decide) o.classified
    (if reciprocal then prepared.poor else prepared.rich) prepared.common i (fun _ _ => le_rfl)
  have hOld := GeneralPaperOriginalDrawBounds.arithmetic_draw_work price index Ap model o hm
    (if reciprocal then columns.poor else columns.rich) hR hW hS c hConserved hBijective i l
  have hCost : (GeneralPaperCachedCircleSampler.draw false model 1 o hR c prepared reciprocal i l).2=
      selected.2+(GeneralPaperOriginalCirclePreparation.draw model o hR c
        (GeneralPaperOriginalCirclePreparation.run price index Ap o hm (if reciprocal then columns.poor else columns.rich)).1 i l).2 := by
    dsimp only [GeneralPaperCachedCircleSampler.draw,Bool.false_eq_true,ite_false,selected,prepared,
      GeneralPaperOriginalCirclePreparation.draw,GeneralPaperStoredCirclePreparation.draw]
    rw [pair_materialize price index (fun _ => 1) Ap 1 o hm columns reciprocal i]
    exact Nat.add_assoc _ _ _
  rw [hCost]
  exact Nat.add_le_add hSelected hOld

theorem run_work {n K : ℕ} (model : RationalCostModel) (price index : ℕ → ℕ) (Ap R L T S : ℕ)
    (hT : T=2^R) (hS : S=2^L) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (hR : 0<o.representatives) (hW : 0<o.classified.lightWeight) (c : ℚ)
    (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (hBijective : Function.Bijective (GeneralPaperLightFieldIndexEquiv.mapping o.classified))
    (reciprocal : Bool) (fresh : Fin (R+L) → Bool) :
    (GeneralPaperCachedCircleSampler.run false (fun _ => 1) 1 R L T S hT hS model o hR c
      (pair price index Ap o hm columns).1 reciprocal fresh).work≤
      GeneralPaperCachedCircleWork.selectedProfile o.classified.heavy.size 1+
        (1024*(binaryWordWidth (o.representatives*o.classified.lightWeight)+1)+24*o.representatives+816*(n+1)+64)+144*(R+L)+258 := by
  have hf := GeneralPaperNativeFreshBuffer.arithmetic_work 1 fresh
  let buffer := (GeneralPaperNativeFreshBuffer.run (fun _ => 1) 1 fresh).1.1
  let decoded := GeneralPaperNativeDyadicBlocks.run (fun _ => 1) 1 R L T S hT hS buffer
  have hb := GeneralPaperNativeDyadicBlocks.arithmetic_work 1 R L T S hT hS buffer
  have hd := draw_work model price index Ap o hm hR hW (hS ▸ Nat.two_pow_pos L) c columns hConserved hBijective
    reciprocal decoded.row decoded.shift
  unfold GeneralPaperCachedCircleSampler.run
  dsimp only [buffer,decoded] at hb hd ⊢
  nlinarith only [hf,hb,hd]

theorem row_bits (m n k : ℕ) (hm : m≤n) :
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rowBits+(k+6)≤
      4*k+2*binaryWordWidth (n+4)+87 := by
  let lambda := (GeneralPaperProxyParameters.alphabet m k).lambda
  have hSize := GeneralPaperOriginalSourceValueContract.alphabet_size m k
  have hWord := binaryWordWidth_mono hSize
  have h0 := binaryWordWidth_mul (2^30*(m+4)^2) (2^k)
  have h1 := binaryWordWidth_mul (2^30) ((m+4)^2)
  have h2 := binaryWordWidth_mul (m+4) (m+4)
  have hp : binaryWordWidth (2^k)=k+1 := by simp only [binaryWordWidth,Nat.log2_two_pow]
  have hc : binaryWordWidth (2^30)=31 := by decide
  rw [hp] at h0
  rw [hc] at h1
  rw [←pow_two] at h2
  have hL : binaryWordWidth (lambda+1)≤2*binaryWordWidth (m+4)+k+32 := by
    change binaryWordWidth ((GeneralPaperProxyParameters.alphabet m k).lambda+1)≤_ at hWord
    dsimp only [lambda]
    omega
  have hL' := (binaryWordWidth_mono (show lambda+2≤2*(lambda+1) by omega)).trans (binaryWordWidth_mul 2 (lambda+1))
  rw [show binaryWordWidth 2=2 by decide] at hL'
  have hProduct := binaryWordWidth_mul (lambda+2) (2^(35+k))
  rw [show binaryWordWidth (2^(35+k))=35+k+1 by simp only [binaryWordWidth,Nat.log2_two_pow]] at hProduct
  have hRows := GeneralPaperTrajectoryParameters.rowBits_bound lambda k
  have hN := binaryWordWidth_mono (Nat.add_le_add_right hm 4)
  dsimp only [lambda] at hL hL' hProduct hRows
  omega

end Blotto.GeneralPaperCachedArithmeticSampling
