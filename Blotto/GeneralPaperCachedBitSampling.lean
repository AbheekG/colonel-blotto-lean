import Blotto.GeneralPaperSourcePairAnchorHeights
import Blotto.GeneralPaperNativeFairBitPrice

/-! Operand-sensitive bit prices for the actual shared cached sampler and
the identity branch. Only the selected kept row is materialized. Rational
budget products and output writes, fresh buffer and decoder are included. -/
namespace Blotto.GeneralPaperCachedBitSampling
open GeneralPaperCachedCircleRows GeneralPaperOriginalDrawEquilibrium
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

def profile (model : RationalCostModel) (A Rb Lb R W S C H n g h : ℕ) : ℕ :=
  GeneralPaperNativeFairBitPrice.profile model A Rb Lb R W S C H n g+
    GeneralPaperCachedCircleWork.selectedProfile h A

theorem draw_work {n T K S : ℕ} (model : RationalCostModel) (A C H : ℕ) (hA : 1≤A)
    (price index : ℕ → ℕ) (Ap : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (hR : 0<o.representatives)
    (hW : 0<o.classified.lightWeight) (hS : 0<S) (c : ℚ) (hc : RationalHeight c C)
    (columns : Columns T o.m K) (reciprocal : Bool)
    (hColumns : ∀ j l,RationalHeight ((((if reciprocal then columns.poor else columns.rich).read j).anchors).read l) H)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (hBijective : Function.Bijective (GeneralPaperLightFieldIndexEquiv.mapping o.classified))
    (hCapacity : 1+binaryWordWidth (2*n+o.representatives+2)≤A) (hRow : binaryWordWidth (T+1)≤A)
    (i : Fin T) (l : Fin S) :
    (GeneralPaperCachedCircleSampler.draw true model A o hR c (pair price index Ap o hm columns).1 reciprocal i l).2≤
      GeneralPaperCachedCircleWork.selectedProfile o.classified.heavy.size A+
        GeneralPaperNamedCircleBitPrice.drawProfile model A o.representatives o.classified.lightWeight S C H n o.classified.light.size+64*A := by
  let prepared := (pair price index Ap o hm columns).1
  let selected := materialize (fun w => w) A o.classified (if reciprocal then prepared.poor else prepared.rich) prepared.common i
  have hIndex (j : ℕ) (hj : j≤o.classified.heavy.size) : binaryWordWidth (j+1)≤A := by
    have hs := GeneralPaperOriginalScatterLaw.size o.classified hBijective
    exact (binaryWordWidth_mono (by omega : j+1≤2*n+o.representatives+2)).trans (by omega)
  have hSelected := GeneralPaperCachedCircleWork.selected_work (fun w => w) A hA o.classified
    (if reciprocal then prepared.poor else prepared.rich) prepared.common i hIndex
  have hOld := GeneralPaperStoredCircleBitPrice.original_work model A C H hA o hm hR hW hS c price index Ap
    (if reciprocal then columns.poor else columns.rich) hColumns hConserved hBijective hc hCapacity hRow i l
  have hCost : (GeneralPaperCachedCircleSampler.draw true model A o hR c prepared reciprocal i l).2=
      selected.2+(GeneralPaperStoredCircleBitDraw.original model A o hR c
        (GeneralPaperOriginalCirclePreparation.run price index Ap o hm (if reciprocal then columns.poor else columns.rich)).1 i l).2 := by
    dsimp only [GeneralPaperCachedCircleSampler.draw,ite_true,selected,prepared,
      GeneralPaperStoredCircleBitDraw.original,GeneralPaperStoredCircleBitDraw.run]
    rw [pair_materialize price index (fun w => w) Ap A o hm columns reciprocal i]
    exact Nat.add_assoc _ _ _
  rw [hCost]
  exact (Nat.add_le_add hSelected hOld).trans_eq (by omega)

theorem run_work {n K : ℕ} (model : RationalCostModel) (A C H : ℕ) (hA : 1≤A)
    (price index : ℕ → ℕ) (Ap Rb Lb T S : ℕ) (hT : T=2^Rb) (hS : S=2^Lb)
    (o : GeneralPaperReducedValuesDriver.Output n) (hm : o.m=o.classified.heavy.size+o.representatives)
    (hR : 0<o.representatives) (hW : 0<o.classified.lightWeight) (c : ℚ) (hc : RationalHeight c C)
    (columns : Columns T o.m K) (reciprocal : Bool)
    (hColumns : ∀ j l,RationalHeight ((((if reciprocal then columns.poor else columns.rich).read j).anchors).read l) H)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (hBijective : Function.Bijective (GeneralPaperLightFieldIndexEquiv.mapping o.classified))
    (hCapacity : 1+binaryWordWidth (2*n+o.representatives+2)≤A) (hRow : binaryWordWidth (T+1)≤A)
    (fresh : Fin (Rb+Lb) → Bool) :
    (GeneralPaperCachedCircleSampler.run true model.rat A Rb Lb T S hT hS model o hR c
      (pair price index Ap o hm columns).1 reciprocal fresh).work≤
        profile model A Rb Lb o.representatives o.classified.lightWeight S C H n o.classified.light.size o.classified.heavy.size := by
  have hf := GeneralPaperNativeFreshBufferBits.work model.rat model.monotone A fresh
  let buffer := (GeneralPaperNativeFreshBuffer.run model.rat A fresh).1.1
  let decoded := GeneralPaperNativeDyadicBlocks.run model.rat A Rb Lb T S hT hS buffer
  have hd := GeneralPaperNativeDyadicBlocksBits.work model.rat model.monotone A Rb Lb T S hT hS buffer
  have ho := draw_work model A C H hA price index Ap o hm hR hW (hS ▸ Nat.two_pow_pos Lb) c hc columns reciprocal
    hColumns hConserved hBijective hCapacity hRow decoded.row decoded.shift
  unfold GeneralPaperCachedCircleSampler.run profile GeneralPaperNativeFairBitPrice.profile
  dsimp only [buffer,decoded] at hd ho ⊢
  omega

theorem run_height {n K : ℕ} (model : RationalCostModel) (A C H : ℕ)
    (price index : ℕ → ℕ) (Ap Rb Lb T S : ℕ) (hT : T=2^Rb) (hS : S=2^Lb)
    (o : GeneralPaperReducedValuesDriver.Output n) (hm : o.m=o.classified.heavy.size+o.representatives)
    (hR : 0<o.representatives) (c : ℚ) (hc : RationalHeight c C)
    (columns : Columns T o.m K) (reciprocal : Bool)
    (hColumns : ∀ j l,RationalHeight ((((if reciprocal then columns.poor else columns.rich).read j).anchors).read l) H)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (hBijective : Function.Bijective (GeneralPaperLightFieldIndexEquiv.mapping o.classified))
    (fresh : Fin (Rb+Lb) → Bool) (j : Fin n) :
    RationalHeight ((GeneralPaperCachedCircleSampler.run true model.rat A Rb Lb T S hT hS model o hR c
      (pair price index Ap o hm columns).1 reciprocal fresh).output.read j)
      (C+(binaryWordWidth o.representatives+2*binaryWordWidth o.classified.lightWeight+H)) := by
  rw [GeneralPaperCachedCircleSampler.data]
  exact GeneralPaperNativeFairEveryOutput.height price index model.rat Ap A Rb Lb T S hT hS model o hm
    (if reciprocal then columns.poor else columns.rich) hR c hConserved hBijective C H hc hColumns fresh j

def directProfile (model : RationalCostModel) (A Rb Lb C H n : ℕ) : ℕ :=
  GeneralPaperNativeFreshBufferBits.profile model.rat A (Rb+Lb)+
    GeneralPaperNativeDyadicBlocksBits.profile model.rat A Rb Lb+
    n*(2*model.rat (1+2*(C+H))+192*A)+88*(n+1)*A+128*A

theorem direct_work {n m K : ℕ} (model : RationalCostModel) (A C H Rb Lb T S : ℕ) (hA : 1≤A)
    (hT : T=2^Rb) (hS : S=2^Lb) (hm : m=n) (c : ℚ) (hc : RationalHeight c C)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (hColumns : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H)
    (hIndex : ∀ i≤n,binaryWordWidth (i+1)≤A) (fresh : Fin (Rb+Lb) → Bool) :
    (GeneralPaperDirectRowSampler.run model.rat (fun w => w) model.rat A Rb Lb T S hT hS hm c columns fresh).work≤
      directProfile model A Rb Lb C H n := by
  have hf := GeneralPaperNativeFreshBufferBits.work model.rat model.monotone A fresh
  let buffer := (GeneralPaperNativeFreshBuffer.run model.rat A fresh).1.1
  let decoded := GeneralPaperNativeDyadicBlocks.run model.rat A Rb Lb T S hT hS buffer
  have hd := GeneralPaperNativeDyadicBlocksBits.work model.rat model.monotone A Rb Lb T S hT hS buffer
  have ho := GeneralPaperDirectRowSampler.work model.rat (fun w => w) model.monotone A hA hm c columns C H hc hColumns hIndex decoded.row
  unfold GeneralPaperDirectRowSampler.run directProfile
  dsimp only [buffer,decoded] at hd ho ⊢
  omega

end Blotto.GeneralPaperCachedBitSampling
