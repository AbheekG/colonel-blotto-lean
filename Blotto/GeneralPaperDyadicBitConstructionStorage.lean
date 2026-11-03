import Blotto.GeneralPaperOriginalSourcePreparationStorage

/-! Literal native linear-doubling bit-constructor frames. Actual returned
power/depth/unpriced-work and priced-work fields, pending child records,
partial priced counters and multiply scratch are all retained. -/
namespace Blotto.GeneralPaperDyadicBitConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 4000000

def width (N : ℕ) : ℕ := 16+4*N
def price (model : RationalCostModel) (W N : ℕ) : ℕ := 64*(N+1)*(W+model.rat (width N))
def cap (model : RationalCostModel) (W N : ℕ) : ℕ := N+8*N+price model W N+32*W+32

def controls (model : RationalCostModel) (W : ℕ) (e : ℕ) : List ℕ :=
  let made := GeneralPaperDyadicPowerBits.run model.rat W e
  [e,made.1.doublings,made.1.work,made.2]++match e with
  | 0 => [16*W]
  | j+1 =>
    let old := GeneralPaperDyadicPowerBits.run model.rat W j
    let multiply := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 old.1.power
    [j,old.1.doublings,old.1.work,old.2,old.1.doublings+1,old.1.work+8,32*W,multiply,old.2+32*W]

def frame (model : RationalCostModel) (W e : ℕ) : ℕ :=
  let made := GeneralPaperDyadicPowerBits.run model.rat W e
  natBits made.1.power+fields W (controls model W e)+128*W+match e with
  | 0 => 0
  | j+1 =>
    let old := GeneralPaperDyadicPowerBits.run model.rat W j
    natBits 2+natBits old.1.power+natBits (2*old.1.power)+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 old.1.power

def frameProfile (model : RationalCostModel) (W N : ℕ) : ℕ :=
  4*width N+2*model.rat (width N)+13*(natBits (cap model W N)+W)+160*W

def window (model : RationalCostModel) (W : ℕ) : ℕ → ℕ
  | 0 => frame model W 0
  | j+1 => frame model W (j+1)+window model W j

def profile (model : RationalCostModel) (W N : ℕ) : ℕ := (N+1)*frameProfile model W N

theorem data_bounds (model : RationalCostModel) (W N e : ℕ) (he : e≤N) :
    let made := GeneralPaperDyadicPowerBits.run model.rat W e
    natBits made.1.power≤width N ∧ made.1.doublings=e ∧ made.1.work=8*e+2 := by
  simp only [GeneralPaperDyadicPowerBits.data,GeneralPaperScoreScaleParameters.power_data]
  refine ⟨?_,by trivial,by trivial⟩
  simp only [natBits,binaryWordWidth,Nat.log2_two_pow]
  unfold width
  omega

theorem work (model : RationalCostModel) (W N e : ℕ) (he : e≤N) :
    (GeneralPaperDyadicPowerBits.run model.rat W e).2≤price model W N := by
  have hw := GeneralPaperDyadicPowerBits.work model.rat model.monotone W e
  have hm := model.monotone (show 8+2*e≤width N by unfold width;omega)
  exact hw.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 64 (Nat.add_le_add_right he 1)) (Nat.add_le_add_left hm W))

theorem frame_bound (model : RationalCostModel) (W N e : ℕ) (he : e≤N) : frame model W e≤frameProfile model W N := by
  have hd := data_bounds model W N e he
  have hw := work model W N e he
  cases e with
  | zero =>
    have hf := fields_bound W (natBits (cap model W N)) (controls model W 0) (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [controls,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold cap
      rcases hz with (rfl|rfl|rfl|rfl)|rfl <;> omega)
    change fields W _≤5*(natBits (cap model W N)+W)+32*W at hf
    unfold frame frameProfile
    dsimp only
    omega
  | succ j =>
    let old := GeneralPaperDyadicPowerBits.run model.rat W j
    let multiply := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 old.1.power
    have ho := data_bounds model W N j (by omega)
    have hOld := work model W N j (by omega)
    have hDouble : natBits (2*old.1.power)≤width N := by
      rw [show old.1.power=2^j by rw [GeneralPaperDyadicPowerBits.data,(GeneralPaperScoreScaleParameters.power_data j).1],
        show 2*2^j=2^(j+1) by rw [pow_succ];omega]
      simp only [natBits,binaryWordWidth,Nat.log2_two_pow]
      unfold width
      omega
    have hTwo : natBits 2≤width N := by unfold width;norm_num [natBits,binaryWordWidth];omega
    have hMul : multiply≤2*model.rat (width N) :=
      GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) 2 old.1.power (width N)
        hTwo ho.1 hDouble
    have hShape : (GeneralPaperDyadicPowerBits.run model.rat W (j+1)).2=old.2+32*W+multiply := rfl
    have hf := fields_bound W (natBits (cap model W N)) (controls model W (j+1)) (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [controls,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold cap
      rcases hz with (rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> dsimp only [old,multiply] at * <;> omega)
    change fields W _≤13*(natBits (cap model W N)+W)+32*W at hf
    unfold frame frameProfile
    dsimp only [old,multiply] at *
    omega

theorem bounded (model : RationalCostModel) (W N e : ℕ) (he : e≤N) : window model W e≤(e+1)*frameProfile model W N := by
  induction e with
  | zero => simpa only [window,Nat.zero_add,Nat.one_mul] using frame_bound model W N 0 he
  | succ j ih =>
    have hf := frame_bound model W N (j+1) he
    have hj := ih (by omega)
    rw [window]
    exact (Nat.add_le_add hf hj).trans_eq (by ring)

@[fun_prop]
theorem scaling (model : RationalCostModel) (N : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => profile model W N) := by
  unfold profile frameProfile cap price
  fun_prop

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds

theorem profile_poly {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W N : Input → ℕ) (hW : Tight W) (hN : Tight N) : Polylog (fun x => profile model (W x) (N x)) := by
  have hNSmall := of_tight hN
  have hWSmall := of_tight hW
  have hWP := poly_tight W hW
  have hNP := poly_tight N hN
  have hWidth : Polylog (fun x => width (N x)) := by unfold width;fun_prop
  have hWidthSmall := GeneralPaperCacheConstructionGrowth.small_of_poly hWidth
  have hRat : Polylog (fun x => model.rat (width (N x))) := primitive_preserves hg hWidth hWidthSmall
  have hRatSmall := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ hWidthSmall
  unfold profile frameProfile cap price natBits
  fun_prop

end Blotto.GeneralPaperDyadicBitConstructionStorage
