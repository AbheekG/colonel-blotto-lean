import Blotto.GeneralPaperValueWeightSumConstructionStorage

/-! Native repeated-squaring bit-work fields and primitive scratch join
the already checked complete power-data frames. Every reached prefix uses
the actual bit constructor; no power/height/work census is executed. -/
namespace Blotto.GeneralPaperNatPowerBitConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

def price (model : RationalCostModel) (W base E : ℕ) : ℕ :=
  64*(binaryWordWidth E+1)*(W+model.rat (GeneralPaperNatPowerOperands.width base E))
def cap (model : RationalCostModel) (W base E : ℕ) : ℕ := base+E+price model W base E+64*W+1

def controls (model : RationalCostModel) (W base e : ℕ) : List ℕ :=
  let made := GeneralPaperNatPowerBits.run model.rat W base e
  let test := GeneralPaperIntegerWordPrice.compare model.rat e 0
  if e=0 then [base,e,test,16*W,made.2] else
    let old := GeneralPaperNatPowerBits.run model.rat W base (e/2)
    let divide := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a/b) e 2
    let modulus := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a%b) e 2
    let parity := GeneralPaperIntegerWordPrice.compare model.rat (e%2) 0
    let square := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) old.1.power old.1.power
    let extra := if e%2=0 then 0 else GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b)
      (old.1.power*old.1.power) base
    [base,e,e/2,e%2,old.2,made.2,test,divide,modulus,parity,square,extra,48*W,
      old.2+48*W,old.2+48*W+test,old.2+48*W+test+divide,old.2+48*W+test+divide+modulus,
      old.2+48*W+test+divide+modulus+parity,old.2+48*W+test+divide+modulus+parity+square]

def scratch (model : RationalCostModel) (W base e : ℕ) : ℕ :=
  let test := GeneralPaperIntegerWordPrice.compare model.rat e 0
  if e=0 then test else
    let old := GeneralPaperNatPowerBits.run model.rat W base (e/2)
    test+GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a/b) e 2+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a%b) e 2+
      GeneralPaperIntegerWordPrice.compare model.rat (e%2) 0+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) old.1.power old.1.power+
      (if e%2=0 then 0 else GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) (old.1.power*old.1.power) base)

def frame (model : RationalCostModel) (W base e : ℕ) : ℕ := fields W (controls model W base e)+scratch model W base e+128*W
def frameProfile (model : RationalCostModel) (W base E : ℕ) : ℕ :=
  19*(natBits (cap model W base E)+W)+price model W base E+160*W

theorem work (model : RationalCostModel) (W base E e : ℕ) (hb : 0<base) (he : e≤E) :
    (GeneralPaperNatPowerBits.run model.rat W base e).2≤price model W base E := by
  have hw := GeneralPaperNatPowerBits.work model.rat model.monotone W base e hb
  have hE := binaryWordWidth_mono he
  have hMul := Nat.mul_le_mul_right (binaryWordWidth base) he
  have hWidth : GeneralPaperNatPowerOperands.width base e≤GeneralPaperNatPowerOperands.width base E := by
    unfold GeneralPaperNatPowerOperands.width
    omega
  exact hw.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 64 (Nat.add_le_add_right hE 1))
    (Nat.add_le_add_left (model.monotone hWidth) W))

theorem frame_bound (model : RationalCostModel) (W base E e : ℕ) (hb : 0<base) (he : e≤E) :
    frame model W base e≤frameProfile model W base E := by
  have hw := work model W base E e hb he
  by_cases hz : e=0
  · subst e
    have hShape : (GeneralPaperNatPowerBits.run model.rat W base 0).2=
      16*W+GeneralPaperIntegerWordPrice.compare model.rat 0 0 := by rw [GeneralPaperNatPowerBits.run];rfl
    have hf := fields_bound W (natBits (cap model W base E)) (controls model W base 0) (by
      intro z hm
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [controls,ite_true,List.mem_cons,List.not_mem_nil,or_false] at hm
      unfold cap
      rcases hm with rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields W _≤5*(natBits (cap model W base E)+W)+32*W at hf
    unfold frame frameProfile scratch
    simp only [ite_true]
    omega
  · let old := GeneralPaperNatPowerBits.run model.rat W base (e/2)
    let test := GeneralPaperIntegerWordPrice.compare model.rat e 0
    let divide := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a/b) e 2
    let modulus := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a%b) e 2
    let parity := GeneralPaperIntegerWordPrice.compare model.rat (e%2) 0
    let square := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) old.1.power old.1.power
    let extra := if e%2=0 then 0 else GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) (old.1.power*old.1.power) base
    have hShape : (GeneralPaperNatPowerBits.run model.rat W base e).2=
      old.2+48*W+test+divide+modulus+parity+square+extra := by
      rw [GeneralPaperNatPowerBits.run,ite_eq_right hz]
    have hHalf : e/2≤E := (Nat.div_le_self e 2).trans he
    have hMod : e%2≤E := (Nat.mod_le e 2).trans he
    have hf := fields_bound W (natBits (cap model W base E)) (controls model W base e) (by
      intro z hm
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [controls,ite_eq_right hz,List.mem_cons,List.not_mem_nil,or_false] at hm
      change z=base ∨ z=e ∨ z=e/2 ∨ z=e%2 ∨ z=old.2 ∨ z=(GeneralPaperNatPowerBits.run model.rat W base e).2 ∨
        z=test ∨ z=divide ∨ z=modulus ∨ z=parity ∨ z=square ∨ z=extra ∨ z=48*W ∨
        z=old.2+48*W ∨ z=old.2+48*W+test ∨ z=old.2+48*W+test+divide ∨
        z=old.2+48*W+test+divide+modulus ∨ z=old.2+48*W+test+divide+modulus+parity ∨
        z=old.2+48*W+test+divide+modulus+parity+square at hm
      unfold cap
      rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    have hLength : (controls model W base e).length=19 := by
      simp only [controls,ite_eq_right hz,List.length_cons,List.length_nil]
    rw [hLength] at hf
    have hScratch : scratch model W base e≤price model W base E := by
      unfold scratch
      rw [ite_eq_right hz]
      change test+divide+modulus+parity+square+extra≤_
      omega
    unfold frame frameProfile
    omega

def frames (model : RationalCostModel) (W base e : ℕ) : ℕ :=
  frame model W base e+if e=0 then 0 else frames model W base (e/2)
termination_by e
decreasing_by omega

theorem frames_bound (model : RationalCostModel) (W base E e : ℕ) (hb : 0<base) (he : e≤E) :
    frames model W base e≤((GeneralPaperNatPower.run base e).steps+1)*frameProfile model W base E := by
  have hf := frame_bound model W base E e hb he
  rw [frames]
  by_cases hz : e=0
  · subst e
    rw [GeneralPaperNatPower.run]
    simpa only [ite_true,Nat.add_zero,Nat.zero_add,Nat.one_mul] using hf
  · rw [ite_eq_right hz]
    have hi := frames_bound model W base E (e/2) hb ((Nat.div_le_self e 2).trans he)
    have hs : (GeneralPaperNatPower.run base e).steps=(GeneralPaperNatPower.run base (e/2)).steps+1 := by
      rw [GeneralPaperNatPower.run,ite_eq_right hz]
    rw [hs]
    nlinarith only [hf,hi]
termination_by e
decreasing_by omega

def dataFrame (model : RationalCostModel) (W base e : ℕ) : ℕ :=
  let child := (GeneralPaperNatPowerBits.run model.rat W base (e/2)).1
  let made := (GeneralPaperNatPowerBits.run model.rat W base e).1
  fields W [base,e,e/2,e%2,child.power*child.power]+
    GeneralPaperNatPowerConstructionStorage.record W child+GeneralPaperNatPowerConstructionStorage.record W made+256*W

theorem data_frame_eq (model : RationalCostModel) (W base e : ℕ) :
    dataFrame model W base e=GeneralPaperNatPowerConstructionStorage.frame W base e := by
  simp only [dataFrame,GeneralPaperNatPowerConstructionStorage.frame,GeneralPaperNatPowerBits.data]

def dataFrames (model : RationalCostModel) (W base e : ℕ) : ℕ :=
  dataFrame model W base e+if e=0 then 0 else dataFrames model W base (e/2)
termination_by e
decreasing_by omega

theorem data_frames_eq (model : RationalCostModel) (W base e : ℕ) :
    dataFrames model W base e=GeneralPaperNatPowerConstructionStorage.peak W base e := by
  rw [dataFrames,GeneralPaperNatPowerConstructionStorage.peak,data_frame_eq]
  split_ifs
  · rfl
  · rw [data_frames_eq model W base (e/2)]
termination_by e
decreasing_by omega

def window (model : RationalCostModel) (W base e : ℕ) : ℕ :=
  dataFrames model W base e+frames model W base e+128*W
def profile (model : RationalCostModel) (W base E : ℕ) : ℕ :=
  (binaryWordWidth E+1)*(12*GeneralPaperNatPowerConstructionStorage.payload base E+384*W+frameProfile model W base E)+128*W

theorem bounded (model : RationalCostModel) (W base E e : ℕ) (hb : 0<base) (he : e≤E) :
    window model W base e≤profile model W base E := by
  have hData := GeneralPaperNatPowerConstructionStorage.depth_bound W base E e hb he
  have hFrames := frames_bound model W base E e hb he
  have hs := GeneralPaperNatPower.steps_le base e (binaryWordWidth E)
    ((lt_pow_binaryWordWidth e).trans_le (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (binaryWordWidth_mono he)))
  have hF := hFrames.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hs 1))
  unfold window profile
  rw [data_frames_eq]
  nlinarith only [hData,hF]

@[fun_prop]
theorem scaling (model : RationalCostModel) (base E : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => profile model W base E) := by
  unfold profile frameProfile cap price
  fun_prop

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds

theorem dyadic_profile_poly {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W : Input → ℕ) (hW : Tight W) : Polylog (fun x => profile model (W x) 2 x.k) := by
  have hw := of_tight hW
  have hr : Polylog W := poly_tight W hW
  have hPower : Small (fun x => 2^x.k) := pow_two _ k_tight
  have hOperand : Polylog (fun x => GeneralPaperNatPowerOperands.width 2 x.k) := by
    unfold GeneralPaperNatPowerOperands.width
    fun_prop
  have hOperandSmall := GeneralPaperCacheConstructionGrowth.small_of_poly hOperand
  have hRat : Polylog (fun x => model.rat (GeneralPaperNatPowerOperands.width 2 x.k)) := primitive_preserves hg hOperand hOperandSmall
  have hRatSmall := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ hOperandSmall
  unfold profile frameProfile cap price GeneralPaperNatPowerConstructionStorage.payload natBits
  fun_prop

end Blotto.GeneralPaperNatPowerBitConstructionStorage
