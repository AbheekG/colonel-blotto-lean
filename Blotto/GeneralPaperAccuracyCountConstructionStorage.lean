import Blotto.GeneralPaperBooleanRulerWorkStorage

/-! Actual Boolean-ruler-to-natural counter. The full input list is owned
once; every reached recursive frame retains both returned scalars, partial
work fields and the exact unsigned-addition scratch. No length pass executes.
The input length and cap below occur only in erased bounds. -/
namespace Blotto.GeneralPaperAccuracyCountConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperBinaryAccuracy
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def width (E : ℕ) : ℕ := 1+binaryWordWidth (E+1)
def step (W E : ℕ) : ℕ := 32*W+2*width E
def price (W E : ℕ) : ℕ := E*step W E+16*W
def cap (W E : ℕ) : ℕ := E+price W E+2*width E+32*W+1

def controls (W : ℕ) (bits : List Bool) : List ℕ :=
  let made := count (fun w => w) W bits
  [made.1,made.2]++match bits with
  | [] => [16*W]
  | _::rest =>
    let old := count (fun w => w) W rest
    let add := GeneralPaperNaturalPrimitivePrice.binary (fun w => w) (fun a b => a+b) old.1 1
    [old.1,old.2,add,32*W,old.1+1,old.2+add]

def frame (W : ℕ) (bits : List Bool) : ℕ :=
  fields W (controls W bits)+128*W+1+match bits with
  | [] => 0
  | _::rest => GeneralPaperNaturalPrimitivePrice.binary (fun w => w) (fun a b => a+b) (count (fun w => w) W rest).1 1

def frameProfile (W E : ℕ) : ℕ := 8*(natBits (cap W E)+W)+2*width E+160*W+1

def frames (W : ℕ) : List Bool → ℕ
  | [] => frame W []
  | b::rest => frame W (b::rest)+frames W rest

def window (W : ℕ) (bits : List Bool) : ℕ := listFootprint W (fun _ : Bool => 1) bits+frames W bits

def profile (W E : ℕ) : ℕ := E*(1+2*W)+32*W+(E+1)*frameProfile W E

theorem addition (W E : ℕ) (bits : List Bool) (hc : bits.length≤E) :
    GeneralPaperNaturalPrimitivePrice.binary (fun w => w) (fun a b => a+b) (count (fun w => w) W bits).1 1≤2*width E := by
  rw [count_data]
  exact GeneralPaperNaturalPrimitivePrice.binary_le (fun w => w) (fun _ _ h => h) (fun a b => a+b) bits.length 1 (E+1)
    (by omega) (by omega) (by omega)

theorem work (W E : ℕ) (bits : List Bool) (hc : bits.length≤E) :
    (count (fun w => w) W bits).2≤bits.length*step W E+16*W := by
  induction bits with
  | nil => simp only [count,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons b rest ih =>
    have hi := ih (by simp only [List.length_cons] at hc;omega)
    have ha := addition W E rest (by simp only [List.length_cons] at hc;omega)
    change (count (fun w => w) W rest).2+
      GeneralPaperNaturalPrimitivePrice.binary (fun w => w) (fun a b => a+b) (count (fun w => w) W rest).1 1+32*W≤_
    simp only [List.length_cons]
    unfold step at *
    nlinarith only [hi,ha]

theorem work_cap (W E : ℕ) (bits : List Bool) (hc : bits.length≤E) : (count (fun w => w) W bits).2≤price W E :=
  (work W E bits hc).trans (Nat.add_le_add_right (Nat.mul_le_mul_right (step W E) hc) _)

theorem frame_bound (W E : ℕ) (bits : List Bool) (hc : bits.length≤E) : frame W bits≤frameProfile W E := by
  have hw := work_cap W E bits hc
  have hm : (count (fun w => w) W bits).1≤E := by rw [count_data];exact hc
  cases bits with
  | nil =>
    have hf := fields_bound W (natBits (cap W E)) (controls W []) (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [controls,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold cap
      rcases hz with (rfl|rfl)|rfl <;> omega)
    change fields W _≤3*(natBits (cap W E)+W)+32*W at hf
    unfold frame frameProfile
    dsimp only
    omega
  | cons b rest =>
    let old := count (fun w => w) W rest
    let add := GeneralPaperNaturalPrimitivePrice.binary (fun w => w) (fun a b => a+b) old.1 1
    have hRest : rest.length≤E := by simp only [List.length_cons] at hc;omega
    have hOld := work_cap W E rest hRest
    have hOldCount : old.1≤E := by rw [count_data];exact hRest
    have hAdd := addition W E rest hRest
    have hShape : (count (fun w => w) W (b::rest)).2=old.2+add+32*W := rfl
    have hf := fields_bound W (natBits (cap W E)) (controls W (b::rest)) (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [controls,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold cap
      rcases hz with (rfl|rfl)|(rfl|rfl|rfl|rfl|rfl|rfl) <;> dsimp only [old,add] at * <;> omega)
    change fields W _≤8*(natBits (cap W E)+W)+32*W at hf
    unfold frame frameProfile
    dsimp only [old,add] at *
    omega

theorem frames_bound (W E : ℕ) (bits : List Bool) (hc : bits.length≤E) : frames W bits≤(bits.length+1)*frameProfile W E := by
  induction bits with
  | nil => simpa only [frames,List.length_nil,Nat.zero_add,Nat.one_mul] using frame_bound W E [] hc
  | cons b rest ih =>
    have hf := frame_bound W E (b::rest) hc
    have hi := ih (by simp only [List.length_cons] at hc;omega)
    rw [frames]
    exact (Nat.add_le_add hf hi).trans_eq (by simp only [List.length_cons];ring)

theorem bounded (W E : ℕ) (bits : List Bool) (hc : bits.length≤E) : window W bits≤profile W E := by
  have hf := frames_bound W E bits hc
  have hF := hf.trans (Nat.mul_le_mul_right (frameProfile W E) (Nat.add_le_add_right hc 1))
  have hi := list_bound W 1 (fun _ : Bool => 1) bits (fun _ _ => le_rfl)
  have hI := hi.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (1+2*W) hc) _)
  exact Nat.add_le_add hI hF

@[fun_prop]
theorem scaling (E : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => profile W E) := by
  unfold profile frameProfile cap price step
  fun_prop

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth

theorem profile_rate (W E : Input → ℕ) (hW : Tight W) (hE : Small E) : Linear (fun x => profile (W x) (E x)) E := by
  have hw := of_tight hW
  have hWP := poly_tight W hW
  unfold profile frameProfile cap price step width natBits
  fun_prop

end Blotto.GeneralPaperAccuracyCountConstructionStorage
