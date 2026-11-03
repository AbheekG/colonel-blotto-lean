import Blotto.GeneralPaperQuotientConstructionStorage
import Blotto.GeneralPaperScoreConstructionStorage
import Blotto.GeneralPaperReferenceScaling

/-! Storage for the actual bit-priced bounded quotient. The earlier data
and primitive-scratch window is retained; native bit-work counters and the
intermediate common-price accumulator are encoded in additional frames.
Their values enter only through word lengths, never as total runtime space.
The input rational is shared along the descent. -/
namespace Blotto.GeneralPaperBitQuotientStorage
open GeneralPaperBoundedQuotient GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

def common (model : RationalCostModel) (W : ℕ) (x a : ℚ) (d : ℕ) : ℕ :=
  let higher := runWithBits model W x (2*a) d
  higher.2+64*W+primitivePrice model 2 a+rationalWordWidth (2*a)+primitivePrice model a higher.1.remainder

theorem common_le_return (model : RationalCostModel) (W : ℕ) (x a : ℚ) (d : ℕ) :
    common model W x a d≤(runWithBits model W x a (d+1)).2 := by
  unfold runWithBits
  dsimp only
  split
  all_goals unfold common; dsimp only; omega

def counters (model : RationalCostModel) (W : ℕ) (x a : ℚ) : ℕ → ℕ
  | 0 => fields W [0,(runWithBits model W x a 0).2]+128*W
  | d+1 => fields W [d+1,(runWithBits model W x (2*a) d).2,common model W x a d,
      (runWithBits model W x a (d+1)).2]+128*W+counters model W x (2*a) d

def metadataCap (model : RationalCostModel) (W A t d : ℕ) : ℕ := d+1+bitProfile model W A t d

def counterFrameProfile (model : RationalCostModel) (W A t d : ℕ) : ℕ :=
  4*(natBits (metadataCap model W A t d)+W)+160*W

theorem metadata_step (model : RationalCostModel) (W A t d : ℕ) :
    metadataCap model W A (t+2) d≤metadataCap model W A t (d+1) := by
  unfold metadataCap bitProfile
  rw [budget_step]
  have h := Nat.mul_le_mul_right (64*W+6*model.rat (1+2*heightBudget A t (d+1)))
    (show d+1≤d+1+1 by omega)
  omega

theorem frame_step (model : RationalCostModel) (W A t d : ℕ) :
    counterFrameProfile model W A (t+2) d≤counterFrameProfile model W A t (d+1) := by
  have h := binaryWordWidth_mono (metadata_step model W A t d)
  unfold counterFrameProfile natBits
  omega

theorem counters_bound (model : RationalCostModel) (W : ℕ) (x a : ℚ) (ha : 0<a) (d A t : ℕ)
    (hx : 0≤x) (hc : x<a*(2:ℚ)^d) (hX : RationalHeight x A) (hA : RationalHeight a t) :
    counters model W x a d≤(d+1)*counterFrameProfile model W A t d := by
  induction d generalizing a t with
  | zero =>
    have hw := run_bit_work model W x a ha 0 A t hx hc hX hA
    have hm : (runWithBits model W x a 0).2≤metadataCap model W A t 0 := by unfold metadataCap; omega
    have hf := GeneralPaperScoreConstructionStorage.two_fields_bound W (metadataCap model W A t 0) 0
      (runWithBits model W x a 0).2 (Nat.zero_le _) hm
    change fields W [0,(runWithBits model W x a 0).2]+128*W≤1*counterFrameProfile model W A t 0
    unfold counterFrameProfile
    omega
  | succ d ih =>
    have hcap : x<(2*a)*(2:ℚ)^d := by rw [pow_succ] at hc; nlinarith only [hc]
    have hDouble := doubled_height a t hA
    have hRec := ih (a:=2*a) (t:=t+2) (by positivity) hcap hDouble
    have hRec' := hRec.trans (Nat.mul_le_mul_left (d+1) (frame_step model W A t d))
    have hChild := run_bit_work model W x (2*a) (by positivity) d A (t+2) hx hcap hX hDouble
    have hChild' : (runWithBits model W x (2*a) d).2≤metadataCap model W A t (d+1) := by
      have hStep := metadata_step model W A t d
      unfold metadataCap at *
      omega
    have hCurrent := run_bit_work model W x a ha (d+1) A t hx hc hX hA
    have hCurrent' : (runWithBits model W x a (d+1)).2≤metadataCap model W A t (d+1) := by
      unfold metadataCap
      omega
    have hCommon := (common_le_return model W x a d).trans hCurrent'
    have hf := fields_bound W (natBits (metadataCap model W A t (d+1)))
      [d+1,(runWithBits model W x (2*a) d).2,common model W x a d,(runWithBits model W x a (d+1)).2] (by
        intro n hn
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
        rcases hn with rfl|rfl|rfl|rfl
        · unfold metadataCap; omega
        · exact hChild'
        · exact hCommon
        · exact hCurrent')
    change fields W _≤4*(natBits (metadataCap model W A t (d+1))+W)+32*W at hf
    have hFrame : fields W [d+1,(runWithBits model W x (2*a) d).2,common model W x a d,
        (runWithBits model W x a (d+1)).2]+128*W≤counterFrameProfile model W A t (d+1) := by
      unfold counterFrameProfile
      omega
    exact (Nat.add_le_add hFrame hRec').trans_eq (by ring)

def peak (model : RationalCostModel) (W : ℕ) (x a : ℚ) (d : ℕ) : ℕ :=
  GeneralPaperQuotientConstructionStorage.peak model W x a d+counters model W x a d

def profile (model : RationalCostModel) (W A t d : ℕ) : ℕ :=
  (d+1)*GeneralPaperQuotientConstructionStorage.frameCap W t d+
    GeneralPaperQuotientConstructionStorage.localCap model W A t d+(d+1)*counterFrameProfile model W A t d

theorem bounded (model : RationalCostModel) (W : ℕ) (x a : ℚ) (ha : 0<a) (d A t : ℕ)
    (hx : 0≤x) (hc : x<a*(2:ℚ)^d) (hX : RationalHeight x A) (hA : RationalHeight a t) :
    peak model W x a d≤profile model W A t d :=
  Nat.add_le_add (GeneralPaperQuotientConstructionStorage.bounded model W x a ha d A t hx hc hX hA)
    (counters_bound model W x a ha d A t hx hc hX hA)

theorem returned_record (model : RationalCostModel) (W : ℕ) (x a : ℚ) (ha : 0<a) (d A t : ℕ)
    (hx : 0≤x) (hc : x<a*(2:ℚ)^d) (hX : RationalHeight x A) (hA : RationalHeight a t) :
    GeneralPaperQuotientConstructionStorage.record W (runWithBits model W x a d).1≤4*(1+2*heightBudget A t d)+128*W := by
  rw [run_data]
  exact GeneralPaperQuotientConstructionStorage.record_bound W x a ha d A t hx hc hX hA

@[fun_prop]
theorem scaling (model : RationalCostModel) (A t d : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => profile model W A t d) := by
  unfold profile counterFrameProfile metadataCap bitProfile GeneralPaperQuotientConstructionStorage.frameCap
    GeneralPaperQuotientConstructionStorage.localCap
  fun_prop

end Blotto.GeneralPaperBitQuotientStorage
