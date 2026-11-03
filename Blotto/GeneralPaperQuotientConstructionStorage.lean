import Blotto.GeneralPaperSelectionConstructionStorage

/-! Native bounded-quotient stack storage. Descent retains divisor/control
frames and shares x; only the selected unwind step owns child/current
remainders. Thus original-input precision is charged once, not at every
ancestor. All observers are erased; no replay or trace is introduced. -/
namespace Blotto.GeneralPaperQuotientConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperBoundedQuotient
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def record (W : ℕ) (r : Result) : ℕ := fields W [r.quotient,r.work]+rationalWordWidth r.remainder+64*W

theorem record_bound (W : ℕ) (x a : ℚ) (ha : 0<a) (d A t : ℕ) (hx : 0≤x)
    (hc : x<a*(2:ℚ)^d) (hX : RationalHeight x A) (hA : RationalHeight a t) :
    record W (run x a d)≤4*(1+2*heightBudget A t d)+128*W := by
  have hq := GeneralPaperBoundedQuotient.quotient_words x a ha d hx hc
  have hw := run_work x a d
  have hwm := GeneralPaperRayOperandWidthEnvelope.word_add (12*d) 2
  have hwp := binaryWordWidth_mul 12 d
  have h12 : binaryWordWidth 12=4 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  have hd := GeneralPaperInitializerControlCounters.word_le_self d
  have hf := fields_bound W (d+12) [(run x a d).quotient,(run x a d).work] (by
    intro n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl|rfl <;> unfold natBits
    · omega
    · rw [hw]; omega)
  have hr := rationalWordWidth_of_height (remainder_common x a ha d A t hx hc hX hA)
  change _≤2*(d+12+W)+32*W at hf
  unfold record heightBudget at *
  omega

def frame (W : ℕ) (a : ℚ) (d : ℕ) : ℕ := rationalWordWidth a+fields W [d]+64*W

def frameCap (W t d : ℕ) : ℕ := 4*(t+2*d+8)+128*W

theorem frame_bound (W t d : ℕ) (a : ℚ) (ha : RationalHeight a t) : frame W a d≤frameCap W t d := by
  have h := rationalWordWidth_of_height ha
  have hd := GeneralPaperInitializerControlCounters.word_le_self d
  unfold frame fields frameCap natBits
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega

def localWindow (model : RationalCostModel) (W : ℕ) (x a : ℚ) (d : ℕ) : ℕ :=
  let child := run x (2*a) d
  record W child+record W (run x a (d+1))+rationalWordWidth (2*a)+
    primitivePrice model 2 a+primitivePrice model a child.remainder+
      primitivePrice model child.remainder a+
        fields W [2*child.quotient,2*child.quotient+1]+256*W

def localCap (model : RationalCostModel) (W A t d : ℕ) : ℕ :=
  let H := 1+2*heightBudget A t d
  32*H+640*W+8*model.rat H

theorem local_bound (model : RationalCostModel) (W : ℕ) (x a : ℚ) (ha : 0<a) (d A t : ℕ)
    (hx : 0≤x) (hc : x<a*(2:ℚ)^(d+1)) (hX : RationalHeight x A) (hA : RationalHeight a t) :
    localWindow model W x a d≤localCap model W A t (d+1) := by
  let H := 1+2*heightBudget A t (d+1)
  have hcap : x<(2*a)*(2:ℚ)^d := by rw [pow_succ] at hc; nlinarith only [hc]
  have hdouble := doubled_height a t hA
  have hchild := record_bound W x (2*a) (by positivity) d A (t+2) hx hcap hX hdouble
  rw [budget_step] at hchild
  have hcurrent := record_bound W x a ha (d+1) A t hx hc hX hA
  have hold : rationalWordWidth a≤H :=
    rationalWordWidth_of_height (hA.mono (by dsimp [H,heightBudget]; omega))
  have htwo : rationalWordWidth (2:ℚ)≤H := by
    have h2 : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
    exact rationalWordWidth_of_height (h2.mono (by dsimp [H,heightBudget]; omega))
  have hd : rationalWordWidth (2*a)≤H :=
    rationalWordWidth_of_height (hdouble.mono (by dsimp [H,heightBudget]; omega))
  have hr := rationalWordWidth_of_height (higher_remainder_common x a ha d A t hx hc hX hA)
  change rationalWordWidth (run x (2*a) d).remainder≤H at hr
  have hp0 := primitivePrice_le model 2 a H htwo hold
  have hp1 := primitivePrice_le model a (run x (2*a) d).remainder H hold hr
  have hp2 := primitivePrice_le model (run x (2*a) d).remainder a H hr hold
  have hq := GeneralPaperInitializerRoundingBits.quotient_shape x (2*a) d
  have hq0 : 2*(run x (2*a) d).quotient<2^(d+1) := by rw [pow_succ]; omega
  have hq1 : 2*(run x (2*a) d).quotient+1<2^(d+1) := by rw [pow_succ]; omega
  have hw0 := binaryWordWidth_le_of_lt_pow (by omega : 0<d+1) hq0
  have hw1 := binaryWordWidth_le_of_lt_pow (by omega : 0<d+1) hq1
  have hf := fields_bound W (d+2) [2*(run x (2*a) d).quotient,2*(run x (2*a) d).quotient+1] (by
    intro n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl|rfl <;> unfold natBits <;> omega)
  change _≤2*(d+2+W)+32*W at hf
  unfold localWindow localCap
  dsimp only
  change _≤32*H+640*W+8*model.rat H
  change record W (run x (2*a) d)≤4*H+128*W at hchild
  change record W (run x a (d+1))≤4*H+128*W at hcurrent
  have hH : d+2≤H := by dsimp [H,heightBudget]; omega
  omega

def peak (model : RationalCostModel) (W : ℕ) (x a : ℚ) : ℕ → ℕ
  | 0 => frame W a 0+record W (run x a 0)+model.rat (rationalWordWidth x)+256*W
  | d+1 => frame W a (d+1)+max (peak model W x (2*a) d) (localWindow model W x a d)

theorem bounded (model : RationalCostModel) (W : ℕ) (x a : ℚ) (ha : 0<a) (d A t : ℕ)
    (hx : 0≤x) (hc : x<a*(2:ℚ)^d) (hX : RationalHeight x A) (hA : RationalHeight a t) :
    peak model W x a d≤(d+1)*frameCap W t d+localCap model W A t d := by
  induction d generalizing a t with
  | zero =>
    have hf := frame_bound W t 0 a hA
    have hr := record_bound W x a ha 0 A t hx hc hX hA
    have hXw : rationalWordWidth x≤1+2*heightBudget A t 0 :=
      rationalWordWidth_of_height (hX.mono (by unfold heightBudget; omega))
    have hs := model.monotone hXw
    unfold peak localCap
    simp only [Nat.zero_add,Nat.one_mul]
    omega
  | succ d ih =>
    have hcap : x<(2*a)*(2:ℚ)^d := by rw [pow_succ] at hc; nlinarith only [hc]
    have hi := ih (a:=2*a) (t:=t+2) (by positivity) hcap (doubled_height a t hA)
    have hf := frame_bound W t (d+1) a hA
    have hl := local_bound model W x a ha d A t hx hc hX hA
    have he : frameCap W (t+2) d=frameCap W t (d+1) := by unfold frameCap; omega
    have he' : localCap model W A (t+2) d=localCap model W A t (d+1) := by
      unfold localCap
      rw [budget_step]
    rw [he,he'] at hi
    have hlocal : localWindow model W x a d≤(d+1)*frameCap W t (d+1)+localCap model W A t (d+1) :=
      hl.trans (Nat.le_add_left _ _)
    have hm := max_le hi hlocal
    change frame W a (d+1)+max (peak model W x (2*a) d) (localWindow model W x a d)≤_
    nlinarith only [hf,hm]

end Blotto.GeneralPaperQuotientConstructionStorage
