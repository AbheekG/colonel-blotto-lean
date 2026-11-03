import Blotto.GeneralPaperSourceColumnInputReachedRates

/-! The actual adaptive natural quotient stack. Only reached tests and
successful doublings recurse. Each frame counts complete natural operands,
both returned records, primitive scratch and native partial-work fields.
Fuel is encoded metadata; stack size uses the actual successful depth. -/
namespace Blotto.GeneralPaperNativeGrowingQuotientStorage
open GeneralPaperEncodedScalarStorage GeneralPaperIntegerWordPrice
open GeneralPaperGrowingQuotientBits (run extra)
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

def workCap (model : RationalCostModel) (W M D : ℕ) : ℕ :=
  256*(D+1)*(W+model.rat (1+binaryWordWidth M))
def metadataCap (model : RationalCostModel) (W M F D : ℕ) : ℕ :=
  M+15*F+workCap model W M D+256*W+16

theorem result_bounds (model : RationalCostModel) (W n a fuel : ℕ) (ha : 0<a) :
    (run model.rat W n a fuel).1.quotient≤n ∧ (run model.rat W n a fuel).1.remainder≤n ∧
      (run model.rat W n a fuel).1.depth≤fuel ∧ (run model.rat W n a fuel).1.work≤14*fuel+4 := by
  rw [GeneralPaperGrowingQuotientBits.data]
  have hb := GeneralPaperNaturalGrowingQuotient.operand_bounds n a fuel ha
  have hc := GeneralPaperNaturalGrowingQuotient.counters n a fuel
  exact ⟨hb.1,hb.2.1,hc.2,by omega⟩

theorem depth_step (model : RationalCostModel) (W n a fuel : ℕ) (hs : ¬n<a) :
    (run model.rat W n a (fuel+1)).1.depth=(run model.rat W n (2*a) fuel).1.depth+1 := by
  rw [run,ite_eq_right hs]
  dsimp only
  split <;> rfl

theorem work_bound (model : RationalCostModel) (W n a fuel M D : ℕ) (ha : 0<a)
    (hn : 2*(n+1)≤M) (hA : a≤M) (hd : (run model.rat W n a fuel).1.depth≤D) :
    (run model.rat W n a fuel).2≤workCap model W M D :=
  (GeneralPaperGrowingQuotientBits.bounded_work model.rat model.monotone W n a fuel M ha hn hA).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 256 (Nat.add_le_add_right hd 1)))

def scratch (model : RationalCostModel) (W n a : ℕ) : ℕ → ℕ
  | 0 => model.rat (1+binaryWordWidth n)
  | fuel+1 =>
    let test := compare model.rat n a
    if n<a then test+model.rat (1+binaryWordWidth n) else
      let higher := run model.rat W n (2*a) fuel
      test+GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 a+
        compare model.rat a higher.1.remainder+
        GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 higher.1.quotient+
        extra model.rat a higher.1

theorem scratch_bound (model : RationalCostModel) (W n a fuel M : ℕ) (ha : 0<a)
    (hn : 2*(n+1)≤M) (hA : a≤M) : scratch model W n a fuel≤10*model.rat (1+binaryWordWidth M) := by
  let L := 1+binaryWordWidth M
  let P := model.rat L
  have bound (x : ℕ) (hx : x≤M) : 1+binaryWordWidth x≤L :=
    Nat.add_le_add_left (binaryWordWidth_mono hx) 1
  have hw := model.monotone (bound n (by omega))
  have ht := compare_le model.rat model.monotone n a L (bound n (by omega)) (bound a hA)
  change _≤P at hw ht
  change scratch model W n a fuel≤10*P
  cases fuel with
  | zero => exact hw.trans (by omega)
  | succ fuel =>
    by_cases hs : n<a
    · change (if n<a then _ else _)≤_
      rw [ite_eq_left hs]
      omega
    · have hb := result_bounds model W n (2*a) fuel (by omega)
      have hDouble : 2*a≤M := by omega
      have hD := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b) 2 a M (by omega) hA hDouble
      have hC := compare_le model.rat model.monotone a (run model.rat W n (2*a) fuel).1.remainder L
        (bound a hA) (bound _ (by omega))
      have hQ := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b)
        2 (run model.rat W n (2*a) fuel).1.quotient M (by omega) (by omega) (by omega)
      have hE : extra model.rat a (run model.rat W n (2*a) fuel).1≤4*P := by
        unfold extra
        split
        · have hAdd := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b)
            (2*(run model.rat W n (2*a) fuel).1.quotient) 1 M (by omega) (by omega) (by omega)
          have hSub := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a-b)
            (run model.rat W n (2*a) fuel).1.remainder a M (by omega) hA (by omega)
          change _≤2*P at hAdd hSub
          omega
        · exact (model.monotone (bound _ (by omega))).trans (by omega)
      change (if n<a then _ else _)≤_
      rw [ite_eq_right hs]
      change _≤P at ht hC
      change _≤2*P at hD hQ
      omega

def controls (model : RationalCostModel) (W n a : ℕ) : ℕ → List ℕ
  | 0 => [n,a,0,0,n,0,4,(run model.rat W n a 0).2,model.rat (1+binaryWordWidth n),16*W]
  | fuel+1 =>
    let test := compare model.rat n a
    let result := run model.rat W n a (fuel+1)
    if n<a then [n,a,fuel+1,0,n,0,4,result.2,test,model.rat (1+binaryWordWidth n),32*W,32*W+test,1] else
      let higher := run model.rat W n (2*a) fuel
      let doubleA := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 a
      let bitTest := compare model.rat a higher.1.remainder
      let doubleQ := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 higher.1.quotient
      let tail := extra model.rat a higher.1
      [n,a,fuel+1,2*a,2*higher.1.quotient,2*higher.1.quotient+1,higher.1.remainder-a,
        higher.1.quotient,higher.1.remainder,higher.1.depth,higher.1.work,
        result.1.quotient,result.1.remainder,result.1.depth,result.1.work,
        higher.2,result.2,test,doubleA,bitTest,doubleQ,tail,higher.2+64*W,higher.2+64*W+test,
        higher.2+64*W+test+doubleA,higher.2+64*W+test+doubleA+bitTest,
        higher.2+64*W+test+doubleA+bitTest+doubleQ,64*W,if a≤higher.1.remainder then 1 else 0]

theorem controls_length (model : RationalCostModel) (W n a fuel : ℕ) : (controls model W n a fuel).length≤32 := by
  cases fuel with
  | zero => simp only [controls,List.length_cons,List.length_nil]; omega
  | succ fuel =>
    by_cases hs : n<a
    · simp only [controls,ite_eq_left hs,List.length_cons,List.length_nil]; omega
    · simp only [controls,ite_eq_right hs,List.length_cons,List.length_nil]; omega

theorem controls_bound (model : RationalCostModel) (W n a fuel M F D : ℕ) (ha : 0<a)
    (hn : 2*(n+1)≤M) (hA : a≤M) (hf : fuel≤F) (hd : (run model.rat W n a fuel).1.depth≤D) :
    ∀ z∈controls model W n a fuel,z≤metadataCap model W M F D := by
  have hw := work_bound model W n a fuel M D ha hn hA hd
  cases fuel with
  | zero =>
    have he : (run model.rat W n a 0).2=16*W+model.rat (1+binaryWordWidth n) := rfl
    intro z hz
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold metadataCap; omega
  | succ fuel =>
    by_cases hs : n<a
    · have he : (run model.rat W n a (fuel+1)).2=32*W+compare model.rat n a+model.rat (1+binaryWordWidth n) := by
        rw [run,ite_eq_left hs]
      intro z hz
      simp only [controls,ite_eq_left hs,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega
    · let higher := run model.rat W n (2*a) fuel
      let result := run model.rat W n a (fuel+1)
      let test := compare model.rat n a
      let doubleA := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 a
      let bitTest := compare model.rat a higher.1.remainder
      let doubleQ := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 higher.1.quotient
      let tail := extra model.rat a higher.1
      have hHigher := result_bounds model W n (2*a) fuel (by omega)
      change higher.1.quotient≤n ∧ higher.1.remainder≤n ∧ higher.1.depth≤fuel ∧ higher.1.work≤14*fuel+4 at hHigher
      have hResult := result_bounds model W n a (fuel+1) ha
      change result.1.quotient≤n ∧ result.1.remainder≤n ∧ result.1.depth≤fuel+1 ∧ result.1.work≤14*(fuel+1)+4 at hResult
      have he : result.2=higher.2+64*W+test+doubleA+bitTest+doubleQ+tail := by
        change (run model.rat W n a (fuel+1)).2=_
        rw [run,ite_eq_right hs]
      change result.2≤workCap model W M D at hw
      intro z hz
      simp only [controls,ite_eq_right hs] at hz
      change z∈[n,a,fuel+1,2*a,2*higher.1.quotient,2*higher.1.quotient+1,higher.1.remainder-a,
        higher.1.quotient,higher.1.remainder,higher.1.depth,higher.1.work,
        result.1.quotient,result.1.remainder,result.1.depth,result.1.work,
        higher.2,result.2,test,doubleA,bitTest,doubleQ,tail,higher.2+64*W,higher.2+64*W+test,
        higher.2+64*W+test+doubleA,higher.2+64*W+test+doubleA+bitTest,
        higher.2+64*W+test+doubleA+bitTest+doubleQ,64*W,if a≤higher.1.remainder then 1 else 0] at hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap
      all_goals first | split_ifs <;> omega | omega

def frame (model : RationalCostModel) (W n a fuel : ℕ) : ℕ :=
  fields W (controls model W n a fuel)+scratch model W n a fuel+256*W
def frameProfile (model : RationalCostModel) (W M F D : ℕ) : ℕ :=
  32*(natBits (metadataCap model W M F D)+W)+10*model.rat (1+binaryWordWidth M)+320*W

theorem frame_bound (model : RationalCostModel) (W n a fuel M F D : ℕ) (ha : 0<a)
    (hn : 2*(n+1)≤M) (hA : a≤M) (hf : fuel≤F) (hd : (run model.rat W n a fuel).1.depth≤D) :
    frame model W n a fuel≤frameProfile model W M F D := by
  have hFields := fields_bound W (natBits (metadataCap model W M F D)) (controls model W n a fuel)
    (fun z hz => Nat.add_le_add_left (binaryWordWidth_mono (controls_bound model W n a fuel M F D ha hn hA hf hd z hz)) 1)
  have hLength := Nat.mul_le_mul_right (natBits (metadataCap model W M F D)+W) (controls_length model W n a fuel)
  have hScratch := scratch_bound model W n a fuel M ha hn hA
  unfold frame frameProfile
  omega

def peak (model : RationalCostModel) (W n a : ℕ) : ℕ → ℕ
  | 0 => frame model W n a 0
  | fuel+1 => frame model W n a (fuel+1)+(if n<a then 0 else peak model W n (2*a) fuel)

theorem peak_bound (model : RationalCostModel) (W n a fuel M F D : ℕ) (ha : 0<a)
    (hn : 2*(n+1)≤M) (hA : a≤M) (hf : fuel≤F) (hd : (run model.rat W n a fuel).1.depth≤D) :
    peak model W n a fuel≤((run model.rat W n a fuel).1.depth+1)*frameProfile model W M F D := by
  induction fuel generalizing a with
  | zero => simpa only [peak,run,Nat.zero_add,Nat.one_mul] using frame_bound model W n a 0 M F D ha hn hA hf hd
  | succ fuel ih =>
    have hFrame := frame_bound model W n a (fuel+1) M F D ha hn hA hf hd
    by_cases hs : n<a
    · simpa only [peak,run,ite_eq_left hs,Nat.add_zero,Nat.zero_add,Nat.one_mul] using hFrame
    · have he := depth_step model W n a fuel hs
      have hi := ih (a:=2*a) (by omega) (by omega) (by omega) (by omega)
      rw [peak,ite_eq_right hs]
      exact (Nat.add_le_add hFrame hi).trans_eq (by rw [he]; ring)

def profile (model : RationalCostModel) (W M F D : ℕ) : ℕ := (D+1)*frameProfile model W M F D

theorem bounded (model : RationalCostModel) (W n a fuel M F D : ℕ) (ha : 0<a)
    (hn : 2*(n+1)≤M) (hA : a≤M) (hf : fuel≤F) (hd : (run model.rat W n a fuel).1.depth≤D) :
    peak model W n a fuel≤profile model W M F D :=
  (peak_bound model W n a fuel M F D ha hn hA hf hd).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hd 1))

end Blotto.GeneralPaperNativeGrowingQuotientStorage
