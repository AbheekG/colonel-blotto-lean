import Blotto.GeneralPaperScoreConstructionStorage
import Blotto.GeneralPaperValueWeightSum

/-! Actual stored-natural summation: all prefix sums, native work metadata
and intermediate price accumulators are bounded from the complete total.
Input array payloads are borrowed. Primitive scratch is a separate maximum
over single additions; the complete summation time is not used as space. -/
namespace Blotto.GeneralPaperNaturalSumStorage
open GeneralPaperEncodedScalarStorage GeneralPaperValueWeightSum GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

def workCap (model : RationalCostModel) (W n S : ℕ) : ℕ :=
  n*(2*model.rat (1+binaryWordWidth S)+128*arrayWord W n)+64*arrayWord W n

def metadataCap (model : RationalCostModel) (W n S : ℕ) : ℕ := n+S+1+workCap model W n S

theorem prefix_work {n : ℕ} (model : RationalCostModel) (W S : ℕ) (values : FixedArrayTable n ℕ)
    (hS : (scan true model W values n le_rfl).1≤S) (count : ℕ) (hc : count≤n) :
    (scan true model W values count hc).2≤workCap model W n S :=
  (bit_work model W S values hS count hc).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) _)

def addition {n : ℕ} (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable n ℕ) (count : ℕ) (hc : count<n) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b)
    (scan true model W values count hc.le).1 (values.read ⟨count,hc⟩)

theorem addition_bound {n : ℕ} (model : RationalCostModel) (W S : ℕ) (values : FixedArrayTable n ℕ)
    (hS : (scan true model W values n le_rfl).1≤S) (count : ℕ) (hc : count<n) :
    addition model W values count hc≤2*model.rat (1+binaryWordWidth S) := by
  have hp := (prefix_mono true model W values count n hc.le le_rfl).trans hS
  have hv := (item_le_total true model W values ⟨count,hc⟩).trans hS
  have ho := (prefix_mono true model W values (count+1) n (by omega) le_rfl).trans hS
  exact GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b) _ _ S hp hv ho

def frame {n : ℕ} (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable n ℕ) : (count : ℕ) → count≤n → ℕ
  | 0,_ => fields W [0,(scan true model W values 0 (Nat.zero_le _)).1,(scan true model W values 0 (Nat.zero_le _)).2,arrayWord W n]+128*arrayWord W n
  | count+1,hc =>
    let previous := scan true model W values count (by omega)
    let current := scan true model W values (count+1) hc
    let item := values.read ⟨count,by omega⟩
    let price := addition model W values count (by omega)
    let step := PaperIndexedArrayConstruction.stepWork (fun w => w) (arrayWord W n) count
    fields W [count+1,previous.1,previous.2,item,current.1,current.2,price,step,arrayWord W n,previous.2+price,previous.2+price+step]+128*arrayWord W n

def frameProfile (model : RationalCostModel) (W n S : ℕ) : ℕ :=
  11*(natBits (metadataCap model W n S)+W)+32*W+128*arrayWord W n

theorem frame_bound {n : ℕ} (model : RationalCostModel) (W S : ℕ) (values : FixedArrayTable n ℕ)
    (hS : (scan true model W values n le_rfl).1≤S) (count : ℕ) (hc : count≤n) :
    frame model W values count hc≤frameProfile model W n S := by
  have hAddress : arrayWord W n≤workCap model W n S := by unfold workCap; omega
  cases count with
  | zero =>
    have hw := prefix_work model W S values hS 0 (Nat.zero_le _)
    have hf := fields_bound W (natBits (metadataCap model W n S))
      [0,(scan true model W values 0 (Nat.zero_le _)).1,(scan true model W values 0 (Nat.zero_le _)).2,arrayWord W n] (by
        intro x hx
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl
        · exact Nat.zero_le _
        · change 0≤_; exact Nat.zero_le _
        · unfold metadataCap; omega
        · unfold metadataCap; omega)
    change fields W _≤4*(natBits (metadataCap model W n S)+W)+32*W at hf
    change fields W _+128*arrayWord W n≤_
    unfold frameProfile
    omega
  | succ count =>
    let previous := scan true model W values count (by omega)
    let current := scan true model W values (count+1) hc
    let item := values.read ⟨count,by omega⟩
    let price := addition model W values count (by omega)
    let step := PaperIndexedArrayConstruction.stepWork (fun w => w) (arrayWord W n) count
    have hp : previous.1≤S := (prefix_mono true model W values count n (by omega) le_rfl).trans hS
    have ho : current.1≤S := (prefix_mono true model W values (count+1) n hc le_rfl).trans hS
    have hv : item≤S := (item_le_total true model W values ⟨count,by omega⟩).trans hS
    have hwp : previous.2≤workCap model W n S := prefix_work model W S values hS count (by omega)
    have hwo : current.2≤workCap model W n S := prefix_work model W S values hS (count+1) hc
    have hShape : current.2=previous.2+price+step+64*arrayWord W n := rfl
    have hf := fields_bound W (natBits (metadataCap model W n S))
      [count+1,previous.1,previous.2,item,current.1,current.2,price,step,arrayWord W n,previous.2+price,previous.2+price+step] (by
        intro x hx
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals unfold metadataCap; omega)
    change fields W _≤11*(natBits (metadataCap model W n S)+W)+32*W at hf
    exact Nat.add_le_add_right hf _

def frames {n : ℕ} (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable n ℕ) : (count : ℕ) → count≤n → ℕ
  | 0,hc => frame model W values 0 hc
  | count+1,hc => frames model W values count (by omega)+frame model W values (count+1) hc

theorem frames_bound {n : ℕ} (model : RationalCostModel) (W S : ℕ) (values : FixedArrayTable n ℕ)
    (hS : (scan true model W values n le_rfl).1≤S) (count : ℕ) (hc : count≤n) :
    frames model W values count hc≤(count+1)*frameProfile model W n S := by
  induction count with
  | zero => simpa only [frames,Nat.zero_add,Nat.one_mul] using frame_bound model W S values hS 0 hc
  | succ count ih =>
    have hp := ih (by omega)
    have hn := frame_bound model W S values hS (count+1) hc
    exact (Nat.add_le_add hp hn).trans_eq (by ring)

def primitivePeak {n : ℕ} (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable n ℕ) : (count : ℕ) → count≤n → ℕ
  | 0,_ => 0
  | count+1,hc => max (primitivePeak model W values count (by omega)) (addition model W values count (by omega))

theorem primitive_bound {n : ℕ} (model : RationalCostModel) (W S : ℕ) (values : FixedArrayTable n ℕ)
    (hS : (scan true model W values n le_rfl).1≤S) (count : ℕ) (hc : count≤n) :
    primitivePeak model W values count hc≤2*model.rat (1+binaryWordWidth S) := by
  induction count with
  | zero => exact Nat.zero_le _
  | succ count ih => exact max_le (ih (by omega)) (addition_bound model W S values hS count (by omega))

def profile (model : RationalCostModel) (W n S : ℕ) : ℕ := (n+1)*frameProfile model W n S+2*model.rat (1+binaryWordWidth S)

theorem bounded {n : ℕ} (model : RationalCostModel) (W S : ℕ) (values : FixedArrayTable n ℕ)
    (hS : (scan true model W values n le_rfl).1≤S) (count : ℕ) (hc : count≤n) :
    frames model W values count hc+primitivePeak model W values count hc≤profile model W n S :=
  Nat.add_le_add ((frames_bound model W S values hS count hc).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hc 1))) (primitive_bound model W S values hS count hc)

end Blotto.GeneralPaperNaturalSumStorage
