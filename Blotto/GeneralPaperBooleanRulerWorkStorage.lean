import Blotto.GeneralPaperClosedSamplerConstructionStorage

/-! Native Boolean accuracy-ruler work metadata. The recurrences observe
exactly the existing reached calls and all their natural work fields and
partial sums. The cap is erased analysis, never a runtime traversal/query.
Complete retained Boolean data are joined to the checked lifetime traces. -/
namespace Blotto.GeneralPaperBooleanRulerWorkStorage
open GeneralPaperEncodedScalarStorage BinaryRulerPrecisionWork
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRulerPrecisionLifetime
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def budget (W C : ℕ) : ℕ := 64*(natBits (C+64)+W)
def node (W : ℕ) (xs : List ℕ) : ℕ := fields W xs+64*W

theorem node_bound (W C : ℕ) (xs : List ℕ) (hLen : xs.length≤7) (h : ∀ z∈xs,z≤C+64) : node W xs≤2*budget W C := by
  have hf := fields_bound W (natBits (C+64)) xs (fun z hz => Nat.add_le_add_left (binaryWordWidth_mono (h z hz)) 1)
  have hc := hf.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) _)
  unfold node budget
  omega

theorem node_literal (W C a : ℕ) (ha : 2≤a ∧ a≤64) : node W [a]≤a*budget W C := by
  have hn := node_bound W C [a] (by norm_num) (fun z hz => by simp only [List.mem_cons,List.not_mem_nil,or_false] at hz;rw [hz];omega)
  exact hn.trans (Nat.mul_le_mul_right _ ha.1)

def differenceMeta (W : ℕ) : List Bool → List Bool → ℕ
  | _,[] => node W [2]
  | [],_::_ => node W [2]
  | _::bits,_::other =>
    let child := differenceWithWork bits other
    node W [child.2,4,child.2+4]+differenceMeta W bits other

def compareMeta (W : ℕ) : List Bool → List Bool → ℕ
  | [],_ => node W [2]
  | _::_,[] => node W [2]
  | _::bits,_::other =>
    let child := compareLengthWithWork bits other
    node W [child.2,4,child.2+4]+compareMeta W bits other

def scanMeta (W : ℕ) : List Bool → List Bool → ℕ
  | [],_ => node W [2]
  | _::_,[] => node W [2]
  | a::bits,b::other =>
    if a=b then
      let child := leScanWithWork bits other
      node W [child.2,5,child.2+5]+scanMeta W bits other
    else node W [5]

def falseMeta (W : ℕ) : List Bool → ℕ
  | [] => node W [2]
  | _::rest =>
    let child := falseMapWithWork rest
    node W [child.2,4,child.2+4]+falseMeta W rest

def appendMeta (W : ℕ) : List Bool → List Bool → ℕ
  | [],_ => node W [2]
  | _::left,right =>
    let child := appendWithWork left right
    node W [child.2,4,child.2+4]+appendMeta W left right

theorem difference_bound (W C : ℕ) (bits other : List Bool) (hc : (differenceWithWork bits other).2≤C) :
    differenceMeta W bits other≤(differenceWithWork bits other).2*budget W C := by
  induction bits generalizing other with
  | nil => cases other <;> exact node_literal W C 2 (by norm_num)
  | cons bit rest ih => cases other with
    | nil => exact node_literal W C 2 (by norm_num)
    | cons head tail =>
      change (differenceWithWork rest tail).2+4≤C at hc
      have hi := ih tail (by omega)
      have hn := node_bound W C [(differenceWithWork rest tail).2,4,(differenceWithWork rest tail).2+4] (by norm_num) (by
        intro z hz
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl|rfl|rfl <;> omega)
      change node W _+differenceMeta W rest tail≤((differenceWithWork rest tail).2+4)*budget W C
      nlinarith only [hn,hi,Nat.zero_le (budget W C)]

theorem compare_bound (W C : ℕ) (bits other : List Bool) (hc : (compareLengthWithWork bits other).2≤C) :
    compareMeta W bits other≤(compareLengthWithWork bits other).2*budget W C := by
  induction bits generalizing other with
  | nil => cases other <;> exact node_literal W C 2 (by norm_num)
  | cons bit rest ih => cases other with
    | nil => exact node_literal W C 2 (by norm_num)
    | cons head tail =>
      change (compareLengthWithWork rest tail).2+4≤C at hc
      have hi := ih tail (by omega)
      have hn := node_bound W C [(compareLengthWithWork rest tail).2,4,(compareLengthWithWork rest tail).2+4] (by norm_num) (by
        intro z hz
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl|rfl|rfl <;> omega)
      change node W _+compareMeta W rest tail≤((compareLengthWithWork rest tail).2+4)*budget W C
      nlinarith only [hn,hi,Nat.zero_le (budget W C)]

theorem scan_bound (W C : ℕ) (bits other : List Bool) (hc : (leScanWithWork bits other).2≤C) :
    scanMeta W bits other≤(leScanWithWork bits other).2*budget W C := by
  induction bits generalizing other with
  | nil => exact node_literal W C 2 (by norm_num)
  | cons bit rest ih => cases other with
    | nil => exact node_literal W C 2 (by norm_num)
    | cons head tail =>
      by_cases he : bit=head
      · have hc' : (leScanWithWork rest tail).2+5≤C := by simpa only [leScanWithWork,ite_eq_left he] using hc
        have hi := ih tail (by omega)
        have hn := node_bound W C [(leScanWithWork rest tail).2,5,(leScanWithWork rest tail).2+5] (by norm_num) (by
          intro z hz
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
          rcases hz with rfl|rfl|rfl <;> omega)
        simp only [scanMeta,leScanWithWork,ite_eq_left he]
        nlinarith only [hn,hi,Nat.zero_le (budget W C)]
      · simpa only [scanMeta,leScanWithWork,ite_eq_right he] using node_literal W C 5 (by norm_num)

theorem false_bound (W C : ℕ) (bits : List Bool) (hc : (falseMapWithWork bits).2≤C) :
    falseMeta W bits≤(falseMapWithWork bits).2*budget W C := by
  induction bits with
  | nil => exact node_literal W C 2 (by norm_num)
  | cons bit rest ih =>
    change (falseMapWithWork rest).2+4≤C at hc
    have hi := ih (by omega)
    have hn := node_bound W C [(falseMapWithWork rest).2,4,(falseMapWithWork rest).2+4] (by norm_num) (by
      intro z hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl <;> omega)
    change node W _+falseMeta W rest≤((falseMapWithWork rest).2+4)*budget W C
    nlinarith only [hn,hi,Nat.zero_le (budget W C)]

theorem append_bound (W C : ℕ) (left right : List Bool) (hc : (appendWithWork left right).2≤C) :
    appendMeta W left right≤(appendWithWork left right).2*budget W C := by
  induction left with
  | nil => exact node_literal W C 2 (by norm_num)
  | cons bit rest ih =>
    change (appendWithWork rest right).2+4≤C at hc
    have hi := ih (by omega)
    have hn := node_bound W C [(appendWithWork rest right).2,4,(appendWithWork rest right).2+4] (by norm_num) (by
      intro z hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl <;> omega)
    change node W _+appendMeta W rest right≤((appendWithWork rest right).2+4)*budget W C
    nlinarith only [hn,hi,Nat.zero_le (budget W C)]

def shiftedMeta (W : ℕ) (word : PositiveBinaryWord) (ruler : List Bool) : ℕ :=
  let zeros := falseMapWithWork ruler
  let appended := appendWithWork word.tail zeros.1
  node W [zeros.2,appended.2,zeros.2+appended.2,4,(shiftedWithWork word ruler).2]+
    falseMeta W ruler+appendMeta W word.tail zeros.1

theorem shifted_bound (W C : ℕ) (word : PositiveBinaryWord) (ruler : List Bool) (hc : (shiftedWithWork word ruler).2≤C) :
    shiftedMeta W word ruler≤(shiftedWithWork word ruler).2*budget W C := by
  let a := falseMapWithWork ruler
  let b := appendWithWork word.tail a.1
  have hs : (shiftedWithWork word ruler).2=a.2+b.2+4 := rfl
  have ha := false_bound W C ruler (by change a.2≤C;omega)
  have hb := append_bound W C word.tail a.1 (by change b.2≤C;omega)
  have hn := node_bound W C [a.2,b.2,a.2+b.2,4,(shiftedWithWork word ruler).2] (by norm_num) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega)
  change node W [a.2,b.2,a.2+b.2,4,(shiftedWithWork word ruler).2]+falseMeta W ruler+appendMeta W word.tail a.1≤_
  change _≤a.2*budget W C at ha
  change _≤b.2*budget W C at hb
  rw [hs] at hn ⊢
  nlinarith only [hn,ha,hb,Nat.zero_le (budget W C)]

def leMeta (W : ℕ) (a b : PositiveBinaryWord) : ℕ :=
  let compared := compareLengthWithWork a.tail b.tail
  match compared.1 with
  | .lt | .gt => node W [compared.2,4,compared.2+4]+compareMeta W a.tail b.tail
  | .eq =>
    let scanned := leScanWithWork a.bits b.bits
    node W [compared.2,scanned.2,compared.2+scanned.2,4,compared.2+scanned.2+4]+
      compareMeta W a.tail b.tail+scanMeta W a.bits b.bits

theorem le_bound (W C : ℕ) (a b : PositiveBinaryWord) (hc : (leWithWork a b).2≤C) :
    leMeta W a b≤(leWithWork a b).2*budget W C := by
  let c := compareLengthWithWork a.tail b.tail
  let s := leScanWithWork a.bits b.bits
  unfold leMeta leWithWork
  dsimp only
  cases he:c.1
  all_goals change _≤C at hc;unfold leWithWork at hc;dsimp only at hc
  all_goals rw [he] at hc;dsimp only at hc ⊢
  · change c.2+4≤C at hc
    have hi := compare_bound W C a.tail b.tail (by change c.2≤C;omega)
    have hn := node_bound W C [c.2,4,c.2+4] (by norm_num) (by
      intro z hz;simp only [List.mem_cons,List.not_mem_nil,or_false] at hz;rcases hz with rfl|rfl|rfl <;> omega)
    change node W [c.2,4,c.2+4]+compareMeta W a.tail b.tail≤(c.2+4)*budget W C
    change _≤c.2*budget W C at hi
    nlinarith only [hn,hi,Nat.zero_le (budget W C)]
  · change c.2+s.2+4≤C at hc
    have hi := compare_bound W C a.tail b.tail (by change c.2≤C;omega)
    have hj := scan_bound W C a.bits b.bits (by change s.2≤C;omega)
    have hn := node_bound W C [c.2,s.2,c.2+s.2,4,c.2+s.2+4] (by norm_num) (by
      intro z hz;simp only [List.mem_cons,List.not_mem_nil,or_false] at hz;rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega)
    change node W [c.2,s.2,c.2+s.2,4,c.2+s.2+4]+compareMeta W a.tail b.tail+scanMeta W a.bits b.bits≤(c.2+s.2+4)*budget W C
    change _≤c.2*budget W C at hi
    change _≤s.2*budget W C at hj
    nlinarith only [hn,hi,hj,Nat.zero_le (budget W C)]
  · change c.2+4≤C at hc
    have hi := compare_bound W C a.tail b.tail (by change c.2≤C;omega)
    have hn := node_bound W C [c.2,4,c.2+4] (by norm_num) (by
      intro z hz;simp only [List.mem_cons,List.not_mem_nil,or_false] at hz;rcases hz with rfl|rfl|rfl <;> omega)
    change node W [c.2,4,c.2+4]+compareMeta W a.tail b.tail≤(c.2+4)*budget W C
    change _≤c.2*budget W C at hi
    nlinarith only [hn,hi,Nat.zero_le (budget W C)]

def prepareMeta (W : ℕ) (a b : PositiveBinaryWord) : ℕ :=
  let candidate := differenceWithWork a.tail b.tail
  let aligned := shiftedWithWork b candidate.1
  let compared := leWithWork a aligned.1
  node W [candidate.2,aligned.2,compared.2,candidate.2+aligned.2,candidate.2+aligned.2+compared.2,5,(prepareWithWork a b).2]+
    differenceMeta W a.tail b.tail+shiftedMeta W b candidate.1+leMeta W a aligned.1

theorem prepare_bound (W C : ℕ) (a b : PositiveBinaryWord) (hc : (prepareWithWork a b).2≤C) :
    prepareMeta W a b≤(prepareWithWork a b).2*budget W C := by
  let c := differenceWithWork a.tail b.tail
  let s := shiftedWithWork b c.1
  let l := leWithWork a s.1
  have hs : (prepareWithWork a b).2=c.2+s.2+l.2+5 := rfl
  have hd := difference_bound W C a.tail b.tail (by change c.2≤C;omega)
  have ha := shifted_bound W C b c.1 (by change s.2≤C;omega)
  have hl := le_bound W C a s.1 (by change l.2≤C;omega)
  have hn := node_bound W C [c.2,s.2,l.2,c.2+s.2,c.2+s.2+l.2,5,(prepareWithWork a b).2] (by norm_num) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change node W [c.2,s.2,l.2,c.2+s.2,c.2+s.2+l.2,5,(prepareWithWork a b).2]+
    differenceMeta W a.tail b.tail+shiftedMeta W b c.1+leMeta W a s.1≤_
  change _≤c.2*budget W C at hd
  change _≤s.2*budget W C at ha
  change _≤l.2*budget W C at hl
  rw [hs] at hn ⊢
  nlinarith only [hn,hd,ha,hl,Nat.zero_le (budget W C)]

def shiftedTrace (word : PositiveBinaryWord) (ruler : List Bool) : Trace :=
  let zeros := falseMapWithWork ruler
  wrap 24 2 [(BinaryRulerControlLifetime.falseMapWithTrace ruler).2,
    (BinaryPRGOutputLifetime.appendWithTrace word.tail zeros.1).2]

def leTrace (a b : PositiveBinaryWord) : Trace :=
  let compared := compareLengthWithWork a.tail b.tail
  match compared.1 with
  | .lt | .gt => wrap 16 2 [(BinaryRulerControlLifetime.compareLengthWithTrace a.tail b.tail).2]
  | .eq => wrapList 2 24 2 [(BinaryRulerControlLifetime.compareLengthWithTrace a.tail b.tail).2,
      (BinaryRulerControlLifetime.leScanWithTrace a.bits b.bits).2]

def prepareTrace (a b : PositiveBinaryWord) : Trace :=
  let candidate := differenceWithWork a.tail b.tail
  let aligned := shiftedWithWork b candidate.1
  wrapList 1 32 2 [(BinaryRulerControlLifetime.differenceWithTrace a.tail b.tail).2,
    shiftedTrace b candidate.1,leTrace a aligned.1]

theorem shifted_trace_eq (word : PositiveBinaryWord) (ruler : List Bool) :
    shiftedTrace word ruler=(shiftedWithTrace word ruler).2 := by
  unfold shiftedTrace shiftedWithTrace
  simp only [falseMap_state]

theorem le_trace_eq (a b : PositiveBinaryWord) : leTrace a b=(leWithTrace a b).2 := by
  unfold leTrace leWithTrace
  dsimp only
  rw [compareLength_state]
  cases (BinaryRulerControlLifetime.compareLengthWithTrace a.tail b.tail).1 <;> rfl

theorem prepare_trace_eq (a b : PositiveBinaryWord) : prepareTrace a b=(prepareWithTrace a b).2 := by
  unfold prepareTrace prepareWithTrace
  simp only [shifted_trace_eq,le_trace_eq,difference_state,shifted_state]

def wordFoot (W : ℕ) (word : PositiveBinaryWord) : ℕ := listFootprint W (fun _ : Bool => 1) word.tail+64*W

theorem word_bound (W : ℕ) (word : PositiveBinaryWord) : wordFoot W word≤word.width*(1+2*W)+96*W := by
  have h := list_bound W 1 (fun _ : Bool => 1) word.tail (fun _ _ => le_rfl)
  unfold wordFoot PositiveBinaryWord.width
  nlinarith only [h,Nat.zero_le W]

def window (W : ℕ) (a b : PositiveBinaryWord) : ℕ :=
  wordFoot W a+wordFoot W b+32*W+(1+4*W)*usage (prepareTrace a b)+prepareMeta W a b

def profile (W E : ℕ) : ℕ :=
  E*(1+2*W)+224*W+256*(E+1)*(1+4*W)+32*(E+1)*budget W (32*(E+1))

theorem bounded (W : ℕ) (a b : PositiveBinaryWord) : window W a b≤profile W (a.width+b.width) := by
  let E := a.width+b.width
  have hw := BinaryRulerPrecisionWork.prepare_work a b
  have hm := prepare_bound W (32*(E+1)) a b hw
  have hm' := hm.trans (Nat.mul_le_mul_right (budget W (32*(E+1))) hw)
  have ht := BinaryRulerPrecisionLifetime.prepareWithTrace_usage a b
  rw [←prepare_trace_eq] at ht
  have ht' := Nat.mul_le_mul_left (1+4*W) ht
  have ha := word_bound W a
  have hb := word_bound W b
  unfold window profile
  dsimp only [E] at *
  nlinarith only [hm',ht',ha,hb]

@[fun_prop]
theorem scaling (E : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => profile W E) := by
  unfold profile budget
  fun_prop

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth

theorem profile_rate (W E : Input → ℕ) (hW : Tight W) (hE : Small E) :
    Linear (fun x => profile (W x) (E x)) E := by
  have hw := of_tight hW
  have hWP := poly_tight W hW
  unfold profile budget natBits
  fun_prop

end Blotto.GeneralPaperBooleanRulerWorkStorage
