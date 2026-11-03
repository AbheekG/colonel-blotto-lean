import Blotto.GeneralPaperFixedViolationScanStorage

/-! Complete native original blocker recovery: literal midpoint, fixed-table
scan, full selected predecessor and guarded one-pass label decode. Table,
budget/sample/entry/returned row and all parent partial counters are owned.
No extra DP or tuple search is introduced. -/
namespace Blotto.GeneralPaperHighBlockerStorage
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayFixedViolation
open GeneralPaperRayUniformSize GeneralPaperAffineWitnessStorage GeneralPaperFixedViolationCandidateStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (W m S R : ℕ) : ℕ := GeneralPaperHighBlockerPrice.profile m S W (model.rat (6*R+9))
def metadataCap (model : RationalCostModel) (W m S R : ℕ) : ℕ := m+2*S+1+3*price model W m S R+16*W

def decodeWork {S K : ℕ} (W m : ℕ) (a : Option (Entry S K)) : ℕ :=
  match a with
  | none => 0
  | some e => (GeneralPaperFixedTupleDecodePrice.run (fun w => w) W m e.2).2

def decodeWindow {S K : ℕ} (W m copied : ℕ) (a : Option (Entry S K)) : ℕ :=
  match a with
  | none => 0
  | some e => GeneralPaperFixedTupleDecodeStorage.window W m copied e.2

def window {S K : ℕ} (model : RationalCostModel) (W m copied : ℕ) (table : Table S K) (h : ℕ) (beta lo hi : ℚ)
    (active : Option (Fin (S+1))) : ℕ :=
  let midpoint := GeneralPaperRayMidpointPrice.run model.rat W lo hi
  let found := GeneralPaperFixedViolationPrice.run model.rat W table h beta midpoint.1
  let result := GeneralPaperHighBlockerPrice.run model.rat (fun w => w) W m table h beta lo hi
  GeneralPaperRayMidpointStorage.window model W lo hi+
    GeneralPaperFixedViolationScanStorage.window model W copied table h beta midpoint.1 active+
    entryFoot W found.value+decodeWindow W m copied found.value+GeneralPaperFixedTupleDecodeStorage.rowFoot W result.1+
    fields W [m,S,h,midpoint.2,found.work,result.2,decodeWork W m found.value,
      midpoint.2+found.work,midpoint.2+found.work+decodeWork W m found.value,8*W,16*W]+256*W

def profile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  GeneralPaperRayMidpointStorage.profile model W R+GeneralPaperFixedViolationScanStorage.profile model W m K S R (2*R+3)+
    entryProfile W m K S R+GeneralPaperFixedTupleDecodeStorage.profile W m K R+GeneralPaperFixedTupleDecodeStorage.rowProfile W m K+
      11*(natBits (metadataCap model W m S R)+W)+288*W

theorem bounded {S K : ℕ} (model : RationalCostModel) (W copied D E m X V P : ℕ) (hD : 0<D) (hE : 0<E)
    (table : Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V m table) (h : ℕ) (hhS : h≤S)
    (beta : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta) (lo hi : ℚ)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P))
    (hW : 1≤W) (hIndex : binaryWordWidth (m+1)≤W) (active : Option (Fin (S+1))) :
    window model W m copied table h beta lo hi active≤profile model W m K S (width D E m X V P) := by
  let R := width D E m X V P
  let midpoint := GeneralPaperRayMidpointPrice.run model.rat W lo hi
  let found := GeneralPaperFixedViolationPrice.run model.rat W table h beta midpoint.1
  let result := GeneralPaperHighBlockerPrice.run model.rat (fun w => w) W m table h beta lo hi
  have hMidpoint := GeneralPaperRayMidpointStorage.bounded model W R lo hi hl hh
  have hSample : RationalHeight midpoint.1 (2*R+3) := GeneralPaperRayAffineBound.midpoint_height hl hh
  have hScan := GeneralPaperFixedViolationScanStorage.native_bounded model W copied D E m X V P hD hE table hp h hhS beta midpoint.1 hb hSample active
  have hGood := processed_good D E X V m m P hD hE le_rfl table hp
  have hEntry := entry_bound W m R table hGood found.value (by
    intro e he; rw [GeneralPaperFixedViolationPrice.data] at he
    exact (GeneralPaperRayFixedViolation.scan_valid table h beta midpoint.1 (List.finRange (S+1)) e he).2.1)
  have hDecode : decodeWindow W m copied found.value≤GeneralPaperFixedTupleDecodeStorage.profile W m K R := by
    cases he : found.value with
    | none => dsimp only [decodeWindow]; omega
    | some e =>
      have hv : table.read e.1=some e.2 := by
        have hr := he; rw [GeneralPaperFixedViolationPrice.data] at hr
        exact (GeneralPaperRayFixedViolation.scan_valid table h beta midpoint.1 (List.finRange (S+1)) e hr).2.1
      have hc := hGood e.1 e.2 hv
      exact GeneralPaperFixedTupleDecodeStorage.bounded W m R copied e.2 hc.1 hc.2.1 hc.2.2 hW hIndex
  have hRow := GeneralPaperFixedTupleDecodeStorage.row_bound W result.1
  have hWork := GeneralPaperHighBlockerPrice.bit_work model W D E m X V P hD hE table hp h beta hb lo hi hl hh hW hIndex
  change result.2≤price model W m S R at hWork
  have hBase : midpoint.2+found.work+decodeWork W m found.value≤result.2 := by
    change _≤(match found.value with
      | none => (none,midpoint.2+found.work+8*W)
      | some e =>
        let row := GeneralPaperFixedTupleDecodePrice.run (fun w => w) W m e.2
        (row.1,midpoint.2+found.work+row.2+16*W)).2
    cases found.value <;> dsimp only [decodeWork] <;> omega
  have hf := fields_bound W (natBits (metadataCap model W m S R))
    [m,S,h,midpoint.2,found.work,result.2,decodeWork W m found.value,
      midpoint.2+found.work,midpoint.2+found.work+decodeWork W m found.value,8*W,16*W] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤11*(natBits (metadataCap model W m S R)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [R,midpoint,found,result] at hMidpoint hScan hEntry hDecode hRow hf
  omega

end Blotto.GeneralPaperHighBlockerStorage
