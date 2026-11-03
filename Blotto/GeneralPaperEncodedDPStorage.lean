import Blotto.GeneralPaperEncodedForestStorage

/-! Complete retained DP table representation: exact tag payloads, typed
predecessor indices, array slots, record headers and child references.
No table or predecessor census executes in the source. -/
namespace Blotto.GeneralPaperEncodedDPStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def traceBits {K J : ℕ} : (h : ℕ) → Trace K J h → ℕ
  | 0,i => 1+binaryWordWidth i.val
  | _+1,ij => 2+binaryWordWidth ij.1.val+binaryWordWidth ij.2.val

def traceWord (K J : ℕ) : ℕ := 2*(1+binaryWordWidth (max K J+1))

theorem trace_bound {K J : ℕ} (h : ℕ) (trace : Trace K J h) : traceBits h trace≤traceWord K J := by
  cases h with
  | zero =>
    have hi : trace.val≤max K J+1 := by have h:=trace.isLt; have hm:=Nat.le_max_left K J; omega
    have hw := binaryWordWidth_mono hi
    dsimp only [traceBits,traceWord]
    omega
  | succ h =>
    have hi : trace.1.val≤max K J+1 := by have h:=trace.1.isLt; have hm:=Nat.le_max_right K J; omega
    have hj : trace.2.val≤max K J+1 := by have h:=trace.2.isLt; have hm:=Nat.le_max_right K J; omega
    have hw := binaryWordWidth_mono hi
    have hv := binaryWordWidth_mono hj
    dsimp only [traceBits,traceWord]
    omega

def tableMetadata {Witness : Type*} {J : ℕ} (W : ℕ) (encode : Witness → ℕ) (states : Table Tag Witness J) : ℕ :=
  64*W+∑ j, (W+1+match states.read j with
    | none => 0
    | some selected => 8*W+encode selected.predecessor)

theorem table_metadata_bound {Witness : Type*} {J : ℕ} (W P : ℕ) (encode : Witness → ℕ)
    (he : ∀ witness,encode witness≤P) (states : Table Tag Witness J) :
    tableMetadata W encode states≤64*W+J*(9*W+P+1) := by
  have hb (j : Fin J) : (W+1+match states.read j with
      | none => 0
      | some selected => 8*W+encode selected.predecessor)≤9*W+P+1 := by
    cases hs : states.read j with
    | none => dsimp only; omega
    | some selected =>
      dsimp only
      calc
        _≤W+1+(8*W+P) := Nat.add_le_add_left (Nat.add_le_add_left (he selected.predecessor) (8*W)) (W+1)
        _=9*W+P+1 := by ring
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hb j)
  have h' := Nat.add_le_add_left h (64*W)
  simpa only [tableMetadata,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using h'

def footprint {K J : ℕ} (W : ℕ) : {h : ℕ} → Computation Tag K J h → ℕ
  | _,.leaf states => GeneralPaperRetainedDPStorage.tableTagBits states+tableMetadata W (traceBits (K:=K) (J:=J) 0) states+16*W
  | h+1,.node left right states => footprint W left+footprint W right+
      GeneralPaperRetainedDPStorage.tableTagBits states+tableMetadata W (traceBits (K:=K) (J:=J) (h+1)) states+32*W

theorem bounded {K J h : ℕ} (W : ℕ) (computed : Computation Tag K J h) :
    footprint W computed≤GeneralPaperRetainedDPStorage.tagBits computed+
      GeneralPaperRetainedDPStorage.slots computed*(9*W+traceWord K J+1)+128*W*GeneralPaperRetainedDPStorage.tables computed := by
  induction computed with
  | leaf states =>
    have hm := table_metadata_bound W (traceWord K J) (traceBits (K:=K) (J:=J) 0) (trace_bound 0) states
    simp only [footprint,GeneralPaperRetainedDPStorage.tagBits,GeneralPaperRetainedDPStorage.slots,
      GeneralPaperRetainedDPStorage.tables,states.size]
    omega
  | @node h left right states ihl ihr =>
    have hm := table_metadata_bound W (traceWord K J) (traceBits (K:=K) (J:=J) (h+1)) (trace_bound (h+1)) states
    simp only [footprint,GeneralPaperRetainedDPStorage.tagBits,GeneralPaperRetainedDPStorage.slots,
      GeneralPaperRetainedDPStorage.tables,states.size]
    nlinarith only [ihl,ihr,hm]

theorem tables_bound {K J h : ℕ} (computed : Computation Tag K J h) : GeneralPaperRetainedDPStorage.tables computed≤2*2^h := by
  have ht := GeneralPaperRetainedDPStorage.tables_exact computed
  rw [pow_succ (2:ℕ) h] at ht
  omega

def profile (W K J s h : ℕ) : ℕ :=
  J*(h+1)*2^h*(2*s+4)+(2*J*2^h)*(9*W+traceWord K J+1)+256*W*2^h

theorem native {K q w B h : ℕ} (W : ℕ) (grid : GeneralPaperProfitGridPrepare.Prepared q w B)
    (tree : Tree Tag K h) (s : ℕ) (hl : GeneralPaperOrderedDPHeight.Leaves s tree) :
    footprint W (GeneralPaperOrderedProfitDP.run grid tree)≤profile W K grid.size s h := by
  let computed := GeneralPaperOrderedProfitDP.run grid tree
  have hb := bounded W computed
  have ht := (GeneralPaperRetainedDPStorage.native_tag_bits grid tree s hl).trans
    (GeneralPaperRetainedDPStorage.tag_profile_bound grid.size s h)
  have hs := Nat.mul_le_mul_right (9*W+traceWord K grid.size+1) (GeneralPaperRetainedDPStorage.slots_bound computed)
  have hn := Nat.mul_le_mul_left (128*W) (tables_bound computed)
  have h := Nat.add_le_add (Nat.add_le_add ht hs) hn
  exact hb.trans (h.trans_eq (by unfold profile; ring))

theorem ready {m k : ℕ} (W : ℕ) (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Prefix k)) :
    footprint W (GeneralPaperOrderedProfitDP.run prepared.grid
      (GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes ready.cached))≤
        profile W ((GeneralPaperSourceParameters.prepare k).summarySize+2) prepared.grid.size (ready.alphabet.lambda+1) prepared.parameters.height :=
  native W prepared.grid _ _ (GeneralPaperOrderedDPHeight.native_tree prepared T ready weights prefixes)

theorem priced_ready {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Prefix k)) :
    footprint W (GeneralPaperOrderedDPExecution.run bits index price W prepared.grid
      (GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes ready.cached)).1≤
        profile W ((GeneralPaperSourceParameters.prepare k).summarySize+2) prepared.grid.size (ready.alphabet.lambda+1) prepared.parameters.height := by
  rw [GeneralPaperOrderedDPExecution.data]
  exact GeneralPaperEncodedDPStorage.ready W prepared T ready weights prefixes

end Blotto.GeneralPaperEncodedDPStorage
