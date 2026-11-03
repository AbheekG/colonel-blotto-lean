import Blotto.GeneralPaperNativeEndpointAnchorStorage

/-! Actual nested endpoint-column construction. Full input columns and
borrowed choice, inner/outer native fill buffers and frames, full returned
arrays and caller work fields coexist with independent fill cursors. -/
namespace Blotto.GeneralPaperNativeEndpointColumnsStorage
open GeneralPaperEncodedScalarStorage GeneralPaperSourceEndpointBranch
open GeneralPaperEnclosingSourceOwners GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384

def fieldPrice (model : RationalCostModel) (W m K : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.workCap W K (GeneralPaperNativeEndpointAnchorStorage.callbackPrice model W m K)+64*W

def price (model : RationalCostModel) (W m K : ℕ) : ℕ := GeneralPaperNativePayloadFillStorage.workCap W m (fieldPrice model W m K)
def fieldCap (model : RationalCostModel) (W T m K : ℕ) : ℕ := T+m+K+fieldPrice model W m K+1

def fieldWindow {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (choice : Choice (m*(K-1)))
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (j : Fin m) (count : ℕ) (hc : count≤K) : ℕ :=
  let callback := GeneralPaperNativeEndpointAnchor.run model.rat W choice j
  let anchors := PaperIndexedArrayConstruction.run (fun w => w) W callback
  let result := GeneralPaperNativeEndpointColumns.field model.rat (fun w => w) W choice (columns.read j) j
  columnFoot W (columns.read j)+GeneralPaperRetainedCompilerBranchStorage.choiceFoot W choice+
    GeneralPaperNativePayloadFillStorage.window W rationalWordWidth callback
      (fun l => GeneralPaperNativeEndpointAnchorStorage.window model W choice j l) count hc+
    fields W [T,m,K,j.val,count,anchors.2,result.2,64*W]+128*W

def fieldProfile (model : RationalCostModel) (W T m K R B : ℕ) : ℕ :=
  columnProfile W T K R+B+GeneralPaperNativePayloadFillStorage.profile W (3+B) K
    (GeneralPaperNativeEndpointAnchorStorage.callbackPrice model W m K) (GeneralPaperNativeEndpointAnchorStorage.profile model W m K (3+B))+
    8*(natBits (fieldCap model W T m K)+W)+160*W

def metadataCap (model : RationalCostModel) (W T m K : ℕ) : ℕ := T+m+K+price model W m K+64*W+1

def window {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (choice : Choice (m*(K-1)))
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤K) : ℕ :=
  let callback := fun j => GeneralPaperNativeEndpointColumns.field model.rat (fun w => w) W choice (columns.read j) j
  let result := GeneralPaperNativeEndpointColumns.run model.rat (fun w => w) W choice columns
  columnsFoot W columns+GeneralPaperRetainedCompilerBranchStorage.choiceFoot W choice+
    GeneralPaperNativePayloadFillStorage.window W (columnFoot W) callback (fun j => fieldWindow model W choice columns j inner hi) outer ho+
    fields W [T,m,K,outer,result.2,64*W]+128*W

def profile (model : RationalCostModel) (W T m K R B : ℕ) : ℕ :=
  columnsProfile W T m K R+B+GeneralPaperNativePayloadFillStorage.profile W (columnProfile W T K (3+B)) m
    (fieldPrice model W m K) (fieldProfile model W T m K R B)+
    6*(natBits (metadataCap model W T m K)+W)+160*W

theorem labels {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (choice : Choice (m*(K-1)))
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (j : Fin m) :
    ((GeneralPaperNativeEndpointColumns.run model.rat (fun w => w) W choice columns).1.read j).labels=(columns.read j).labels := by
  simp only [GeneralPaperNativeEndpointColumns.data,FixedArrayTable.read_ofFn]

theorem anchor_word {T m K : ℕ} (model : RationalCostModel) (W B : ℕ) (choice : Choice (m*(K-1)))
    (hB : GeneralPaperRetainedCompilerBranchStorage.choiceFoot W choice≤B)
    (old : GeneralPaperQuantizedColumn.Column T K) (j : Fin m) (l : Fin K) :
    rationalWordWidth (((GeneralPaperNativeEndpointColumns.field model.rat (fun w => w) W choice old j).1.anchors).read l)≤3+B := by
  change rationalWordWidth ((PaperIndexedArrayConstruction.run (fun w => w) W
    (GeneralPaperNativeEndpointAnchor.run model.rat W choice j)).1.read l)≤_
  rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact (GeneralPaperNativeEndpointAnchorStorage.entry_word model W choice j l).trans (Nat.add_le_add_left hB 3)

theorem field_payload {T m K : ℕ} (model : RationalCostModel) (W B : ℕ) (choice : Choice (m*(K-1)))
    (hB : GeneralPaperRetainedCompilerBranchStorage.choiceFoot W choice≤B)
    (old : GeneralPaperQuantizedColumn.Column T K) (j : Fin m) :
    columnFoot W (GeneralPaperNativeEndpointColumns.field model.rat (fun w => w) W choice old j).1≤columnProfile W T K (3+B) :=
  column_bound W (3+B) _ (anchor_word model W B choice hB old j)

theorem field_work {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (choice : Choice (m*(K-1)))
    (old : GeneralPaperQuantizedColumn.Column T K) (j : Fin m) (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) :
    (GeneralPaperNativeEndpointColumns.field model.rat (fun w => w) W choice old j).2≤fieldPrice model W m K := by
  have h := GeneralPaperNativePayloadFillStorage.prefix_work W (GeneralPaperNativeEndpointAnchorStorage.callbackPrice model W m K)
    (GeneralPaperNativeEndpointAnchor.run model.rat W choice j)
    (fun l => GeneralPaperNativeEndpointAnchor.work model.rat model.monotone W choice j l) hW hK K le_rfl
  exact Nat.add_le_add_right h (64*W)

theorem field_bounded {T m K : ℕ} (model : RationalCostModel) (W R B : ℕ) (choice : Choice (m*(K-1)))
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (hR : ∀ j l,rationalWordWidth ((columns.read j).anchors.read l)≤R)
    (hB : GeneralPaperRetainedCompilerBranchStorage.choiceFoot W choice≤B)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (j : Fin m) (count : ℕ) (hc : count≤K) :
    fieldWindow model W choice columns j count hc≤fieldProfile model W T m K R B := by
  let callback := GeneralPaperNativeEndpointAnchor.run model.rat W choice j
  let anchors := PaperIndexedArrayConstruction.run (fun w => w) W callback
  let result := GeneralPaperNativeEndpointColumns.field model.rat (fun w => w) W choice (columns.read j) j
  have hColumn := column_bound W R (columns.read j) (hR j)
  have hAnchors : anchors.2≤GeneralPaperNativePayloadFillStorage.workCap W K (GeneralPaperNativeEndpointAnchorStorage.callbackPrice model W m K) :=
    GeneralPaperNativePayloadFillStorage.prefix_work W _ callback
      (fun l => GeneralPaperNativeEndpointAnchor.work model.rat model.monotone W choice j l) hW hK K le_rfl
  have hResult := field_work model W choice (columns.read j) j hW hK
  change result.2≤fieldPrice model W m K at hResult
  unfold fieldPrice at hResult
  have hEntry (l) : rationalWordWidth (callback l).1≤3+B :=
    (GeneralPaperNativeEndpointAnchorStorage.entry_word model W choice j l).trans (Nat.add_le_add_left hB 3)
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W (3+B)
    (GeneralPaperNativeEndpointAnchorStorage.callbackPrice model W m K) (GeneralPaperNativeEndpointAnchorStorage.profile model W m K (3+B))
    rationalWordWidth callback (fun l => GeneralPaperNativeEndpointAnchorStorage.window model W choice j l)
    hEntry (fun l => GeneralPaperNativeEndpointAnchor.work model.rat model.monotone W choice j l)
    (fun l => GeneralPaperNativeEndpointAnchorStorage.bounded model W (3+B) choice j l (hEntry l)) hW hK count hc
  have hf := fields_bound W (natBits (fieldCap model W T m K)) [T,m,K,j.val,count,anchors.2,result.2,64*W] (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold fieldCap fieldPrice;have hj:=j.isLt;omega)
  change fields W _≤8*(natBits (fieldCap model W T m K)+W)+32*W at hf
  unfold fieldWindow fieldProfile
  change columnFoot W (columns.read j)+GeneralPaperRetainedCompilerBranchStorage.choiceFoot W choice+
    GeneralPaperNativePayloadFillStorage.window W rationalWordWidth callback
      (fun l => GeneralPaperNativeEndpointAnchorStorage.window model W choice j l) count hc+
    fields W [T,m,K,j.val,count,anchors.2,result.2,64*W]+128*W≤_
  omega

theorem work {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (choice : Choice (m*(K-1)))
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) :
    (GeneralPaperNativeEndpointColumns.run model.rat (fun w => w) W choice columns).2≤price model W m K :=
  GeneralPaperNativePayloadFillStorage.prefix_work W (fieldPrice model W m K)
    (fun j => GeneralPaperNativeEndpointColumns.field model.rat (fun w => w) W choice (columns.read j) j)
    (fun j => field_work model W choice (columns.read j) j hW hK) hW hM m le_rfl

theorem returned {T m K : ℕ} (model : RationalCostModel) (W B : ℕ) (choice : Choice (m*(K-1)))
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (hB : GeneralPaperRetainedCompilerBranchStorage.choiceFoot W choice≤B) :
    columnsFoot W (GeneralPaperNativeEndpointColumns.run model.rat (fun w => w) W choice columns).1≤columnsProfile W T m K (3+B) := by
  apply array_bound W (columnProfile W T K (3+B)) (columnFoot W)
  intro j
  change columnFoot W ((PaperIndexedArrayConstruction.run (fun w => w) W
    (fun j => GeneralPaperNativeEndpointColumns.field model.rat (fun w => w) W choice (columns.read j) j)).1.read j)≤_
  rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact field_payload model W B choice hB (columns.read j) j

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W R B : ℕ) (choice : Choice (m*(K-1)))
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (hR : ∀ j l,rationalWordWidth ((columns.read j).anchors.read l)≤R)
    (hB : GeneralPaperRetainedCompilerBranchStorage.choiceFoot W choice≤B)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤K) :
    window model W choice columns outer ho inner hi≤profile model W T m K R B := by
  let callback := fun j => GeneralPaperNativeEndpointColumns.field model.rat (fun w => w) W choice (columns.read j) j
  let result := GeneralPaperNativeEndpointColumns.run model.rat (fun w => w) W choice columns
  have hColumns := columns_bound W R columns hR
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W (columnProfile W T K (3+B)) (fieldPrice model W m K)
    (fieldProfile model W T m K R B) (columnFoot W) callback (fun j => fieldWindow model W choice columns j inner hi)
    (fun j => field_payload model W B choice hB (columns.read j) j)
    (fun j => field_work model W choice (columns.read j) j hW hK)
    (fun j => field_bounded model W R B choice columns hR hB hW hK j inner hi) hW hM outer ho
  have hWork := work model W choice columns hW hK hM
  change result.2≤price model W m K at hWork
  have hf := fields_bound W (natBits (metadataCap model W T m K)) [T,m,K,outer,result.2,64*W] (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold metadataCap;omega)
  change fields W _≤6*(natBits (metadataCap model W T m K)+W)+32*W at hf
  unfold window profile
  change columnsFoot W columns+GeneralPaperRetainedCompilerBranchStorage.choiceFoot W choice+
    GeneralPaperNativePayloadFillStorage.window W (columnFoot W) callback (fun j => fieldWindow model W choice columns j inner hi) outer ho+
    fields W [T,m,K,outer,result.2,64*W]+128*W≤_
  omega

end Blotto.GeneralPaperNativeEndpointColumnsStorage
