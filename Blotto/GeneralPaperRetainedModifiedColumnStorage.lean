import Blotto.GeneralPaperNativeEndpointColumnsStorage

/-! Native modified-column caller: original columns/values, returned
branch choice and optional columns, reached nested array construction and
thirteen native parent fields. Rejection builds no endpoint anchors. -/
namespace Blotto.GeneralPaperRetainedModifiedColumnStorage
open GeneralPaperEncodedScalarStorage GeneralPaperSourceEndpointBranch GeneralPaperEnclosingSourceOwners
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384

def optionFoot {T m K : ℕ} (W : ℕ) : Option (FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) → ℕ
  | none => 1
  | some columns => 1+columnsFoot W columns+32*W

def child {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (branch : Option (Result T m K))
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) : Option (FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))×ℕ :=
  match branch with
  | none => (none,0)
  | some result =>
    let prepared := GeneralPaperNativeEndpointColumns.run model.rat (fun w => w) W result.choice columns
    (some prepared.1,prepared.2)

def price (model : RationalCostModel) (W m K P : ℕ) : ℕ := P+GeneralPaperNativeEndpointColumnsStorage.price model W m K+64*W
def metadataCap (model : RationalCostModel) (W T m K P : ℕ) : ℕ := T+m+K+price model W m K P+1

def window {T m K : ℕ} (model : RationalCostModel) (W depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (values : GeneralPaperRetainedFieldValues.Values m)
    (own opposing : ℚ) (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ)
    (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤K) : ℕ :=
  let branch := GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value
  let prepared := child model W branch.1 columns
  let result := GeneralPaperRetainedModifiedColumnBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value
  columnsFoot W columns+GeneralPaperEncodedRationalRows.rowFootprint W values.values+
    GeneralPaperRetainedCompilerBranchStorage.resultFoot W branch.1+optionFoot W result.1+
    (match branch.1 with
     | none => 0
     | some r => GeneralPaperNativeEndpointColumnsStorage.window model W r.choice columns outer ho inner hi)+
    fields W [T,m,K,outer,inner,branch.2,prepared.2,result.2,branch.2+prepared.2,32*W,64*W,
      GeneralPaperFinalStaticLoopStorage.bit branch.1.isSome,GeneralPaperFinalStaticLoopStorage.bit result.1.isSome]+128*W

def profile (model : RationalCostModel) (W T m K R V B P : ℕ) : ℕ :=
  columnsProfile W T m K R+GeneralPaperEncodedRationalRows.rowProfile W m V+
    (1+B+32*W)+(1+columnsProfile W T m K (3+B)+32*W)+
    GeneralPaperNativeEndpointColumnsStorage.profile model W T m K R B+
    13*(natBits (metadataCap model W T m K P)+W)+160*W

theorem data {T m K : ℕ} (model : RationalCostModel) (W depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (values : GeneralPaperRetainedFieldValues.Values m)
    (own opposing : ℚ) (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) :
    (GeneralPaperRetainedModifiedColumnBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value).1=
      (child model W (GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value).1 columns).1 := by
  cases hr : (GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value).1 <;>
    simp only [GeneralPaperRetainedModifiedColumnBits.run,hr,child]

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W depth S H p q R V B P : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (values : GeneralPaperRetainedFieldValues.Values m)
    (own opposing : ℚ) (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ)
    (hR : ∀ j l,rationalWordWidth ((columns.read j).anchors.read l)≤R)
    (hV : ∀ j,RationalHeight (values.values.read j) V)
    (hB : ∀ result,(GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value).1=some result →
      GeneralPaperRetainedCompilerBranchStorage.choiceFoot W result.choice≤B)
    (hP : (GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value).2≤P)
    (hW : 1≤W) (hLabel : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤K) :
    window model W depth S H p q hK columns values own opposing reciprocal endpoint value outer ho inner hi≤profile model W T m K R V B P ∧
    (GeneralPaperRetainedModifiedColumnBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value).2≤price model W m K P := by
  let branch := GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value
  let prepared := child model W branch.1 columns
  let result := GeneralPaperRetainedModifiedColumnBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value
  change branch.2≤P at hP
  have hColumns := columns_bound W R columns hR
  have hValues := GeneralPaperEncodedRationalRows.row_bound W V values.values hV
  have hBranch : GeneralPaperRetainedCompilerBranchStorage.resultFoot W branch.1≤1+B+32*W := by
    cases hr : branch.1 with
    | none => simp only [GeneralPaperRetainedCompilerBranchStorage.resultFoot];omega
    | some r =>
      have h := hB r hr
      simp only [GeneralPaperRetainedCompilerBranchStorage.resultFoot]
      omega
  have hPrepared : prepared.2≤GeneralPaperNativeEndpointColumnsStorage.price model W m K := by
    dsimp only [prepared]
    unfold child
    split
    · exact Nat.zero_le _
    · exact GeneralPaperNativeEndpointColumnsStorage.work model W _ columns hW hLabel hM
  have hReturned : optionFoot W result.1≤1+columnsProfile W T m K (3+B)+32*W := by
    rw [data]
    cases hr : branch.1 with
    | none => change 1≤_;omega
    | some r =>
      have h := GeneralPaperNativeEndpointColumnsStorage.returned model W B r.choice columns (hB r hr)
      change 1+columnsFoot W (GeneralPaperNativeEndpointColumns.run model.rat (fun w => w) W r.choice columns).1+32*W≤_
      omega
  have hChild : (match branch.1 with
      | none => 0
      | some r => GeneralPaperNativeEndpointColumnsStorage.window model W r.choice columns outer ho inner hi)≤
      GeneralPaperNativeEndpointColumnsStorage.profile model W T m K R B := by
    cases hr : branch.1 with
    | none => exact Nat.zero_le _
    | some r => exact GeneralPaperNativeEndpointColumnsStorage.bounded model W R B r.choice columns hR (hB r hr) hW hLabel hM outer ho inner hi
  have hShape : result.2≤branch.2+prepared.2+64*W := by
    dsimp only [result,GeneralPaperRetainedModifiedColumnBits.run,prepared,child,branch]
    cases hr : (GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value).1 <;>
      simp only [] <;> omega
  have hWork : result.2≤price model W m K P := by unfold price;omega
  unfold price at hWork
  have hb := GeneralPaperFinalStaticLoopStorage.bit_bound branch.1.isSome
  have hr := GeneralPaperFinalStaticLoopStorage.bit_bound result.1.isSome
  have hf := fields_bound W (natBits (metadataCap model W T m K P))
    [T,m,K,outer,inner,branch.2,prepared.2,result.2,branch.2+prepared.2,32*W,64*W,
      GeneralPaperFinalStaticLoopStorage.bit branch.1.isSome,GeneralPaperFinalStaticLoopStorage.bit result.1.isSome] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap price;omega)
  change fields W _≤13*(natBits (metadataCap model W T m K P)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  unfold window profile
  change columnsFoot W columns+GeneralPaperEncodedRationalRows.rowFootprint W values.values+
    GeneralPaperRetainedCompilerBranchStorage.resultFoot W branch.1+optionFoot W result.1+
    (match branch.1 with
     | none => 0
     | some r => GeneralPaperNativeEndpointColumnsStorage.window model W r.choice columns outer ho inner hi)+
    fields W [T,m,K,outer,inner,branch.2,prepared.2,result.2,branch.2+prepared.2,32*W,64*W,
      GeneralPaperFinalStaticLoopStorage.bit branch.1.isSome,GeneralPaperFinalStaticLoopStorage.bit result.1.isSome]+128*W≤_
  omega

end Blotto.GeneralPaperRetainedModifiedColumnStorage
