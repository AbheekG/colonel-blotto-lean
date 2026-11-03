import Blotto.GeneralPaperBasisCoordinateStorage

/-! Literal sparse additive scatter, before cancellation. Conservative
frames retain full old/updated/returned vectors, operands/result scratch
and native counters. Zero-fill buffers, input terms and full returned
vector join. No array release, coefficient census or space oracle runs. -/
namespace Blotto.GeneralPaperBasisScatterStorage
open GeneralPaperBasisStoredProducts GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint array_bound)
open GeneralPaperBasisCoordinateStorage (packedTermFoot packedTermProfile packed_term_bound)
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def Good {d : ℕ} (M : ℕ) (v : Vector d) : Prop := ∀ i,(v.read i).natAbs≤M
def vectorProfile (W d M : ℕ) : ℕ := GeneralPaperEncodedBasisStorage.arrayProfile W d (1+binaryWordWidth M)

theorem vector_bound {d : ℕ} (W M : ℕ) (v : Vector d) (hv : Good M v) :
    arrayFootprint W integerBits v≤vectorProfile W d M :=
  array_bound W (1+binaryWordWidth M) integerBits v (fun i => Nat.add_le_add_left (binaryWordWidth_mono (hv i)) 1)

theorem write_good {d : ℕ} (A : ℕ) (values : Vector d) (hv : Good A values) (t : Fin d×ℤ) (ht : t.2.natAbs≤1) :
    Good (A+1) (values.write t.1 (values.read t.1+t.2)) := by
  intro i
  rw [FixedArrayTable.read_write]
  split
  · exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add (hv t.1) ht)
  · exact (hv i).trans (Nat.le_succ A)

theorem loop_values {d : ℕ} (model : RationalCostModel) (W A : ℕ) (terms : List (Fin d×ℤ))
    (values : Vector d) (spent : ℕ) (hu : ∀ t∈terms,t.2.natAbs≤1) (hv : Good A values) :
    Good (A+terms.length) (GeneralPaperBasisScatterBits.loop model.rat W terms values spent).vector := by
  induction terms generalizing A values spent with
  | nil => simpa only [GeneralPaperBasisScatterBits.loop,List.length_nil,Nat.add_zero] using hv
  | cons t rest ih =>
    have h := ih (A+1) (values.write t.1 (values.read t.1+t.2))
      (spent+32*W+GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a+b) (values.read t.1) t.2)
      (fun u hu' => hu u (List.mem_cons_of_mem _ hu')) (write_good A values hv t (hu t List.mem_cons_self))
    simpa only [GeneralPaperBasisScatterBits.loop,List.length_cons,Nat.add_assoc,Nat.add_comm 1 rest.length] using h

def stepCap (model : RationalCostModel) (W M : ℕ) : ℕ := 32*W+2*model.rat (1+binaryWordWidth M)
def metadataCap (model : RationalCostModel) (W d M N B : ℕ) : ℕ := d+N+1+3*(B+2*W)+stepCap model W M+32*W

def frame {d : ℕ} (model : RationalCostModel) (W : ℕ) (terms : List (Fin d×ℤ)) (values : Vector d) (spent : ℕ) : ℕ :=
  let result := GeneralPaperBasisScatterBits.loop model.rat W terms values spent
  match terms with
  | [] => arrayFootprint W integerBits values+arrayFootprint W integerBits result.vector+
      fields W [d,0,spent,result.work,2*W]+128*W
  | t::rest =>
    let sum := values.read t.1+t.2
    let next := values.write t.1 sum
    let op := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a+b) (values.read t.1) t.2
    arrayFootprint W integerBits values+arrayFootprint W integerBits next+arrayFootprint W integerBits result.vector+
      packedTermFoot W t+integerBits (values.read t.1)+integerBits t.2+integerBits sum+op+
      fields W [d,(t::rest).length,spent,op,result.work,spent+32*W+op,32*W]+192*W

def frameProfile (model : RationalCostModel) (W d M N B : ℕ) : ℕ :=
  3*vectorProfile W d M+packedTermProfile W d+3*(1+binaryWordWidth M)+2*model.rat (1+binaryWordWidth M)+
    7*(natBits (metadataCap model W d M N B)+W)+224*W

theorem frame_bound {d : ℕ} (model : RationalCostModel) (W A M N B : ℕ) (terms : List (Fin d×ℤ))
    (values : Vector d) (spent : ℕ) (hu : ∀ t∈terms,t.2.natAbs≤1) (hv : Good A values)
    (hn : terms.length≤N) (hm : A+terms.length≤M) (hb : spent+terms.length*stepCap model W M≤B) :
    frame model W terms values spent≤frameProfile model W d M N B := by
  let result := GeneralPaperBasisScatterBits.loop model.rat W terms values spent
  have hOld := vector_bound W M values (fun i => (hv i).trans (by omega))
  have hReturned := vector_bound W M result.vector (fun i => (loop_values model W A terms values spent hu hv i).trans hm)
  have hWork := GeneralPaperBasisScatterBits.loop_work model.rat model.monotone W A M terms values spent hu hv hm
  change result.work≤spent+terms.length*stepCap model W M+2*W at hWork
  have hReturnWork : result.work≤B+2*W := by omega
  cases terms with
  | nil =>
    have hf := fields_bound W (natBits (metadataCap model W d M N B)) [d,0,spent,result.work,2*W] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; simp only [List.length_nil,Nat.zero_mul,Nat.add_zero] at hb; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (metadataCap model W d M N B)+W)+32*W at hf
    unfold frame frameProfile
    dsimp only
    dsimp only [result] at hReturned hf
    omega
  | cons t rest =>
    have ht := hu t List.mem_cons_self
    have hNext := vector_bound W M (values.write t.1 (values.read t.1+t.2))
      (fun i => (write_good A values hv t ht i).trans (by simp only [List.length_cons] at hm; omega))
    have hT := packed_term_bound W t ht
    have hA := Nat.add_le_add_left (binaryWordWidth_mono ((hv t.1).trans (show A≤M by omega))) 1
    have hB := Nat.add_le_add_left (binaryWordWidth_mono (ht.trans (show 1≤M by simp only [List.length_cons] at hm; omega))) 1
    have hSum : (values.read t.1+t.2).natAbs≤M := ((Int.natAbs_add_le _ _).trans (Nat.add_le_add (hv t.1) ht)).trans (by simp only [List.length_cons] at hm; omega)
    have hC := Nat.add_le_add_left (binaryWordWidth_mono hSum) 1
    have hOp := GeneralPaperIntegerPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b) (values.read t.1) t.2 M
      ((hv t.1).trans (by omega)) (ht.trans (by simp only [List.length_cons] at hm; omega)) hSum
    let op := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a+b) (values.read t.1) t.2
    have hNextSpent : spent+32*W+op≤B := by
      change op≤2*model.rat (1+binaryWordWidth M) at hOp
      have h := Nat.le_mul_of_pos_left (stepCap model W M) (show 0<(t::rest).length by simp)
      unfold stepCap at hb h
      omega
    have hf := fields_bound W (natBits (metadataCap model W d M N B))
      [d,(t::rest).length,spent,op,result.work,spent+32*W+op,32*W] (by
        intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals unfold metadataCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤7*(natBits (metadataCap model W d M N B)+W)+32*W at hf
    unfold frame frameProfile
    dsimp only
    dsimp only [result,op] at hReturned hf hNextSpent
    change integerBits (values.read t.1)≤1+binaryWordWidth M at hA
    change integerBits t.2≤1+binaryWordWidth M at hB
    change integerBits (values.read t.1+t.2)≤1+binaryWordWidth M at hC
    omega

def loopWindow {d : ℕ} (model : RationalCostModel) (W : ℕ) : List (Fin d×ℤ) → Vector d → ℕ → ℕ
  | [],values,spent => frame model W [] values spent
  | t::rest,values,spent => frame model W (t::rest) values spent+
      loopWindow model W rest (values.write t.1 (values.read t.1+t.2))
        (spent+32*W+GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a+b) (values.read t.1) t.2)

theorem loop_bound {d : ℕ} (model : RationalCostModel) (W A M N B : ℕ) (terms : List (Fin d×ℤ))
    (values : Vector d) (spent : ℕ) (hu : ∀ t∈terms,t.2.natAbs≤1) (hv : Good A values)
    (hn : terms.length≤N) (hm : A+terms.length≤M) (hb : spent+terms.length*stepCap model W M≤B) :
    loopWindow model W terms values spent≤(terms.length+1)*frameProfile model W d M N B := by
  induction terms generalizing A values spent with
  | nil => simpa only [loopWindow,List.length_nil,Nat.zero_add,Nat.one_mul] using frame_bound model W A M N B [] values spent hu hv hn hm hb
  | cons t rest ih =>
    have hFrame := frame_bound model W A M N B (t::rest) values spent hu hv hn hm hb
    have ht := hu t List.mem_cons_self
    have hSum : (values.read t.1+t.2).natAbs≤M := ((Int.natAbs_add_le _ _).trans (Nat.add_le_add (hv t.1) ht)).trans (by simp only [List.length_cons] at hm; omega)
    have hOp := GeneralPaperIntegerPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b) (values.read t.1) t.2 M
      ((hv t.1).trans (by omega)) (ht.trans (by simp only [List.length_cons] at hm; omega)) hSum
    have hBudget : spent+32*W+GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a+b) (values.read t.1) t.2+
        rest.length*stepCap model W M≤B := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hb
      unfold stepCap at hb ⊢
      omega
    have hRest := ih (A+1) (values.write t.1 (values.read t.1+t.2))
      (spent+32*W+GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a+b) (values.read t.1) t.2)
      (fun u hu' => hu u (List.mem_cons_of_mem _ hu')) (write_good A values hv t ht)
      (by simp only [List.length_cons] at hn; omega) (by simp only [List.length_cons] at hm; omega) hBudget
    exact (Nat.add_le_add hFrame hRest).trans_eq (by simp only [List.length_cons]; ring)

def callerCap (model : RationalCostModel) (W d N : ℕ) : ℕ := d+N+1+3*(64*(d+1)*W+N*stepCap model W N+10*W)+8*W

def window {d : ℕ} (model : RationalCostModel) (W copied : ℕ) (terms : List (Fin d×ℤ)) : ℕ :=
  let initial := GeneralPaperBasisScatterBits.zeroRun W d
  let inner := GeneralPaperBasisScatterBits.loop model.rat W terms initial.1 0
  let result := GeneralPaperBasisScatterBits.run model.rat W terms
  listFootprint W (packedTermFoot W) terms+
    GeneralPaperNativePayloadFillStorage.window W integerBits (fun _ : Fin d => ((0:ℤ),2*W)) (fun _ => 0)
      (min copied d) (Nat.min_le_right _ _)+loopWindow model W terms initial.1 0+arrayFootprint W integerBits result.vector+
    fields W [d,terms.length,initial.2,inner.work,result.work,initial.2+inner.work,8*W]+256*W
def profile (model : RationalCostModel) (W d N : ℕ) : ℕ :=
  N*(packedTermProfile W d+2*W)+32*W+GeneralPaperNativePayloadFillStorage.profile W 2 d (2*W) 0+
    (N+1)*frameProfile model W d N N (N*stepCap model W N)+vectorProfile W d N+
    7*(natBits (callerCap model W d N)+W)+288*W

theorem bounded {d : ℕ} (model : RationalCostModel) (W N copied : ℕ) (terms : List (Fin d×ℤ))
    (hn : terms.length≤N) (hu : ∀ t∈terms,t.2.natAbs≤1) (hW : 1≤W) (hIndex : binaryWordWidth (d+1)≤W) :
    window model W copied terms≤profile model W d N := by
  let initial := GeneralPaperBasisScatterBits.zeroRun W d
  let inner := GeneralPaperBasisScatterBits.loop model.rat W terms initial.1 0
  let result := GeneralPaperBasisScatterBits.run model.rat W terms
  have hZero : Good 0 initial.1 := by
    intro i
    change ((GeneralPaperBasisScatterBits.zeroRun W d).1.read i).natAbs≤0
    simp only [GeneralPaperBasisScatterBits.zeroRun,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn,Int.natAbs_zero,le_refl]
  have hList := (list_bound W (packedTermProfile W d) (packedTermFoot W) terms (fun t ht => packed_term_bound W t (hu t ht))).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W 2 (2*W) 0 integerBits
    (fun _ : Fin d => ((0:ℤ),2*W)) (fun _ => 0) (by intro i; change 1+binaryWordWidth 0≤2; decide)
    (fun _ => le_rfl) (fun _ => le_rfl) hW hIndex (min copied d) (Nat.min_le_right _ _)
  have hLoop := (loop_bound model W 0 N N (N*stepCap model W N) terms initial.1 0 hu hZero hn (by omega)
    (by simpa only [Nat.zero_add] using Nat.mul_le_mul_right (stepCap model W N) hn)).trans
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right hn 1))
  have hReturned := vector_bound W N result.vector (fun i => (loop_values model W 0 terms initial.1 0 hu hZero i).trans (by omega))
  have hInitialWork := GeneralPaperBasisScatterBits.zero_work W d hW hIndex
  change initial.2≤64*(d+1)*W at hInitialWork
  have hInnerWork := GeneralPaperBasisScatterBits.loop_work model.rat model.monotone W 0 N terms initial.1 0 hu hZero (by omega)
  change inner.work≤0+terms.length*stepCap model W N+2*W at hInnerWork
  have hInner := hInnerWork.trans (Nat.add_le_add_right (by simpa only [Nat.zero_add] using Nat.mul_le_mul_right (stepCap model W N) hn) (2*W))
  have hShape : result.work=initial.2+inner.work+8*W := rfl
  have hf := fields_bound W (natBits (callerCap model W d N))
    [d,terms.length,initial.2,inner.work,result.work,initial.2+inner.work,8*W] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold callerCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤7*(natBits (callerCap model W d N)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [initial,inner,result] at hLoop hReturned hf
  omega

end Blotto.GeneralPaperBasisScatterStorage
