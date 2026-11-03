import Blotto.GeneralPaperBasisGridEntryStorage

/-! Literal selected grid writes. Conservative recursive frames retain
full old/updated/returned vectors, current entry/value and all native work
fields. Original value words are preserved by write; no arithmetic value
accumulation or runtime word census executes. -/
namespace Blotto.GeneralPaperBasisGridWriteStorage
open GeneralPaperBasisStoredProducts GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
open GeneralPaperBasisCoordinateStorage (packedTermFoot)
open GeneralPaperBasisGridEntryStorage (packedProfile packed_bound)
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def Good {d : ℕ} (R : ℕ) (values : Vector d) : Prop := ∀ i,integerBits (values.read i)≤R
theorem write_good {d : ℕ} (R : ℕ) (values : Vector d) (hv : Good R values) (t : Fin d×ℤ) (ht : integerBits t.2≤R) :
    Good R (values.write t.1 t.2) := by
  intro i
  rw [FixedArrayTable.read_write]
  split
  · exact ht
  · exact hv i
theorem returned_good {d : ℕ} (W R : ℕ) (terms : List (Fin d×ℤ)) (values : Vector d)
    (hv : Good R values) (ht : ∀ t∈terms,integerBits t.2≤R) : Good R (GeneralPaperBasisGridPackingPrice.writes W terms values).1 := by
  induction terms generalizing values with
  | nil => exact hv
  | cons t rest ih =>
    exact ih (values.write t.1 t.2) (write_good R values hv t (ht t List.mem_cons_self))
      (fun u hu => ht u (List.mem_cons_of_mem _ hu))
theorem vector_bound {d : ℕ} (W R : ℕ) (values : Vector d) (hv : Good R values) :
    arrayFootprint W integerBits values≤arrayProfile W d R := GeneralPaperEncodedBasisStorage.array_bound W R integerBits values hv
def price (W n : ℕ) : ℕ := 24*n*W+2*W
def metadataCap (W d n : ℕ) : ℕ := d+n+1+3*price W n+24*W
theorem work_bound {d : ℕ} (W n : ℕ) (terms : List (Fin d×ℤ)) (values : Vector d) (hn : terms.length≤n) :
    (GeneralPaperBasisGridPackingPrice.writes W terms values).2≤price W n := by
  rw [GeneralPaperBasisGridPackingPrice.writes_work]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right W (Nat.mul_le_mul_left 24 hn)) _
def frame {d : ℕ} (W : ℕ) (terms : List (Fin d×ℤ)) (values : Vector d) : ℕ :=
  let result := GeneralPaperBasisGridPackingPrice.writes W terms values
  match terms with
  | [] => arrayFootprint W integerBits values+arrayFootprint W integerBits result.1+fields W [d,0,result.2,2*W]+128*W
  | t::rest =>
    let next := values.write t.1 t.2
    let child := GeneralPaperBasisGridPackingPrice.writes W rest next
    arrayFootprint W integerBits values+arrayFootprint W integerBits next+arrayFootprint W integerBits result.1+
      packedTermFoot W t+integerBits t.2+fields W [d,(t::rest).length,child.2,result.2,24*W,child.2+24*W]+192*W
def frameProfile (W d R n : ℕ) : ℕ :=
  3*arrayProfile W d R+packedProfile W d R+R+6*(natBits (metadataCap W d n)+W)+224*W
theorem frame_bound {d : ℕ} (W R n : ℕ) (terms : List (Fin d×ℤ)) (values : Vector d)
    (hv : Good R values) (ht : ∀ t∈terms,integerBits t.2≤R) (hn : terms.length≤n) : frame W terms values≤frameProfile W d R n := by
  let result := GeneralPaperBasisGridPackingPrice.writes W terms values
  have hOld := vector_bound W R values hv
  have hReturned := vector_bound W R result.1 (returned_good W R terms values hv ht)
  have hWork := work_bound W n terms values hn
  change result.2≤price W n at hWork
  cases terms with
  | nil =>
    have hf := fields_bound W (natBits (metadataCap W d n)) [d,0,result.2,2*W] (by
      intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold metadataCap
      rcases hz with rfl|rfl|rfl|rfl <;> omega)
    change fields W [d,0,result.2,2*W]≤4*(natBits (metadataCap W d n)+W)+32*W at hf
    unfold frame frameProfile
    dsimp only
    dsimp only [result] at hReturned hf
    omega
  | cons t rest =>
    let next := values.write t.1 t.2
    let child := GeneralPaperBasisGridPackingPrice.writes W rest next
    have hT := ht t List.mem_cons_self
    have hP := packed_bound W R t hT
    have hNext := vector_bound W R next (write_good R values hv t hT)
    have hChild := work_bound W n rest next (by simp only [List.length_cons] at hn; omega)
    change child.2≤price W n at hChild
    have hShape : result.2=child.2+24*W := rfl
    have hf := fields_bound W (natBits (metadataCap W d n)) [d,(t::rest).length,child.2,result.2,24*W,child.2+24*W] (by
      intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold metadataCap
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields W [d,(t::rest).length,child.2,result.2,24*W,child.2+24*W]≤6*(natBits (metadataCap W d n)+W)+32*W at hf
    unfold frame frameProfile
    dsimp only
    dsimp only [result,next,child] at hReturned hNext hf
    omega
def frames {d : ℕ} (W : ℕ) : List (Fin d×ℤ) → Vector d → ℕ
  | [],values => frame W [] values
  | t::rest,values => frame W (t::rest) values+frames W rest (values.write t.1 t.2)
theorem frames_bound {d : ℕ} (W R n : ℕ) (terms : List (Fin d×ℤ)) (values : Vector d)
    (hv : Good R values) (ht : ∀ t∈terms,integerBits t.2≤R) (hn : terms.length≤n) :
    frames W terms values≤(terms.length+1)*frameProfile W d R n := by
  induction terms generalizing values with
  | nil => simpa only [frames,List.length_nil,Nat.zero_add,Nat.one_mul] using frame_bound W R n [] values hv ht hn
  | cons t rest ih =>
    have hF := frame_bound W R n (t::rest) values hv ht hn
    have hRest := ih (values.write t.1 t.2) (write_good R values hv t (ht t List.mem_cons_self))
      (fun u hu => ht u (List.mem_cons_of_mem _ hu)) (by simp only [List.length_cons] at hn; omega)
    exact (Nat.add_le_add hF hRest).trans_eq (by simp only [List.length_cons]; ring)
def window {d : ℕ} (W : ℕ) (terms : List (Fin d×ℤ)) (values : Vector d) : ℕ :=
  listFootprint W (packedTermFoot W) terms+frames W terms values
def profile (W d R n : ℕ) : ℕ := n*(packedProfile W d R+2*W)+32*W+(n+1)*frameProfile W d R n
theorem bounded {d : ℕ} (W R n : ℕ) (terms : List (Fin d×ℤ)) (values : Vector d)
    (hv : Good R values) (ht : ∀ t∈terms,integerBits t.2≤R) (hn : terms.length≤n) : window W terms values≤profile W d R n := by
  have hList := (list_bound W (packedProfile W d R) (packedTermFoot W) terms (fun t ht' => packed_bound W R t (ht t ht'))).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  have hFrames := (frames_bound W R n terms values hv ht hn).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hn 1))
  exact Nat.add_le_add hList hFrames

end Blotto.GeneralPaperBasisGridWriteStorage
