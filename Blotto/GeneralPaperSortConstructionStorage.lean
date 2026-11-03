import Blotto.GeneralPaperMergeConstructionStorage

/-! Source merge-sort buffers and structural frames. Parent split lists
and completed children are conservatively retained together. Recursion uses
the existing selected depth/fuel and permutation certificates. All control
words derive from the native length/depth/work expressions, not a capacity
or phase-space oracle passed to the algorithm. -/
namespace Blotto.GeneralPaperSortConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def controlCap (W depth N : ℕ) : ℕ := N+depth+(16*N+26+12*depth)*W+(12*depth+2)+256
def controlWord (W depth N : ℕ) : ℕ := natBits (controlCap W depth N)

def controls {α : Type*} (W depth fuel : ℕ) (xs : List α) : ℕ :=
  fields W [depth,fuel,xs.length,GeneralPaperPricedSortSplit.cut depth xs,
    (GeneralPaperRankMidpoint.midpoint depth 0 (xs.length+1)).work,
    (GeneralPaperPricedSortSplit.run W depth xs).work]

theorem controls_bound {α : Type*} (W depth fuel N : ℕ) (xs : List α)
    (hf : fuel≤depth) (hn : xs.length≤N) (hs : N+1<2^depth) :
    controls W depth fuel xs≤6*(controlWord W depth N+W)+32*W := by
  have hm := GeneralPaperRankMidpoint.midpoint_bounds (xs.length+1) depth 0 (xs.length+1)
    (Nat.zero_le _) (Nat.le_refl _) (lt_of_le_of_lt (Nat.add_le_add_right hn 1) hs)
  have hw := GeneralPaperRankMidpoint.midpoint_work depth 0 (xs.length+1)
  have hSplit := GeneralPaperPricedSortSplit.work W depth xs
  have hMul := Nat.mul_le_mul_right W (show 16*xs.length+26+12*depth≤16*N+26+12*depth by omega)
  have bounded (a : ℕ) (ha : a≤controlCap W depth N) : natBits a≤controlWord W depth N :=
    Nat.add_le_add_left (binaryWordWidth_mono ha) 1
  unfold controls
  apply fields_bound W (controlWord W depth N)
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with ha|ha|ha|ha|ha|ha <;> rw [ha] <;> apply bounded <;>
    simp only [controlCap,GeneralPaperPricedSortSplit.cut] <;> omega

def frame {α : Type*} (W : ℕ) (encode : α → ℕ) (compare : α → α → Bool × ℕ)
    (depth fuel : ℕ) (xs : List α) : ℕ :=
  let halves := GeneralPaperPricedSortSplit.run W depth xs
  let left := (GeneralPaperPricedMergeSort.run compare W depth fuel halves.left).1
  let right := (GeneralPaperPricedMergeSort.run compare W depth fuel halves.right).1
  listFootprint W encode xs+listFootprint W encode halves.left+listFootprint W encode halves.right+
    listFootprint W encode left+listFootprint W encode right+controls W depth fuel xs+256*W

theorem frame_bound {α : Type*} (W P depth fuel N : ℕ) (encode : α → ℕ) (compare : α → α → Bool × ℕ)
    (xs : List α) (hf : fuel≤depth) (hn : xs.length≤N) (hs : N+1<2^depth) (he : ∀ x∈xs,encode x≤P) :
    frame W encode compare depth fuel xs≤3*N*(P+2*W)+6*controlWord W depth N+454*W := by
  let halves := GeneralPaperPricedSortSplit.run W depth xs
  have hl : ∀ x∈halves.left,encode x≤P := fun x hx => he x (GeneralPaperPricedSortSplit.left_mem W depth xs x hx)
  have hr : ∀ x∈halves.right,encode x≤P := fun x hx => he x (GeneralPaperPricedSortSplit.right_mem W depth xs x hx)
  have hLeft : ∀ x∈(GeneralPaperPricedMergeSort.run compare W depth fuel halves.left).1,encode x≤P :=
    fun x hx => hl x ((GeneralPaperPricedMergeSort.mem compare W depth fuel halves.left x).mp hx)
  have hRight : ∀ x∈(GeneralPaperPricedMergeSort.run compare W depth fuel halves.right).1,encode x≤P :=
    fun x hx => hr x ((GeneralPaperPricedMergeSort.mem compare W depth fuel halves.right x).mp hx)
  have a := list_bound W P encode xs he
  have b := list_bound W P encode halves.left hl
  have c := list_bound W P encode halves.right hr
  have d := list_bound W P encode (GeneralPaperPricedMergeSort.run compare W depth fuel halves.left).1 hLeft
  have e := list_bound W P encode (GeneralPaperPricedMergeSort.run compare W depth fuel halves.right).1 hRight
  rw [GeneralPaperPricedMergeSort.length] at d e
  have hLengths := GeneralPaperPricedSortSplit.lengths W depth xs
  change halves.left.length+halves.right.length=xs.length at hLengths
  have hControl := controls_bound W depth fuel N xs hf hn hs
  have hSum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add a b) c) d) e) hControl
  have hLenPrice := Nat.mul_le_mul_right (P+2*W) hn
  unfold frame
  dsimp only
  nlinarith only [hSum,hLenPrice,hLengths]

def peak {α : Type*} (W : ℕ) (encode : α → ℕ) (compare : α → α → Bool × ℕ) (depth : ℕ) : ℕ → List α → ℕ
  | 0,xs => listFootprint W encode xs+64*W
  | _+1,[] => listFootprint W encode []+64*W
  | _+1,[x] => listFootprint W encode [x]+64*W
  | fuel+1,x::y::rest =>
    let xs := x::y::rest
    let halves := GeneralPaperPricedSortSplit.run W depth xs
    let left := (GeneralPaperPricedMergeSort.run compare W depth fuel halves.left).1
    let right := (GeneralPaperPricedMergeSort.run compare W depth fuel halves.right).1
    frame W encode compare depth fuel xs+
      max (peak W encode compare depth fuel halves.left)
        (max (peak W encode compare depth fuel halves.right) (GeneralPaperMergeConstructionStorage.window W encode compare left right))

def coefficient (W P C depth N : ℕ) : ℕ :=
  (N+1)*(16*P+4*C+4096*W+32*controlWord W depth N)

theorem bounded {α : Type*} (W P C depth fuel N : ℕ) (encode : α → ℕ) (compare : α → α → Bool × ℕ)
    (xs : List α) (hf : fuel≤depth) (hn : xs.length≤N) (hs : N+1<2^depth)
    (he : ∀ x∈xs,encode x≤P) (hc : ∀ x∈xs,∀ y∈xs,(compare x y).2≤C) :
    peak W encode compare depth fuel xs≤(fuel+1)*coefficient W P C depth N := by
  have reserve (ys : List α) (hyn : ys.length≤N) (hye : ∀ y∈ys,encode y≤P) :
      listFootprint W encode ys+64*W≤coefficient W P C depth N := by
    have hList := list_bound W P encode ys hye
    have hLen := Nat.mul_le_mul_right (P+2*W) hyn
    unfold coefficient
    nlinarith only [hList,hLen,Nat.zero_le N,Nat.zero_le (N*C),Nat.zero_le (N*controlWord W depth N)]
  induction fuel generalizing xs with
  | zero => simpa only [peak,Nat.zero_add,one_mul] using reserve xs hn he
  | succ fuel ih =>
    cases xs with
    | nil =>
      change _≤(fuel+1+1)*coefficient W P C depth N
      exact (reserve [] hn he).trans (Nat.le_mul_of_pos_left _ (by omega))
    | cons x rest =>
      cases rest with
      | nil =>
        change _≤(fuel+1+1)*coefficient W P C depth N
        exact (reserve [x] hn he).trans (Nat.le_mul_of_pos_left _ (by omega))
      | cons y rest =>
        let xs := x::y::rest
        let halves := GeneralPaperPricedSortSplit.run W depth xs
        let left := (GeneralPaperPricedMergeSort.run compare W depth fuel halves.left).1
        let right := (GeneralPaperPricedMergeSort.run compare W depth fuel halves.right).1
        have hLengths := GeneralPaperPricedSortSplit.lengths W depth xs
        change halves.left.length+halves.right.length=xs.length at hLengths
        have hL : ∀ a∈halves.left,a∈xs := fun a ha => GeneralPaperPricedSortSplit.left_mem W depth xs a ha
        have hR : ∀ a∈halves.right,a∈xs := fun a ha => GeneralPaperPricedSortSplit.right_mem W depth xs a ha
        have hLeft := ih halves.left (by omega) (by dsimp only [xs] at hLengths; omega)
          (fun a ha => he a (hL a ha)) (fun a ha b hb => hc a (hL a ha) b (hL b hb))
        have hRight := ih halves.right (by omega) (by dsimp only [xs] at hLengths; omega)
          (fun a ha => he a (hR a ha)) (fun a ha b hb => hc a (hR a ha) b (hR b hb))
        have hLeftMem : ∀ a∈left,a∈xs := fun a ha => hL a ((GeneralPaperPricedMergeSort.mem compare W depth fuel halves.left a).mp ha)
        have hRightMem : ∀ a∈right,a∈xs := fun a ha => hR a ((GeneralPaperPricedMergeSort.mem compare W depth fuel halves.right a).mp ha)
        have hMerge := GeneralPaperMergeConstructionStorage.whole W P C encode compare left right
          (fun a ha => he a (hLeftMem a ha)) (fun a ha => he a (hRightMem a ha))
          (fun a ha b hb => hc a (hLeftMem a ha) b (hRightMem b hb))
        have hOutLengths : left.length+right.length=xs.length := by
          dsimp only [left,right]
          rw [GeneralPaperPricedMergeSort.length,GeneralPaperPricedMergeSort.length]
          exact hLengths
        rw [hOutLengths] at hMerge
        have hM := hMerge.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (4*P+C+68*W) hn) _)
        have hFrame := frame_bound W P depth fuel N encode compare xs (by omega) hn hs he
        have hBoth : frame W encode compare depth fuel xs+GeneralPaperMergeConstructionStorage.window W encode compare left right≤
            coefficient W P C depth N := by
          unfold coefficient
          nlinarith only [hFrame,hM,Nat.zero_le N,Nat.zero_le (N*controlWord W depth N)]
        have hF : frame W encode compare depth fuel xs≤coefficient W P C depth N := by omega
        change frame W encode compare depth fuel xs+max _ (max _ _)≤(fuel+1+1)*coefficient W P C depth N
        rw [←Nat.add_max_add_left,←Nat.add_max_add_left]
        refine max_le ?_ (max_le ?_ ?_)
        · exact (Nat.add_le_add hF hLeft).trans_eq (by ring)
        · exact (Nat.add_le_add hF hRight).trans_eq (by ring)
        · exact hBoth.trans (Nat.le_mul_of_pos_left _ (by omega))

end Blotto.GeneralPaperSortConstructionStorage
