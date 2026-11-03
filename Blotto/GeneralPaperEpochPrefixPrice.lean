import Blotto.GeneralPaperEpochPrefixQuery
import Blotto.GeneralPaperEpochPointPrice

/-! The native running prefix scan, with its one input conversion and one
output materialization. Every running addition is priced from the total cap;
reference conversion costs are linear. No prefix is independently rescanned.
-/
namespace Blotto.GeneralPaperEpochPrefixPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def scan (price : ℕ → ℕ) (W total : ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([total],32*W)
  | value::rest =>
    let next := scan price W (total+value) rest
    (total::next.1,next.2+GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) total value+64*W)

theorem scan_data (price : ℕ → ℕ) (W total : ℕ) (values : List ℕ) :
    (scan price W total values).1=GeneralPaperEpochPrefixArray.scan total values := by
  induction values generalizing total with
  | nil => rfl
  | cons value rest ih => simp only [scan,GeneralPaperEpochPrefixArray.scan,ih]

theorem scan_length (price : ℕ → ℕ) (W total : ℕ) (values : List ℕ) :
    (scan price W total values).1.length=values.length+1 := by
  rw [scan_data,GeneralPaperEpochPrefixArray.scan_length]

theorem scan_work (price : ℕ → ℕ) (hMono : Monotone price) (W cap L total : ℕ) (values : List ℕ)
    (hTotal : total+values.sum≤cap) (hWord : 1+binaryWordWidth cap≤L) :
    (scan price W total values).2≤values.length*(2*price L+64*W)+32*W := by
  induction values generalizing total with
  | nil => simp only [scan,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons value rest ih =>
    have ht : total+value+rest.sum≤cap := by simpa only [List.sum_cons,Nat.add_assoc] using hTotal
    have hr := ih (total+value) ht
    have ha := (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) total value cap
      (by omega) (by omega) (by omega)).trans (Nat.mul_le_mul_left 2 (hMono hWord))
    change (scan price W (total+value) rest).2+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) total value+64*W≤_
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem scan_bounds (price : ℕ → ℕ) (W cap total : ℕ) (values : List ℕ)
    (hTotal : total+values.sum≤cap) (x : ℕ) (hx : x∈(scan price W total values).1) : x≤cap := by
  induction values generalizing total with
  | nil =>
    have he : x=total := by simpa only [scan,List.mem_singleton] using hx
    rw [he]
    simpa using hTotal
  | cons value rest ih =>
    change x∈total::(scan price W (total+value) rest).1 at hx
    rcases List.mem_cons.mp hx with rfl|hx
    · simp only [List.sum_cons] at hTotal; omega
    · apply ih (total+value) (by simpa only [List.sum_cons,Nat.add_assoc] using hTotal) hx

def run {n : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (values : FixedArrayTable n ℕ) :
    FixedArrayTable (n+1) ℕ × ℕ :=
  let A := if bits then arrayWord W (n+2) else W
  let input := StoredArrayReferenceList.list values.data
  let prefixes := scan price W 0 input
  let output := PaperListReferenceArray.run index A prefixes.1
  (⟨output.1,by
    rw [PaperListReferenceArray.size,scan_length]
    dsimp only [input]
    rw [StoredArrayReferenceList.list_data,Array.length_toList,values.size]⟩,
    StoredArrayReferenceList.work index A values.data.size+prefixes.2+output.2+64*W)

theorem data {n : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (values : FixedArrayTable n ℕ) :
    (run bits index price W values).1=GeneralPaperEpochPrefixArray.build values := by
  unfold run GeneralPaperEpochPrefixArray.build
  dsimp only
  simp only [PaperListReferenceArray.data,scan_data,StoredArrayReferenceList.list_data]

theorem sum_bound (values : List ℕ) (U : ℕ) (h : ∀ x∈values,x≤U) : values.sum≤values.length*U := by
  induction values with
  | nil => simp
  | cons x rest ih =>
    have hx := h x List.mem_cons_self
    have hr := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem array_sum_bound {n : ℕ} (values : FixedArrayTable n ℕ) (U : ℕ) (h : ∀ r,values.read r≤U) :
    values.data.toList.sum≤n*U := by
  have hs := sum_bound values.data.toList U (fun x hx => GeneralPaperEpochPointExecution.member_bound U values h x hx)
  simpa only [Array.length_toList,values.size] using hs

def profile (price : ℕ → ℕ) (W n L : ℕ) : ℕ :=
  n*(2*price L+64*W)+96*W+(16*(n+1)+64*(n+2))*arrayWord W (n+2)

def arithmeticProfile (n : ℕ) : ℕ := n*66+96+16*(n+1)+64*(n+2)

theorem bit_work {n : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W cap L : ℕ)
    (values : FixedArrayTable n ℕ) (hTotal : values.data.toList.sum≤cap) (hWord : 1+binaryWordWidth cap≤L) :
    (run true (fun w => w) price W values).2≤profile price W n L := by
  let A := arrayWord W (n+2)
  let input := StoredArrayReferenceList.list values.data
  let prefixes := scan price W 0 input
  have hi : input.length=n := by simp only [input,StoredArrayReferenceList.list_data,Array.length_toList,values.size]
  have hp : prefixes.1.length=n+1 := by rw [scan_length,hi]
  have hScan := scan_work price hMono W cap L 0 input (by simpa only [input,StoredArrayReferenceList.list_data,Nat.zero_add] using hTotal) hWord
  rw [hi] at hScan
  have hA : 1≤A := GeneralPaperSummaryArrayControls.array_word_positive W (n+2)
  have hListBound := GeneralPaperCataloguePointPrice.list_bit_work W n
  have hOutput := PaperListReferenceArray.bit_work A prefixes.1 hA
    (by rw [hp]; exact GeneralPaperSummaryArrayControls.array_index W (n+2) (n+1) (by omega))
  rw [hp] at hOutput
  change StoredArrayReferenceList.work (fun w => w) A values.data.size+prefixes.2+
    (PaperListReferenceArray.run (fun w => w) A prefixes.1).2+64*W≤_
  rw [values.size]
  change prefixes.2≤_ at hScan
  unfold profile
  change _≤n*(2*price L+64*W)+96*W+(16*(n+1)+64*(n+2))*A
  nlinarith only [hListBound,hScan,hOutput]

theorem arithmetic_work {n : ℕ} (values : FixedArrayTable n ℕ) :
    (run false (fun _ => 1) (fun _ => 1) 1 values).2≤arithmeticProfile n := by
  let input := StoredArrayReferenceList.list values.data
  let prefixes := scan (fun _ => 1) 1 0 input
  have hi : input.length=n := by simp only [input,StoredArrayReferenceList.list_data,Array.length_toList,values.size]
  have hp : prefixes.1.length=n+1 := by rw [scan_length,hi]
  have hScan := scan_work (fun _ => 1) (fun _ _ _ => Nat.le_refl _) 1 input.sum
    (1+binaryWordWidth input.sum) 0 input (by omega) (Nat.le_refl _)
  rw [hi] at hScan
  have hList := GeneralPaperCataloguePointPrice.list_arithmetic_work n
  have hOutput := GeneralPaperControlArrayPrice.list_work (fun _ => 1) 1 prefixes.1 (Nat.le_refl _) (fun _ _ => Nat.le_refl _)
  rw [hp] at hOutput
  change StoredArrayReferenceList.work (fun _ => 1) 1 values.data.size+prefixes.2+
    (PaperListReferenceArray.run (fun _ => 1) 1 prefixes.1).2+64≤_
  rw [values.size]
  change prefixes.2≤n*66+32 at hScan
  unfold arithmeticProfile
  nlinarith only [hList,hScan,hOutput]

theorem same_data {n : ℕ} (price : ℕ → ℕ) (W : ℕ) (values : FixedArrayTable n ℕ) :
    (run true (fun w => w) price W values).1=(run false (fun _ => 1) (fun _ => 1) 1 values).1 := by rw [data,data]

end Blotto.GeneralPaperEpochPrefixPrice
