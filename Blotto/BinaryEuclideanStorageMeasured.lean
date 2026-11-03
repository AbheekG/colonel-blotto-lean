import Blotto.BinaryDivisionStorageMeasured
import Blotto.BinaryNormalizationAllocation

/-! The retained Euclidean normalizer produces its Boolean data, allocation,
held buffers, old source charge and reached division work in one execution.
The old observer programs occur only in proofs. These are source/list-cell
contracts; native metadata arithmetic, references and allocator costs remain. -/
namespace Blotto.BinaryEuclideanStorageMeasured
open BinaryRationalNormalization
open BinaryDivisionStorageMeasured (Result)
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem divisionProduced_data_widths (first second : List Bool) :
    (BinaryDivisionStorageMeasured.divideProduced first second).1.data.1.length = first.length ∧
      (BinaryDivisionStorageMeasured.divideProduced first second).1.data.2.length = second.length := by
  change (BinaryDivisionStorageMeasured.divide first second).data.1.length = _ ∧
    (BinaryDivisionStorageMeasured.divide first second).data.2.length = _
  rw [BinaryDivisionStorageMeasured.divide_data]
  exact BinaryLongDivision.divide_lengths first second

def loopReference : ℕ → List Bool → List Bool → Result (List Bool)
  | 0,first,second => ⟨first,1,first.length+second.length+1,1,1⟩
  | fuel+1,first,second =>
      let scanned := BinaryNormalizationAllocation.scanWithFrames second
      if scanned.1 then
        let divided := BinaryDivisionStorageMeasured.divide first second
        let later := loopReference fuel second divided.data.2
        ⟨later.data,scanned.2+2+divided.allocated+later.allocated,
          first.length+second.length+scanned.2+3+divided.data.1.length+
            divided.data.2.length+divided.storage+later.held,
          3*(second.length+1)+2+(divided.source+later.source),
          3*(second.length+1)+2+(divided.work+later.work)⟩
      else ⟨first,scanned.2+2,first.length+second.length+scanned.2+3,
        3*(second.length+1)+2,3*(second.length+1)+2⟩

def loopAt : ℕ → List Bool → List Bool → ℕ → ℕ → Result (List Bool) × ℕ
  | 0,first,_second,n,m => (⟨first,1,n+m+1,1,1⟩,n)
  | fuel+1,first,second,n,m =>
      let scanned := BinaryNormalizationAllocation.scanWithFrames second
      if scanned.1 then
        let produced := BinaryDivisionStorageMeasured.divideProduced first second
        let divided := produced.1
        let later := loopAt fuel second divided.data.2 m produced.2.2
        (⟨later.1.data,scanned.2+2+divided.allocated+later.1.allocated,
          n+m+scanned.2+3+produced.2.1+produced.2.2+divided.storage+later.1.held,
          3*(m+1)+2+(divided.source+later.1.source),
          3*(m+1)+2+(divided.work+later.1.work)⟩,later.2)
      else (⟨first,scanned.2+2,n+m+scanned.2+3,3*(m+1)+2,3*(m+1)+2⟩,n)

theorem loopAt_record (fuel : ℕ) (first second : List Bool) (n m : ℕ)
    (hN : n=first.length) (hM : m=second.length) :
    (loopAt fuel first second n m).1 = loopReference fuel first second := by
  induction fuel generalizing first second n m with
  | zero => simp only [loopAt,loopReference,hN,hM]
  | succ fuel ih =>
      have hw := divisionProduced_data_widths first second
      have hr : (BinaryDivisionStorageMeasured.divideProduced first second).2.2 =
          (BinaryDivisionStorageMeasured.divideProduced first second).1.data.2.length := by
        rw [BinaryDivisionStorageMeasured.divideProduced_lengths]
        exact hw.2.symm
      simp only [loopAt,loopReference]
      split
      · rw [ih second (BinaryDivisionStorageMeasured.divideProduced first second).1.data.2 m
          (BinaryDivisionStorageMeasured.divideProduced first second).2.2 hM hr]
        simp only [BinaryDivisionStorageMeasured.divideProduced_lengths,BinaryDivisionStorageMeasured.divide,
          hw.1,hw.2,hN,hM]
      · simp only [hN,hM]

theorem loopAt_width (fuel : ℕ) (first second : List Bool) (n m : ℕ)
    (hN : n=first.length) (hM : m=second.length) :
    (loopAt fuel first second n m).2 = (loopAt fuel first second n m).1.data.length := by
  induction fuel generalizing first second n m with
  | zero => exact hN
  | succ fuel ih =>
      have hw := divisionProduced_data_widths first second
      have hr : (BinaryDivisionStorageMeasured.divideProduced first second).2.2 =
          (BinaryDivisionStorageMeasured.divideProduced first second).1.data.2.length := by
        rw [BinaryDivisionStorageMeasured.divideProduced_lengths]
        exact hw.2.symm
      simp only [loopAt]
      split
      · exact ih second (BinaryDivisionStorageMeasured.divideProduced first second).1.data.2 m
          (BinaryDivisionStorageMeasured.divideProduced first second).2.2 hM hr
      · exact hN

theorem loopAt_scan_control_work (fuel : ℕ) (first second : List Bool) (n m : ℕ)
    (hM : m=second.length) :
    (BinaryNormalizationAllocation.scanWithFrames second).2+2 ≤
      (loopAt (fuel+1) first second n m).1.work := by
  have hs := BinaryNormalizationAllocation.scanWithFrames_bound second
  simp only [loopAt]
  split <;> dsimp only <;> omega

def loop : ℕ → List Bool → List Bool → Result (List Bool)
  | fuel,first,second => (loopAt fuel first second
      (BinaryBorrowDropMetadata.countFrom first 0) (BinaryBorrowDropMetadata.countFrom second 0)).1

theorem loop_compat (fuel : ℕ) (first second : List Bool) :
    loop fuel first second = loopReference fuel first second := by
  apply loopAt_record
  · simp only [BinaryBorrowDropMetadata.count_exact,Nat.zero_add]
  · simp only [BinaryBorrowDropMetadata.count_exact,Nat.zero_add]

theorem loopAt_public (fuel : ℕ) (first second : List Bool) (n m : ℕ)
    (hN : n=first.length) (hM : m=second.length) :
    (loopAt fuel first second n m).1 = loop fuel first second := by
  rw [loop_compat]
  exact loopAt_record fuel first second n m hN hM

theorem loop_zero (first second : List Bool) :
    loop 0 first second = ⟨first,1,first.length+second.length+1,1,1⟩ := by
  rw [loop_compat]; rfl

theorem loop_succ (fuel : ℕ) (first second : List Bool) :
    loop (fuel+1) first second = (
      let scanned := BinaryNormalizationAllocation.scanWithFrames second
      if scanned.1 then
        let divided := BinaryDivisionStorageMeasured.divide first second
        let later := loop fuel second divided.data.2
        ⟨later.data,scanned.2+2+divided.allocated+later.allocated,
          first.length+second.length+scanned.2+3+divided.data.1.length+
            divided.data.2.length+divided.storage+later.held,
          3*(second.length+1)+2+(divided.source+later.source),
          3*(second.length+1)+2+(divided.work+later.work)⟩
      else ⟨first,scanned.2+2,first.length+second.length+scanned.2+3,
        3*(second.length+1)+2,3*(second.length+1)+2⟩) := by
  simp only [loop_compat,loopReference]

theorem loop_erases (fuel : ℕ) (first second : List Bool) :
    ((loop fuel first second).data,(loop fuel first second).allocated) =
      BinaryNormalizationAllocation.gcdLoopWithAllocation fuel first second := by
  induction fuel generalizing first second with
  | zero => simp only [loop_zero,BinaryNormalizationAllocation.gcdLoopWithAllocation]
  | succ fuel ih =>
      simp only [loop_succ,loop_zero,BinaryNormalizationAllocation.gcdLoopWithAllocation,
        ← BinaryDivisionStorageMeasured.divide_erases,← ih]
      split <;> rfl

theorem loop_data (fuel : ℕ) (first second : List Bool) :
    (loop fuel first second).data = BinaryEuclideanGCD.loop fuel first second := by
  have h := congrArg Prod.fst (loop_erases fuel first second)
  simpa only [BinaryNormalizationAllocation.gcdLoopWithAllocation_refines] using h

theorem loop_held (fuel : ℕ) (first second : List Bool) :
    (loop fuel first second).held = BinaryNormalizationAllocation.gcdLoopHeld fuel first second := by
  induction fuel generalizing first second with
  | zero => simp only [loop_zero,BinaryNormalizationAllocation.gcdLoopHeld]
  | succ fuel ih =>
      simp only [loop_succ,loop_zero,BinaryNormalizationAllocation.gcdLoopHeld,
        BinaryNormalizationAllocation.scanWithFrames_state,BinaryDivisionStorageMeasured.divide_data,
        BinaryDivisionStorageMeasured.divide_storage,ih]
      split <;> dsimp only <;> omega

theorem loop_source (fuel : ℕ) (first second : List Bool) :
    (loop fuel first second).source = (BinaryEuclideanGCD.loopWithWork fuel first second).2 := by
  induction fuel generalizing first second with
  | zero => simp only [loop_zero,BinaryEuclideanGCD.loopWithWork]
  | succ fuel ih =>
      simp only [loop_succ,loop_zero,BinaryEuclideanGCD.loopWithWork,
        BinaryNormalizationAllocation.scanWithFrames_state,BinaryDivisionStorageMeasured.divide_source,
        BinaryDivisionStorageMeasured.divide_data,BinaryLongDivision.divideWithWork_refines,
        BinaryEuclideanGCD.zeroScanWork,ih]
      split <;> rfl

theorem loop_work_bound (fuel : ℕ) (first second : List Bool) :
    (loop fuel first second).work ≤ 4*(loop fuel first second).source := by
  induction fuel generalizing first second with
  | zero => change 1 ≤ 4*1; omega
  | succ fuel ih =>
      have hd := BinaryDivisionStorageMeasured.divide_work_bound first second
      have ht := ih second (BinaryDivisionStorageMeasured.divide first second).data.2
      simp only [loop_succ,loop_zero]
      split <;> dsimp only <;> omega

def gcdProduced (first second : List Bool) : (Result (List Bool) × ℕ) × (ℕ × ℕ) :=
  let n := BinaryBorrowDropMetadata.countFrom first 0
  let m := BinaryBorrowDropMetadata.countFrom second 0
  let W := max n m
  let returned := loopAt (2*(W+1)) first second n m
  let base := n+m+4*(W+1)
  ((⟨returned.1.data,base+returned.1.allocated,base+returned.1.held,
    base+returned.1.source,base+returned.1.work⟩,returned.2),(n,m))

theorem gcdProduced_lengths (first second : List Bool) :
    (gcdProduced first second).2 = (first.length,second.length) := by
  simp only [gcdProduced,BinaryBorrowDropMetadata.count_exact,Nat.zero_add]

theorem gcdProduced_width (first second : List Bool) :
    (gcdProduced first second).1.2 = (gcdProduced first second).1.1.data.length := by
  simp only [gcdProduced]
  apply loopAt_width
  · simp only [BinaryBorrowDropMetadata.count_exact,Nat.zero_add]
  · simp only [BinaryBorrowDropMetadata.count_exact,Nat.zero_add]

theorem gcdProduced_record (first second : List Bool) :
    (gcdProduced first second).1.1 = (
  let W := BinaryEuclideanGCD.width first second
  let returned := loop (2*(W+1)) first second
  let base := first.length+second.length+4*(W+1)
  ⟨returned.data,base+returned.allocated,base+returned.held,
    base+returned.source,base+returned.work⟩) := by
  simp only [gcdProduced,BinaryBorrowDropMetadata.count_exact,Nat.zero_add]
  rw [loopAt_public _ first second first.length second.length rfl rfl]
  rfl

theorem gcd_setup_work_bound (first second : List Bool) :
    (BinaryBorrowDropMetadata.countFrom first 0+1)+(BinaryBorrowDropMetadata.countFrom second 0+1) ≤
      first.length+second.length+4*(BinaryEuclideanGCD.width first second+1) := by
  simp only [BinaryBorrowDropMetadata.count_exact,Nat.zero_add]
  omega

attribute [irreducible] loopAt gcdProduced

def gcd (first second : List Bool) : Result (List Bool) := (gcdProduced first second).1.1

theorem gcd_previous_record (first second : List Bool) :
    gcd first second = (
  let W := BinaryEuclideanGCD.width first second
  let returned := loop (2*(W+1)) first second
  let base := first.length+second.length+4*(W+1)
  ⟨returned.data,base+returned.allocated,base+returned.held,
    base+returned.source,base+returned.work⟩) := gcdProduced_record first second

theorem gcd_erases (first second : List Bool) :
    ((gcd first second).data,(gcd first second).allocated) =
      BinaryNormalizationAllocation.gcdWithAllocation first second := by
  simp only [gcd_previous_record,BinaryNormalizationAllocation.gcdWithAllocation,← loop_erases]

theorem gcd_data (first second : List Bool) :
    (gcd first second).data = (BinaryEuclideanGCD.gcdWithWork first second).1 := by
  rw [BinaryEuclideanGCD.gcdWithWork,BinaryEuclideanGCD.loopWithWork_refines]
  simp only [gcd_previous_record]
  exact loop_data _ _ _

theorem gcd_storage (first second : List Bool) :
    (gcd first second).storage = BinaryNormalizationAllocation.gcdStorage first second := by
  have ha := congrArg Prod.snd (gcd_erases first second)
  change (gcd first second).allocated = _ at ha
  simp only [BinaryDivisionStorageMeasured.Result.storage]
  rw [ha]
  simp only [gcd_previous_record,BinaryNormalizationAllocation.gcdStorage,loop_held]

theorem gcd_source (first second : List Bool) :
    (gcd first second).source = (BinaryEuclideanGCD.gcdWithWork first second).2 := by
  simp only [gcd_previous_record,BinaryEuclideanGCD.gcdWithWork,loop_source]

theorem gcd_work_bound (first second : List Bool) :
    (gcd first second).work ≤ 4*(gcd first second).source := by
  have h := loop_work_bound (2*(BinaryEuclideanGCD.width first second+1)) first second
  simp only [gcd_previous_record]
  omega

def normalize (word : SignedWord) : Result SignedWord :=
  let commonProduced := gcdProduced word.numerator word.denominator
  let common := commonProduced.1.1
  let numeratorProduced := BinaryDivisionStorageMeasured.divideProduced word.numerator common.data
  let numerator := numeratorProduced.1
  let denominatorProduced := BinaryDivisionStorageMeasured.divideProduced word.denominator common.data
  let denominator := denominatorProduced.1
  let scanned := BinaryNormalizationAllocation.scanWithFrames numerator.data.1
  ⟨⟨word.negative && scanned.1,numerator.data.1,denominator.data.1⟩,
    common.allocated+numerator.allocated+denominator.allocated+scanned.2+4,
    commonProduced.2.1+commonProduced.2.2+1+commonProduced.1.2+
      numeratorProduced.2.1+numeratorProduced.2.2+denominatorProduced.2.1+
      denominatorProduced.2.2+scanned.2+4+common.storage+numerator.storage+denominator.storage,
    common.source+numerator.source+denominator.source+3*(commonProduced.2.1+1)+2,
    common.work+numerator.work+denominator.work+3*(commonProduced.2.1+1)+2⟩

theorem normalize_previous_record (word : SignedWord) :
    normalize word = (
  let common := gcd word.numerator word.denominator
  let numerator := BinaryDivisionStorageMeasured.divide word.numerator common.data
  let denominator := BinaryDivisionStorageMeasured.divide word.denominator common.data
  let scanned := BinaryNormalizationAllocation.scanWithFrames numerator.data.1
  ⟨⟨word.negative && scanned.1,numerator.data.1,denominator.data.1⟩,
    common.allocated+numerator.allocated+denominator.allocated+scanned.2+4,
    word.numerator.length+word.denominator.length+1+common.data.length+
      numerator.data.1.length+numerator.data.2.length+denominator.data.1.length+
      denominator.data.2.length+scanned.2+4+common.storage+numerator.storage+denominator.storage,
    common.source+numerator.source+denominator.source+3*(word.numerator.length+1)+2,
    common.work+numerator.work+denominator.work+3*(word.numerator.length+1)+2⟩) := by
  have hn := divisionProduced_data_widths word.numerator (gcd word.numerator word.denominator).data
  have hd := divisionProduced_data_widths word.denominator (gcd word.numerator word.denominator).data
  change (BinaryDivisionStorageMeasured.divide word.numerator _).data.1.length = _ ∧
    (BinaryDivisionStorageMeasured.divide word.numerator _).data.2.length = _ at hn
  change (BinaryDivisionStorageMeasured.divide word.denominator _).data.1.length = _ ∧
    (BinaryDivisionStorageMeasured.divide word.denominator _).data.2.length = _ at hd
  simp only [normalize,gcdProduced_lengths,gcdProduced_width,
    BinaryDivisionStorageMeasured.divideProduced_lengths]
  simp only [gcd,BinaryDivisionStorageMeasured.divide] at hn hd ⊢
  rw [hn.1,hn.2,hd.1,hd.2]

theorem normalize_erases (word : SignedWord) :
    ((normalize word).data,(normalize word).allocated) =
      BinaryNormalizationAllocation.normalizeWithAllocation word := by
  simp only [normalize_previous_record,BinaryNormalizationAllocation.normalizeWithAllocation,
    ← gcd_erases,← BinaryDivisionStorageMeasured.divide_erases]

theorem normalize_data (word : SignedWord) :
    (normalize word).data = BinaryRationalNormalization.normalize word :=
  (congrArg Prod.fst (normalize_erases word)).trans
    (BinaryNormalizationAllocation.normalizeWithAllocation_state word)

theorem normalize_allocated (word : SignedWord) :
    (normalize word).allocated = (BinaryNormalizationAllocation.normalizeWithAllocation word).2 :=
  congrArg Prod.snd (normalize_erases word)

theorem normalize_storage (word : SignedWord) :
    (normalize word).storage = BinaryNormalizationAllocation.normalizeStorage word := by
  rw [BinaryDivisionStorageMeasured.Result.storage,normalize_allocated]
  simp only [normalize_previous_record,BinaryNormalizationAllocation.normalizeStorage,
    BinaryNormalizationAllocation.normalizeHeld,← gcd_erases,
    BinaryDivisionStorageMeasured.divide_data,BinaryDivisionStorageMeasured.divide_storage,gcd_storage]

theorem normalize_source (word : SignedWord) :
    (normalize word).source = (BinaryRationalNormalization.normalizeWithWork word).2 := by
  simp only [normalize_previous_record,BinaryRationalNormalization.normalizeWithWork,gcd_data,gcd_source,
    BinaryDivisionStorageMeasured.divide_source]

theorem normalize_work_bound (word : SignedWord) :
    (normalize word).work ≤ 4*(normalize word).source := by
  have hc := gcd_work_bound word.numerator word.denominator
  have hn := BinaryDivisionStorageMeasured.divide_work_bound word.numerator (gcd word.numerator word.denominator).data
  have hd := BinaryDivisionStorageMeasured.divide_work_bound word.denominator (gcd word.numerator word.denominator).data
  simp only [normalize_previous_record]
  omega

theorem normalize_work_cubic (word : SignedWord) :
    (normalize word).work ≤ 600*(width word+1)^3 := by
  have h := normalize_work_bound word
  rw [normalize_source] at h
  have hs := normalizeWithWork_bound word
  omega

theorem gcd_storage_bound (first second : List Bool) :
    (gcd first second).storage ≤ 2000*(BinaryEuclideanGCD.width first second+2)^4 := by
  rw [gcd_storage]
  exact BinaryNormalizationAllocation.gcdStorage_bound first second

theorem normalize_storage_bound (word : SignedWord) :
    (normalize word).storage ≤ 4000*(width word+2)^4 := by
  rw [normalize_storage]
  exact BinaryNormalizationAllocation.normalizeStorage_bound word

end Blotto.BinaryEuclideanStorageMeasured
