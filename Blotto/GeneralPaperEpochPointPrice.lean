import Blotto.GeneralPaperEpochPointExecution

/-! Both input conversions, successor arithmetic and both reference
appends are charged. Input descriptor sizes derive conversion words.
-/
namespace Blotto.GeneralPaperEpochPointPrice
open GeneralPaperEpochPointExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def profile (price : ℕ → ℕ) (W n m U : ℕ) : ℕ :=
  16*(n+1)*arrayWord W (n+2)+16*(m+1)*arrayWord W (m+2)+
    (2*price (GeneralPaperCataloguePointOperands.width U)+64*W)*n+70*W

def arithmeticProfile (n m : ℕ) : ℕ := 16*(n+1)+16*(m+1)+66*n+70

theorem successor_work (price : ℕ → ℕ) (hMono : Monotone price) (W U x : ℕ) (hx : x<U) :
    (successor price W x).2≤2*price (GeneralPaperCataloguePointOperands.width U)+32*W := by
  have h := (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) x 1
    (GeneralPaperCataloguePointOperands.magnitude U)
    (by unfold GeneralPaperCataloguePointOperands.magnitude; omega)
    (by unfold GeneralPaperCataloguePointOperands.magnitude; omega)
    (by unfold GeneralPaperCataloguePointOperands.magnitude; omega)).trans
      (Nat.mul_le_mul_left 2 (hMono (GeneralPaperCataloguePointOperands.word_bound U)))
  exact Nat.add_le_add_right h _

theorem bit_work {n m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W U : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) (hPositions : ∀ r,positions.read r<U) :
    (run true (fun w => w) price W positions extras).2≤profile price W n m U := by
  let p := StoredArrayReferenceList.list positions.data
  let e := StoredArrayReferenceList.list extras.data
  let mapped := GeneralPaperPricedListMap.run W (successor price W) p
  let joined := GeneralPaperPricedListAppend.run W p mapped.1
  have hp : p.length=n := by simp only [p,StoredArrayReferenceList.list_data,Array.length_toList,positions.size]
  have hm : mapped.1.length=n := by rw [GeneralPaperPricedListMap.length,hp]
  have hj : joined.1.length=2*n := by rw [GeneralPaperPricedListAppend.data,List.length_append,hp,hm]; omega
  have hb (x : ℕ) (hx : x∈p) : x<U := by
    have h := member_bound (U-1) positions (fun r => by have h := hPositions r; omega) x
      (by simpa only [p,StoredArrayReferenceList.list_data] using hx)
    obtain ⟨i,hi,_⟩ := List.getElem_of_mem hx
    have hiN : i<n := by simpa only [hp] using hi
    have hU := hPositions ⟨i,hiN⟩
    omega
  have hMap := GeneralPaperPricedListMap.work W (2*price (GeneralPaperCataloguePointOperands.width U)+32*W)
    (successor price W) p (fun x hx => successor_work price hMono W U x (hb x hx))
  rw [hp] at hMap
  have ha := GeneralPaperPricedListAppend.work W p mapped.1
  have hc := GeneralPaperPricedListAppend.work W joined.1 e
  rw [hp] at ha
  rw [hj] at hc
  have hP := GeneralPaperCataloguePointPrice.list_bit_work W n
  have hE := GeneralPaperCataloguePointPrice.list_bit_work W m
  change _≤profile price W n m U
  unfold run
  dsimp only
  simp only [ite_true,positions.size,extras.size]
  change _≤_ at hMap
  unfold profile
  dsimp only [p,e,mapped,joined] at hMap ha hc
  nlinarith only [hP,hE,hMap,ha,hc]

theorem arithmetic_work {n m : ℕ} (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) :
    (run false (fun _ => 1) (fun _ => 1) 1 positions extras).2≤arithmeticProfile n m := by
  let p := StoredArrayReferenceList.list positions.data
  let e := StoredArrayReferenceList.list extras.data
  let mapped := GeneralPaperPricedListMap.run 1 (successor (fun _ => 1) 1) p
  let joined := GeneralPaperPricedListAppend.run 1 p mapped.1
  have hp : p.length=n := by simp only [p,StoredArrayReferenceList.list_data,Array.length_toList,positions.size]
  have hm : mapped.1.length=n := by rw [GeneralPaperPricedListMap.length,hp]
  have hj : joined.1.length=2*n := by rw [GeneralPaperPricedListAppend.data,List.length_append,hp,hm]; omega
  have hMap := GeneralPaperPricedListMap.work 1 34 (successor (fun _ => 1) 1) p (fun _ _ => Nat.le_refl _)
  rw [hp] at hMap
  have ha := GeneralPaperPricedListAppend.work 1 p mapped.1
  have hc := GeneralPaperPricedListAppend.work 1 joined.1 e
  rw [hp] at ha
  rw [hj] at hc
  have hP := GeneralPaperCataloguePointPrice.list_arithmetic_work n
  have hE := GeneralPaperCataloguePointPrice.list_arithmetic_work m
  unfold run arithmeticProfile
  dsimp only
  simp only [Bool.false_eq_true,ite_false,positions.size,extras.size]
  dsimp only [p,e,mapped,joined] at hMap ha hc
  nlinarith only [hP,hE,hMap,ha,hc]

end Blotto.GeneralPaperEpochPointPrice
