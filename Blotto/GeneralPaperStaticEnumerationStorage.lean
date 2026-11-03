import Blotto.GeneralPaperStaticFamilyConstructionStorage

/-! Complete actual native static index enumeration construction. Both
variable traversals, all family maps/flatMaps, finite ranges, two literal
list appends/copy prefixes and enclosing native return fields are reserved.
This is only the index constructor; sparse-row constructors are separate. -/
namespace Blotto.GeneralPaperStaticEnumerationStorage
open RationalOrderCell GeneralPaperStaticRayRows GeneralPaperEncodedScalarStorage
open GeneralPaperNativeStaticScanStorage GeneralPaperStaticFamilyConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def callerCap (W T m K : ℕ) : ℕ := T+m+K+count T m K+1+3*enumerationPrice W T m K

def caller (W T m K : ℕ) : ℕ :=
  let b := GeneralPaperStaticEnumerationPrice.boxesRun W T m K
  let o := GeneralPaperStaticEnumerationPrice.ordersRun W T m K
  let r := GeneralPaperStaticEnumerationPrice.budgetsRun W T m K
  let result := GeneralPaperStaticEnumerationPrice.run W T m K
  let append := (16*b.1.length+8*o.1.length+16)*W
  fields W [T,m,K,b.1.length,o.1.length,r.1.length,b.2,o.2,r.2,result.2,append,b.2+o.2,b.2+o.2+r.2]+256*W

def callerProfile (W T m K : ℕ) : ℕ := 13*(natBits (callerCap W T m K)+W)+288*W

theorem caller_bound (W T m K : ℕ) : caller W T m K≤callerProfile W T m K := by
  let b := GeneralPaperStaticEnumerationPrice.boxesRun W T m K
  let o := GeneralPaperStaticEnumerationPrice.ordersRun W T m K
  let r := GeneralPaperStaticEnumerationPrice.budgetsRun W T m K
  let result := GeneralPaperStaticEnumerationPrice.run W T m K
  let append := (16*b.1.length+8*o.1.length+16)*W
  have hWork := GeneralPaperStaticEnumerationPrice.work W T m K
  change result.2≤enumerationPrice W T m K at hWork
  have hShape : result.2=b.2+o.2+r.2+append := rfl
  have hB : b.1.length=2*(m*(K-1)) := GeneralPaperStaticEnumerationPrice.boxes_length W T m K
  have hO : o.1.length=m*(K-1) := GeneralPaperStaticEnumerationPrice.orders_length W T m K
  have hR : r.1.length=T := by dsimp only [r]; rw [GeneralPaperStaticEnumerationPrice.budgets_data]; simp only [budgets,List.length_map,List.length_finRange]
  have hf := fields_bound W (natBits (callerCap W T m K))
    [T,m,K,b.1.length,o.1.length,r.1.length,b.2,o.2,r.2,result.2,append,b.2+o.2,b.2+o.2+r.2] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold callerCap count; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤13*(natBits (callerCap W T m K)+W)+32*W at hf
  change GeneralPaperEncodedScalarStorage.fields W [T,m,K,b.1.length,o.1.length,r.1.length,b.2,o.2,r.2,result.2,append,b.2+o.2,b.2+o.2+r.2]+256*W≤_
  unfold callerProfile
  omega

def window (W T m K copied : ℕ) (activeField : Option (Fin m)) (activeLabel : Option (Fin (K-1)))
    (activeVariable : Option (Variable m K)) (activeBudget : Option (Fin T)) : ℕ :=
  let b := (GeneralPaperStaticEnumerationPrice.boxesRun W T m K).1
  let o := (GeneralPaperStaticEnumerationPrice.ordersRun W T m K).1
  let r := (GeneralPaperStaticEnumerationPrice.budgetsRun W T m K).1
  boxesWindow W T m K copied activeField activeLabel activeVariable+
    ordersWindow W T m K copied activeField activeLabel activeVariable+budgetsWindow W T m K copied activeBudget+
    GeneralPaperPayloadAppendStorage.window W copied (indexFoot W) b o+
    GeneralPaperPayloadAppendStorage.window W copied (indexFoot W) (b++o) r+caller W T m K

def profile (W T m K : ℕ) : ℕ := boxesProfile W T m K+ordersProfile W T m K+budgetsProfile W T m K+
  2*GeneralPaperPayloadAppendStorage.profile W (indexProfile W T m K) (count T m K)+callerProfile W T m K

theorem bounded (W T m K copied : ℕ) (activeField : Option (Fin m)) (activeLabel : Option (Fin (K-1)))
    (activeVariable : Option (Variable m K)) (activeBudget : Option (Fin T)) :
    window W T m K copied activeField activeLabel activeVariable activeBudget≤profile W T m K := by
  let b := (GeneralPaperStaticEnumerationPrice.boxesRun W T m K).1
  let o := (GeneralPaperStaticEnumerationPrice.ordersRun W T m K).1
  let r := (GeneralPaperStaticEnumerationPrice.budgetsRun W T m K).1
  have hB := boxes_bound W T m K copied activeField activeLabel activeVariable
  have hO := orders_bound W T m K copied activeField activeLabel activeVariable
  have hR := budgets_bound W T m K copied activeBudget
  have hC := caller_bound W T m K
  have hBLen : b.length=2*(m*(K-1)) := GeneralPaperStaticEnumerationPrice.boxes_length W T m K
  have hOLen : o.length=m*(K-1) := GeneralPaperStaticEnumerationPrice.orders_length W T m K
  have hRLen : r.length=T := by dsimp only [r]; rw [GeneralPaperStaticEnumerationPrice.budgets_data]; simp only [budgets,List.length_map,List.length_finRange]
  have hFirst := GeneralPaperPayloadAppendStorage.bounded W (indexProfile W T m K) (count T m K) copied (indexFoot W) b o
    (by unfold count; omega) (fun i _ => index_bound W i) (fun i _ => index_bound W i)
  have hSecond := GeneralPaperPayloadAppendStorage.bounded W (indexProfile W T m K) (count T m K) copied (indexFoot W) (b++o) r
    (by rw [List.length_append]; unfold count; omega) (fun i _ => index_bound W i) (fun i _ => index_bound W i)
  unfold window profile
  dsimp only
  dsimp only [b,o,r] at hFirst hSecond
  omega

end Blotto.GeneralPaperStaticEnumerationStorage
