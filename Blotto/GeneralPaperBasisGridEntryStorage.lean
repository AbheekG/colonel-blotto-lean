import Blotto.GeneralPaperSourceInitializerTableStorageReachedRates

/-! Literal grid-packing coordinate/value entries. Original variables,
stored signed values and packed pairs coexist with all native coordinate
scratch, the value-copy primitive and callback/map partial-work fields.
Callback windows are retained conservatively across the complete map. -/
namespace Blotto.GeneralPaperBasisGridEntryStorage
open RationalOrderCell GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits)
open GeneralPaperBasisCoordinateStorage (packedTermFoot scalarWindow scalarProfile scalar_bound)
open GeneralPaperStaticVariableConstructionStorage (variableFoot variableProfile variable_bound)
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def packedProfile (W d R : ℕ) : ℕ := natBits (d+1)+R+32*W
theorem packed_bound {d : ℕ} (W R : ℕ) (t : Fin d×ℤ) (ht : integerBits t.2≤R) :
    packedTermFoot W t≤packedProfile W d R := by
  have h := Nat.add_le_add_left (binaryWordWidth_mono (show t.1.val≤d+1 by omega)) 1
  unfold packedTermFoot packedProfile natBits
  omega
def callback {m K : ℕ} (model : RationalCostModel) (W : ℕ) (value : Variable m K → ℤ) (v : Variable m K) :
    (Fin (m*(K-1))×ℤ)×ℕ :=
  let packed := GeneralPaperBasisCoordinateBits.scalar model.rat W v
  ((packed.1,value v),packed.2+model.rat (1+binaryWordWidth (value v).natAbs)+16*W)
def callbackPrice (model : RationalCostModel) (W d R : ℕ) : ℕ := 40*W+6*model.rat (1+binaryWordWidth (d+1))+model.rat R
def callbackCap (model : RationalCostModel) (W m K R : ℕ) : ℕ := m+K+m*(K-1)+1+3*callbackPrice model W (m*(K-1)) R+16*W
def callbackWindow {m K : ℕ} (model : RationalCostModel) (W : ℕ) (value : Variable m K → ℤ) (v : Variable m K) : ℕ :=
  let packed := GeneralPaperBasisCoordinateBits.scalar model.rat W v
  let copied := model.rat (1+binaryWordWidth (value v).natAbs)
  let result := callback model W value v
  variableFoot W v+integerBits (value v)+packedTermFoot W result.1+scalarWindow model W v+copied+
    fields W [packed.2,copied,packed.2+copied,result.2,16*W]+128*W
def callbackProfile (model : RationalCostModel) (W m K R : ℕ) : ℕ :=
  variableProfile W m K+R+packedProfile W (m*(K-1)) R+scalarProfile model W m K+model.rat R+
    5*(natBits (callbackCap model W m K R)+W)+160*W

theorem callback_work {m K : ℕ} (model : RationalCostModel) (W R : ℕ) (value : Variable m K → ℤ) (v : Variable m K)
    (hv : integerBits (value v)≤R) : (callback model W value v).2≤callbackPrice model W (m*(K-1)) R := by
  have hp := GeneralPaperBasisCoordinateBits.scalar_work model.rat model.monotone W v
  have hc := model.monotone hv
  change model.rat (1+binaryWordWidth (value v).natAbs)≤model.rat R at hc
  unfold callback callbackPrice
  dsimp only
  omega

theorem callback_bound {m K : ℕ} (model : RationalCostModel) (W R : ℕ) (value : Variable m K → ℤ) (v : Variable m K)
    (hv : integerBits (value v)≤R) : callbackWindow model W value v≤callbackProfile model W m K R := by
  let packed := GeneralPaperBasisCoordinateBits.scalar model.rat W v
  let copied := model.rat (1+binaryWordWidth (value v).natAbs)
  let result := callback model W value v
  have hV := variable_bound W v
  have hP := packed_bound W R result.1 hv
  have hS := scalar_bound model W v
  have hCopy : copied≤model.rat R := model.monotone hv
  have hWork := callback_work model W R value v hv
  change result.2≤callbackPrice model W (m*(K-1)) R at hWork
  have hShape : result.2=packed.2+copied+16*W := rfl
  have hf := fields_bound W (natBits (callbackCap model W m K R)) [packed.2,copied,packed.2+copied,result.2,16*W] (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold callbackCap
    rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W [packed.2,copied,packed.2+copied,result.2,16*W]≤5*(natBits (callbackCap model W m K R)+W)+32*W at hf
  unfold callbackWindow callbackProfile
  dsimp only
  dsimp only [packed,copied,result] at hP hCopy hf
  omega

def price (model : RationalCostModel) (W d R n : ℕ) : ℕ := n*(callbackPrice model W d R+8*W)+2*W
def metadataCap (model : RationalCostModel) (W m K R n : ℕ) : ℕ := m+K+m*(K-1)+n+1+3*price model W (m*(K-1)) R n+2*W
def window {m K : ℕ} (model : RationalCostModel) (W : ℕ) (value : Variable m K → ℤ) (vars : List (Variable m K)) : ℕ :=
  let result := GeneralPaperPricedListMap.run W (callback model W value) vars
  listFootprint W (variableFoot W) vars+
    GeneralPaperPricedPayloadStreamStorage.mapWindow W (packedTermFoot W) (callback model W value) (fun _ => 0) none vars+
    (vars.map (callbackWindow model W value)).sum+fields W [m,K,m*(K-1),vars.length,result.2,2*W]+192*W
def profile (model : RationalCostModel) (W m K R n : ℕ) : ℕ :=
  n*(variableProfile W m K+2*W)+32*W+
    GeneralPaperPricedPayloadStreamStorage.filterProfile W (packedProfile W (m*(K-1)) R) (callbackPrice model W (m*(K-1)) R) n 0+
    n*callbackProfile model W m K R+6*(natBits (metadataCap model W m K R n)+W)+224*W

theorem bounded {m K : ℕ} (model : RationalCostModel) (W R n : ℕ) (value : Variable m K → ℤ) (vars : List (Variable m K))
    (hn : vars.length≤n) (hv : ∀ v∈vars,integerBits (value v)≤R) : window model W value vars≤profile model W m K R n := by
  have hList := (list_bound W (variableProfile W m K) (variableFoot W) vars (fun v _ => variable_bound W v)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  have hMap := GeneralPaperPricedPayloadStreamStorage.map_bounded W (packedProfile W (m*(K-1)) R) (callbackPrice model W (m*(K-1)) R) n 0
    (packedTermFoot W) (callback model W value) (fun _ => 0) none vars hn
    (fun v hv' => callback_work model W R value v (hv v hv'))
    (fun v hv' => packed_bound W R _ (hv v hv')) (fun _ _ => le_rfl) (by intro a ha; cases ha)
  have hCallbacks := (sum_bound (callbackWindow model W value) (callbackProfile model W m K R) vars (fun v hv' => callback_bound model W R value v (hv v hv'))).trans
    (Nat.mul_le_mul_right _ hn)
  have hWork : (GeneralPaperPricedListMap.run W (callback model W value) vars).2≤price model W (m*(K-1)) R n := by
    apply (GeneralPaperPricedListMap.work W (callbackPrice model W (m*(K-1)) R) (callback model W value) vars
      (fun v hv' => callback_work model W R value v (hv v hv'))).trans
    unfold price
    simpa only [Nat.mul_comm] using Nat.add_le_add_right (Nat.mul_le_mul_left (callbackPrice model W (m*(K-1)) R+8*W) hn) (2*W)
  have hf := fields_bound W (natBits (metadataCap model W m K R n)) [m,K,m*(K-1),vars.length,(GeneralPaperPricedListMap.run W (callback model W value) vars).2,2*W] (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold metadataCap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤6*(natBits (metadataCap model W m K R n)+W)+32*W at hf
  unfold window profile
  dsimp only
  omega

end Blotto.GeneralPaperBasisGridEntryStorage
