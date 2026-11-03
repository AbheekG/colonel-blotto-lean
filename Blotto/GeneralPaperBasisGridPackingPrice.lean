import Blotto.GeneralPaperInitializerStoredBits

/-! Pack stored integer grid coordinates with the native forward index.
The variable list, coordinate arithmetic, sign conversion/copy, zero array,
selected writes and all control/reference operations are priced. No inverse
coordinate division or dense scan is executed for each assignment.
-/
namespace Blotto.GeneralPaperBasisGridPackingPrice
open RationalOrderCell GeneralPaperBasisStoredProducts GeneralPaperBasisCoordinates
set_option autoImplicit false
set_option maxHeartbeats 8000000

def writes {d : ℕ} (W : ℕ) : List (Fin d × ℤ) → Vector d → Vector d × ℕ
  | [],values => (values,2*W)
  | term::rest,values =>
      let returned := writes W rest (values.write term.1 term.2)
      (returned.1,returned.2+24*W)

theorem writes_data {d : ℕ} (W : ℕ) (terms : List (Fin d × ℤ)) (values : Vector d) :
    (writes W terms values).1=values.patch terms := by
  induction terms generalizing values with
  | nil => rfl
  | cons t rest ih => exact ih _

theorem writes_work {d : ℕ} (W : ℕ) (terms : List (Fin d × ℤ)) (values : Vector d) :
    (writes W terms values).2=24*terms.length*W+2*W := by
  induction terms generalizing values with
  | nil => simp only [writes,List.length_nil,Nat.mul_zero,Nat.zero_mul,Nat.zero_add]
  | cons t rest ih =>
    simp only [writes,ih,List.length_cons]
    ring

def zero (indexPrimitive : ℕ → ℕ) (W d : ℕ) : Vector d × ℕ :=
  PaperIndexedArrayConstruction.run indexPrimitive W (fun _ => (0,2*W))

def run {m K : ℕ} (indexPrimitive primitive : ℕ → ℕ) (W : ℕ) (value : Variable m K → ℤ) : Vector (m*(K-1)) × ℕ :=
  let initial := zero indexPrimitive W (m*(K-1))
  let vars := GeneralPaperStaticEnumerationPrice.variableRun W m K
  let entries := GeneralPaperPricedListMap.run W (fun v =>
    let packed := GeneralPaperBasisCoordinateBits.scalar primitive W v
    ((packed.1,value v),packed.2+primitive (1+binaryWordWidth (value v).natAbs)+16*W)) vars.1
  let result := writes W entries.1 initial.1
  (result.1,initial.2+vars.2+entries.2+result.2+16*W)

theorem data {m K : ℕ} (indexPrimitive primitive : ℕ → ℕ) (W : ℕ) (value : Variable m K → ℤ) :
    (run indexPrimitive primitive W value).1=GeneralPaperBasisGridInputs.pack value := by
  simp only [run,writes_data,zero,PaperIndexedArrayConstruction.run_data,GeneralPaperStaticEnumerationPrice.variable_data,
    GeneralPaperPricedListMap.data,GeneralPaperBasisCoordinateBits.scalar,GeneralPaperBasisGridInputs.pack]

def profile (m K W PC PB : ℕ) : ℕ := 2048*(m*(K-1)+m+1)*(W+PC+PB)

theorem work {m K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W B : ℕ)
    (value : Variable m K → ℤ) (hValues : ∀ v,(value v).natAbs≤B)
    (hW : 1≤W) (hD : binaryWordWidth (m*(K-1)+1)≤W) :
    (run (fun w => w) primitive W value).2≤profile m K W
      (primitive (1+binaryWordWidth (m*(K-1)+1))) (primitive (1+binaryWordWidth B)) := by
  let d := m*(K-1)
  let PC := primitive (1+binaryWordWidth (d+1))
  let PB := primitive (1+binaryWordWidth B)
  have hz := GeneralPaperBasisScatterBits.zero_work W d hW hD
  have hv := GeneralPaperStaticEnumerationPrice.variable_work W m K
  have hn : (GeneralPaperStaticEnumerationPrice.variableRun W m K).1.length=d := by
    rw [GeneralPaperStaticEnumerationPrice.variable_data,GeneralPaperStaticRayRows.variableList_length]
  have hc (v : Variable m K) :
      (GeneralPaperBasisCoordinateBits.scalar primitive W v).2+primitive (1+binaryWordWidth (value v).natAbs)+16*W≤40*W+6*PC+PB := by
    have hi := GeneralPaperBasisCoordinateBits.scalar_work primitive hMono W v
    have hp := hMono (Nat.add_le_add_left (binaryWordWidth_mono (hValues v)) 1)
    change (GeneralPaperBasisCoordinateBits.scalar primitive W v).2≤24*W+6*PC at hi
    dsimp only [PB]
    omega
  have hm := GeneralPaperPricedListMap.work W (40*W+6*PC+PB) (fun v =>
    let packed := GeneralPaperBasisCoordinateBits.scalar primitive W v
    ((packed.1,value v),packed.2+primitive (1+binaryWordWidth (value v).natAbs)+16*W))
    (GeneralPaperStaticEnumerationPrice.variableRun W m K).1 (fun v _ => hc v)
  rw [hn] at hm
  have hl : (GeneralPaperPricedListMap.run W (fun v =>
    let packed := GeneralPaperBasisCoordinateBits.scalar primitive W v
    ((packed.1,value v),packed.2+primitive (1+binaryWordWidth (value v).natAbs)+16*W))
      (GeneralPaperStaticEnumerationPrice.variableRun W m K).1).1.length=d := by
    rw [GeneralPaperPricedListMap.length,hn]
  dsimp only [run]
  rw [writes_work,hl]
  change (GeneralPaperBasisScatterBits.zeroRun W d).2+_+_+(24*d*W+2*W)+16*W≤_
  change _≤2048*(d+m+1)*(W+PC+PB)
  change (GeneralPaperStaticEnumerationPrice.variableRun W m K).2≤128*(d+m+1)*W at hv
  nlinarith only [hz,hv,hm,Nat.zero_le (d*W),Nat.zero_le (m*W),Nat.zero_le (d*PC),Nat.zero_le (m*PC),Nat.zero_le (d*PB),Nat.zero_le (m*PB)]

theorem unit_work {m K : ℕ} (value : Variable m K → ℤ) :
    (run (fun _ => 1) (fun _ => 1) 1 value).2≤1024*(m*(K-1)+m+1) := by
  let d := m*(K-1)
  have hz := PaperIndexedArrayConstruction.run_work (fun _ => 1) 1 (fun _ : Fin d => ((0:ℤ),2))
  have ho := GeneralPaperUnitArrayOverhead.overhead 1 d d
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hz
  have hz' : (zero (fun _ => 1) 1 d).2≤64*(d+1) := by
    change (zero (fun _ => 1) 1 d).2=_ at hz
    nlinarith only [hz,ho]
  have hv := GeneralPaperStaticEnumerationPrice.variable_work 1 m K
  have hn : (GeneralPaperStaticEnumerationPrice.variableRun 1 m K).1.length=d := by
    rw [GeneralPaperStaticEnumerationPrice.variable_data,GeneralPaperStaticRayRows.variableList_length]
  have hm := GeneralPaperPricedListMap.work 1 47 (fun v =>
    let packed := GeneralPaperBasisCoordinateBits.scalar (fun _ => 1) 1 v
    ((packed.1,value v),packed.2+1+16)) (GeneralPaperStaticEnumerationPrice.variableRun 1 m K).1
    (by intro v _; norm_num [GeneralPaperBasisCoordinateBits.scalar,GeneralPaperNaturalPrimitivePrice.binary])
  rw [hn] at hm
  dsimp only [run]
  rw [writes_work,GeneralPaperPricedListMap.length,hn]
  change (zero (fun _ => 1) 1 d).2+_+_+(24*d*1+2*1)+16*1≤_
  change _≤1024*(d+m+1)
  change (GeneralPaperStaticEnumerationPrice.variableRun 1 m K).2≤128*(d+m+1)*1 at hv
  nlinarith only [hz',hv,hm]

end Blotto.GeneralPaperBasisGridPackingPrice
