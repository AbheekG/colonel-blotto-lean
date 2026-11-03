import Blotto.GeneralPaperValueWeightSum

/-! Native independent coordinate rounding followed by one short integer
sum. The returned array/denominator are reused by the source and original
reconstruction. Data, positivity and approximation use the actual return. -/
namespace Blotto.GeneralPaperValueRoundingDriver
open GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

def run {n : ℕ} (bits : Bool) (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ) :
    (FixedArrayTable n ℕ × ℕ) × ℕ :=
  let rounded := GeneralPaperValueRoundArray.run bits model W M values
  let total := GeneralPaperValueWeightSum.scan bits model W rounded.1 n le_rfl
  ((rounded.1,total.1),rounded.2+total.2+128*address bits W n)

theorem array_data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (GeneralPaperValueRoundArray.run bits model W M values).1=FixedArrayTable.ofFn (GeneralPaperPositiveValueRounding.weight M v) := by
  rw [GeneralPaperValueRoundArray.data bits model W M values
    (fun j => by rw [hv]; exact (v.positive j).le) (fun j => by rw [hv]; exact GeneralPaperPositiveValueRounding.input_le_one v j)]
  congr 1
  funext j
  rw [hv]
  rfl

theorem data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run bits model W M values).1=(FixedArrayTable.ofFn (GeneralPaperPositiveValueRounding.weight M v),GeneralPaperPositiveValueRounding.total M v) := by
  unfold run
  dsimp only
  rw [GeneralPaperValueWeightSum.total,array_data bits model W M values v hv]
  simp only [FixedArrayTable.read_ofFn]
  rfl

theorem total_bounds {n : ℕ} (bits : Bool) (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    M≤(run bits model W M values).1.2 ∧ (run bits model W M values).1.2<M+n := by
  rw [data bits model W M values v hv]
  exact ⟨GeneralPaperPositiveValueRounding.total_lower M v,GeneralPaperPositiveValueRounding.total_upper M v⟩

theorem positive {n : ℕ} (bits : Bool) (model : RationalCostModel) (W M : ℕ) (hM : 0<M) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    0<(run bits model W M values).1.2 ∧ ∀ j,0<(run bits model W M values).1.1.read j := by
  rw [data bits model W M values v hv]
  exact ⟨GeneralPaperPositiveValueRounding.total_positive M hM v,
    fun j => by rw [FixedArrayTable.read_ofFn]; exact GeneralPaperPositiveValueRounding.positive_weight M hM v j⟩

theorem sum_weights {n : ℕ} (bits : Bool) (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ) :
    (∑ j,(run bits model W M values).1.1.read j)=(run bits model W M values).1.2 :=
  (GeneralPaperValueWeightSum.total bits model W _).symm

theorem normalized_data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W M : ℕ) (hM : 0<M) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (j : Fin n) :
    ((run bits model W M values).1.1.read j:ℚ)/(run bits model W M values).1.2=
      (GeneralPaperPositiveValueRounding.normalized M hM v).weight j := by
  rw [data bits model W M values v hv,FixedArrayTable.read_ofFn]
  rfl

theorem error {n : ℕ} (bits : Bool) (model : RationalCostModel) (W M : ℕ) (hM : 0<M) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (∑ j,|((run bits model W M values).1.1.read j:ℚ)/(run bits model W M values).1.2-v.weight j|)≤2*(n:ℚ)/M := by
  simp only [normalized_data bits model W M hM values v hv]
  exact GeneralPaperPositiveValueRounding.l1_error M hM v

theorem equal_entries {n : ℕ} (bits : Bool) (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (i j : Fin n) (hij : v.weight i=v.weight j) :
    (run bits model W M values).1.1.read i=(run bits model W M values).1.1.read j := by
  rw [data bits model W M values v hv,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
  exact GeneralPaperPositiveValueRounding.equal_weights M v i j hij

def bitProfile {n : ℕ} (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ) : ℕ :=
  GeneralPaperValueRoundArray.bitProfile model W M values+
    n*(2*model.rat (1+binaryWordWidth (M+n))+128*arrayWord W n)+192*arrayWord W n

theorem bit_work {n : ℕ} (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run true model W M values).2≤bitProfile model W M values := by
  have hArray := GeneralPaperValueRoundArray.bit_work model W M values
  have hQ : (GeneralPaperValueWeightSum.scan true model W
      (GeneralPaperValueRoundArray.run true model W M values).1 n le_rfl).1≤M+n := by
    rw [GeneralPaperValueWeightSum.total,array_data true model W M values v hv]
    simpa only [FixedArrayTable.read_ofFn,GeneralPaperPositiveValueRounding.total] using (GeneralPaperPositiveValueRounding.total_upper M v).le
  have hSum := GeneralPaperValueWeightSum.bit_work model W (M+n)
    (GeneralPaperValueRoundArray.run true model W M values).1 hQ n le_rfl
  unfold run bitProfile
  dsimp only
  simp only [address,ite_true]
  nlinarith only [hArray,hSum]

def arithmeticProfile (n M : ℕ) : ℕ := GeneralPaperValueRoundArray.arithmeticProfile n M+108*n+192

theorem arithmetic_work {n : ℕ} (model : RationalCostModel) (M : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run false model 1 M values).2≤arithmeticProfile n M := by
  have hArray := GeneralPaperValueRoundArray.arithmetic_work model M values
    (fun j => by rw [hv]; exact (v.positive j).le) (fun j => by rw [hv]; exact GeneralPaperPositiveValueRounding.input_le_one v j)
  have hSum := GeneralPaperValueWeightSum.arithmetic_work model (GeneralPaperValueRoundArray.run false model 1 M values).1 n le_rfl
  unfold run arithmeticProfile
  dsimp only
  simp only [address,Bool.false_eq_true,ite_false,Nat.mul_one]
  nlinarith only [hArray,hSum]

theorem models_data {n : ℕ} (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run true model W M values).1=(run false model 1 M values).1 :=
  (data true model W M values v hv).trans (data false model 1 M values v hv).symm

end Blotto.GeneralPaperValueRoundingDriver
