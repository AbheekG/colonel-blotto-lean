import Blotto.GeneralPaperInitializerRoundingBits

/-! Store each native rounded anchor and its computed quotient together,
once, in the two-level field/label array. Rational and original lattice
readers are projections of this shared table. Both indexed constructors
have explicit index/reference prices; unit arithmetic is also included.
-/
namespace Blotto.GeneralPaperInitializerStoredBits
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 7000000

abbrev Table (m K : ℕ) := FixedArrayTable m (FixedArrayTable K (ℕ × ℚ))

def field {K : ℕ} (indexPrimitive : ℕ → ℕ) (W : ℕ) (evaluate : Fin K → (ℕ × ℚ) × ℕ) : FixedArrayTable K (ℕ × ℚ) × ℕ :=
  PaperIndexedArrayConstruction.run indexPrimitive W evaluate

def build {m K : ℕ} (indexPrimitive : ℕ → ℕ) (W : ℕ) (evaluate : Fin m → Fin K → (ℕ × ℚ) × ℕ) : Table m K × ℕ :=
  PaperIndexedArrayConstruction.run indexPrimitive W (fun j => field indexPrimitive W (evaluate j))

theorem build_data {m K : ℕ} (indexPrimitive : ℕ → ℕ) (W : ℕ) (evaluate : Fin m → Fin K → (ℕ × ℚ) × ℕ) :
    (build indexPrimitive W evaluate).1=FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn (fun l => (evaluate j l).1)) := by
  simp only [build,field,PaperIndexedArrayConstruction.run_data]

theorem build_work {m K : ℕ} (W C : ℕ) (evaluate : Fin m → Fin K → (ℕ × ℚ) × ℕ)
    (h : ∀ j l,(evaluate j l).2≤C) (hW : 1≤W)
    (hK : binaryWordWidth (K+1)≤W) (hm : binaryWordWidth (m+1)≤W) :
    (build (fun w => w) W evaluate).2≤m*K*C+88*(m+1)*(K+1)*W := by
  have hField (j : Fin m) : (field (fun w => w) W (evaluate j)).2≤K*C+44*(K+1)*W := by
    have hs := Finset.sum_le_sum (fun l (_ : l∈Finset.univ) => h j l)
    simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
    have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W (evaluate j)
    change (field (fun w => w) W (evaluate j)).2≤_ at hh
    exact hh.trans (Nat.add_le_add hs (GeneralPaperScoreMatrixBits.array_overhead K W hW hK))
  have hs := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hField j)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fun j => field (fun w => w) W (evaluate j))
  change (build (fun w => w) W evaluate).2≤_ at hh
  have ho := GeneralPaperScoreMatrixBits.array_overhead m W hW hm
  nlinarith only [hh,hs,ho,Nat.zero_le (K*W)]

def run {m K : ℕ} (model : RationalCostModel) (W N depth : ℕ) (input : Fin m → Fin K → ℚ) : Table m K × ℕ :=
  build (fun w => w) W (fun j l => GeneralPaperInitializerRoundingBits.run model W N depth (input j l))

def unit {m K : ℕ} (N depth : ℕ) (input : Fin m → Fin K → ℚ) : Table m K × ℕ :=
  build (fun _ => 1) 1 (fun j l => GeneralPaperInitializerRoundingBits.unit N depth (input j l))

theorem data {m K : ℕ} (model : RationalCostModel) (W N depth : ℕ) (input : Fin m → Fin K → ℚ) :
    (run model W N depth input).1=(unit N depth input).1 := by
  simp only [run,unit,build_data,GeneralPaperInitializerRoundingBits.data]

theorem read_data {m K : ℕ} (model : RationalCostModel) (W N depth : ℕ) (input : Fin m → Fin K → ℚ) (j : Fin m) (l : Fin K) :
    (((run model W N depth input).1.read j).read l)=
      (GeneralPaperInitializerRoundingBits.unit N depth (input j l)).1 := by
  simp only [data,unit,build_data,FixedArrayTable.read_ofFn]

def dictionary {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (stored : Table m K) : GeneralPaperDictionary.Dictionary T m K :=
  GeneralPaperStrictScore.replace dict (fun j l => ((stored.read j).read l).2)

theorem dictionary_data {T m K : ℕ} (model : RationalCostModel) (W N depth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m K) :
    dictionary dict (run model W N depth dict.anchor).1=GeneralPaperInitializerDictionary.build dict N depth := by
  unfold dictionary GeneralPaperInitializerDictionary.build
  congr 1
  funext j l
  rw [read_data,GeneralPaperInitializerArray.read]
  rfl

def profile (model : RationalCostModel) (W N depth A m K : ℕ) : ℕ :=
  256*m*K*(depth+1)*(W+model.rat (GeneralPaperInitializerRoundingBits.width A N depth))+88*(m+1)*(K+1)*W

theorem work {m K : ℕ} (model : RationalCostModel) (W N depth A : ℕ) (hN : 0<N) (hCap : N<2^depth)
    (input : Fin m → Fin K → ℚ) (hUnit : ∀ j l,0 ≤ input j l ∧ input j l≤1) (hHeight : ∀ j l,RationalHeight (input j l) A)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hm : binaryWordWidth (m+1)≤W) :
    (run model W N depth input).2≤profile model W N depth A m K := by
  have hh := build_work W (256*(depth+1)*(W+model.rat (GeneralPaperInitializerRoundingBits.width A N depth)))
    (fun j l => GeneralPaperInitializerRoundingBits.run model W N depth (input j l))
    (fun j l => GeneralPaperInitializerRoundingBits.work model W N depth A hN hCap (input j l) (hUnit j l) (hHeight j l)) hW hK hm
  change (run model W N depth input).2≤_ at hh
  exact hh.trans_eq (by unfold profile; ring)

theorem unit_work {m K : ℕ} (N depth : ℕ) (input : Fin m → Fin K → ℚ) :
    (unit N depth input).2≤128*(m+1)*(K+1)*(depth+1) := by
  have hField (j : Fin m) :
      (field (fun _ => 1) 1 (fun l => GeneralPaperInitializerRoundingBits.unit N depth (input j l))).2≤
        K*(12*depth+34)+42*(K+1) := by
    have hh := PaperIndexedArrayConstruction.run_work (fun _ => 1) 1 (fun l => GeneralPaperInitializerRoundingBits.unit N depth (input j l))
    have ho := GeneralPaperUnitArrayOverhead.overhead 1 K K
    simp only [GeneralPaperInitializerRoundingBits.unit_work,Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hh
    change (field (fun _ => 1) 1 (fun l => GeneralPaperInitializerRoundingBits.unit N depth (input j l))).2=_ at hh
    omega
  have hs := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hField j)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have hh := PaperIndexedArrayConstruction.run_work (fun _ => 1) 1
    (fun j => field (fun _ => 1) 1 (fun l => GeneralPaperInitializerRoundingBits.unit N depth (input j l)))
  have ho := GeneralPaperUnitArrayOverhead.overhead 1 m m
  change (unit N depth input).2=_ at hh
  nlinarith only [hs,hh,ho,Nat.zero_le (m*K*depth),Nat.zero_le (K*depth),Nat.zero_le (m*depth)]

end Blotto.GeneralPaperInitializerStoredBits
