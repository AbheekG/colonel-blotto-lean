import Blotto.GeneralPaperBasisGridPackingPrice

/-! Complete rounded-dictionary and original-grid construction on supplied
initializer controls. One stored rounding table feeds both readers and the
grid. Its data equal the original native dictionary/grid, while arithmetic
and bit prices include all array levels, forward packing and references.
Construction of N/depth/beta and the auxiliary numerator is a separate phase.
-/
namespace Blotto.GeneralPaperInitializerGridPrice
open RationalOrderCell GeneralPaperBasisStoredProducts GeneralPaperTransferPolytopePoint
set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxRecDepth 4096

def values {m K : ℕ} (stored : GeneralPaperInitializerStoredBits.Table m K) : Variable m K → ℤ :=
  fun v => (((stored.read v.1).read (positiveLabel v.2)).1:ℤ)

def nativePoint {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (N depth : ℕ) : Variable m K → ℚ :=
  fun v => (GeneralPaperInitializerDictionary.build dict N depth).anchor v.1 (positiveLabel v.2)

def run {T m K : ℕ} (model : RationalCostModel) (W N depth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K) :
    (GeneralPaperDictionary.Dictionary T m K × Vector (m*(K-1))) × ℕ :=
  let stored := GeneralPaperInitializerStoredBits.run model W N depth dict.anchor
  let packed := GeneralPaperBasisGridPackingPrice.run (fun w => w) model.rat W (values stored.1)
  ((GeneralPaperInitializerStoredBits.dictionary dict stored.1,packed.1),stored.2+packed.2+16*W)

def unit {T m K : ℕ} (N depth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K) :
    (GeneralPaperDictionary.Dictionary T m K × Vector (m*(K-1))) × ℕ :=
  let stored := GeneralPaperInitializerStoredBits.unit N depth dict.anchor
  let packed := GeneralPaperBasisGridPackingPrice.run (fun _ => 1) (fun _ => 1) 1 (values stored.1)
  ((GeneralPaperInitializerStoredBits.dictionary dict stored.1,packed.1),stored.2+packed.2+16)

theorem data_unit {T m K : ℕ} (model : RationalCostModel) (W N depth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K) :
    (run model W N depth dict).1=(unit N depth dict).1 := by
  simp only [run,unit,GeneralPaperInitializerStoredBits.data,GeneralPaperBasisGridPackingPrice.data]

theorem values_data {T m K : ℕ} (model : RationalCostModel) (W N depth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K)
    (hN : 0<N) :
    values (GeneralPaperInitializerStoredBits.run model W N depth dict.anchor).1=
      (fun v => latticeNumerator N (nativePoint dict N depth v)) := by
  funext v
  unfold values nativePoint
  rw [GeneralPaperInitializerDictionary.field]
  have hh := GeneralPaperInitializerRoundingBits.numerator_data model W N depth hN (dict.anchor v.1 (positiveLabel v.2))
  rw [GeneralPaperInitializerStoredBits.read_data]
  rw [GeneralPaperInitializerRoundingBits.data] at hh
  exact hh

theorem data {T m K : ℕ} (model : RationalCostModel) (W N depth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K)
    (hN : 0<N) :
    (run model W N depth dict).1=(GeneralPaperInitializerDictionary.build dict N depth,
      GeneralPaperBasisGridInputs.grid N (nativePoint dict N depth)) := by
  simp only [run,GeneralPaperInitializerStoredBits.dictionary_data,GeneralPaperBasisGridPackingPrice.data,
    values_data model W N depth dict hN,GeneralPaperBasisGridInputs.grid]

theorem values_bound {T m K : ℕ} (model : RationalCostModel) (W N depth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K)
    (hN : 0<N) (hCap : N<2^depth) (hUnit : ∀ j l,0≤dict.anchor j l ∧ dict.anchor j l≤1) :
    ∀ v,(values (GeneralPaperInitializerStoredBits.run model W N depth dict.anchor).1 v).natAbs≤N := by
  intro v
  unfold values
  rw [GeneralPaperInitializerStoredBits.read_data,Int.natAbs_natCast]
  exact GeneralPaperInitializerRoundingBits.quotient_le N depth hN hCap _ (hUnit _ _)

def profile (model : RationalCostModel) (W N depth A m K : ℕ) : ℕ :=
  GeneralPaperInitializerStoredBits.profile model W N depth A m K+
    GeneralPaperBasisGridPackingPrice.profile m K W (model.rat (1+binaryWordWidth (m*(K-1)+1))) (model.rat (1+binaryWordWidth N))+16*W

theorem work {T m K : ℕ} (model : RationalCostModel) (W N depth A : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K)
    (hN : 0<N) (hCap : N<2^depth) (hUnit : ∀ j l,0≤dict.anchor j l ∧ dict.anchor j l≤1)
    (hHeight : ∀ j l,RationalHeight (dict.anchor j l) A) (hW : 1≤W)
    (hK : binaryWordWidth (K+1)≤W) (hm : binaryWordWidth (m+1)≤W) (hD : binaryWordWidth (m*(K-1)+1)≤W) :
    (run model W N depth dict).2≤profile model W N depth A m K := by
  have hs := GeneralPaperInitializerStoredBits.work model W N depth A hN hCap dict.anchor hUnit hHeight hW hK hm
  have hg := GeneralPaperBasisGridPackingPrice.work model.rat model.monotone W N
    (values (GeneralPaperInitializerStoredBits.run model W N depth dict.anchor).1)
    (values_bound model W N depth dict hN hCap hUnit) hW hD
  change (GeneralPaperInitializerStoredBits.run model W N depth dict.anchor).2+_+16*W≤_
  unfold profile
  omega

theorem unit_work {T m K : ℕ} (N depth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K) :
    (unit N depth dict).2≤128*(m+1)*(K+1)*(depth+1)+1024*(m*(K-1)+m+1)+16 := by
  have hs := GeneralPaperInitializerStoredBits.unit_work N depth dict.anchor
  have hg := GeneralPaperBasisGridPackingPrice.unit_work (values (GeneralPaperInitializerStoredBits.unit N depth dict.anchor).1)
  change (GeneralPaperInitializerStoredBits.unit N depth dict.anchor).2+_+16≤_
  omega

def width (A N depth m K : ℕ) : ℕ := GeneralPaperInitializerRoundingBits.width A N depth+1+binaryWordWidth (m*(K-1)+1)

theorem profile_bound (model : RationalCostModel) (W N depth A m K : ℕ) :
    profile model W N depth A m K≤8192*(m+1)*(K+1)*(depth+1)*(W+model.rat (width A N depth m K)) := by
  let L := width A N depth m K
  let P := model.rat L
  have hR := model.monotone (show GeneralPaperInitializerRoundingBits.width A N depth≤L by dsimp only [L,width]; omega)
  have hC := model.monotone (show 1+binaryWordWidth (m*(K-1)+1)≤L by dsimp only [L,width]; omega)
  have hN := model.monotone (show 1+binaryWordWidth N≤L by dsimp only [L,width,GeneralPaperInitializerRoundingBits.width]; omega)
  have hS : GeneralPaperInitializerStoredBits.profile model W N depth A m K≤
      256*m*K*(depth+1)*(W+P)+88*(m+1)*(K+1)*W := by
    unfold GeneralPaperInitializerStoredBits.profile
    exact Nat.add_le_add_right (Nat.mul_le_mul_left (256*m*K*(depth+1)) (Nat.add_le_add_left hR W)) _
  have hG : GeneralPaperBasisGridPackingPrice.profile m K W (model.rat (1+binaryWordWidth (m*(K-1)+1)))
      (model.rat (1+binaryWordWidth N))≤6144*(m*(K-1)+m+1)*(W+P) := by
    unfold GeneralPaperBasisGridPackingPrice.profile
    have hh := Nat.mul_le_mul_left (2048*(m*(K-1)+m+1)) (show W+model.rat (1+binaryWordWidth (m*(K-1)+1))+
      model.rat (1+binaryWordWidth N)≤3*(W+P) by dsimp only [P] at *; omega)
    exact hh.trans_eq (by ring)
  have hd : m*(K-1)≤m*K := Nat.mul_le_mul_left m (Nat.sub_le K 1)
  have hc : m*(K-1)+m+1≤(m+1)*(K+1) := by nlinarith only [hd]
  have hg := Nat.mul_le_mul_right (W+P) (Nat.mul_le_mul_left 6144 hc)
  have hmK : m*K≤(m+1)*(K+1) := by nlinarith
  let C := (m+1)*(K+1)
  let F := (depth+1)*(W+P)
  have hF : W+P≤F := by dsimp only [F]; nlinarith only [Nat.zero_le (depth*W),Nat.zero_le (depth*P)]
  have hFW : W≤F := (Nat.le_add_right W P).trans hF
  have hCOne : 1≤C := Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos K)
  have hCF := Nat.mul_le_mul_right F hCOne
  have hSmall : W≤C*F := hFW.trans (by simpa only [one_mul] using hCF)
  have hm := Nat.mul_le_mul_right F (Nat.mul_le_mul_left 256 hmK)
  change 256*(m*K)*F≤256*C*F at hm
  have hsW := Nat.mul_le_mul_left (88*C) hFW
  have hStored : GeneralPaperInitializerStoredBits.profile model W N depth A m K≤256*(m*K)*F+88*C*W :=
    hS.trans_eq (by dsimp only [C,F]; ring)
  have hs' : GeneralPaperInitializerStoredBits.profile model W N depth A m K≤344*C*F := by
    nlinarith only [hStored,hm,hsW]
  have hgF := Nat.mul_le_mul_left (6144*C) hF
  have hg' : GeneralPaperBasisGridPackingPrice.profile m K W (model.rat (1+binaryWordWidth (m*(K-1)+1)))
      (model.rat (1+binaryWordWidth N))≤6144*C*F := by
    change _≤6144*C*(W+P) at hg
    exact (hG.trans hg).trans hgF
  have hExtra := Nat.mul_le_mul_left 16 hSmall
  calc
    _ ≤ 8192*C*F := by unfold profile; nlinarith only [hs',hg',hExtra,Nat.zero_le (C*F)]
    _ = _ := by dsimp only [C,F,P,L]; ring

end Blotto.GeneralPaperInitializerGridPrice
