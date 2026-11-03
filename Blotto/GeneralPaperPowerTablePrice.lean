import Blotto.GeneralPaperPowerTableBounds

/-! Full shared power-table bit implementation. Each noninitial column
calls the fast constructed-mantissa multiplier once. The returned result
supplies both number and metadata; old prefixes are shared by list cons.
All degree arithmetic, guards, metadata sums and result writes are priced.
-/
namespace Blotto.GeneralPaperPowerTablePrice
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable GeneralPaperPowerTableBounds
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def run (primitive : ℕ → ℕ) (W unit p : ℕ) (base : Number) : ℕ → Table × ℕ
  | 0 => (⟨[],⟨1,base⟩,2⟩,16*W)
  | columns+1 =>
    let earlier := run primitive W unit p base columns
    let test := GeneralPaperIntegerWordPrice.compare primitive columns 0
    if columns=0 then
      (⟨⟨1,base⟩::earlier.1.entries,⟨1,base⟩,earlier.1.work+8⟩,
        earlier.2+test+metadataCost primitive earlier.1.work 0 8+32*W)
    else
      let product := GeneralPaperDyadicMultiplyPrice.run primitive W unit p earlier.1.top.number earlier.1.top.number
      let next : Entry := ⟨2*earlier.1.top.degree,product.1.number⟩
      (⟨next::earlier.1.entries,next,earlier.1.work+product.1.work+16⟩,
        earlier.2+product.2+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 earlier.1.top.degree+
          test+metadataCost primitive earlier.1.work product.1.work 16+96*W)

theorem data (primitive : ℕ → ℕ) (W unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (base : Number) (hNormal : Normal unit base) (hPositive : 0<base.mantissa) (columns : ℕ) :
    (run primitive W unit p base columns).1=build unit p base columns := by
  induction columns with
  | zero => rfl
  | succ columns ih =>
    have hn := (build_good unit p hUnit hPower base hNormal hPositive columns).1.2.1
    rw [run,build]
    dsimp only
    rw [ih]
    by_cases hz : columns=0
    · simp only [ite_eq_left hz]
    · simp only [ite_eq_right hz]
      rw [GeneralPaperDyadicMultiplyPrice.data primitive W unit p (by omega) hPower _ _ hn hn]
      simp only [square,Nat.add_assoc]

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W unit p : ℕ) (hUnit : 1<unit)
    (hPower : unit=2^p) (base : Number) (hNormal : Normal unit base) (hPositive : 0<base.mantissa) (columns : ℕ) :
    (run primitive W unit p base columns).2≤1024*(columns+1)*(W+primitive (width p columns base)) := by
  induction columns with
  | zero => change 16*W≤1024*(0+1)*(W+primitive (width p 0 base)); omega
  | succ columns ih =>
    let old := build unit p base columns
    let L := width p (columns+1) base
    let P := primitive L
    let F := W+P
    have hn := (build_good unit p hUnit hPower base hNormal hPositive columns).1.2.1
    have hEarlier := data primitive W unit p hUnit hPower base hNormal hPositive columns
    have hPrice := hMono (mono p columns base)
    have hi := ih.trans (Nat.mul_le_mul_left (1024*(columns+1)) (Nat.add_le_add_left hPrice W))
    change _≤1024*(columns+1)*F at hi
    have hw := GeneralPaperInitializerControlCounters.word_le_self columns
    have h0 : binaryWordWidth 0=1 := by decide
    have ht := GeneralPaperIntegerWordPrice.compare_le primitive hMono columns 0 L
      (by dsimp [L,width]; omega) (by dsimp [L,width]; omega)
    have hOld := build_work unit p columns base
    change old.work≤columns*(12*(p+1)+82)+2 at hOld
    have hWidth := (metadata_word p columns base).trans (mono p columns base)
    change 1+binaryWordWidth (metadataCap p columns)≤L at hWidth
    have hW : W≤F := Nat.le_add_right _ _
    have hP : P≤F := Nat.le_add_left _ _
    rw [run]
    dsimp only
    rw [hEarlier]
    change _≤1024*(columns+1+1)*F
    by_cases hz : columns=0
    · rw [ite_eq_left hz]
      have hm := metadata_work primitive hMono old.work 0 8 (metadataCap p columns) L
        (by unfold metadataCap; nlinarith only [hOld]) hWidth
      change _≤4*P at hm
      change (run primitive W unit p base columns).2+GeneralPaperIntegerWordPrice.compare primitive columns 0+
        metadataCost primitive old.work 0 8+32*W≤_
      change _≤P at ht
      nlinarith only [hi,ht,hm,hW,hP]
    · rw [ite_eq_right hz]
      have he := (exponent_potential unit p columns base).1
      have hB : old.top.number.exponent.natAbs≤budget p (columns+1) base := by
        change old.top.number.exponent.natAbs+p+1≤budget p columns base at he
        exact (show old.top.number.exponent.natAbs≤budget p columns base by omega).trans (budget_mono p columns base)
      have hOperand := multiply_width unit p (columns+1) hPower base old.top.number old.top.number hB hB
      have hMult := (GeneralPaperDyadicMultiplyPrice.work primitive hMono W unit p old.top.number old.top.number hn hn).trans
        (Nat.mul_le_mul_left 256 (Nat.add_le_add_left (hMono hOperand) W))
      change _≤256*F at hMult
      have hNative := GeneralPaperDyadicMultiply.multiply_work unit p old.top.number old.top.number
      have hMeta := metadata_work primitive hMono old.work
        (GeneralPaperDyadicMultiply.multiply unit p old.top.number old.top.number).work 16 (metadataCap p columns) L
        (by unfold metadataCap; nlinarith only [hOld,hNative]) hWidth
      have hDegree := GeneralPaperPowerTableBounds.top_degree unit p columns base
      have hDW := binaryWordWidth_mono hDegree
      have hPW := GeneralPaperNatPowerOperands.power_width 2 columns
      have h2 : binaryWordWidth 2=2 := by decide
      rw [h2] at hPW
      have hDouble := binaryWordWidth_mul 2 old.top.degree
      change binaryWordWidth old.top.degree≤binaryWordWidth (2^columns) at hDW
      have hDCost := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 2 old.top.degree L
        (by dsimp [L,width]; omega) (by dsimp [L,width]; omega) (by dsimp [L,width]; omega)
      rw [GeneralPaperDyadicMultiplyPrice.data primitive W unit p (by omega) hPower _ _ hn hn]
      change (run primitive W unit p base columns).2+
        (GeneralPaperDyadicMultiplyPrice.run primitive W unit p old.top.number old.top.number).2+
        GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 old.top.degree+
        GeneralPaperIntegerWordPrice.compare primitive columns 0+
        metadataCost primitive old.work (GeneralPaperDyadicMultiply.multiply unit p old.top.number old.top.number).work 16+96*W≤_
      change _≤4*P at hMeta
      change _≤2*P at hDCost
      change _≤P at ht
      nlinarith only [hi,hMult,hMeta,hDCost,ht,hW,hP]

theorem native_work (primitive : ℕ → ℕ) (W unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (base : Number) (hNormal : Normal unit base) (hPositive : 0<base.mantissa) (columns : ℕ) :
    (run primitive W unit p base columns).1.work≤columns*(12*(p+1)+82)+2 := by
  rw [data primitive W unit p hUnit hPower base hNormal hPositive columns]
  exact build_work unit p columns base

end Blotto.GeneralPaperPowerTablePrice
