import Blotto.GeneralPaperDyadicMultiply

/-! A shared table of rounded geometric powers, in descending binary-column
order. Each new column squares the preceding stored dyadic number. The
rational powers in `EntryGood` are specification only. No fully expanded
geometric rational is constructed by the table builder.
-/
namespace Blotto.GeneralPaperRoundedPowerTable
open GeneralPaperDyadicFloat GeneralPaperDyadicMultiply
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure Entry where
  degree : ℕ
  number : Number

structure Table where
  entries : List Entry
  top : Entry
  work : ℕ

def square (unit p : ℕ) (entry : Entry) : Entry :=
  ⟨2*entry.degree,(multiply unit p entry.number entry.number).number⟩

def build (unit p : ℕ) (base : Number) : ℕ → Table
  | 0 => ⟨[],⟨1,base⟩,2⟩
  | width+1 =>
    let earlier := build unit p base width
    let next := if width=0 then ⟨1,base⟩ else square unit p earlier.top
    let cost := if width=0 then 8 else (multiply unit p earlier.top.number earlier.top.number).work+16
    ⟨next::earlier.entries,next,earlier.work+cost⟩

def EntryGood (unit : ℕ) (base : ℚ) (entry : Entry) : Prop :=
  0<entry.degree ∧ Normal unit entry.number ∧ 0<entry.number.mantissa ∧
    (retention unit)^(entry.degree-1)*base^entry.degree≤value entry.number ∧
      value entry.number≤base^entry.degree

theorem square_good (unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (base : ℚ) (hBase : 0<base) (entry : Entry) (hEntry : EntryGood unit base entry) :
    EntryGood unit base (square unit p entry) := by
  have hRet := retention_bounds unit hUnit
  have hm := multiply_certificate unit p (by omega) hPower entry.number entry.number hEntry.2.1 hEntry.2.1
  have hl0 : 0≤(retention unit)^(entry.degree-1)*base^entry.degree :=
    mul_nonneg (pow_nonneg hRet.1.le _) (pow_nonneg hBase.le _)
  have hN0 : 0≤value entry.number := value_nonnegative _
  have hSquared := mul_self_le_mul_self hl0 hEntry.2.2.2.1
  have hSqUpper := mul_self_le_mul_self hN0 hEntry.2.2.2.2
  have hLower := mul_le_mul_of_nonneg_left hSquared hRet.1.le
  have hExponent : 2*entry.degree-1=(entry.degree-1)+(entry.degree-1)+1 := by have := hEntry.1; omega
  have hDegree : 2*entry.degree=entry.degree+entry.degree := by omega
  have hLowerEq : retention unit*
      (((retention unit)^(entry.degree-1)*base^entry.degree)*
        ((retention unit)^(entry.degree-1)*base^entry.degree))=
      (retention unit)^(2*entry.degree-1)*base^(2*entry.degree) := by
    rw [hExponent,hDegree]
    simp only [pow_add,pow_one]
    ring
  have hUpperEq : base^entry.degree*base^entry.degree=base^(2*entry.degree) := by rw [hDegree,pow_add]
  refine ⟨by dsimp [square]; have := hEntry.1; omega,
    multiply_normal unit p (by omega) hPower _ _ hEntry.2.1 hEntry.2.1,
    multiply_positive unit p (by omega) hPower _ _ hEntry.2.1 hEntry.2.1 hEntry.2.2.1 hEntry.2.2.1,?_,?_⟩
  · dsimp only [square]
    rw [hLowerEq] at hLower
    exact hLower.trans hm.1
  · dsimp only [square]
    rw [hUpperEq] at hSqUpper
    exact hm.2.trans hSqUpper

theorem base_good (unit : ℕ) (base : Number) (hNormal : Normal unit base) (hPositive : 0<base.mantissa) :
    EntryGood unit (value base) ⟨1,base⟩ := by
  exact ⟨by norm_num,hNormal,hPositive,by simp,by simp⟩

theorem entries_length (unit p width : ℕ) (base : Number) : (build unit p base width).entries.length=width := by
  induction width with
  | zero => rfl
  | succ width ih => change ((build unit p base width).entries.length+1)=width+1; omega

theorem top_degree (unit p width : ℕ) (base : Number) :
    (build unit p base (width+1)).top.degree=2^width := by
  induction width with
  | zero => rfl
  | succ width ih =>
    change 2*(build unit p base (width+1)).top.degree=2^(width+1)
    rw [ih,pow_succ]
    omega

theorem build_good (unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p) (base : Number)
    (hNormal : Normal unit base) (hPositive : 0<base.mantissa) (width : ℕ) :
    EntryGood unit (value base) (build unit p base width).top ∧
      ∀ entry∈(build unit p base width).entries, EntryGood unit (value base) entry := by
  have hBase := value_positive base hPositive
  induction width with
  | zero => exact ⟨base_good unit base hNormal hPositive,by simp [build]⟩
  | succ width ih =>
    have hNext : EntryGood unit (value base)
        (if width=0 then ⟨1,base⟩ else square unit p (build unit p base width).top) := by
      split
      · exact base_good unit base hNormal hPositive
      · exact square_good unit p hUnit hPower _ hBase _ ih.1
    refine ⟨hNext,?_⟩
    intro entry hEntry
    change entry∈(if width=0 then ⟨1,base⟩ else square unit p (build unit p base width).top)::
      (build unit p base width).entries at hEntry
    rcases List.mem_cons.mp hEntry with h|h
    · subst entry; exact hNext
    · exact ih.2 entry h

theorem build_work (unit p width : ℕ) (base : Number) :
    (build unit p base width).work≤width*(12*(p+1)+82)+2 := by
  induction width with
  | zero => simp [build]
  | succ width ih =>
    unfold build
    dsimp only
    split
    · nlinarith
    ·
      have hm := multiply_work unit p (build unit p base width).top.number (build unit p base width).top.number
      nlinarith

end Blotto.GeneralPaperRoundedPowerTable
