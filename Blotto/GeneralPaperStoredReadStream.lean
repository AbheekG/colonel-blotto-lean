import Blotto.GeneralPaperStoredScalarSourceRead

/-! A forward stored-value collector uses the actual loaded header count.
Concrete scalar/bit/rational/natural entry points fix the reader and complete
payload-copy price. Source lists below occur only in erased proofs. -/
namespace Blotto.GeneralPaperStoredReadStream
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperRetainedScalarValue (Scalar)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def loop {α : Type*} (model : RationalCostModel) (A : ℕ) (reader : ℕ → Option α × ℕ) (encode : α → ℕ) :
    ℕ → ℕ → Option (List α) × ℕ
  | _,0 => (some [],64 * (A + 1))
  | start,n + 1 =>
    let current := reader start
    match current.1 with
    | none => (none,current.2 + 64 * (A + 1))
    | some value =>
      let next := GeneralPaperNaturalScalarStep.run model A .add start 1
      let later := loop model A reader encode next.1 n
      (later.1.map (List.cons value),current.2 + next.2 + later.2 + encode value + 128 * (A + 1))

def price {α : Type*} (model : RationalCostModel) (A : ℕ) (reader : ℕ → Option α × ℕ) (encode : α → ℕ) : ℕ → List α → ℕ
  | _,[] => 64 * (A + 1)
  | start,value :: values => (reader start).2 + (GeneralPaperNaturalScalarStep.run model A .add start 1).2 +
      price model A reader encode (start + 1) values + encode value + 128 * (A + 1)

theorem loop_source {α : Type*} (model : RationalCostModel) (A : ℕ) (reader : ℕ → Option α × ℕ) (encode : α → ℕ)
    (values : List α) (start : ℕ)
    (hReads : ∀ index : Fin values.length,(reader (start + index.val)).1 = some values[index.val]) :
    (loop model A reader encode start values.length).1 = some values ∧
      (loop model A reader encode start values.length).2 = price model A reader encode start values := by
  induction values generalizing start with
  | nil => exact ⟨rfl,rfl⟩
  | cons value values ih =>
    have hHead := hReads ⟨0,by simp only [List.length_cons]; omega⟩
    simp only [Nat.add_zero,List.getElem_cons_zero] at hHead
    have hTail : ∀ index : Fin values.length,(reader (start + 1 + index.val)).1 = some values[index.val] := by
      intro index
      have h := hReads ⟨index.val + 1,by simp only [List.length_cons]; omega⟩
      have hi : start + 1 + index.val = start + (index.val + 1) := by omega
      rw [hi]
      simpa only [List.getElem_cons_succ] using h
    obtain ⟨hv,hw⟩ := ih (start + 1) hTail
    simp only [List.length_cons,loop,hHead,GeneralPaperNaturalScalarStep.run,GeneralPaperNaturalScalarStep.Op.apply,
      hv,hw,Option.map_some,price,and_self]

theorem loop_length {α : Type*} (model : RationalCostModel) (A : ℕ) (reader : ℕ → Option α × ℕ) (encode : α → ℕ)
    (start fuel : ℕ) (values : List α) (hReturn : (loop model A reader encode start fuel).1 = some values) : values.length = fuel := by
  induction fuel generalizing start values with
  | zero =>
    have he : values = [] := Option.some.inj hReturn.symm
    rw [he]
    rfl
  | succ fuel ih =>
    cases hCurrent : (reader start).1 with
    | none => simp only [loop,hCurrent] at hReturn; cases hReturn
    | some value =>
      cases hLater : (loop model A reader encode (GeneralPaperNaturalScalarStep.run model A .add start 1).1 fuel).1 with
      | none => simp only [loop,hCurrent,hLater,Option.map_none] at hReturn; cases hReturn
      | some later =>
        simp only [loop,hCurrent,hLater,Option.map_some,Option.some.injEq] at hReturn
        rw [← hReturn,List.length_cons,ih _ later hLater]

structure Result (α : Type*) where
  values : Option (List α)
  count : ℕ
  work : ℕ

def counted {α : Type*} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (reader : ℕ → Option α × ℕ) (encode : α → ℕ) : Result α :=
  let count := GeneralPaperHeaderCountReadback.count model A installed installed.root
  match count.1 with
  | none => ⟨none,0,count.2 + 64 * (A + 1)⟩
  | some n =>
    let actual := loop model A reader encode 0 n
    ⟨actual.1,n,count.2 + actual.2 + 128 * (A + 1)⟩

theorem counted_source {α : Type*} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (reader : ℕ → Option α × ℕ) (encode : α → ℕ) (values : List α)
    (hCount : (GeneralPaperHeaderCountReadback.count model A installed installed.root).1 = some values.length)
    (hReads : ∀ index : Fin values.length,(reader index.val).1 = some values[index.val]) :
    (counted model A installed reader encode).values = some values ∧
      (counted model A installed reader encode).count = values.length ∧
      (counted model A installed reader encode).work =
        (GeneralPaperHeaderCountReadback.count model A installed installed.root).2 + price model A reader encode 0 values + 128 * (A + 1) := by
  obtain ⟨hv,hw⟩ := loop_source model A reader encode values 0 (by simpa only [Nat.zero_add] using hReads)
  simp only [counted,hCount,hv,hw,and_self]

theorem counted_length {α : Type*} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (reader : ℕ → Option α × ℕ) (encode : α → ℕ) (values : List α)
    (hReturn : (counted model A installed reader encode).values = some values) :
    values.length = (counted model A installed reader encode).count := by
  cases hCount : (GeneralPaperHeaderCountReadback.count model A installed installed.root).1 with
  | none => simp only [counted,hCount] at hReturn; cases hReturn
  | some n =>
    simp only [counted,hCount] at hReturn ⊢
    exact loop_length model A reader encode 0 n values hReturn

def scalars (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fixed : ℕ) : Result Scalar :=
  counted model A installed (GeneralPaperStoredScalarRead.read model A installed fixed) GeneralPaperRetainedScalarValue.encode
def naturals (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fixed : ℕ) : Result ℕ :=
  counted model A installed (GeneralPaperStoredScalarRead.natural model A installed fixed) GeneralPaperEncodedScalarStorage.natBits
def rationals (model : RationalCostModel) (A : ℕ) (installed : Installed A) : Result ℚ :=
  counted model A installed (GeneralPaperStoredScalarRead.rational model A installed 64) rationalWordWidth
def bits (model : RationalCostModel) (A : ℕ) (installed : Installed A) : Result Bool :=
  counted model A installed (GeneralPaperStoredScalarRead.bit model A installed 32) (fun _ => 1)

theorem bits_length (model : RationalCostModel) (A : ℕ) (installed : Installed A) (values : List Bool)
    (hReturn : (bits model A installed).values = some values) : values.length = (bits model A installed).count :=
  counted_length model A installed (GeneralPaperStoredScalarRead.bit model A installed 32) (fun _ => 1) values hReturn

end Blotto.GeneralPaperStoredReadStream
