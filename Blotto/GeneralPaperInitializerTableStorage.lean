import Blotto.GeneralPaperSourceInitializerRoundingStorageReachedRates

/-! Literal two-level native stored-anchor constructors. Complete outer
and inner capacity/fill/return buffers retain original quotient/rational
pairs, native callback payloads and price fields. One active inner fill is
reserved; its active rounding scalar stays in the previous caller reserve.
The constructors do not copy or sum full scalar scratch over all entries. -/
namespace Blotto.GeneralPaperInitializerTableStorage
open RationalOrderCell GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile)
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

def pairFoot (W : ℕ) (p : ℕ×ℚ) : ℕ := natBits p.1+rationalWordWidth p.2+32*W
def pairProfile (W R : ℕ) : ℕ := 2*R+32*W
def fieldPrice (model : RationalCostModel) (W K R : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.workCap W K (GeneralPaperInitializerRoundingStorage.price model W R)
def fieldProfile (model : RationalCostModel) (W K R : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.profile W (pairProfile W R) K (GeneralPaperInitializerRoundingStorage.price model W R) 0
def fieldWindow {K : ℕ} (model : RationalCostModel) (W copied N depth : ℕ) (input : Fin K → ℚ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.window W (pairFoot W)
    (fun l => GeneralPaperInitializerRoundingBits.run model W N depth (input l)) (fun _ => 0)
    (min copied K) (Nat.min_le_right _ _)
def window {m K : ℕ} (model : RationalCostModel) (W outerCopied innerCopied N depth : ℕ) (input : Fin m → Fin K → ℚ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.window W (arrayFootprint W (pairFoot W))
    (fun j => GeneralPaperInitializerStoredBits.field (fun w => w) W (fun l => GeneralPaperInitializerRoundingBits.run model W N depth (input j l)))
    (fun j => fieldWindow model W innerCopied N depth (input j))
    (min outerCopied m) (Nat.min_le_right _ _)
def profile (model : RationalCostModel) (W m K R : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.profile W (arrayProfile W K (pairProfile W R)) m (fieldPrice model W K R) (fieldProfile model W K R)

theorem entry_bound (model : RationalCostModel) (W N depth A R : ℕ) (hN : 0<N) (hCap : N<2^depth)
    (u : ℚ) (hu : 0≤u ∧ u≤1) (hR : GeneralPaperInitializerRoundingBits.width A N depth≤R) :
    pairFoot W (GeneralPaperInitializerRoundingBits.run model W N depth u).1≤pairProfile W R := by
  let e := GeneralPaperInitializerRoundingBits.run model W N depth u
  have hq : e.1.1≤N := by
    rw [GeneralPaperInitializerRoundingBits.data]
    exact GeneralPaperInitializerRoundingBits.quotient_le N depth hN hCap u hu
  have hn := GeneralPaperBasisDivideBits.nat_height N
  have hNatural := (GeneralPaperBasisDivideBits.nat_height e.1.1).mono (binaryWordWidth_mono hq)
  have hOut := rationalWordWidth_of_height (hNatural.div hn)
  have hData : e.1.2=(e.1.1:ℚ)/(N:ℚ) := rfl
  have hQ : natBits e.1.1≤R := by
    have h := binaryWordWidth_mono hq
    unfold natBits GeneralPaperInitializerRoundingBits.width at *
    omega
  have hValue : rationalWordWidth e.1.2≤R := by
    rw [hData]
    unfold GeneralPaperInitializerRoundingBits.width at hR
    omega
  change natBits e.1.1+rationalWordWidth e.1.2+32*W≤2*R+32*W
  omega

theorem entry_work (model : RationalCostModel) (W N depth A R : ℕ) (hN : 0<N) (hCap : N<2^depth)
    (u : ℚ) (hu : 0≤u ∧ u≤1) (hHeight : RationalHeight u A) (hR : GeneralPaperInitializerRoundingBits.width A N depth≤R) :
    (GeneralPaperInitializerRoundingBits.run model W N depth u).2≤GeneralPaperInitializerRoundingStorage.price model W R := by
  have hd : depth≤R := by unfold GeneralPaperInitializerRoundingBits.width at hR; omega
  exact (GeneralPaperInitializerRoundingBits.work model W N depth A hN hCap u hu hHeight).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 256 (Nat.add_le_add_right hd 1)) (Nat.add_le_add_left (model.monotone hR) W))

theorem field_bound {K : ℕ} (model : RationalCostModel) (W N depth A R copied : ℕ) (hN : 0<N) (hCap : N<2^depth)
    (input : Fin K → ℚ) (hUnit : ∀ l,0≤ input l ∧ input l≤1) (hHeight : ∀ l,RationalHeight (input l) A)
    (hR : GeneralPaperInitializerRoundingBits.width A N depth≤R) (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) :
    fieldWindow model W copied N depth input≤fieldProfile model W K R :=
  GeneralPaperNativePayloadFillStorage.bounded W (pairProfile W R) (GeneralPaperInitializerRoundingStorage.price model W R) 0
    (pairFoot W) (fun l => GeneralPaperInitializerRoundingBits.run model W N depth (input l)) (fun _ => 0)
    (fun l => entry_bound model W N depth A R hN hCap (input l) (hUnit l) hR)
    (fun l => entry_work model W N depth A R hN hCap (input l) (hUnit l) (hHeight l) hR)
    (fun _ => le_rfl) hW hK (min copied K) (Nat.min_le_right _ _)

theorem bounded {m K : ℕ} (model : RationalCostModel) (W N depth A R outerCopied innerCopied : ℕ) (hN : 0<N) (hCap : N<2^depth)
    (input : Fin m → Fin K → ℚ) (hUnit : ∀ j l,0≤ input j l ∧ input j l≤1) (hHeight : ∀ j l,RationalHeight (input j l) A)
    (hR : GeneralPaperInitializerRoundingBits.width A N depth≤R) (hW : 1≤W)
    (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) :
    window model W outerCopied innerCopied N depth input≤profile model W m K R := by
  let callback := fun j l => GeneralPaperInitializerRoundingBits.run model W N depth (input j l)
  have hPayload (j : Fin m) : arrayFootprint W (pairFoot W)
      (GeneralPaperInitializerStoredBits.field (fun w => w) W (callback j)).1≤arrayProfile W K (pairProfile W R) := by
    apply GeneralPaperEncodedBasisStorage.array_bound
    intro l
    rw [GeneralPaperInitializerStoredBits.field,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact entry_bound model W N depth A R hN hCap (input j l) (hUnit j l) hR
  have hWork (j : Fin m) : (GeneralPaperInitializerStoredBits.field (fun w => w) W (callback j)).2≤fieldPrice model W K R :=
    GeneralPaperNativePayloadFillStorage.prefix_work W (GeneralPaperInitializerRoundingStorage.price model W R) (callback j)
      (fun l => entry_work model W N depth A R hN hCap (input j l) (hUnit j l) (hHeight j l) hR) hW hK K le_rfl
  exact GeneralPaperNativePayloadFillStorage.bounded W (arrayProfile W K (pairProfile W R)) (fieldPrice model W K R) (fieldProfile model W K R)
    (arrayFootprint W (pairFoot W)) (fun j => GeneralPaperInitializerStoredBits.field (fun w => w) W (callback j))
    (fun j => fieldWindow model W innerCopied N depth (input j)) hPayload hWork
    (fun j => field_bound model W N depth A R innerCopied hN hCap (input j) (hUnit j) (hHeight j) hR hW hK)
    hW hM (min outerCopied m) (Nat.min_le_right _ _)

end Blotto.GeneralPaperInitializerTableStorage
