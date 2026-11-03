import Blotto.GeneralPaperNativeSourceRates

/-! The complete balanced DP's actual per-call fast-bit rate is field-linear,
full-code-linear and quadratic in inverse accuracy, up to polynomial logarithms.
The already proved common reference width is used, with no capacity premise.
This is a DP component theorem; full-source and compiler rates are separate. -/
namespace Blotto.GeneralPaperSharpDPSourceRate
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperFastRationalModel
set_option autoImplicit false
set_option maxHeartbeats 2000000

def resourceRate (x : Input) : ℕ := fields x*symbols x
def callRate (x : Input) : ℕ := resourceRate x*(accuracy x)^2

theorem field_linear : Soft fields (fun x => 2*x.m+1) :=
  bounded 2 (fun x => by unfold fields; omega)

theorem symbol_linear : Soft symbols (fun x => 2*symbols x+2) :=
  bounded 4 (fun x => by have h := symbols_positive x; omega)

theorem root_resource_rate : Soft resourceRate (fun x => GeneralPaperFastRootPrice.rootWord x.m (symbols x)) := by
  exact mul field_linear symbol_linear

theorem resource_rate : Soft resourceRate (fun x => GeneralPaperFastOrderedDPPrice.fieldResourceWords x.m (symbols x)) := by
  have hp : Polylog (fun x => binaryWordWidth x.m+1) := by fun_prop
  simpa only [GeneralPaperFastOrderedDPPrice.fieldResourceWords,GeneralPaperFastRootPrice.rootWord,Nat.mul_assoc]
    using poly_mul_rate hp root_resource_rate

theorem resource_small : Small (fun x => GeneralPaperFastOrderedDPPrice.fieldResourceWords x.m (symbols x)) := by
  unfold GeneralPaperFastOrderedDPPrice.fieldResourceWords symbols
  fun_prop

theorem coefficient_rate : Soft (fun x => (accuracy x)^2) (fun x => 2*options x+4*(grid x)^2) := by
  have hincl (x : Input) : accuracy x≤(accuracy x)^2 := by
    have h := accuracy_positive x
    nlinarith only [h]
  have hg : Soft (fun x => (accuracy x)^2) (fun x => (grid x)^2) := by
    simpa only [_root_.pow_two] using mul grid_rate grid_rate
  exact add_same (rate_mono (poly_mul_rate (poly_constant 2) options_rate) hincl)
    (poly_mul_rate (poly_constant 4) hg)

theorem field_profile_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Soft callRate (fun x => GeneralPaperFastOrderedDPPrice.fieldProfile C d (W x)
      x.m (alphabet x).lambda x.k x.Qv (options x) (grid x) (symbols x)) := by
  have hincl (x : Input) : accuracy x≤(accuracy x)^2 := by
    have h := accuracy_positive x
    nlinarith only [h]
  have hbase := add_same (rate_mono (leaf_base_rate C d W hW) hincl) (merge_base_rate C d W hW)
  have hfixed := mul field_linear hbase
  have hfixed' : Soft callRate (fun x => (2*x.m+1)*
      (GeneralPaperOrderedDPAggregatePrice.leafBase (charge C d) (W x) x.m (alphabet x).lambda x.k x.Qv (options x) (grid x)+
       GeneralPaperOrderedDPAggregatePrice.mergeBase (charge C d) (W x) x.m (alphabet x).lambda x.k x.Qv (grid x))) := by
    apply rate_mono hfixed
    intro x
    have hs := symbols_positive x
    dsimp only [callRate,resourceRate]
    nlinarith only [hs,Nat.zero_le (fields x*(accuracy x)^2)]
  have hresource := mul coefficient_rate (charge_preserves C d resource_rate resource_small)
  have hresource' : Soft callRate (fun x => (2*options x+4*(grid x)^2)*
      charge C d (GeneralPaperFastOrderedDPPrice.fieldResourceWords x.m (symbols x))) := by
    apply rate_mono hresource
    intro x
    dsimp only [callRate]
    exact le_of_eq (by ring)
  exact add_same hfixed' hresource'

noncomputable def actualProfile (C d : ℕ) (x : Input) : ℕ :=
  GeneralPaperFastOrderedDPPrice.fieldProfile C d (GeneralPaperLogarithmicSourceReference.width C d x)
    x.m (alphabet x).lambda x.k x.Qv (options x) (grid x) (symbols x)

theorem actual_profile_rate (C d : ℕ) : Soft callRate (actualProfile C d) :=
  field_profile_rate C d _ (GeneralPaperLogarithmicSourceReference.width_tight C d)

theorem actual_profile_bound (C d : ℕ) : ∃ A e : ℕ,∀ x,
    actualProfile C d x≤A*(x.m+1)*((alphabet x).lambda+1)*2^(2*x.k)*(logSize x)^e := by
  rcases actual_profile_rate C d with ⟨A,e,h⟩
  refine ⟨A,e,?_⟩
  intro x
  exact (h x).trans_eq (by
    dsimp only [callRate,resourceRate,fields,symbols,accuracy]
    rw [←pow_mul]
    congr 1
    ring)

end Blotto.GeneralPaperSharpDPSourceRate
