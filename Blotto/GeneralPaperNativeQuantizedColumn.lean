import Blotto.GeneralPaperNativeQuantizedAnchors

/-! A priced quantized column constructs its stable order once, scatters
labels once and materializes K anchor references once. Only labels and
anchors are returned; the temporary sort order is consumed in preparation. -/
namespace Blotto.GeneralPaperNativeQuantizedColumn
set_option autoImplicit false
set_option maxHeartbeats 2400000

def run {K B : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hK : 0<K) (hB : 0<B)
    (value : FixedArrayTable (K*B) ℚ) : GeneralPaperQuantizedColumn.Column (K*B) K×ℕ :=
  let sorted := GeneralPaperNativeRepresentativeSort.run price index A value
  let labels := GeneralPaperNativeQuantizedLabels.run price index A hK hB sorted.1
  let anchors := GeneralPaperNativeQuantizedAnchors.run price index A hB sorted.1 value
  (⟨labels.1,anchors.1⟩,sorted.2+labels.2+anchors.2+64*A)

theorem data {K B : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hK : 0<K) (hB : 0<B)
    (value : FixedArrayTable (K*B) ℚ) : (run price index A hK hB value).1=GeneralPaperQuantizedColumn.build hK hB value := by
  unfold run
  dsimp only
  rw [GeneralPaperNativeQuantizedLabels.data,GeneralPaperNativeQuantizedAnchors.data price index A hK]

theorem models_data {K B : ℕ} (price price' index index' : ℕ → ℕ) (A A' : ℕ) (hK : 0<K) (hB : 0<B)
    (value : FixedArrayTable (K*B) ℚ) :
    (run price index A hK hB value).1=(run price' index' A' hK hB value).1 := by rw [data,data]

def profile (K B A sortPrice blockPrice anchorPrice : ℕ) : ℕ :=
  GeneralPaperNativeRepresentativeSort.profile (K*B) A sortPrice+
    (K*B)*(512*(binaryWordWidth (K*B)+1)*(A+blockPrice)+64*A)+192*(2*(K*B)+1)*A+
    K*(5*anchorPrice+64*A)+44*(K+1)*A+64*A

theorem work {K B : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A H : ℕ) (hA : 1≤A)
    (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ) (hv : ∀ i,rationalWordWidth (value.read i)≤H)
    (hIndex : ∀ i≤2*(K*B)+K,index (binaryWordWidth (i+1))≤A) :
    (run price index A hK hB value).2≤profile K B A (price H)
      (price (GeneralPaperNativeBlockLabel.width (K*B) B)) (price (1+binaryWordWidth (K*B+B+1))) := by
  have hSort := GeneralPaperNativeRepresentativeSort.work price index hMono A H hA value hv (fun i hi => hIndex i (by omega))
  have hLabels := GeneralPaperNativeQuantizedLabels.work price index hMono A hA hK hB
    (GeneralPaperNativeRepresentativeSort.run price index A value).1 (fun i hi => hIndex i (by omega))
  have hAnchors := GeneralPaperNativeQuantizedAnchors.work price index hMono A hA hB
    (GeneralPaperNativeRepresentativeSort.run price index A value).1 value (fun i hi => hIndex i (by omega))
  unfold run profile
  dsimp only
  omega

theorem height {K B : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hK : 0<K) (hB : 0<B)
    (value : FixedArrayTable (K*B) ℚ) (H : ℕ) (hv : ∀ i,RationalHeight (value.read i) H) (l : Fin K) :
    RationalHeight ((run price index A hK hB value).1.anchors.read l) H := by
  rw [data]
  exact GeneralPaperQuantizedHeight.column_height hK hB value H hv l

end Blotto.GeneralPaperNativeQuantizedColumn
