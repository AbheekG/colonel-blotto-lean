import Blotto.BinaryPRGPhysicalFramedLifetime
import Blotto.BinaryPRGFullOutputLifetimePolynomial

/-! Conservative source-storage growth after adopting physical output. The
preceding draw keeps its established bound; no unused old output is executed.
Source-array projection and complete native bit-model pricing stay separate. -/
namespace Blotto.BinaryPRGPhysicalOutputPolynomial
open BinaryPRGFullOutputLifetimePolynomial
set_option maxHeartbeats 300000
set_option maxRecDepth 20000


def extraEnvelopeAt (depth n s K header : ℕ) : ℕ :=
  BinaryPhysicalOutputLifetime.bound n (1+2*expressionHeightBudget (max (3+s) (K+2)) depth) header+128

def extraEnvelope : ℕ → ℕ → ℕ → ℕ → ℕ := extraEnvelopeAt 75

theorem bound_polynomial : NaturalPolynomialEnvelope inputSize (fun p =>
    BinaryPhysicalOutputLifetime.bound p.count p.height p.headerLength) := by
  let c (k : ℕ) := NaturalPolynomialEnvelope.constant inputSize k
  have hn : NaturalPolynomialEnvelope inputSize (fun p : Parameters => p.count) :=
    .of_le_size _ _ (fun _ => by unfold inputSize; omega)
  have hw : NaturalPolynomialEnvelope inputSize (fun p : Parameters => p.height) :=
    .of_le_size _ _ (fun _ => by unfold inputSize; omega)
  have hh : NaturalPolynomialEnvelope inputSize (fun p : Parameters => p.headerLength) :=
    .of_le_size _ _ (fun _ => by unfold inputSize; omega)
  have hH := (c 4).mul hn |>.mul (hw.add (c 1))
  have hH1 := hH.add (c 1)
  have hS := hn.mul (((c 2).mul hH1).add (c 1))
  have hPrep := ((hn.mul (((c 33).mul ((c 100).mul (hH1.pow 2))).add (c 64))).add
    ((c 1024).mul (((hn.mul hH1).add hn).add (c 1)))).add (c 128)
  have hHeapRead := ((hH1.mul (((c 5).mul (hH1.add (c 1))).add (c 4))).add
    ((c 8).mul hH)).add (c 10)
  have hSlotRead := ((c 128).mul (hS.add (c 1))).mul ((hS.add (hn.add (c 1))).add (c 2))
  have hAccess := (((c 64).mul hSlotRead).add
    ((c 32).mul (((hHeapRead.add (hH.mul hH1)).add ((c 2).mul hH)).add (c 5)))).add (c 128)
  have hOp := (c 200000).mul ((hw.add (c 2)).pow 3)
  have hFrames := (c 500).mul ((hw.add (c 2)).pow 2)
  have hStep := ((((hAccess.add hOp).add hFrames).add
    ((c 1024).mul (((c 3).mul hw).add (c 2)))).add
    ((c 128).mul (((c 12).mul hw).add (c 8)))).add (c 256)
  have hFinal := (((hPrep.add (hn.mul hStep)).add ((c 32).mul hn)).add
    ((c 128).mul (hh.add (c 1)))).add (c 256)
  exact hFinal


def reparameterizeAt (depth : ℕ) (p : Parameters) : Parameters :=
  ⟨p.count,1+2*expressionHeightBudget (max (3+p.height) (p.precision+2)) depth,0,0,0,p.headerLength⟩

theorem parameterSizeAt_polynomial (depth : ℕ) : NaturalPolynomialEnvelope inputSize (fun p => inputSize (reparameterizeAt depth p)+1) := by
  have hn : NaturalPolynomialEnvelope inputSize (fun p : Parameters => p.count) :=
    .of_le_size _ _ (fun _ => by unfold inputSize; omega)
  have hs : NaturalPolynomialEnvelope inputSize (fun p : Parameters => p.height) :=
    .of_le_size _ _ (fun _ => by unfold inputSize; omega)
  have hk : NaturalPolynomialEnvelope inputSize (fun p : Parameters => p.precision) :=
    .of_le_size _ _ (fun _ => by unfold inputSize; omega)
  have hh : NaturalPolynomialEnvelope inputSize (fun p : Parameters => p.headerLength) :=
    .of_le_size _ _ (fun _ => by unfold inputSize; omega)
  have hw : NaturalPolynomialEnvelope inputSize (fun p : Parameters =>
      1+2*expressionHeightBudget (max (3+p.height) (p.precision+2)) depth) :=
    .add (.constant _ 1) (.mul (.constant _ 2)
      (.height (.max (.add (.constant _ 3) hs) (.add hk (.constant _ 2))) depth))
  exact (((hn.add hw).add hh).add (.constant _ 1))

def reparameterize : Parameters → Parameters := reparameterizeAt 75

theorem parameterSize_polynomial : NaturalPolynomialEnvelope inputSize (fun p => inputSize (reparameterize p)+1) :=
  parameterSizeAt_polynomial 75

theorem pullback {α β : Type*} (sizeA : α → ℕ) (sizeB f : β → ℕ) (embed : α → β)
    (hF : NaturalPolynomialEnvelope sizeB f)
    (hSize : NaturalPolynomialEnvelope sizeA (fun x => sizeB (embed x)+1)) :
    NaturalPolynomialEnvelope sizeA (fun x => f (embed x)+128) := by
  rcases hF with ⟨C,d,hBound⟩
  rcases hSize with ⟨D,e,hSize⟩
  refine ⟨C*D^d+128,e*d,?_⟩
  intro x
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left (hSize x) d)
  rw [Nat.mul_pow,← Nat.mul_assoc,← pow_mul] at hp
  have hOne := Nat.one_le_pow (e*d) (sizeA x+1) (by omega)
  calc
    _ ≤ (C*D^d)*(sizeA x+1)^(e*d)+128 := Nat.add_le_add_right ((hBound _).trans hp) 128
    _ ≤ (C*D^d)*(sizeA x+1)^(e*d)+128*(sizeA x+1)^(e*d) :=
      Nat.add_le_add_left (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 128 hOne) _
    _ = (C*D^d+128)*(sizeA x+1)^(e*d) := by rw [Nat.add_mul]

theorem extraAt_polynomial (depth : ℕ) : NaturalPolynomialEnvelope inputSize (fun p =>
    extraEnvelopeAt depth p.count p.height p.precision p.headerLength) :=
  pullback inputSize inputSize (fun p => BinaryPhysicalOutputLifetime.bound p.count p.height p.headerLength)
    (reparameterizeAt depth) bound_polynomial (parameterSizeAt_polynomial depth)

theorem extra_polynomial : NaturalPolynomialEnvelope inputSize (fun p =>
    extraEnvelope p.count p.height p.precision p.headerLength) :=
  extraAt_polynomial 75


theorem envelope_decomposition {n : ℕ} (request : BinaryPRGRequest.Request n) (K i b header : ℕ) :
    BinaryPRGPhysicalFramedLifetime.envelope request K i b header =
      BinaryPRGHeapFramedLifetime.envelope request K i b header+
        extraEnvelope n request.source.originalInputWordWidth K header := by
  have hW : BinaryPRGHeapFixedProperties.wordWidth request K =
      1+2*expressionHeightBudget (max (3+request.source.originalInputWordWidth) (K+2)) 75 := rfl
  simp only [BinaryPRGPhysicalFramedLifetime.envelope,extraEnvelope,extraEnvelopeAt,hW,Nat.add_assoc]

theorem framed_envelope_polynomial : ∃ C d : ℕ,∀ {n : ℕ} (request : BinaryPRGRequest.Request n) (K i b header : ℕ),
    BinaryPRGPhysicalFramedLifetime.envelope request K i b header ≤
      C*(n+request.source.originalInputWordWidth+K+i+b+header+2)^d := by
  rcases BinaryPRGFullOutputLifetimePolynomial.framed_envelope_polynomial with ⟨C₁,d₁,h₁⟩
  rcases extra_polynomial with ⟨C₂,d₂,h₂⟩
  refine ⟨C₁+C₂,d₁+d₂,?_⟩
  intro n request K i b header
  let X := n+request.source.originalInputWordWidth+K+i+b+header+2
  have hX : 0 < X := by dsimp [X]; omega
  have hA := h₁ request K i b header
  have hB := h₂ ⟨n,request.source.originalInputWordWidth,K,i,b,header⟩
  change extraEnvelope n request.source.originalInputWordWidth K header ≤
    C₂*(n+request.source.originalInputWordWidth+K+i+b+header+1)^d₂ at hB
  have hp₁ := Nat.pow_le_pow_right hX (show d₁ ≤ d₁+d₂ by omega)
  have hp₂ : (n+request.source.originalInputWordWidth+K+i+b+header+1)^d₂ ≤ X^(d₁+d₂) :=
    (Nat.pow_le_pow_left (by dsimp [X]; omega) d₂).trans (Nat.pow_le_pow_right hX (by omega))
  have h₁' := Nat.mul_le_mul_left C₁ hp₁
  have h₂' := Nat.mul_le_mul_left C₂ hp₂
  rw [envelope_decomposition]
  change _ ≤ (C₁+C₂)*X^(d₁+d₂)
  have ha := hA.trans h₁'
  have hb := hB.trans h₂'
  exact (Nat.add_le_add ha hb).trans_eq (by rw [Nat.add_mul])

end Blotto.BinaryPRGPhysicalOutputPolynomial
