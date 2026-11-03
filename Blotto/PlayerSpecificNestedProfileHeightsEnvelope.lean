import Blotto.PlayerSpecificPolynomialPairTerms
import Blotto.PlayerSpecificNestedFirstProfileSourceCost
import Blotto.PlayerSpecificNestedThirdProfileSourceCost
import Blotto.PlayerSpecificAlgebraicNestedInteriorLinear
import Blotto.PlayerSpecificNestedTerminalDrawSourceCost

/-! The reached nested profile and terminal output heights have linear
polynomial envelopes in original row height and scalar precision. -/
namespace Blotto.PlayerSpecificNestedProfileHeightsEnvelope
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev S := PlayerSpecificPolynomialPairTerms.size
private abbrev F := PlayerSpecificPolynomialPairTerms.first
private abbrev K := PlayerSpecificPolynomialPairTerms.second
private theorem add {f g : ℕ × ℕ → ℕ}
    (hf : NaturalPolynomialEnvelope S f)
    (hg : NaturalPolynomialEnvelope S g) :
    NaturalPolynomialEnvelope S (fun p => f p+g p) :=
  NaturalPolynomialEnvelope.add hf hg
private theorem c (n : ℕ) : NaturalPolynomialEnvelope S (fun _ => n) :=
  NaturalPolynomialEnvelope.constant _ n

theorem first_base : NaturalPolynomialEnvelope S
    (fun p : ℕ × ℕ => PlayerSpecificAlgebraicNestedFirstDrawSizes.base p.1 p.2) := by
  have h := add (add F K) (c 3)
  simpa only [PlayerSpecificAlgebraicNestedFirstDrawSizes.base] using h

theorem first_location_height : NaturalPolynomialEnvelope S
    (fun p : ℕ × ℕ => PlayerSpecificNestedFirstProfileSourceCost.locationHeight p.1 p.2) := by
  have h := PlayerSpecificSourcePolynomialAutomation.iterate_envelope first_base 10
  simpa only [PlayerSpecificNestedFirstProfileSourceCost.locationHeight] using h

theorem first_table_height : NaturalPolynomialEnvelope S
    (fun p : ℕ × ℕ => PlayerSpecificNestedFirstProfileSourceCost.tableHeight p.1 p.2) := by
  have h := PlayerSpecificSourcePolynomialAutomation.iterate_envelope first_base 32
  simpa only [PlayerSpecificNestedFirstProfileSourceCost.tableHeight] using h

theorem remaining_base : NaturalPolynomialEnvelope S
    (fun p : ℕ × ℕ => PlayerSpecificAlgebraicNestedRemainingSizes.base p.1 p.2) := by
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope F 9
  have h := add (add hi K) (c 3)
  simpa only [PlayerSpecificAlgebraicNestedRemainingSizes.base] using h

theorem third_assembly_height : NaturalPolynomialEnvelope S
    (fun p : ℕ × ℕ => PlayerSpecificNestedThirdProfileSourceCost.assemblyHeight p.1 p.2) := by
  let B := (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^9
  let C := (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^32*(B+4)
  refine ⟨C,1,?_⟩
  intro p
  have hi := iterate_bound 9 p.1
  have hb : PlayerSpecificAlgebraicNestedRemainingSizes.base p.1 p.2+1≤
      (B+4)*(p.1+p.2+1) := by
    unfold PlayerSpecificAlgebraicNestedRemainingSizes.base
    have hn := Nat.zero_le (B*p.2)
    dsimp [B] at hi ⊢
    nlinarith only [hi,hn,Nat.zero_le p.1,Nat.zero_le p.2]
  have ho := iterate_bound 32 (PlayerSpecificAlgebraicNestedRemainingSizes.base p.1 p.2)
  have hm := Nat.mul_le_mul_left
    ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^32) hb
  have ht := ho.trans hm
  calc
    PlayerSpecificNestedThirdProfileSourceCost.assemblyHeight p.1 p.2 ≤
        PlayerSpecificNestedThirdProfileSourceCost.assemblyHeight p.1 p.2+1 := Nat.le_succ _
    _ ≤ ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^32)*
        ((B+4)*(p.1+p.2+1)) := ht
    _ = C*(S p+1)^1 := by dsimp only [C,S,PlayerSpecificPolynomialPairTerms.size,pow_one]; ring

theorem interior_profile_height : NaturalPolynomialEnvelope S
    (fun p : ℕ × ℕ => PlayerSpecificAlgebraicNestedInteriorSizes.height p.1 p.2) := by
  let C := (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^35*
    ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^18+4)
  refine ⟨4*C,1,?_⟩
  intro p
  have h := PlayerSpecificAlgebraicNestedInteriorLinear.profile_linear p.1 p.2
  have hs : p.1+p.2+4≤4*(S p+1) := by dsimp [S,PlayerSpecificPolynomialPairTerms.size]; omega
  have hm := Nat.mul_le_mul_left C hs
  calc
    PlayerSpecificAlgebraicNestedInteriorSizes.height p.1 p.2 ≤ C*(p.1+p.2+4) := by dsimp [C] at h ⊢; omega
    _ ≤ C*(4*(S p+1)) := hm
    _ = (4*C)*(S p+1)^1 := by ring

theorem interior_draw_height : NaturalPolynomialEnvelope S
    (fun p : ℕ × ℕ => PlayerSpecificAlgebraicNestedInteriorDraw.height p.1 p.2) := by
  refine ⟨PlayerSpecificAlgebraicNestedInteriorLinear.coefficient,1,?_⟩
  intro p
  have h := PlayerSpecificAlgebraicNestedInteriorLinear.height_linear p.1 p.2
  simp only [S,PlayerSpecificPolynomialPairTerms.size,pow_one]
  omega

theorem terminal_output_height : NaturalPolynomialEnvelope S
    (fun p : ℕ × ℕ => PlayerSpecificNestedTerminalDrawSourceCost.outputHeight p.1 p.2) := by
  have hs := PlayerSpecificSourcePolynomialAutomation.step_envelope F
  have hsize := add hs K
  have h := PlayerSpecificPolynomialSubstitution.substitute
    (g := fun p : ℕ × ℕ => (step p.1,p.2)) interior_draw_height hsize
  simpa only [PlayerSpecificNestedTerminalDrawSourceCost.outputHeight] using h

end Blotto.PlayerSpecificNestedProfileHeightsEnvelope
