import Blotto.GeneralPaperAdaptiveLossBounds

/-! The selected optimizer's fixed geometric profit grid. Only grid-sized
lists are generated, never an alphabet or an allocation-product list.
The common denominator is F = 2^B*w and the endpoint is exactly two.
-/
namespace Blotto.GeneralPaperProfitGridPoints
set_option autoImplicit false
set_option maxHeartbeats 3500000

def denominator (w B : ℕ) : ℕ := 2^B*w

def band (w h : ℕ) : List ℕ := (List.range w).map (fun r => (w+r)*2^h)

def points (w B : ℕ) : List ℕ := (List.range (B+1)).flatMap (band w)

theorem band_length (w h : ℕ) : (band w h).length=w := by simp [band]

theorem points_length (w B : ℕ) : (points w B).length=(B+1)*w := by
  simp [points,List.length_flatMap,band_length]

theorem band_mem (w h value : ℕ) : value∈band w h ↔
    ∃ a, w≤a ∧ a<2*w ∧ value=a*2^h := by
  simp only [band,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact ⟨w+r,by omega,by omega,rfl⟩
  · rintro ⟨a,ha,hu,rfl⟩
    exact ⟨a-w,by omega,by congr 1; omega⟩

theorem points_mem (w B value : ℕ) : value∈points w B ↔
    ∃ h≤B, ∃ a, w≤a ∧ a<2*w ∧ value=a*2^h := by
  simp only [points,List.mem_flatMap,List.mem_range,band_mem]
  constructor
  · rintro ⟨h,hh,he⟩
    exact ⟨h,by omega,he⟩
  · rintro ⟨h,hh,he⟩
    exact ⟨h,by omega,he⟩

theorem points_bound (w B value : ℕ) (hValue : value∈points w B) : value≤2*denominator w B := by
  obtain ⟨h,hh,a,ha,hu,rfl⟩ := (points_mem w B value).mp hValue
  have hp := Nat.pow_le_pow_right (by decide : 1≤2) hh
  have he := Nat.mul_le_mul (show a≤2*w by omega) hp
  simpa only [denominator,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using he

theorem denominator_positive (w B : ℕ) (hW : 0<w) : 0<denominator w B := Nat.mul_pos (Nat.two_pow_pos B) hW

end Blotto.GeneralPaperProfitGridPoints
