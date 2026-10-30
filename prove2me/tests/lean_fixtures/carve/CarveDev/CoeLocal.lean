/-! # CarveDev.CoeLocal: uses the elaborated term cannot show

oaiq-096 (CubicMoment, the foreign PNT module `Wiener`):
* `local instance : Coe (E → ℝ) (E → ℂ)`: the coercion unfolds to a lambda, no constant and no
  instance problem remains, so the carver neither kept nor re-activated the instance ("Application
  type mismatch ℕ → ℝ vs ℕ → ℂ" in the piece). Here `Nat → Nat` into `Nat → Int`.
* `@[local gcongr] theorem norm_lt_norm_of_nonneg` kept in a bundle: a local attribute does not
  export, so `gcongr` in the piece "did not make progress". Here `@[local simp] k_eq`. -/

namespace CD.CL

section

local instance : Coe (Nat → Nat) (Nat → Int) := ⟨fun f n => (f n : Int)⟩

theorem coerced (f : Nat → Nat) : (f : Nat → Int) 0 = ((f 0 : Nat) : Int) := rfl

end

def k (n : Nat) : Nat := n

section

@[local simp] theorem k_eq (n : Nat) : k n = n := rfl

theorem uses_k (n : Nat) : k (k n) = n := by simp

end

end CD.CL
