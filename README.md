# How to read Lean

Here we will teach you how to read math written in Lean.

```lean
lemma difference_of_cubes {R : Type} [CommRing R] (x y : R) :
    (x^2 + x*y + y^2) * (x - y) = x^3 - y^3 := by
  ring
```
TODO

```lean
lemma abs_pow_lt_one_of_abs_lt_one {R : Type} [LinearOrderedRing R]
    {a : R} (ha : |a| < 1) {n : ℕ} (hn : n ≠ 0) :
    |a ^ n| < 1 :=
  abs_pow a n ▸ pow_lt_one (abs_nonneg a) ha hn
```
TODO

In `Mathlib/Data/Real/Irrational.lean`:
```lean
def Irrational (x : ℝ) :=
  x ∉ Set.range ((↑) : ℚ → ℝ)

theorem irrational_sqrt_two : Irrational (√2) := by
  simpa using Nat.prime_two.irrational_sqrt
```
TODO

In `Mathlib/Analysis/Complex/Polynomial/Basic.lean`:
```lean
theorem exists_root {f : ℂ[X]} (hf : 0 < degree f) : ∃ z : ℂ, IsRoot f z := by
  by_contra! hf'
  /- Since `f` has no roots, `f⁻¹` is differentiable. And since `f` is a polynomial, it tends to
  infinity at infinity, thus `f⁻¹` tends to zero at infinity. By Liouville's theorem, `f⁻¹ = 0`. -/
  have (z : ℂ) : (f.eval z)⁻¹ = 0 :=
    (f.differentiable.inv hf').apply_eq_of_tendsto_cocompact z <|
      Metric.cobounded_eq_cocompact (α := ℂ) ▸ (Filter.tendsto_inv₀_cobounded.comp <| by
        simpa only [tendsto_norm_atTop_iff_cobounded]
          using f.tendsto_norm_atTop hf tendsto_norm_cobounded_atTop)
  -- Thus `f = 0`, contradicting the fact that `0 < degree f`.
  obtain rfl : f = C 0 := Polynomial.funext fun z ↦ inv_injective <| by simp [this]
  simp at hf
```
TODO

In `Mathlib/Analysis/InnerProductSpace/Basic.lean`:
```lean
theorem norm_inner_le_norm {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (x y : E) :
    ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  rw [norm_eq_sqrt_inner (𝕜 := 𝕜) x, norm_eq_sqrt_inner (𝕜 := 𝕜) y]
  letI : PreInnerProductSpace.Core 𝕜 E := PreInnerProductSpace.toCore
  exact InnerProductSpace.Core.norm_inner_le_norm x y
```
TODO
