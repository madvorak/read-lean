# How to read Lean

Here we will teach you how to read math written in Lean.

Let's review an easy lemma we know from the middle school (even tho we probably didn't call it "lemma" back then).

```lean
lemma difference_of_cubes {R : Type} [CommRing R] (x y : R) :
    (x^2 + x*y + y^2) * (x - y) = x^3 - y^3 := by
  ring
```
Let's break it down!
* `lemma` ... keyword; means the same thing as `theorem`
* `difference_of_cubes` ... the name of the lemma being declared
* `{R : Type}` ... generic type parameter (there will be some terms of type `R` chosen by the user)
* `[CommRing R]` ... requirement that `R` must be a commutative ring
* `(x y : R)` ... `x` and `y` are arguments of type `R` (similar to writing $x, y \in R$ on paper)
* `:` here comes what the lemma says
* `(x^2 + x*y + y^2) * (x - y) = x^3 - y^3` ... the lemma says $(x^2 + x \cdot y + y^2) \cdot (x - y) = x^3 - y^3$
* `:=` ... here comes the proof
* `by` ... the proof will be done by tactic(s)
* `ring` ... the name of the tactic that generates the proof

The great thing about Lean is that you don't have to trust the implementation of the tactic `ring` in order to believe the result.
The tactic generates a proof in the underlying system, and the Lean core checks that the proof is a valid derivation in the system
using existing definitions and existing axioms.
If there is a bug in the implementation of the tactic `ring` that will lead to generating an incorrect proof, the proof will be
rejected by the Lean core and the user will be notified.
As a reader of math written in Lean, you are usually not equipped with a Lean compiler.
You will typically trust the author that they ran the code through the compiler and no errors were found.

Long story short, you can ignore everything after `:=` when you read a theorem written in Lean.
All you need to read to understand the lemma is
`{R : Type} [CommRing R] (x y : R) : (x^2 + x*y + y^2) * (x - y) = x^3 - y^3`
and possibly the definitions and notations used in the statement.

Let's have a look at another lemma!

```lean
lemma abs_pow_lt_one_of_abs_lt_one {R : Type} [LinearOrderedRing R]
    {a : R} (ha : |a| < 1) {n : ℕ} (hn : n ≠ 0) :
    |a ^ n| < 1 :=
  abs_pow a n ▸ pow_lt_one (abs_nonneg a) ha hn
```
The declaration is made of similar parts to the previous one.
* `lemma` ... keyword
* `abs_pow_lt_one_of_abs_lt_one` ... the name of the lemma being declared
* `{R : Type}` ... generic type parameter
* `[LinearOrderedRing R]` ... requirement that `R` must be a linearly ordered ring
* `{a : R}` ... argument $a \in R$
* `(ha : |a| < 1)` ... assumption $|a|<1$
* `{n : ℕ}` ... argument $n \in ℕ$
* `(hn : n ≠ 0)` ... assumption $n \neq 0$
* `:` here comes what the lemma says
* `|a ^ n| < 1` ... the lemma says $|a^n|<1$
* `:=` ... here comes the proof
* `abs_pow a n ▸ pow_lt_one (abs_nonneg a) ha hn` ... the proof

The proof refers to the names of the assumptions and uses existing lemmas.
As you already know, you can ignore the proof (whatever is written after `:=`), hence you can ignore the names `ha` and `hn` as well.

Note that the first lemma requires `CommRing` (a commutative ring, which needn't be ordered) whereäs the second lemma requires
`LinearOrderedRing` (a linearly ordered ring, where multiplication needn't be commutative).
In Lean, we like to make every lemma as general as possible.
A part of the reason is that we can make reasoning "by lemma XYZ" but not reasoning "by the proof of lemma XYZ" (as in "follow
the same steps that the proof of lemma XYZ uses but in a different setting").
One thing to keep in mind is that, once you publish a lemma about a matrix whose rows are indexed by {0, 1, 2, 3},
you cannot directly apply the lemma to a matrix whose rows indexed by {dog, cat, fox, owl}.
Therefore, lemmas about matrices usually come with a type argument saying "this is the set of indices and it must be finite".

It is time to explain the difference between `(term : type)` and `{term : type}` TODO.

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
