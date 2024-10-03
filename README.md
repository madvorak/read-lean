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
The declaration is made of similar parts to the previous.
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
One thing to keep in mind is that, once you publish a lemma about a matrix with rows indexed by {0, 1, 2, 3},
the user cannot directly apply the lemma to a matrix with rows indexed by {dog, cat, fox, owl}.
Therefore, lemmas about matrices usually come with a type argument saying "this is the set of indices and it must be finite".

It is time to explain the difference between `(term : type)` and `{term : type}` in declarations.
The former is an explicit argument (which is supposed to be written when calling the lemma).
The latter is an implicit argument (it is automatically inferred from other arguments when calling the lemma,
unless the user writes `@` to make all arguments explicit).
It is especially important to distinguish between explicit arguments and implicit arguments in definitions.
If we declare a function `def foo {x y : ℝ} (z : ℝ) (hxy : x < y) :` followed by a type of the output
and the body, calling it as `foo 3 myproof` means that `z` is the real number `3` and that the values of `x` and `y`
are inferred from the argument `myproof` which carries the information that `x` is less than `y`
(and thereby makes their values possible to infer).

The following theorem in `Mathlib/Data/Real/Irrational.lean` says that `√2` is an irrational number.
Let us first check the definition.
We don't define "irrational numbers" as a set; we define "being irrational" as a predicate
(which is essentially the same thing – both for Lean and for us).
```lean
def Irrational (x : ℝ) :=
  x ∉ Set.range ((↑) : ℚ → ℝ)

theorem irrational_sqrt_two : Irrational (√2) := by
  simpa using Nat.prime_two.irrational_sqrt
```
We would like to define irrationals numbers to be the set difference $ℝ - ℚ$.
Unfortunately, we cannot quite write it this way in Lean.
Lean isn't based on set theory; Lean uses type theory.
Therefore, we cannot say that rational numbers are a subset of real numbers; for example,
the rational number `5` and the real number `5` are of different types.
Instead, rational numbers are embedded in real numbers (each rational number corresponds to a unique real number).
In our example, the operator `↑` denotes this embedding (in fact, it could denote several other embeddings,
thus the explicit type annotation `ℚ → ℝ` is necessary).
We see that `x` is irrational iff `x` isn't in the range of the embedding function, i.e,
`x` is a real number that doesn't correspond to any rational number.
We check that it agrees with our intuition what "being irrational" means and go on.
* `theorem` ... keyword
* `irrational_sqrt_two` ... the name of the theorem being declared
* `:` here comes what the theorem says
* `Irrational (√2)` ... the square root of two is irrational
* `:=` ... here comes the proof
* `by` ... the proof will be done by tactic(s)
* `simpa using Nat.prime_two.irrational_sqrt` ... we utilize a theorem "two is a prime" and a theorem "square root of a prime is irrational"

Note that the theorem `irrational_sqrt_two` has no arguments; it says exactly one thing: `√2` is irrational.
Again, it isn't important what the proof is; Lean checks that the proof is correct.

Let's have a look at a more complicated theorem. In `Mathlib/Analysis/Complex/Polynomial/Basic.lean`:
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

This is the fundamental theorem of algebra!
* `theorem` ... keyword
* `exists_root` ... the name of the theorem being declared
* `{f : ℂ[X]}` ... argument `f` that is a complex polynomial in single variable `X`
* `(hf : 0 < degree f)` ... assumption that the degree of `f` is strictly positive
* `:` here comes what the theorem says
* `∃ z : ℂ, IsRoot f z` ... there is a complex number `z` that is a root of `f`
* `:=` ... here comes the proof

Then a rather complicated proof follows.
Note that `--` starts a single-line comment whereäs `/- comment -/` can be of any length.
As we already know, nothing after `:=` needs to be read by us if we want to use the theorem
or just be informed what theorem has been formally verified.

Let's review one more theorem theorem. In `Mathlib/Analysis/InnerProductSpace/Basic.lean`:
```lean
theorem norm_inner_le_norm {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (x y : E) :
    ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  rw [norm_eq_sqrt_inner (𝕜 := 𝕜) x, norm_eq_sqrt_inner (𝕜 := 𝕜) y]
  letI : PreInnerProductSpace.Core 𝕜 E := PreInnerProductSpace.toCore
  exact InnerProductSpace.Core.norm_inner_le_norm x y
```

This is the Cauchy-Schwarz inequality!
* `theorem` ... keyword
* `norm_inner_le_norm` ... the name of the theorem being declared
* `{𝕜 E : Type*}` ... the theorem uses some types `𝕜` and `E`
* `[RCLike 𝕜]` ... `𝕜` is either ℝ or ℂ
* `[SeminormedAddCommGroup E]` ... `E` forms an abelian group with a pseudometric space structure
* `[InnerProductSpace 𝕜 E]` ... `E` forms a vector space over `𝕜`, with an inner product that induces the norm
* `(x y : E)` ... the only explicit arguments of this theorem (everything else should be inferred from them when the theorem is used)
* `:` here comes what the theorem says
* `‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖` ... the norm of the inner product of two vectors is less or equal to the product of respective norms
* `:=` ... here comes the proof
