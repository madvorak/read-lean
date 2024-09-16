import Mathlib.Tactic

lemma difference_of_cubes {R : Type} [CommRing R] (x y : R) :
    (x^2 + x*y + y^2) * (x - y) = x^3 - y^3 := by
  ring

lemma abs_pow_lt_one_of_abs_lt_one {R : Type} [LinearOrderedRing R]
    {a : R} (ha : |a| < 1) {n : ℕ} (hn : n ≠ 0) :
    |a ^ n| < 1 :=
  abs_pow a n ▸ pow_lt_one (abs_nonneg a) ha hn
