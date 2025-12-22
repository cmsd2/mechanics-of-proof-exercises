/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by rel [hn]
    _ < 2 := by numbers
  apply ne_of_gt
  calc
    n ^ 2 ≥ 2 ^ 2 := by rel [hn]
    _ > 2 := by numbers


example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h2a | h2b := h2
  · left
    addarith [h2a]
  · right
    addarith [h2b]

example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]


/-! # Exercises -/


example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain hx | hx := h
  · calc
      x ^ 2 + 1
        =  4 ^ 2 + 1 := by rw [hx]
      _ = 17 := by numbers
  · calc
      x ^ 2 + 1
        = (-4) ^ 2 + 1 := by rw [hx]
      _ = 17 := by numbers

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain hx | hx := h
  · calc
      x ^ 2 - 3 * x + 2
        = 1 ^ 2 - 3 * 1 + 2 := by rw [hx]
      _ = 0 := by numbers
  · calc
      x ^ 2 - 3 * x + 2
        = 2 ^ 2 - 3 * 2 + 2 := by rw [hx]
      _ = 0 := by numbers

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain hx | hx := h
  · calc
      t ^ 2 - t - 6
        = (-2) ^ 2 - (-2) - 6 := by rw[hx]
      _ = 0 := by numbers
  · calc
      t ^ 2 - t - 6
        = 3 ^ 2 - 3 - 6 := by rw[hx]
      _ = 0 := by numbers

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain hx | hx := h
  · calc
      x * y + 2 * x
        = 2 * y + 2 * 2 := by rw[hx]
      _ = 2 * y + 4 := by ring
  · calc
      x * y + 2 * x
        = x * (-2) + 2 * x := by rw[hx]
      _ = 0 := by ring
      _ = 2 * y - 2 * y := by ring
      _ = 2 * y - 2 * (-2) := by rw[hx]
      _ = 2 * y + 4 := by ring

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  addarith [h]

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  addarith [h]

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  left
  calc
    y / 2 = x + 1 / 2 := by addarith[h]
    _ > x := by extra

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h1 :=
  calc
    (x + 3) * (x - 1)
      = x ^ 2 + 2 * x - 3 := by ring
    _ = 0 := by rw[hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h3a | h3b := h2
  · left
    addarith [h3a]
  · right
    addarith [h3b]

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have h1 :=
  calc
    (a - b) * (a - 2 * b)
      = a ^ 2 + 2 * b ^ 2 - 3 * a * b := by ring
    _ = 0 := by addarith[hab]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h3 | h3 := h2
  · left
    addarith [h3]
  · right
    addarith [h3]

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h1 :=
  calc
    (t ^ 2) * (t - 1)
      = t ^ 3 - t ^ 2 := by ring
    _ = 0 := by addarith[ht]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h3 | h3 := h2
  · right
    cancel 2 at h3
  · left
    addarith[h3]

example {n : ℕ} : n ^ 2 ≠ 7 := by
  have hn := le_or_succ_le n 2
  obtain hn | hn := hn
  apply ne_of_lt
  calc
    n ^ 2 ≤ 2 ^ 2 := by rel[hn]
    _ < 7 := by numbers
  apply ne_of_gt
  calc
    n ^ 2 ≥ 3 ^ 2 := by rel[hn]
    _ > 7 := by numbers

example {x : ℤ} : 2 * x ≠ 3 := by
  have hx := le_or_succ_le x 1
  obtain hx | hx := hx
  apply ne_of_lt
  calc
    2 * x ≤ 2 * 1 := by rel[hx]
    _ < 3 := by numbers
  apply ne_of_gt
  calc
    2 * x ≥ 2 * 2 := by rel[hx]
    _ > 3 := by numbers

example {t : ℤ} : 5 * t ≠ 18 := by
  have ht := le_or_succ_le t 3
  obtain ht | ht := ht
  apply ne_of_lt
  calc
    5 * t ≤ 5 * 3 := by rel[ht]
    _ < 18 := by numbers
  apply ne_of_gt
  calc
    5 * t ≥ 5 * 4 := by rel[ht]
    _ > 18 := by numbers

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  have hm := le_or_succ_le m 5
  obtain hm | hm := hm
  apply ne_of_lt
  calc
    m ^ 2 + 4 * m ≤ 5 ^ 2 + 4 * 5 := by rel[hm]
    _ < 46 := by numbers
  apply ne_of_gt
  calc
    m ^ 2 + 4 * m ≥ 6 ^ 2 + 4 * 6 := by rel[hm]
    _ > 46 := by numbers
