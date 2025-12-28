/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers


example : Odd (-3 : ℤ) := by
  dsimp [Odd]
  use -2
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (7 * k + 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] at *
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + a + 3 * b + 1
  calc
    x * y + 2 * y = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    _ = 4 * a * b + 2 * a + 2 * b + 4 * b + 3 := by ring
    _ = 2 * (2 * a * b + a + 3 * b + 1) + 1 := by ring

example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  dsimp [Odd, Even] at *
  obtain ⟨k, hk⟩ := hm
  use 3 * k - 1
  calc
    3 * m - 5 = 3 * (2 * k + 1) - 5 := by rw[hk]
    _ = 2 * (3 * k - 1) := by ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Odd, Even] at *
  obtain ⟨k, hk⟩ := hn
  use 2 * k ^ 2 + 2 * k - 3
  calc
    n ^ 2 + 2 * n - 5 = (2 * k) ^ 2 + 2 * (2 * k) - 5 := by rw[hk]
    _ = 2 * (2 * k ^ 2 + 2 * k - 3) + 1 := by ring

example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Odd (-9 : ℤ) := by
  dsimp [Odd]
  use -5
  calc
    -9 = 2 * (-5) + 1 := by numbers

example : Even (26 : ℤ) := by
  dsimp [Even]
  use 13
  calc
    26 = 2 * 13 := by numbers

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  dsimp [Odd, Even] at *
  obtain ⟨mk, hmk⟩ := hm
  obtain ⟨nk, hnk⟩ := hn
  use nk + mk
  calc
    n + m = (2 * nk) + (2 * mk + 1) := by rw[hnk, hmk]
    _ = 2 * (nk + mk) + 1 := by ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  dsimp [Odd, Even] at *
  obtain ⟨pk, hpk⟩ := hp
  obtain ⟨qk, hqk⟩ := hq
  use pk - qk - 2
  calc
    p - q - 4 = (2 * pk + 1) - (2 * qk) - 4 := by rw[hpk, hqk]
    _ = 2 * (pk - qk - 2) + 1 := by ring

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  dsimp [Odd, Even] at *
  obtain ⟨ak, hak⟩ := ha
  obtain ⟨bk, hbk⟩ := hb
  use 3 * ak + bk - 1
  calc
    3 * a + b - 3 = 3 * (2 * ak) + (2 * bk + 1) - 3 := by rw[hak, hbk]
    _ = 2 * (3 * ak + bk - 1) := by ring

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  dsimp [Odd, Even] at *
  obtain ⟨rk, hrk⟩ := hr
  obtain ⟨sk, hsk⟩ := hs
  use 3 * rk - 5 * sk - 1
  calc
    3 * r - 5 * s = 3 * (2 * rk + 1) - 5 * (2 * sk + 1) := by rw [hrk, hsk]
    _ = 2 * (3 * rk - 5 * sk - 1) := by ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  dsimp [Odd] at *
  obtain ⟨xk, hxk⟩ := hx
  use 4 * xk ^ 3 + 6 * xk ^ 2 + 3 * xk
  calc
    x ^ 3 = (2 * xk + 1) ^ 3 := by rw[hxk]
    _ = (2 * xk) ^ 3 + 3 * (2 * xk) ^ 2 + 3 * (2 * xk) + 1 := by ring
    _ = 2 * (4 * xk ^ 3 + 6 * xk ^ 2 + 3 * xk) + 1 := by ring

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  dsimp [Odd, Even] at *
  obtain ⟨nk, hnk⟩ := hn
  use 2 * nk ^ 2 - nk
  calc
    n ^ 2 - 3 * n + 2 = (2 * nk + 1) ^ 2 - 3 * (2 * nk + 1) + 2 := by rw[hnk]
    _ = 4 * nk ^ 2 + 4 * nk + 1 - 6 * nk - 3 + 2 := by ring
    _ = 2 * (2 * nk ^ 2 - nk) := by ring

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  dsimp [Odd] at *
  obtain ⟨ak, hak⟩ := ha
  use 2 * ak ^ 2 + 4 * ak - 1
  calc
    a ^ 2 + 2 * a - 4 = (2 * ak + 1)^2 + 2 * (2 * ak + 1) - 4 := by rw[hak]
    _ = 4 * ak ^ 2 + 4 * ak + 1 + 4 * ak + 2 - 4 := by ring
    _ = 2 * (2 * ak ^ 2 + 4 * ak - 1) + 1 := by ring

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  dsimp [Odd] at *
  obtain ⟨pk, hpk⟩ := hp
  use 2 * pk ^ 2 + 5 * pk - 1
  calc
    p ^ 2 + 3 * p - 5 = (2 * pk + 1) ^ 2 + 3 * (2 * pk + 1) - 5 := by rw[hpk]
    _ = 4 * pk ^ 2 + 4 * pk + 1 + 6 * pk + 3 - 5 := by ring
    _ = 2 * (2 * pk ^ 2 + 5 * pk - 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  dsimp [Odd] at *
  obtain ⟨xk, hxk⟩ := hx
  obtain ⟨yk, hyk⟩ := hy
  use 2 * xk * yk + xk + yk
  calc
    x * y = (2 * xk + 1) * (2 * yk + 1) := by rw[hxk, hyk]
    _ = 4 * xk * yk + 2 * xk + 2 * yk + 1 := by ring
    _ = 2 * (2 * xk * yk + xk + yk) + 1 := by ring

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  dsimp [Odd]
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨k, hk⟩ := hn
    use 6 * k ^ 2 + 3 * k - 1
    calc
      3 * n ^ 2 + 3 * n - 1 = 3 * (2 * k) ^ 2 + 3 * (2 * k) - 1 := by rw[hk]
      _ = 2 * (6 * k ^ 2 + 3 * k - 1) + 1 := by ring
  · obtain ⟨k, hk⟩ := hn
    use 6 * k ^ 2 + 9 * k + 2
    calc
      3 * n ^ 2 + 3 * n - 1 = 3 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 1 := by rw[hk]
      _ = 2 * (6 * k ^ 2 + 9 * k + 2) + 1 := by ring

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  dsimp [Odd]
  obtain hn | hn := Int.even_or_odd n
  · dsimp [Even] at hn
    use n + 1
    obtain ⟨k, hk⟩ := hn
    constructor
    extra
    use k
    calc
      n + 1 = n + 1 := by rfl
      _ = 2 * k + 1 := by rw[hk]
  · dsimp [Odd] at hn
    use (n + 2)
    obtain ⟨k, hk⟩ := hn
    constructor
    extra
    use k + 1
    calc
      n + 2 = n + 2 := by rfl
      _ = 2 * k + 1 + 2 := by rw[hk]
      _ = 2 * (k + 1) + 1 := by ring

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha | ha := Int.even_or_odd a
  · obtain hb | hb := Int.even_or_odd b
    · dsimp [Odd, Even] at *
      left
      obtain ⟨ak, hak⟩ := ha
      obtain ⟨bk, hbk⟩ := hb
      use ak - bk
      calc
        a - b = (2 * ak) - (2 * bk) := by rw[hak, hbk]
        _ = 2 * (ak - bk) := by ring
    · obtain hc | hc := Int.even_or_odd c
      · right
        left
        obtain ⟨ak, hak⟩ := ha
        obtain ⟨ck, hck⟩ := hc
        use ak + ck
        calc
          a + c = (2 * ak) + (2 * ck) := by rw[hak, hck]
          _ = 2 * (ak + ck) := by ring
      · right
        right
        obtain ⟨bk, hbk⟩ := hb
        obtain ⟨ck, hck⟩ := hc
        use bk - ck
        calc
          b - c = (2 * bk + 1) - (2 * ck + 1) := by rw[hbk, hck]
          _ = 2 * (bk - ck) := by ring
  · obtain hb | hb := Int.even_or_odd b
    · obtain hc | hc := Int.even_or_odd c
      · right
        right
        obtain ⟨bk, hbk⟩ := hb
        obtain ⟨ck, hck⟩ := hc
        use bk - ck
        calc
          b - c = (2 * bk) - (2 * ck) := by rw[hbk, hck]
          _ = 2 * (bk - ck) := by ring
      · right
        left
        obtain ⟨ak, hak⟩ := ha
        obtain ⟨ck, hck⟩ := hc
        use ak + ck + 1
        calc
          a + c = (2 * ak + 1) + (2 * ck + 1) := by rw[hak, hck]
          _ = 2 * (ak + ck + 1) := by ring
    · obtain hc | hc := Int.even_or_odd c
      · left
        obtain ⟨ak, hak⟩ := ha
        obtain ⟨bk, hbk⟩ := hb
        use ak - bk
        calc
          a - b = (2 * ak + 1) - (2 * bk + 1) := by rw[hak, hbk]
          _ = 2 * (ak - bk) := by ring
      · right
        right
        obtain ⟨bk, hbk⟩ := hb
        obtain ⟨ck, hck⟩ := hc
        use bk - ck
        calc
          b - c = (2 * bk + 1) - (2 * ck + 1) := by rw[hbk, hck]
          _ = 2 * (bk - ck) := by ring
