-- Chapter 4

-- 1.
variables (α : Type) (p q : α → Prop)

-- naming:  eq = equivalence.
theorem eq1 : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
  (assume h : (∀ x, p x ∧ q x),
    and.intro
      (assume z : α, (h z).left)
      (assume z : α, (h z).right))
  (assume h : (∀ x, p x) ∧ (∀ x, q x),
    show (∀ x, p x ∧ q x), from
      assume z : α, and.intro (h.left z) (h.right z))


theorem eq2 : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
assume h₁ : (∀ x, p x → q x),
assume h₂ : (∀ x, p x),
  assume z : α, (h₁ z) (h₂ z)

theorem eq3 : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
assume h₁ : (∀ x, p x) ∨ (∀ x, q x),
assume z : α,
  or.elim h₁
    (assume hpx : (∀ x, p x), or.inl (hpx z))
    (assume hqx : (∀ x, q x), or.inr (hqx z))

-- 2.
-- variables (α : Type) (p q : α → Prop)
variable r : Prop
open classical

--naming: two{1,2,3}

theorem two1 : α → ((∀ x : α, r) ↔ r) :=
(assume z : α,
  iff.intro
    (assume h₁ : (∀ x : α, r), h₁ z)
    (assume hr : r, assume z : α, hr))

theorem two2 : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
iff.intro
  (assume h₁ : (∀ x, p x ∨ r),
    or.elim (em r)
      (assume hr : r,
        or.inr hr)
      (assume hnr : ¬r,
      -- this next bit took an hour. my god.
      or.inl (assume z : α,
        (h₁ z).elim
          (assume hpz : p z, hpz)
          (assume hr : r, absurd hr hnr))))
  (assume h₂ : (∀ x, p x) ∨ r,
    h₂.elim
      (assume hpx : ∀ x, p x,
        assume z : α, or.inl (hpx z))
      (assume hr : r,
        assume z : α, or.inr hr))

theorem two3 : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
iff.intro
  (assume h₁ : (∀ x, r → p x),
    show (r → ∀ x, p x), from
      assume hr : r,
      assume z : α,
      have hpz : p z, from (h₁ z) hr,
    hpz)
  (assume h₂ : (r → ∀ x, p x),
    show (∀ x, r → p x), from
      assume z : α,
      assume hr : r,
      have hpz : p z, from (h₂ hr) z,
      hpz)

-- 3. Barber Paradox
variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

-- theorem barber1 (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=



-- -- 4 / 5.
-- namespace hidden

-- def divides (m n : ℕ) : Prop := ∃ k, m * k = n

-- instance : has_dvd nat := ⟨divides⟩

-- def even (n : ℕ) : Prop := 2 ∣ n -- You can enter the '∣' character by typing \mid

-- section
--   variables m n : ℕ

--   #check m ∣ n
--   #check m^n
--   #check even (m^n +3)
-- end

-- end hidden

-- def prime (n : ℕ) : Prop := sorry

-- def infinitely_many_primes : Prop := sorry

-- def Fermat_prime (n : ℕ) : Prop := sorry

-- def infinitely_many_Fermat_primes : Prop := sorry

-- def goldbach_conjecture : Prop := sorry

-- def Goldbach's_weak_conjecture : Prop := sorry

-- def Fermat's_last_theorem : Prop := sorry


-- -- 6.
-- variables (real : Type) [ordered_ring real]
-- variables (log exp : real → real)
-- variable  log_exp_eq : ∀ x, log (exp x) = x
-- variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
-- variable  exp_pos    : ∀ x, exp x > 0
-- variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- -- this ensures the assumptions are available in tactic proofs
-- include log_exp_eq exp_log_eq exp_pos exp_add

-- example (x y z : real) :
--   exp (x + y + z) = exp x * exp y * exp z :=
-- by rw [exp_add, exp_add]

-- example (y : real) (h : y > 0)  : exp (log y) = y :=
-- exp_log_eq h

-- theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
--   log (x * y) = log x + log y :=
-- sorry


-- -- 7.
-- #check sub_self

-- example (x : ℤ) : x * 0 = 0 :=
-- sorry
