-- Chapter 3

variables p q r s: Prop

-- #check p → q → p ∧ q
-- #check ¬p → p ↔ false
-- #check p ∨ q → q ∧ p

-- commutativity of ∧ and ∨
theorem and_comm_ : p ∧ q ↔ q ∧ p :=
iff.intro
  (assume hpq : p ∧ q,
    show q ∧ p, from ⟨(and.right hpq), (and.left hpq)⟩)
  (assume hqp : q ∧ p,
    show p ∧ q, from ⟨(and.right hqp), (and.left hqp)⟩)

theorem or_comm_ : p ∨ q ↔ q ∨ p :=
iff.intro
  (assume hpq: p ∨ q,
    hpq.elim
      (assume hp:p, or.inr hp)
      (assume hq:q, or.inl hq))
  (assume hqp: q ∨ p,
    hqp.elim
      (assume hq:q, or.inr hq)
      (assume hp:p, or.inl hp))

-- associativity of ∧ and ∨
theorem and_assoc_ : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
iff.intro
  (assume h : (p ∧ q) ∧ r,
    show p ∧ (q ∧ r), from ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
  (assume h : p ∧ (q ∧ r),
      show (p ∧ q) ∧ r, from ⟨⟨h.left, h.right.left⟩,h.right.right⟩)

theorem or_assoc_ : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
iff.intro
  (assume h: (p ∨ q) ∨ r,
    or.elim h
      (assume hpq : p ∨ q,
        show p ∨ (q ∨ r),
        from hpq.elim
          (assume hp : p, or.inl hp)
          (assume hq : q, or.inr (or.inl hq)))
      (assume hr : r,
        show p ∨ (q ∨ r),
        from or.inr (or.inr hr)))
  (assume h: p ∨ (q ∨ r),
    or.elim h
    (assume hp : p,
      show (p ∨ q) ∨ r,
      from or.inl (or.inl hp))
    (assume hqr : q ∨ r,
      or.elim hqr
      (assume hq : q,
        show (p ∨ q) ∨ r,
        from or.inl (or.inr hq))
      (assume hr : r,
        show (p ∨ q) ∨ r,
        from or.inr hr)))

-- distributivity
theorem and_to_or_dist : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
iff.intro
  (assume h : p ∧ (q ∨ r),
    show (p ∧ q) ∨ (p ∧ r),
    from or.elim h.right
      (assume hq : q, or.inl ⟨h.left,hq⟩)
      (assume hr : r, or.inr ⟨h.left,hr⟩))
  (assume h :(p ∧ q) ∨ (p ∧ r),
      show p ∧ (q ∨ r),
      from or.elim h
        (assume hpq : p ∧ q, and.intro hpq.left (or.inl hpq.right))
        (assume hpr : p ∧ r, and.intro hpr.left (or.inr hpr.right)))

theorem or_to_and_dist : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
iff.intro
  (assume h : p ∨ (q ∧ r),
    show (p ∨ q) ∧ (p ∨ r),
    from h.elim
      (assume hp : p, and.intro (or.inl hp) (or.inl hp))
      (assume hqr : q ∧ r, and.intro (or.inr hqr.left) (or.inr hqr.right)))
  (assume h : (p ∨ q) ∧ (p ∨ r),
    show p ∨ (q ∧ r), from
    have hpq : p ∨ q, from h.left,
    have hpr : p ∨ r, from h.right,
    hpq.elim
      (assume hp : p, or.inl hp)
      (assume hq : q,
        hpr.elim
          (assume hp : p, or.inl hp)
          (assume hr : r, or.inr ⟨hq, hr⟩)))

-- other properties
-- exportation name comes from book 'Modern Formal Logic', McKay
theorem exportation : (p → (q → r)) ↔ (p ∧ q → r) :=
iff.intro
  (assume h : p → (q → r),
    assume hpq : p ∧ q,
      h hpq.left hpq.right)
  (assume h : p ∧ q → r,
    assume hp : p,
      assume hq : q,
        h ⟨hp, hq⟩)


-- resorting to numbering, who knows what these should be called
theorem t1 : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
iff.intro
  (assume h : (p ∨ q) → r,
    show (p → r) ∧ (q → r),
    from and.intro
      (assume hp : p,
        h (or.inl hp))
      (assume hq : q,
        h (or.inr hq)))
  (assume h : (p → r) ∧ (q → r),
    show (p ∨ q) → r,
    from assume hpq : p ∨ q,
      hpq.elim
        (assume hp : p,
          have hr : r, from h.left hp, hr)
        (assume hq : q,
          have hr : r, from h.right hq, hr))

-- DeMorgan's laws
theorem dem1 : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
iff.intro
  (assume h : ¬(p ∨ q),
    show ¬p ∧ ¬q,
    from and.intro
      (show ¬p, from assume hp : p, absurd (or.inl hp) h)
      (show ¬q, from assume hq : q, absurd (or.inr hq) h))
  (assume h : ¬p ∧ ¬q,
    show ¬(p ∨ q),
    from assume hpq : p ∨ q,
    show false, from hpq.elim
        (assume hp : p, absurd hp h.left)
        (assume hq : q, absurd hq h.right))

theorem dem2 : ¬p ∨ ¬q → ¬(p ∧ q) :=
assume h : ¬p ∨ ¬q,
  assume hpq : p ∧ q, h.elim
    (assume hnp : ¬p, absurd hpq.left hnp)
    (assume hnq : ¬q, absurd hpq.right hnq)

theorem paradox : ¬(p ∧ ¬p) :=
assume h : p ∧ ¬p, absurd h.left h.right

theorem t2: p ∧ ¬q → ¬(p → q) :=
assume h : p ∧ ¬q,
  assume hptq : p → q,
  have hq : q, from hptq h.left,
  show false, from absurd hq h.right

theorem t3 : ¬p → (p → q) :=
assume h : ¬p,
  assume hp : p,
    false.elim (h hp)

theorem t4 : (¬p ∨ q) → (p → q) :=
assume h : ¬p ∨ q,
  assume hp : p, h.elim
    (assume hnp : ¬p, absurd hp hnp)
    (assume hq : q, hq)

theorem t5 : p ∨ false ↔ p :=
iff.intro
  (assume h : p ∨ false,
    h.elim (λ hp, hp) (λ false, false.elim))
  (assume p,
    or.inl p)

theorem t6 : p ∧ false ↔ false :=
iff.intro
  (assume h : p ∧ false, h.right)
  (assume false, false.elim)

theorem t7 : ¬(p ↔ ¬p) :=
assume h : p ↔ ¬p,
  have hnp : p → false, from
    assume hp : p, have hnp : ¬p, from h.mp hp, absurd hp hnp,
  absurd (h.mpr hnp) hnp

-- helper function, modus tollens
theorem modus_tollens : (p → q) → ¬q → ¬p :=
assume h : p → q,
  assume hnq : ¬q,
    assume hp : p, absurd (h hp) hnq

theorem t8 : (p → q) → (¬q → ¬p) :=
assume h : p → q,
  assume hnq : ¬q, (modus_tollens p q) h hnq

-- classical section:
open classical

-- variables p q r s : Prop

theorem c1 : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
assume h : p → r ∨ s,
or.elim (em p)
  (assume hp : p,
  show ((p → r) ∨ (p → s)), from
    have hrs : r ∨ s, from h hp,
      hrs.elim
      (assume hr : r,
        suffices hpr : p → r,
        from or.inl hpr,
        assume hp : p, hr)
      (assume hs : s,
        suffices hps : p → s,
        from or.inr hps,
        assume hp: p, hs))
  (assume hnp : ¬p,
  show ((p → r) ∨ (p → s)), from
    suffices hpr : p → r, from or.inl hpr,
      assume hp : p, absurd hp hnp)

theorem c2 : ¬(p ∧ q) → ¬p ∨ ¬q :=
assume h : ¬(p ∧ q),
show ¬p ∨ ¬q, from
or.elim (em p)
  (assume hp : p,
    or.elim (em q)
    (assume hq : q,
      absurd (and.intro hp hq) h)
    (assume hnq : ¬q,
      or.inr hnq))
  (assume hnp : ¬p,
    or.inl hnp)

theorem c3 : ¬(p → q) → p ∧ ¬q :=
assume h : ¬(p → q),
show p ∧ ¬q, from
or.elim (em p)
  (assume hp : p,
    or.elim (em q)
      (assume hq : q,
        have hptq : p → q, from assume hp : p, hq,
        absurd hptq h)
      (assume hnq : ¬q,
        and.intro hp hnq))
  (assume hnp : ¬p,
    or.elim (em q)
      (assume hq : q,
        have hptq : p → q, from assume hp : p, hq,
        absurd hptq h)
      (assume hnq : ¬q,
        suffices hptq : p → q, from false.elim (h hptq),
        assume hp : p, absurd hp hnp))

theorem c4 : (p → q) → (¬p ∨ q) :=
assume h : p → q,
show (¬p ∨ q), from
or.elim (em p)
  (assume hp : p,
    or.elim (em q)
      (assume hq : q,
        or.inr hq)
      (assume hnq : ¬q,
        have hq : q, from h hp,
        absurd hq hnq))
  (assume hnp : ¬p,
    or.elim (em q)
      (assume hq : q,
        or.inr hq)
      (assume hnq : ¬q,
        or.inl hnp))


theorem c5 : (¬q → ¬p) → (p → q) :=
assume h : (¬q → ¬p),
show p → q, from
or.elim (em q)
  (assume hq : q,
    or.elim (em p)
      (assume hp : p,
        (assume hp : p, hq))
      (assume hnp : ¬p,
        (assume hp : p, hq)))
  (assume hnq : ¬q,
    or.elim (em p)
      (assume hp : p,
        have hnp : ¬p, from h hnq,
        absurd hp hnp)
      (assume hnp : ¬p,
        (assume hp : p,
        absurd hp hnp)))

theorem c6 : p ∨ ¬p :=
or.elim (em p)
  (assume hp : p,
    or.inl hp)
  (assume hnp : ¬p,
      or.inr hnp)

theorem c7 : (((p → q) → p) → p) :=
assume h : ((p → q) → p),
show p, from
or.elim (em p)
  (assume hp : p, hp)
  (assume hnp : ¬p,
    have hptq : p → q, from assume hp : p, absurd hp hnp,
  absurd (h hptq) hnp)
