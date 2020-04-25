-- Chapter 2
def double (x:ℕ): ℕ := x+x

-- incorrectly notated in the book

-- 2.4

def do_twice {α: Type}(f: α → α) (x: α) := f (f x)

#check do_twice

#reduce do_twice double 3

def compose {α β γ : Type} (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

def Do_Twice {α: Type}(f:((α → α) → (α → α))) (g: α → α) (x : α) : α := f g (f g x)

#reduce Do_Twice do_twice double 5

def curry {α β γ : Type} (f : α × β → γ) : α → β → γ := λ x y, f(x,y)

def uncurry {α β γ : Type} (f: α → β → γ) :  α × β → γ := λ p, f p.1 p.2

#check uncurry

def ident {α : Type} := λ (x:α), x

#check ident double

#check list.append


namespace hidden

universe u

constant list   : Type u → Type u

constant cons   : Π α : Type u, α → list α → list α
constant nil    : Π α : Type u, list α
constant head   : Π α : Type u, list α → α
constant tail   : Π α : Type u, list α → list α
constant append : Π α : Type u, list α → list α → list α

end hidden


universe u
constant vec : Type u → ℕ → Type u

namespace vec
  constant empty : Π α : Type u, vec α 0
  constant cons :
    Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
  constant append :
    Π (α : Type u) (n m : ℕ),  vec α m → vec α n → vec α (n + m)

  -- exercises: vec_add, vec_reverse ↓
  constant vec_add :
    Π (α : Type u) (n : ℕ) ,  vec α n → vec α n → vec α n
  constant vec_reverse :
    Π (α : Type u) (n : ℕ) ,  vec α n → vec α n
end vec

-- matrix type def
constant matrix : Type → ℕ → ℕ → Type

namespace matrix
  constant matrix_add :
    Π {α : Type} {n m : ℕ},  matrix α n m → matrix α n m
  constant matrix_mul :
    Π {α : Type} {n m z: ℕ},  matrix α n m → matrix α m z → matrix α n z
end matrix
