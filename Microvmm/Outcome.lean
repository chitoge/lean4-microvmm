namespace Microvmm

inductive Outcome (ε : Type) (α : Type) where
  | error : ε → Outcome ε α
  | ok : α → Outcome ε α
deriving Repr, DecidableEq

namespace Outcome

def map (f : α → β) : Outcome ε α → Outcome ε β
  | .error err => .error err
  | .ok value => .ok (f value)

def bind (result : Outcome ε α) (next : α → Outcome ε β) : Outcome ε β :=
  match result with
  | .error err => .error err
  | .ok value => next value

instance {ε : Type} : Functor (Outcome ε) where
  map := map

instance {ε : Type} : Pure (Outcome ε) where
  pure := Outcome.ok

instance {ε : Type} : Seq (Outcome ε) where
  seq fs xs :=
    match fs with
    | .error err => .error err
    | .ok f => map f (xs ())

instance {ε : Type} : Bind (Outcome ε) where
  bind := bind

instance {ε : Type} : Applicative (Outcome ε) where
  pure := Pure.pure
  seq := Seq.seq
  map := Functor.map

instance {ε : Type} : Monad (Outcome ε) where
  pure := Pure.pure
  bind := Bind.bind
  map := Functor.map
  seq := Seq.seq

end Outcome

end Microvmm