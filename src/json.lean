import tactic.basic

namespace json

universe u

inductive value : Type
| null
| bool   : bool → value
| string : string → value
| number : int → value
| array  : list value → value
| object : list (string × value) → value

#check value.bool true
#check value.bool false
#check value.array [value.null, value.bool true]

structure parser (α : Type u) := (
  runParser : list char → option (list char × α)
)

def fmap {α β : Type u} (f : α → β) : parser α → parser β
| ⟨ p ⟩ := parser.mk $ λ input, do
  (input', a) ← p input,
  some (input', f a)

instance : functor parser := {
  map := @json.fmap
}

def pure {α : Type u} (a : α) : parser α :=
  parser.mk $ λ input, some (input, a)

def seq {α β : Type u} : parser (α → β) → parser α → parser β
| ⟨ p1 ⟩ ⟨ p2 ⟩ := parser.mk $ λ input, do
  (input', f) ← p1 input,
  (input'', a) ← p2 input',
  some (input'', f a)

instance : applicative parser := {
  pure := @json.pure,
  seq := @json.seq,
}

section parsers

def char_p (c : char) : parser char :=
  parser.mk $ λ input,
  match input with
  | (x::xs) := if x = c then some (xs, x) else none
  | _       := none
  end

#eval parser.runParser (char_p 'n') "nice".to_list
#eval parser.runParser (char_p 'n') "".to_list

end parsers

end json
