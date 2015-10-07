(*--build-config
  options:--verify_module Ex1 --codegen C;
  --*)

module Ex1

(* Monomorphization example *)

(* Type of pairs, written with a data constructor *)
type pair (a:Type) (b:Type) = | Pair: fst:a -> snd:b -> pair a b

(* Polymorphic function *)
val test_pair_1: #a:Type -> #b:Type -> x:a -> y:b -> Tot (pair a b)
let test_pair_1 x y =
  let res = Pair x y in
  res

(* Partially polymorphic function *)
val test_pair_2: #a:Type -> x:char -> y:a -> Tot (pair char a)
let test_pair_2 x y =
  let res = Pair x y in
  res

(* Non polymorphic function *)
val test_pair_3: x:char -> y:int -> Tot (pair char int)
let test_pair_3 x y =
  let res = Pair x y in
  res

(* Test function *)
val global_test: x:char -> y:int -> Tot int
let global_test x y =
  let z = x in
  let a1 = test_pair_1 x z in
  let a2 = test_pair_1 x y in
  let a3 = test_pair_2 x y in
  let a4 = test_pair_3 x y in
  let res = y in
  res

