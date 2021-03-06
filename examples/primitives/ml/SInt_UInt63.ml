let n = 63
type uint63 = int
type native_int = uint63

let (zero:uint63) = 0
let (one:uint63) = 1
let (ones:uint63) = -1

let bits = 63

(* Standard operators *)
let add a b = a + b
let add_mod a b = a + b
let sub a b = a - b
let sub_mod a b = a - b
let mul a b = a * b
let mul_mod a b = a * b
let div a b = a / b
let rem a b = a mod b

let logand a b = a land b
let logxor a b = a lxor b
let logor a b = a lor b
let lognot a = lnot a

let shift_left a s = a lsl s
let shift_right a s = a lsr s

let rotate_left a s = (a lsl s) + (a lsr (63-s))
let rotate_right a s = (a lsl (63-s)) + (a lsr s)

(*
val to_uint63: sint -> Tot uint63
let to_uint63 s = to_usint n s
 *)
                                          
let op_Hat_Plus = add
let op_Hat_Subtraction = sub
let op_Hat_Star = mul
let op_Hat_Slash = div
let op_Hat_Less_Less = shift_left
let op_Hat_Greater_Greater = shift_right
let op_Hat_Amp = logand
let op_Hat_Bar = logor
let op_Hat_Hat = logxor


let of_uint32 s = s

(* TODO *)
let eq x y = if x = y then -1 else 0
let gte x y = if x >= y then -1 else 0

