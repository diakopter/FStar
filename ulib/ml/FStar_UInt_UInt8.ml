type uint8 = int
type byte = uint8

let (%) x y = if x < 0 then (x mod y) + y else x mod y

let v (x:uint8) : Prims.int = Prims.parse_int (string_of_int x)

let zero = 0
let one = 1
let ones = 255
                                              
let add (a:uint8) (b:uint8) : uint8 = a + b
let add_underspec a b = add a b
let add_mod a b = (add a b) land 255

let sub (a:uint8) (b:uint8) : uint8 = a - b
let sub_underspec a b = sub a b
let sub_mod a b = (sub a b) land 255

let mul (a:uint8) (b:uint8) : uint8 = a * b
let mul_underspec a b = mul a b
let mul_mod a b = (mul a b) land 255

let div (a:uint8) (b:uint8) : uint8 = a / b

let rem (a:uint8) (b:uint8) : uint8 = a mod b

let logand (a:uint8) (b:uint8) : uint8 = a land b
let logxor (a:uint8) (b:uint8) : uint8 = a lxor b
let logor  (a:uint8) (b:uint8) : uint8 = a lor b
let lognot (a:uint8) : uint8 = lnot a
       
let int_to_uint8 (x:Prims.int) : uint8 = int_of_string (Prims.to_string x) % 256

let shift_right (a:uint8) (b:uint8) : uint8 = a lsr b
let shift_left  (a:uint8) (b:uint8) : uint8 = (a lsl b) land 255

(* Comparison operators *)
let eq (a:uint8) (b:uint8) : bool = a = b
let gt (a:uint8) (b:uint8) : bool = a > b
let gte (a:uint8) (b:uint8) : bool = a >= b
let lt (a:uint8) (b:uint8) : bool = a < b
let lte (a:uint8) (b:uint8) : bool =  a <= b

(* Infix notations *)
let op_Hat_Plus = add
let op_Hat_Plus_Question = add_underspec
let op_Hat_Plus_Percent = add_mod
let op_Hat_Subtraction = sub
let op_Hat_Subtraction_Question = sub_underspec
let op_Hat_Subtraction_Percent = sub_mod
let op_Hat_Star = mul
let op_Hat_Star_Question = mul_underspec
let op_Hat_Star_Percent = mul_mod
let op_Hat_Slash = div
let op_Hat_Percent = rem
let op_Hat_Hat = logxor  
let op_Hat_Amp = logand
let op_Hat_Bar = logor
let op_Hat_Less_Less = shift_left
let op_Hat_Greater_Greater = shift_right
let op_Hat_Equal = eq
let op_Hat_Greater = gt
let op_Hat_Greater_Equal = gte
let op_Hat_Less = gt
let op_Hat_Less_Equal = gte

let to_string s = string_of_int s
