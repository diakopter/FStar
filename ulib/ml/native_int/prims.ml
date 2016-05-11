include MkPrims.Make(struct

  type nonrec int = int
  let ( + ) = ( + )
  let ( - ) = ( - )
  let ( * ) = ( * )
  let ( / ) = ( / )
  let ( <= ) = ( <= )
  let ( >= ) = ( >= )
  let ( < ) = ( < )
  let ( > ) = ( > )
  let ( % ) = ( mod )
  let op_Minus x = - x
  let parse_int  = int_of_string
  let to_string = string_of_int
                    
end)
