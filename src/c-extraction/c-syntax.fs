module FStar.Extraction.C.Syntax

open FStar
open FStar.Absyn.Syntax

type t = list<module_t>

and module_t = 
    | C_FunctionDefinition of identifier_t * type_t * list<(identifier_t * type_t)>
    | C_TypeDecl of identifier_t * type_t * list<(identifier_t * type_t)>
    | C_FunctionDeclaration of identifier_t * type_t * list<(identifier_t * type_t)> * list<block_t>
    | C_GlobalVar of bool * identifier_t * type_t * option<value_t> // bool = extern ?
    
and primitive_t =
    | C_Char of byte
    | C_Int32 of int32 (* Number of bits *)
    | C_UInt32 of uint32
    | C_Int64 of int64
    | C_UInt64 of uint64

(* Other types *)
and type_t = 
    | C_Primitive of primitive_t
    | C_Structure of identifier_t * list<type_t>
    | C_Union of identifier_t * list<type_t>
    | C_Ptr of type_t
    | C_Void
    | C_Array of type_t * int // Number of elements
    | C_FunctionType of type_t * list<type_t> // Necessary ?

and identifier_t = string

and block_t =
    | C_LinearBlock of list<statement_t>
    | C_If of expr_t * block_t * block_t
    | C_While of expr_t * block_t
    | C_Switch of value_t (* integer constant *) * list<(value_t * block_t)>

and statement_t =
    | C_LocalVar of identifier_t * type_t
    | C_Assign of identifier_t * expr_t
    | C_VoidCall of identifier_t * list<value_t>
    | C_Alloc of identifier_t * int
    | C_Free of identifier_t
    | C_NestedBlock of block_t
    | C_Return of expr_t

and expr_t =
    | C_BinOp of binop_t
    | C_Cast of type_t * value_t
    | C_Call of identifier_t * list<value_t>
    | C_ArrayAccess of identifier_t * int
    | C_StructAccess of identifier_t // consider concatenation
    | C_GetPtr of identifier_t
    | C_GetAddr of identifier_t
    | C_Cmp of identifier_t * cond_t * value_t * value_t

and binop_t =
    | C_Add of identifier_t * value_t * value_t      
    | C_Sub of identifier_t * value_t * value_t     
    | C_Mul of identifier_t * value_t * value_t       
    | C_Div of identifier_t * value_t * value_t    
    | C_Rem of identifier_t * value_t * value_t       
    | C_ShiftL of identifier_t * value_t * value_t     
    | C_LogicalShiftR of identifier_t * value_t * value_t  
    | C_ArithmeticShiftR of identifier_t * value_t * value_t  
    | C_And of identifier_t * value_t * value_t
    | C_Or of identifier_t * value_t * value_t
    | C_Xor of identifier_t * value_t * value_t

and cond_t = | Eq | NE | Ugt | Uge | Ult | Ule | Sgt | Sge | Slt | Sle
    // equal / not equal / unsigned greater that / unsigned lower than etc..

and value_t = 
    | C_Var of type_t * bool (* Local/global *) * identifier_t
    | C_ConstInt of int
    | LL_ConstString of string

type ctydecl = identifier_t * type_t * list<(identifier_t * type_t)>
type path = list<string> * string