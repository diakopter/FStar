(*--build-config
  options:--verify_module LS --z3timeout 20;
  other-files:ext.fst set.fsi set.fst heap.fst st.fst all.fst list.fst ../low-level/stack.fst ../low-level/listset.fst ghost.fst ../low-level/located.fst ../low-level/lref.fst ../low-level/stackAndHeap.fst ../low-level/sst.fst ../low-level/sstCombinators.fst
  --*)

module LS

open StackAndHeap
open Located
open FStar.Heap
open Stack
open FStar.Set
open FStar.List
open Lref
open Located
open ListSet
open FStar.Ghost
open SST
open SSTCombinators

// Instantiate a fake instance of any type
// Needed to get the "size" of the element for salloc which must be known statically at compile
// time
assume val instanceOf:
  a:Type -> Tot a

// Standard return by value call
val call: 
  #a:Type -> #pre:(smem -> Type) -> #post:(smem -> SSTPost a) -> #mods:modset -> 
  body:(unit -> WNSC a pre post mods) ->
  Mem a pre post mods
let call 'a 'pre 'post #mods body =
  pushStackFrame ();
  let v = body() in
  popStackFrame ();
  v

// Return by reference call (change of calling convention)
val call_return_by_ref:
  #a:Type -> #pre:(smem -> Type) -> #post:(smem -> SSTPost a) -> #mods:modset -> 
  body:(unit -> WNSC a 
		    (fun m -> (exists m' (r:lref a). 
		     isNonEmpty (st m') /\ not (contains (topstb m') r) /\
		     m = allocateInTopR r (instanceOf a) m' /\ pre m' /\ isNonEmpty (st m)))
//		    (fun m0 a m1 -> 
		    post 
		    mods) ->
  Mem a 
      (fun m0 -> pre m0 /\ isNonEmpty (st m0)) 
      post 
      mods
let call_return_by_ref 'a 'pre 'post #mods body =
  let m0 = SST.get() in

  let ret_addr = salloc (instanceOf 'a) in

  // JK : this should work since salloc should return a fresh address
  admitP ( True /\ not (FStar.Set.mem (Ref ret_addr) (reveal mods)));

  pushStackFrame ();

  let v = body() in

  (*
  let mem = SST.get() in 
  cut (refExistsInStack ret_addr (topstid (mtail (reveal mem))) (st (reveal mem)) /\ True );
  cut ( b2t (liveRef ret_addr (reveal mem)) );
  *)
  
  memwrite ret_addr v;
  popStackFrame ();

  let r = memread ret_addr in

  let m1 = SST.get() in

  // TODO : FIXME
  admit();

  r

val is_on_stack_aux:
  #a:Type -> 
  id:sidt ->
  r:lref a{ is_InStack (refLoc r) /\ InStack.id (refLoc r) = id } ->
  s:Stack (sidt * region) ->
  Tot bool
let is_on_stack_aux id r s =
  match s with
  | [] -> false
  | hd::tl -> if (fst hd = id) then (contains (snd hd) r) else is_on_stack_aux id r tl

val is_on_stack_aux_lemma:
  #a:Type -> r:lref a{ is_InStack (refLoc r) } -> m:Stack(sidt * region) ->
  Lemma
    (requires (is_on_stack_aux (InStack.id (refLoc r)) r m))
    (ensures (refExistsInStack r (InStack.id (refLoc r)) m))
let is_on_stack_aux_lemma r m =
  match m with
  | [] -> ()
  | hd::tl -> 
    let id = InStack.id (refLoc r) in
    if fst hd = id then () else 
    is_on_stack_aux_lemma r tl

assume val is_on_stack: 
  #a:Type -> 
  m:smem -> 
  r:lref a -> 
  Tot (b:bool{ b = (is_InStack (refLoc r) && is_on_stack_aux (InStack.id (refLoc r)) r (st m)) })

val is_on_stack_write_lemma:
  #a:Type -> m0:smem -> r:lref a{ is_on_stack m0 r} -> v:a ->
  Lemma
    (requires (True))
    (ensures (liveRef r (hp m0, writeInMemStack r (st m0) (InStack.id (refLoc r)) v)) )
  [SMTPat (writeInMemStack r (st m0) (InStack.id (refLoc r)) v)]
let is_on_stack_write_lemma m0 r v =
  is_on_stack_aux_lemma r (st m0)

assume val write_on_stack: 
  #a:Type -> 
  m0:smem -> 
  r:lref a{ is_on_stack m0 r } -> 
  v:a ->
  Tot (m1:smem{ (hp m0 = hp m1)
		/\ (st m1 = writeInMemStack r (st m0) (InStack.id (refLoc r)) v)
		/\ (loopkupRef r m1 = v) })

assume val restrict_from_top:
  #a:Type -> m0:smem{ isNonEmpty (st m0) } -> r:lref a{ contains (topstb m0) r } ->
  Tot (m1:smem{ (isNonEmpty (st m1))
		/\ (hp m0 == hp m1)
		/\ (mtail m0 == mtail m1)
		/\ (topstb m1 == restrict (topstb m0) (singleton (Ref r)))})

assume val liveRef_lemma_1:
  #a:Type -> m:smem{ isNonEmpty (st m) } -> r:lref a ->
  Lemma
    (requires (contains (topstb m) r))
    (ensures (liveRef r m))
    [SMTPat (contains (topstb m) r)]

effect CALL (a:Type) (pre:(smem -> Type)) (post:(smem -> SSTPost a)) (mod:modset) (r:lref a) =
  Mem a
    (fun m -> 
      (isNonEmpty (st m))
      /\ (contains (topstb (mtail m)) r)
      /\ (topstb m = emp)
      /\ (pre (restrict_from_top (mtail m) r)) )
    (fun m0 v m1 ->
      (post (restrict_from_top (mtail m0) r) v (restrict_from_top (mtail m1) r))
      /\ (contains (topstb (mtail m1)) r)
      /\ (loopkupRef r (mtail m1) = v) )
    mod

val call_with_ref_aux :
  #a:Type -> #pre:(smem -> Type) -> #post:(smem -> SSTPost a) -> #mod:modset -> 
  r:lref a ->
  body:(unit -> CALL a pre post mod r) ->
  Mem unit
    (fun m0 -> 
      (isNonEmpty (st m0))
      /\ (contains (topstb m0) r)
      /\ (pre (restrict_from_top m0 r))
     )
    (fun m0 _ m1 ->
      (isNonEmpty (st m0))
      /\ (isNonEmpty (st m1))
      /\ (contains (topstb m0) r)
      /\ (contains (topstb m1) r)
      /\ (post (restrict_from_top m0 r) (loopkupRef r m1) (restrict_from_top m1 r))
      )
    mod
let call_with_ref_aux 'a 'pre 'post #mod r body =
  pushStackFrame();
  let v = body() in
  let m4 = SST.get() in
  memwrite r v;
  let m2 = SST.get() in

  // TODO : write the lemma to get this property
  admitP (True /\ restrict_from_top (mtail (reveal m4)) r = restrict_from_top (mtail (reveal m2)) r);

  popStackFrame()

val call_with_ref :
  #a:Type -> #pre:(smem -> Type) -> #post:(smem -> SSTPost a) -> #mod:modset -> 
  body:(r:(lref a) -> CALL a pre post mod r) ->  
  Mem a
    (fun m0 -> 
      (isNonEmpty (st m0))
      /\ (pre m0)
     )
    (fun m0 v m1 ->
      (isNonEmpty (st m0))
      /\ (isNonEmpty (st m1))
      /\ (post m0 v m1)
      )
    mod
let call_with_ref 'a 'pre 'post #mod body =
  let m0 = SST.get() in
  let ret_addr = salloc (instanceOf 'a) in
  let m = SST.get() in

  admitP (restrict_from_top (reveal m) ret_addr == reveal m0 /\ True );
  
  call_with_ref_aux #'a #'pre #'post #mod ret_addr (fun () -> body ret_addr);

  let v = memread ret_addr in
  v


(*
// What is expected
val ...
  body:
let call_combinator 'a 'pre 'post #mod body =
  let ret_addr = salloc (instanceOf 'a) in
  pushStackFrame();
  let v = body() in
  memwrite ret_addr v;
  popStackFrame();
  memread ret_addr
*)
