(*--build-config
  options:--verify_module Ex --z3timeout 300;
  variables:SST=../low-level;
  other-files:classical.fst ext.fst set.fsi set.fst seq.fsi seq.fst heap.fst st.fst all.fst  seqproperties.fst list.fst listTot.fst listproperties.fst $SST/stack.fst $SST/listset.fst ghost.fst $SST/located.fst $SST/lref.fst $SST/regions.fst $SST/rst.fst $SST/sstCombinators.fst lsarray.fst
  --*)


module Ex

open RST
open Located
open Lref
open FStar.Set
open FStar.Ghost
open Regions
open Stack
open RSTCombinators
open LSarray

type char = b:nat

val encrypt:
  buffer:LSarray.array char -> len:nat ->
  Mem 
    unit
    (requires (fun m -> 
      (isNonEmpty (st m))
      /\ (live buffer m)
      /\ (len <= glength buffer)))
    (ensures (fun m0 _ m1 ->
      (isNonEmpty (st m0))
      /\ (isNonEmpty (st m1))
      /\ (live buffer m0)
      /\ (live buffer m1)
      /\ (len <= glength buffer)
      /\ (forall (i:nat{ i < len }). gget buffer i m1 = op_Hat_Bar (gget buffer i m0) 42)))
    (eonly (asRef buffer))
let encrypt buffer len =
  let m_init = RST.get() in
  pushRegion();
  let ctr = ralloc #nat 0 in
  scopedWhile1 ctr 
	      (fun x -> x < len) 
	      (fun m -> 
		(isNonEmpty (st m))
		/\ (refIsLive ctr m)
		/\ (live buffer m)
		/\ (lookupRef ctr m <= len)
		/\ (forall (i:nat{ i < lookupRef ctr m }). gget buffer i m = op_Hat_Bar (gget buffer i (reveal m_init)) 42 )
		/\ (forall (i:nat{ i >= lookupRef ctr m /\ i < len }). gget buffer i m = gget buffer i (reveal m_init)))
	      (eunion (only ctr) (eonly (asRef buffer)))
	      (fun (u:unit) ->
		let idx = memread ctr in
		let v = LSarray.get buffer idx in
		let v' = v ^| 42 in
		LSarray.upd buffer idx v';
		memwrite ctr (idx + 1)
		);
  let m = RST.get() in
  popRegion()


type wellFormed (m:smem) (buffer:LSarray.array char) =
  (live buffer m)
  /\ (glength buffer >= 2)
  /\ (glength buffer >= (gget buffer 0 m + 256 * (gget buffer 1 m)) + 2) 

val process_msg:
  buffer:LSarray.array char -> 
  Mem unit
    (requires (fun m -> 
      (isNonEmpty (st m))
      /\ (wellFormed m buffer)))
    (ensures (fun m0 _ m1 -> True))
    (eonly (asRef buffer))
let process_msg buffer =
  let l0 = get buffer 0 in
  let l1 = get buffer 1 in
  let len = l0 + 256 * l1 in
  let msg_body = sub buffer 2 len in
  encrypt msg_body len

val array_test: 
  int -> Mem int (requires (fun m -> isNonEmpty (st m))) (ensures (fun m0 _ m1 -> True)) (hide empty)
let array_test x =
  let zero = 0 in
  let buffer = LSarray.create int 256 in
  LSarray.upd buffer 32 0;
  LSarray.upd buffer 33 1;
  let v = LSarray.get buffer 32 in
  let sub_buffer = LSarray.sub buffer 42 128 in
  //admit();
  0

