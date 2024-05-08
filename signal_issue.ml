module Picos_thread = struct
  let main_thread = Thread.id (Thread.self ())
  let is_main_thread () = Thread.id (Thread.self ()) = main_thread

  module TLS = struct
    (* see: https://discuss.ocaml.org/t/a-hack-to-implement-efficient-tls-thread-local-storage/13264 *)

    (* sanity check *)
    let () = assert (Obj.field (Obj.repr (Thread.self ())) 1 = Obj.repr ())

    type 'a key = {
      index : int;  (** Unique index for this key. *)
      compute : unit -> 'a;
          (** Initializer for values for this key. Called at most
        once per thread. *)
    }

    (** Counter used to allocate new keys *)
    let counter = Atomic.make 0

    (** Value used to detect a TLS slot that was not initialized yet.
    Because [counter] is private and lives forever, no other
    object the user can see will have the same address. *)
    let[@inline] sentinel_value_for_uninit_tls_ () : Obj.t = Obj.repr counter

    let new_key compute : _ key =
      let index = Atomic.fetch_and_add counter 1 in
      { index; compute }

    type thread_internal_state = {
      _id : int;  (** Thread ID (here for padding reasons) *)
      mutable tls : Obj.t;  (** Our data, stowed away in this unused field *)
      _other : Obj.t;
          (** Here to avoid lying to ocamlopt/flambda about the size of [Thread.t] *)
    }
    (** A partial representation of the internal type [Thread.t], allowing us to
        access the second field (unused after the thread has started) and stash
        TLS data in it. *)

    let ceil_pow_2_minus_1 (n : int) : int =
      let n = n lor (n lsr 1) in
      let n = n lor (n lsr 2) in
      let n = n lor (n lsr 4) in
      let n = n lor (n lsr 8) in
      let n = n lor (n lsr 16) in
      if Sys.int_size > 32 then n lor (n lsr 32) else n

    (** Grow the array so that [index] is valid. *)
    let[@inline never] grow_tls (old : Obj.t array) (index : int) : Obj.t array
        =
      let new_length = ceil_pow_2_minus_1 (index + 1) in
      let new_ = Array.make new_length (sentinel_value_for_uninit_tls_ ()) in
      Array.blit old 0 new_ 0 (Array.length old);
      new_

    let[@inline] get_tls_ (index : int) : Obj.t array =
      let thread : thread_internal_state = Obj.magic (Thread.self ()) in
      let tls = thread.tls in
      if Obj.is_int tls then (
        let new_tls = grow_tls [||] index in
        thread.tls <- Obj.repr new_tls;
        new_tls)
      else
        let tls = (Obj.obj tls : Obj.t array) in
        if index < Array.length tls then tls
        else
          let new_tls = grow_tls tls index in
          thread.tls <- Obj.repr new_tls;
          new_tls

    let[@inline never] get_compute_ tls (key : 'a key) : 'a =
      let value = key.compute () in
      Array.set tls key.index (Obj.repr (Sys.opaque_identity value));
      value

    let[@inline] get (key : 'a key) : 'a =
      let tls = get_tls_ key.index in
      let value = Array.get tls key.index in
      if value != sentinel_value_for_uninit_tls_ () then
        (* fast path *)
        Obj.obj value
      else
        (* slow path: we need to compute the initial value *)
        get_compute_ tls key

    let[@inline] set key value : unit =
      let tls = get_tls_ key.index in
      Array.set tls key.index (Obj.repr (Sys.opaque_identity value))
  end
end

module Multicore_magic = struct
  let copy_as_padded = Fun.id
  let instantaneous_domain_index () = 0
end

module Backoff = struct
  type t = int

  let single_mask = Bool.to_int (Domain.recommended_domain_count () = 1) - 1
  let bits = 5
  let max_wait_log = 30 (* [Random.bits] returns 30 random bits. *)
  let mask = (1 lsl bits) - 1

  let create ?(lower_wait_log = 4) ?(upper_wait_log = 17) () =
    assert (
      0 <= lower_wait_log
      && lower_wait_log <= upper_wait_log
      && upper_wait_log <= max_wait_log);
    (upper_wait_log lsl (bits * 2))
    lor (lower_wait_log lsl bits) lor lower_wait_log

  let get_upper_wait_log backoff = backoff lsr (bits * 2)
  let get_lower_wait_log backoff = (backoff lsr bits) land mask
  let get_wait_log backoff = backoff land mask

  let reset backoff =
    let lower_wait_log = get_lower_wait_log backoff in
    backoff land lnot mask lor lower_wait_log

  let[@inline never] once backoff =
    let wait_log = get_wait_log backoff in
    let wait_mask = (1 lsl wait_log) - 1 in
    let t = Random.bits () land wait_mask land single_mask in
    for _ = 0 to t do
      Domain.cpu_relax ()
    done;
    let upper_wait_log = get_upper_wait_log backoff in
    let next_wait_log = Int.min upper_wait_log (wait_log + 1) in
    backoff lxor wait_log lor next_wait_log

  let default = create ()
end

module Exn_bt = struct
  type t = { exn : exn; bt : Printexc.raw_backtrace }

  let get exn =
    let bt = Printexc.get_raw_backtrace () in
    { exn; bt }

  let empty_backtrace = Printexc.get_callstack 0

  let get_callstack n exn =
    let bt = if n <= 0 then empty_backtrace else Printexc.get_callstack n in
    { exn; bt }

  let raise t = Printexc.raise_with_backtrace t.exn t.bt
  let discontinue k t = Effect.Deep.discontinue_with_backtrace k t.exn t.bt

  let discontinue_with k t handler =
    Effect.Shallow.discontinue_with_backtrace k t.exn t.bt handler
end

module Picos_thread_atomic = struct
  let[@poll error] [@inline never] compare_and_set x before after =
    !x == before
    && begin
         x := after;
         true
       end

  let[@poll error] [@inline never] exchange x after =
    let before = !x in
    x := after;
    before
end

module Picos_mpsc_queue = struct
  type 'a t = { tail : 'a tail Atomic.t; head : 'a head Atomic.t }

  and ('a, _) tdt =
    | Head : ('a, [> `Head ]) tdt
    | Cons : { value : 'a; mutable next : 'a head } -> ('a, [> `Cons ]) tdt
    | Tail : ('a, [> `Tail ]) tdt
    | Snoc : { mutable prev : 'a tail; value : 'a } -> ('a, [> `Snoc ]) tdt

  and 'a head = H : ('a, [< `Head | `Cons ]) tdt -> 'a head [@@unboxed]
  and 'a tail = T : ('a, [< `Tail | `Snoc ]) tdt -> 'a tail [@@unboxed]

  exception Empty

  let[@inline never] impossible () =
    invalid_arg "multiple consumers not allowed"

  let create () =
    let tail = Multicore_magic.copy_as_padded @@ Atomic.make (T Tail) in
    let head = Multicore_magic.copy_as_padded @@ Atomic.make (H Head) in
    Multicore_magic.copy_as_padded { tail; head }

  let rec push_head head (Cons r as after : (_, [< `Cons ]) tdt) backoff =
    let before = Atomic.get head in
    r.next <- before;
    if not (Atomic.compare_and_set head before (H after)) then
      push_head head after (Backoff.once backoff)

  let push_head t value =
    let head = t.head in
    let before = Atomic.get head in
    let after = Cons { value; next = before } in
    if not (Atomic.compare_and_set head before (H after)) then
      push_head head after Backoff.default

  let rec append_to (Cons cons_r : (_, [< `Cons ]) tdt) tail =
    match cons_r.next with
    | H Head -> cons_r.next <- tail
    | H (Cons _ as head) -> append_to head tail

  let rec push tail (Snoc r as after : (_, [< `Snoc ]) tdt) backoff =
    let before = Atomic.get tail in
    r.prev <- before;
    if not (Atomic.compare_and_set tail before (T after)) then
      push tail after (Backoff.once backoff)

  let push t value =
    let tail = t.tail in
    let before = Atomic.get tail in
    let after = Snoc { prev = before; value } in
    if not (Atomic.compare_and_set tail before (T after)) then
      push tail after Backoff.default

  let rec rev_to head (Snoc r : (_, [< `Snoc ]) tdt) =
    let head = Cons { value = r.value; next = H head } in
    match r.prev with T Tail -> head | T (Snoc _ as prev) -> rev_to head prev

  let rec pop_exn t backoff = function
    | H (Cons head_r as head) ->
        if Atomic.compare_and_set t.head (H head) head_r.next then head_r.value
        else
          let backoff = Backoff.once backoff in
          pop_exn t backoff (Atomic.get t.head)
    | H Head ->
        if Atomic.get t.tail != T Tail then
          match Atomic.exchange t.tail (T Tail) with
          | T Tail -> impossible ()
          | T (Snoc snoc_r) -> begin
              match snoc_r.prev with
              | T Tail -> begin
                  match Atomic.get t.head with
                  | H Head -> snoc_r.value
                  | H (Cons _ as head) ->
                      let next = Cons { value = snoc_r.value; next = H Head } in
                      append_to head (H next);
                      pop_head_exn t backoff head
                end
              | T (Snoc _ as prev) ->
                  let next = Cons { value = snoc_r.value; next = H Head } in
                  let (Cons cons_r as next : (_, [< `Cons ]) tdt) =
                    rev_to next prev
                  in
                  if Atomic.compare_and_set t.head (H Head) cons_r.next then
                    cons_r.value
                  else begin
                    match Atomic.get t.head with
                    | H Head -> impossible ()
                    | H (Cons _ as head) ->
                        append_to head (H next);
                        pop_head_exn t backoff head
                  end
            end
        else begin
          match Atomic.get t.head with
          | H Head -> raise_notrace Empty
          | H (Cons _ as head) -> pop_head_exn t backoff head
        end

  and pop_head_exn t backoff (Cons head_r as head : (_, [< `Cons ]) tdt) =
    if Atomic.compare_and_set t.head (H head) head_r.next then head_r.value
    else
      let backoff = Backoff.once backoff in
      pop_exn t backoff (Atomic.get t.head)

  let[@inline] pop_exn t = pop_exn t Backoff.default (Atomic.get t.head)

  let rec prepend_to_seq t tl =
    match t with
    | H Head -> tl
    | H (Cons r) -> fun () -> Seq.Cons (r.value, prepend_to_seq r.next tl)

  let rev = function T Tail -> H Head | T (Snoc r) -> H (rev_to Head (Snoc r))

  let rev_prepend_to_seq t tl =
    let t = ref (Either.Left t) in
    fun () ->
      let t =
        match !t with
        | Left t' ->
            let t' = rev t' in
            t := Right t';
            t'
        | Right t' -> t'
      in
      prepend_to_seq t tl ()

  let rec drop_tail_after cut = function
    | T Tail -> impossible ()
    | T (Snoc r) ->
        if r.prev == cut then r.prev <- T Tail else drop_tail_after cut r.prev

  let rec drop_head_after cut = function
    | H Head -> impossible ()
    | H (Cons r) ->
        if r.next == cut then r.next <- H Head else drop_head_after cut r.next

  let rec pop_all t =
    let head = Atomic.get t.head in
    let tail = Atomic.get t.tail in
    if Atomic.get (Sys.opaque_identity t.head) == head then begin
      if not (Atomic.compare_and_set t.tail tail (T Tail)) then
        drop_tail_after tail (Atomic.get t.tail);
      if not (Atomic.compare_and_set t.head head (H Head)) then
        drop_head_after head (Atomic.get t.head);
      Seq.empty |> rev_prepend_to_seq tail |> prepend_to_seq head
    end
    else pop_all t
end

module Picos_htbl = struct
  let[@inline never] impossible () = failwith "impossible"

  type 'k hashed_type = (module Stdlib.Hashtbl.HashedType with type t = 'k)

  type ('k, 'v, _) tdt =
    | Nil : ('k, 'v, [> `Nil ]) tdt
    | Cons : {
        key : 'k;
        value : 'v;
        rest : ('k, 'v, [ `Nil | `Cons ]) tdt;
      }
        -> ('k, 'v, [> `Cons ]) tdt
    | Resize : {
        spine : ('k, 'v, [ `Nil | `Cons ]) tdt;
      }
        -> ('k, 'v, [> `Resize ]) tdt
        (** During resizing and snapshotting target buckets will be initialized
          with a physically unique [Resize] value and the source buckets will
          then be gradually updated to [Resize] values and the target buckets
          updated with data from the source buckets. *)

  type ('k, 'v) bucket =
    | B : ('k, 'v, [< `Nil | `Cons | `Resize ]) tdt -> ('k, 'v) bucket
  [@@unboxed]

  type ('k, 'v) pending =
    | Nothing
    | Resize of {
        buckets : ('k, 'v) bucket Atomic.t array;
        non_linearizable_size : int Atomic.t array;
      }

  type ('k, 'v) state = {
    hash : 'k -> int;
    buckets : ('k, 'v) bucket Atomic.t array;
    equal : 'k -> 'k -> bool;
    non_linearizable_size : int Atomic.t array;
    pending : ('k, 'v) pending;
  }

  type ('k, 'v) t = ('k, 'v) state Atomic.t

  let min_buckets = 16

  let max_buckets =
    let n = Sys.max_array_length lsr 1 in
    let n = n lor (n lsr 1) in
    let n = n lor (n lsr 2) in
    let n = n lor (n lsr 4) in
    let n = n lor (n lsr 8) in
    let n = n lor (n lsr 16) in
    let n = if Sys.int_size <= 32 then n else n lor (n lsr 32) in
    let n = n + 1 in
    Int.min n (1 lsl 30 (* Limit of [hash] *))

  let create (type k) ?hashed_type () =
    let equal, hash =
      match hashed_type with
      | None -> (( = ), Stdlib.Hashtbl.seeded_hash (Random.bits ()))
      | Some ((module Hashed_type) : k hashed_type) ->
          (Hashed_type.equal, Hashed_type.hash)
    in
    let buckets = Array.init min_buckets @@ fun _ -> Atomic.make (B Nil) in
    let non_linearizable_size =
      [| Atomic.make 0 |> Multicore_magic.copy_as_padded |]
    in
    let pending = Nothing in
    { hash; buckets; equal; non_linearizable_size; pending }
    |> Multicore_magic.copy_as_padded |> Atomic.make
    |> Multicore_magic.copy_as_padded

  (* *)

  let[@tail_mod_cons] rec filter t msk chk = function
    | Nil -> Nil
    | Cons r ->
        if t r.key land msk = chk then
          Cons { r with rest = filter t msk chk r.rest }
        else filter t msk chk r.rest

  let split_hi r target i t spine =
    let high = Array.length r.buckets in
    let b = Array.get target (i + high) in
    match Atomic.get b with
    | B (Resize _ as before) ->
        (* The [before] value is physically different for each resize and so
           checking that the resize has not finished is sufficient to ensure that
           the [compare_and_set] below does not disrupt the next resize. *)
        if Atomic.get t == r then
          let ((Nil | Cons _) as after) = filter r.hash high high spine in
          Atomic.compare_and_set b (B before) (B after) |> ignore
    | B (Nil | Cons _) -> ()

  let split_lo r target i t spine =
    let b = Array.get target i in
    match Atomic.get b with
    | B (Resize _ as before) ->
        (* The [before] value is physically different for each resize and so
           checking that the resize has not finished is sufficient to ensure that
           the [compare_and_set] below does not disrupt the next resize. *)
        if Atomic.get t == r then begin
          let ((Nil | Cons _) as after) =
            filter r.hash (Array.length r.buckets) 0 spine
          in
          Atomic.compare_and_set b (B before) (B after) |> ignore;
          split_hi r target i t spine
        end
    | B (Nil | Cons _) -> split_hi r target i t spine

  let rec split_at r target i t backoff =
    let b = Array.get r.buckets i in
    match Atomic.get b with
    | B ((Nil | Cons _) as spine) ->
        if Atomic.compare_and_set b (B spine) (B (Resize { spine })) then
          split_lo r target i t spine
        else split_at r target i t (Backoff.once backoff)
    | B (Resize spine_r) -> split_lo r target i t spine_r.spine

  let rec split_all r target i t step =
    Atomic.get t == r
    &&
    let i = (i + step) land (Array.length r.buckets - 1) in
    split_at r target i t Backoff.default;
    i = 0 || split_all r target i t step

  (* *)

  let[@tail_mod_cons] rec merge rest = function
    | Nil -> rest
    | Cons r -> Cons { r with rest = merge rest r.rest }

  let merge_at r target i t spine_lo spine_hi =
    let b = Array.get target i in
    match Atomic.get b with
    | B (Resize _ as before) ->
        (* The [before] value is physically different for each resize and so
           checking that the resize has not finished is sufficient to ensure that
           the [compare_and_set] below does not disrupt the next resize. *)
        if Atomic.get t == r then
          let ((Nil | Cons _) as after) = merge spine_lo spine_hi in
          Atomic.compare_and_set b (B before) (B after) |> ignore
    | B (Nil | Cons _) -> ()

  let rec merge_hi r target i t spine_lo backoff =
    let b = Array.get r.buckets (i + Array.length target) in
    match Atomic.get b with
    | B ((Nil | Cons _) as spine) ->
        if Atomic.compare_and_set b (B spine) (B (Resize { spine })) then
          merge_at r target i t spine_lo spine
        else merge_hi r target i t spine_lo (Backoff.once backoff)
    | B (Resize spine_r) -> merge_at r target i t spine_lo spine_r.spine

  let rec merge_lo r target i t backoff =
    let b = Array.get r.buckets i in
    match Atomic.get b with
    | B ((Nil | Cons _) as spine) ->
        if Atomic.compare_and_set b (B spine) (B (Resize { spine })) then
          merge_hi r target i t spine Backoff.default
        else merge_lo r target i t (Backoff.once backoff)
    | B (Resize spine_r) -> merge_hi r target i t spine_r.spine Backoff.default

  let rec merge_all r target i t step =
    Atomic.get t == r
    &&
    let i = (i + step) land (Array.length target - 1) in
    merge_lo r target i t Backoff.default;
    i = 0 || merge_all r target i t step

  (* *)

  let copy_to r target i t
      ((Nil | Cons _) as spine : (_, _, [ `Nil | `Cons ]) tdt) =
    let b = Array.get target i in
    match Atomic.get b with
    | B (Resize _ as before) ->
        (* The [before] value is physically different for each resize and so
           checking that the resize has not finished is sufficient to ensure that
           the [compare_and_set] below does not disrupt the next resize. *)
        if Atomic.get t == r then
          Atomic.compare_and_set b (B before) (B spine) |> ignore
    | B (Nil | Cons _) -> ()

  let rec copy_at r target i t backoff =
    let b = Array.get r.buckets i in
    match Atomic.get b with
    | B ((Nil | Cons _) as spine) ->
        if Atomic.compare_and_set b (B spine) (B (Resize { spine })) then
          copy_to r target i t spine
        else copy_at r target i t (Backoff.once backoff)
    | B (Resize spine_r) -> copy_to r target i t spine_r.spine

  let rec copy_all r target i t step =
    Atomic.get t == r
    &&
    let i = (i + step) land (Array.length target - 1) in
    copy_at r target i t Backoff.default;
    i = 0 || copy_all r target i t step

  (* *)

  let[@inline never] rec finish t r =
    match r.pending with
    | Nothing -> r
    | Resize { buckets; non_linearizable_size } ->
        let high_source = Array.length r.buckets in
        let high_target = Array.length buckets in
        (* We step by random amount to better allow cores to work in parallel.
           The number of buckets is always a power of two, so any odd number is
           relatively prime or coprime. *)
        let step = Random.bits () lor 1 in
        if
          if high_source < high_target then begin
            (* We are growing the table. *)
            split_all r buckets 0 t step
          end
          else if high_target < high_source then begin
            (* We are shrinking the table. *)
            merge_all r buckets 0 t step
          end
          else begin
            (* We are snaphotting the table. *)
            copy_all r buckets 0 t step
          end
        then
          let new_r =
            { r with buckets; non_linearizable_size; pending = Nothing }
            |> Multicore_magic.copy_as_padded
          in
          if Atomic.compare_and_set t r new_r then new_r
          else finish t (Atomic.get t)
        else finish t (Atomic.get t)

  (* *)

  let rec estimated_size cs n sum =
    let n = n - 1 in
    if 0 <= n then estimated_size cs n (sum + Atomic.get (Array.get cs n))
    else sum

  (** This only gives an "estimate" of the size, which can be off by one or more
    and even be negative, so this must be used with care. *)
  let estimated_size r =
    let cs = r.non_linearizable_size in
    let n = Array.length cs - 1 in
    estimated_size cs n (Atomic.get (Array.get cs n))

  let[@inline never] try_resize t r new_capacity ~clear =
    (* We must make sure that on every resize we use a physically different
       [Resize _] value to indicate unprocessed target buckets.  The use of
       [Sys.opaque_identity] below ensures that a new value is allocated. *)
    let resize_avoid_aba =
      if clear then B Nil else B (Resize { spine = Sys.opaque_identity Nil })
    in
    let buckets =
      Array.init new_capacity @@ fun _ -> Atomic.make resize_avoid_aba
    in
    let non_linearizable_size =
      if clear then
        Array.init (Array.length r.non_linearizable_size) @@ fun _ ->
        Atomic.make 0 |> Multicore_magic.copy_as_padded
      else r.non_linearizable_size
    in
    let new_r =
      { r with pending = Resize { buckets; non_linearizable_size } }
    in
    Atomic.compare_and_set t r new_r
    && begin
         finish t new_r |> ignore;
         true
       end

  let rec adjust_estimated_size t r mask delta result =
    let i = Multicore_magic.instantaneous_domain_index () in
    let n = Array.length r.non_linearizable_size in
    if i < n then begin
      Atomic.fetch_and_add (Array.get r.non_linearizable_size i) delta |> ignore;
      (* Reading the size is potentially expensive, so we only check it
         occasionally.  The bigger the table the less frequently we should need to
         resize. *)
      if Random.bits () land mask = 0 && Atomic.get t == r then begin
        let estimated_size = estimated_size r in
        let capacity = Array.length r.buckets in
        if capacity < estimated_size && capacity < max_buckets then
          try_resize t r (capacity + capacity) ~clear:false |> ignore
        else if
          min_buckets < capacity
          && estimated_size + estimated_size + estimated_size < capacity
        then try_resize t r (capacity lsr 1) ~clear:false |> ignore
      end;
      result
    end
    else
      let new_cs =
        (* We use [n + n + 1] as it keeps the length of the array as a power of 2
           minus 1 and so the size of the array/block including header word will
           be a power of 2. *)
        Array.init (n + n + 1) @@ fun i ->
        if i < n then Array.get r.non_linearizable_size i
        else Atomic.make 0 |> Multicore_magic.copy_as_padded
      in
      let new_r =
        { r with non_linearizable_size = new_cs }
        |> Multicore_magic.copy_as_padded
      in
      let r =
        if Atomic.compare_and_set t r new_r then new_r else Atomic.get t
      in
      adjust_estimated_size t r mask delta result

  (* *)

  (** [get] only returns with a state where [pending = Nothing]. *)
  let[@inline] get t =
    let r = Atomic.get t in
    if r.pending == Nothing then r else finish t r

  (* *)

  let rec assoc_node t key = function
    | Nil -> (Nil : (_, _, [< `Nil | `Cons ]) tdt)
    | Cons r as cons -> if t r.key key then cons else assoc_node t key r.rest

  let find_node t key =
    (* Reads can proceed in parallel with writes. *)
    let r = Atomic.get t in
    let h = r.hash key in
    let mask = Array.length r.buckets - 1 in
    let i = h land mask in
    match Atomic.get (Array.get r.buckets i) with
    | B Nil -> Nil
    | B (Cons cons_r as cons) ->
        if r.equal cons_r.key key then cons
        else assoc_node r.equal key cons_r.rest
    | B (Resize resize_r) ->
        (* A resize is in progress.  The spine of the resize still holds what was
           in the bucket before resize reached that bucket. *)
        assoc_node r.equal key resize_r.spine

  (* *)

  let find_exn t key =
    match find_node t key with
    | Nil -> raise_notrace Not_found
    | Cons r -> r.value

  let mem t key = find_node t key != Nil

  (* *)

  let rec try_add t key value backoff =
    let r = get t in
    let h = r.hash key in
    let mask = Array.length r.buckets - 1 in
    let i = h land mask in
    let b = Array.get r.buckets i in
    match Atomic.get b with
    | B Nil ->
        let after = Cons { key; value; rest = Nil } in
        if Atomic.compare_and_set b (B Nil) (B after) then
          adjust_estimated_size t r mask 1 true
        else try_add t key value (Backoff.once backoff)
    | B (Cons _ as before) ->
        if assoc_node r.equal key before != Nil then false
        else
          let after = Cons { key; value; rest = before } in
          if Atomic.compare_and_set b (B before) (B after) then
            adjust_estimated_size t r mask 1 true
          else try_add t key value (Backoff.once backoff)
    | B (Resize _) -> try_add t key value Backoff.default

  let try_add t key value = try_add t key value Backoff.default

  (* *)

  let[@tail_mod_cons] rec dissoc t key = function
    | Nil -> raise_notrace Not_found
    | Cons r ->
        if t key r.key then r.rest
        else Cons { r with rest = dissoc t key r.rest }

  let rec remove_node t key backoff =
    let r = get t in
    let h = r.hash key in
    let mask = Array.length r.buckets - 1 in
    let i = h land mask in
    let b = Array.get r.buckets i in
    match Atomic.get b with
    | B Nil -> Nil
    | B (Cons cons_r as before) -> begin
        if r.equal cons_r.key key then
          if Atomic.compare_and_set b (B before) (B cons_r.rest) then
            adjust_estimated_size t r mask (-1) before
          else remove_node t key (Backoff.once backoff)
        else
          match dissoc r.equal key cons_r.rest with
          | (Nil | Cons _) as rest ->
              if
                Atomic.compare_and_set b (B before)
                  (B (Cons { cons_r with rest }))
              then
                assoc_node r.equal key cons_r.rest
                |> adjust_estimated_size t r mask (-1)
              else remove_node t key (Backoff.once backoff)
          | exception Not_found -> Nil
      end
    | B (Resize _) -> remove_node t key Backoff.default

  let try_remove t key = remove_node t key Backoff.default != Nil

  let remove_exn t key =
    match remove_node t key Backoff.default with
    | Nil -> raise_notrace Not_found
    | Cons r -> r.value

  (* *)

  let rec snapshot t ~clear backoff =
    let r = get t in
    if try_resize t r (Array.length r.buckets) ~clear then begin
      (* At this point the resize has been completed and a new array is used for
         buckets and [r.buckets] now has an immutable copy of what was in the hash
         table. *)
      let snapshot = r.buckets in
      let rec loop i kvs () =
        match kvs with
        | Nil ->
            if i = Array.length snapshot then Seq.Nil
            else
              loop (i + 1)
                (match Atomic.get (Array.get snapshot i) with
                | B (Resize spine_r) -> spine_r.spine
                | B (Nil | Cons _) ->
                    (* After resize only [Resize] values should be left in the old
                       buckets. *)
                    assert false)
                ()
        | Cons r -> Seq.Cons ((r.key, r.value), loop i r.rest)
      in
      loop 0 Nil
    end
    else snapshot t ~clear (Backoff.once backoff)

  let to_seq t = snapshot t ~clear:false Backoff.default
  let remove_all t = snapshot t ~clear:true Backoff.default

  (* *)

  let rec try_find_random_non_empty_bucket buckets seed i =
    let bucket = Array.get buckets i in
    match Atomic.get bucket with
    | B Nil | B (Resize { spine = Nil }) ->
        let mask = Array.length buckets - 1 in
        let i = (i + 1) land mask in
        if i <> seed land mask then
          try_find_random_non_empty_bucket buckets seed i
        else Nil
    | B (Cons cons_r) | B (Resize { spine = Cons cons_r }) -> Cons cons_r

  let try_find_random_non_empty_bucket t =
    let buckets = (Atomic.get t).buckets in
    let seed = Random.bits () in
    try_find_random_non_empty_bucket buckets seed
      (seed land (Array.length buckets - 1))

  let rec length spine n =
    match spine with Nil -> n | Cons r -> length r.rest (n + 1)

  let length spine = length spine 0

  let rec nth spine i =
    match spine with
    | Nil -> impossible ()
    | Cons r -> if i <= 0 then r.key else nth r.rest (i - 1)

  let find_random_exn t =
    match try_find_random_non_empty_bucket t with
    | (Cons cons_r as spine : (_, _, [< `Nil | `Cons ]) tdt) ->
        (* We found a non-empty bucket - the fast way. *)
        if cons_r.rest == Nil then cons_r.key
        else
          let n = length spine in
          nth spine (Random.int n)
    | Nil ->
        (* We couldn't find a non-empty bucket - the slow way. *)
        let bindings = to_seq t |> Array.of_seq in
        let n = Array.length bindings in
        if n <> 0 then fst (Array.get bindings (Random.int n))
        else raise_notrace Not_found
end

module Picos = struct
  module Trigger = struct
    let[@inline never] error_awaiting () = invalid_arg "already awaiting"

    type state =
      | Signaled
      | Awaiting : { action : t -> 'x -> 'y -> unit; x : 'x; y : 'y } -> state
      | Initial

    and t = state Atomic.t

    let create () = Atomic.make Initial
    let is_signaled t = Atomic.get t == Signaled

    let is_initial t =
      match Atomic.get t with
      | Initial -> true
      | Awaiting _ -> error_awaiting ()
      | Signaled -> false

    let rec finish t ~allow_awaiting =
      match Atomic.get t with
      | Signaled -> ()
      | Awaiting r as before ->
          if allow_awaiting then
            if Atomic.compare_and_set t before Signaled then r.action t r.x r.y
            else finish t ~allow_awaiting
          else error_awaiting ()
      | Initial ->
          if not (Atomic.compare_and_set t Initial Signaled) then
            finish t ~allow_awaiting

    let signal t = finish t ~allow_awaiting:true
    let dispose t = finish t ~allow_awaiting:false

    let rec on_signal t x y action =
      match Atomic.get t with
      | Signaled -> false
      | Awaiting _ -> error_awaiting ()
      | Initial ->
          Atomic.compare_and_set t Initial (Awaiting { action; x; y })
          || on_signal t x y action

    let from_action x y action = Atomic.make (Awaiting { action; x; y })

    type _ Effect.t += Await : t -> Exn_bt.t option Effect.t

    let await t = if is_initial t then Effect.perform (Await t) else None
  end

  module Computation = struct
    let[@inline never] error_negative_or_nan () =
      invalid_arg "seconds must be non-negative"

    let[@inline never] error_returned () = invalid_arg "already returned"

    type 'a state =
      | Canceled of Exn_bt.t
      | Returned of 'a
      | Continue of { balance_and_mode : int; triggers : Trigger.t list }

    type 'a t = 'a state Atomic.t

    let fifo_bit = 1
    let one = 2

    let create ?(mode : [ `FIFO | `LIFO ] = `FIFO) () =
      let balance_and_mode = Bool.to_int (mode == `FIFO) in
      Atomic.make (Continue { balance_and_mode; triggers = [] })

    let with_action ?(mode : [ `FIFO | `LIFO ] = `FIFO) x y action =
      let balance_and_mode = one + Bool.to_int (mode == `FIFO) in
      let trigger = Trigger.from_action x y action in
      Atomic.make (Continue { balance_and_mode; triggers = [ trigger ] })

    let is_canceled t =
      match Atomic.get t with
      | Canceled _ -> true
      | Returned _ | Continue _ -> false

    let canceled t =
      match Atomic.get t with
      | Canceled exn_bt -> Some exn_bt
      | Returned _ | Continue _ -> None

    (** [gc] is called when balance becomes negative by both [try_attach] and
      [detach].  This ensures that the [O(n)] lazy removal done by [gc] cannot
      cause starvation, because the only reason that CAS fails after [gc] is
      that someone else completed the [gc]. *)
    let rec gc balance_and_mode triggers = function
      | [] ->
          let triggers =
            if balance_and_mode <= one + fifo_bit then triggers
            else List.rev triggers
          in
          Continue { balance_and_mode; triggers }
      | r :: rs ->
          if Trigger.is_signaled r then gc balance_and_mode triggers rs
          else gc (balance_and_mode + one) (r :: triggers) rs

    let rec try_attach t trigger backoff =
      match Atomic.get t with
      | Returned _ | Canceled _ -> false
      | Continue r as before ->
          (* We check the trigger before potential allocations. *)
          (not (Trigger.is_signaled trigger))
          &&
          let after =
            if fifo_bit <= r.balance_and_mode then
              let balance_and_mode = r.balance_and_mode + one in
              let triggers = trigger :: r.triggers in
              Continue { balance_and_mode; triggers }
            else
              gc
                (one + (r.balance_and_mode land fifo_bit))
                [ trigger ] r.triggers
          in
          Atomic.compare_and_set t before after
          || try_attach t trigger (Backoff.once backoff)

    let try_attach t trigger = try_attach t trigger Backoff.default

    let rec unsafe_unsuspend t backoff =
      match Atomic.get t with
      | Returned _ -> true
      | Canceled _ -> false
      | Continue r as before ->
          let after =
            if fifo_bit <= r.balance_and_mode then
              Continue
                { r with balance_and_mode = r.balance_and_mode - (2 * one) }
            else gc (r.balance_and_mode land fifo_bit) [] r.triggers
          in
          Atomic.compare_and_set t before after
          || unsafe_unsuspend t (Backoff.once backoff)

    let detach t trigger =
      Trigger.signal trigger;
      unsafe_unsuspend t Backoff.default |> ignore

    (** This cannot be [@@unboxed] because [Atomic.t] is opaque *)
    type packed = Packed : 'a t -> packed

    let is_running t =
      match Atomic.get t with
      | Canceled _ | Returned _ -> false
      | Continue _ -> true

    let rec try_terminate t after backoff =
      match Atomic.get t with
      | Returned _ | Canceled _ -> false
      | Continue r as before ->
          if Atomic.compare_and_set t before after then begin
            List.iter Trigger.signal
              (if r.balance_and_mode land fifo_bit = fifo_bit then
                 List.rev r.triggers
               else r.triggers);
            true
          end
          else try_terminate t after (Backoff.once backoff)

    let returned_unit = Returned (Obj.magic ())

    let make_returned value =
      if value == Obj.magic () then returned_unit else Returned value

    let returned value = Atomic.make (make_returned value)
    let finished = Atomic.make (make_returned ())

    let try_return t value =
      try_terminate t (make_returned value) Backoff.default

    let try_finish t = try_terminate t returned_unit Backoff.default
    let try_cancel t exn_bt = try_terminate t (Canceled exn_bt) Backoff.default
    let return t value = try_return t value |> ignore
    let finish t = try_finish t |> ignore
    let cancel t exn_bt = try_cancel t exn_bt |> ignore

    let try_capture t fn x =
      match fn x with
      | y -> try_return t y
      | exception exn -> try_cancel t (Exn_bt.get exn)

    let capture t fn x = try_capture t fn x |> ignore

    let check t =
      match Atomic.get t with
      | Canceled exn_bt -> Exn_bt.raise exn_bt
      | Returned _ | Continue _ -> ()

    let peek t =
      match Atomic.get t with
      | Canceled exn_bt -> Some (Error exn_bt)
      | Returned value -> Some (Ok value)
      | Continue _ -> None

    let propagate _ from into =
      match Atomic.get from with
      | Returned _ | Continue _ -> ()
      | Canceled _ as after ->
          try_terminate into after Backoff.default |> ignore

    let canceler ~from ~into = Trigger.from_action from into propagate

    let check_non_negative seconds =
      if not (0.0 <= seconds) then error_negative_or_nan ()

    let rec get_or block t =
      match Atomic.get t with
      | Returned value -> value
      | Canceled exn_bt -> Exn_bt.raise exn_bt
      | Continue _ -> get_or block (block t)

    let attach_canceler ~from ~into =
      let canceler = canceler ~from ~into in
      if try_attach from canceler then canceler
      else begin
        check from;
        error_returned ()
      end

    type _ Effect.t +=
      | Cancel_after : {
          seconds : float;
          exn_bt : Exn_bt.t;
          computation : 'a t;
        }
          -> unit Effect.t

    let cancel_after computation ~seconds exn_bt =
      check_non_negative seconds;
      Effect.perform (Cancel_after { seconds; exn_bt; computation })

    let block t =
      let trigger = Trigger.create () in
      if try_attach t trigger then begin
        match Trigger.await trigger with
        | None -> t
        | Some exn_bt ->
            detach t trigger;
            Exn_bt.raise exn_bt
      end
      else t

    let await t = get_or block t
    let wait t = if is_running t then ignore (block t)
  end

  module Fiber = struct
    type non_float = [ `Non_float of non_float ]

    type _ tdt =
      | Nothing : [> `Nothing ] tdt
      | Fiber : {
          mutable forbid : bool;
          mutable packed : Computation.packed;
          mutable fls : non_float array;
        }
          -> [> `Fiber ] tdt

    type t = [ `Fiber ] tdt

    let create_packed ~forbid packed = Fiber { forbid; packed; fls = [||] }

    let create ~forbid computation =
      create_packed ~forbid (Computation.Packed computation)

    let has_forbidden (Fiber r : t) = r.forbid

    let is_canceled (Fiber r : t) =
      (not r.forbid)
      &&
      let (Packed computation) = r.packed in
      Computation.is_canceled computation

    let canceled (Fiber r : t) =
      if r.forbid then None
      else
        let (Packed computation) = r.packed in
        Computation.canceled computation

    let get_computation (Fiber r : t) = r.packed
    let set_computation (Fiber r : t) packed = r.packed <- packed

    let check (Fiber r : t) =
      if not r.forbid then
        let (Packed computation) = r.packed in
        Computation.check computation

    let[@inline] equal t1 t2 = t1 == t2

    let exchange (Fiber r : t) ~forbid =
      let before = r.forbid in
      r.forbid <- forbid;
      before

    let set (Fiber r : t) ~forbid = r.forbid <- forbid

    let explicitly (Fiber r : t) body ~forbid =
      if r.forbid = forbid then body ()
      else
        match body (r.forbid <- forbid) with
        | value ->
            r.forbid <- not forbid;
            value
        | exception exn ->
            r.forbid <- not forbid;
            raise exn

    let forbid t body = explicitly t body ~forbid:true
    let permit t body = explicitly t body ~forbid:false

    let try_suspend (Fiber r : t) trigger x y resume =
      let (Packed computation) = r.packed in
      if not r.forbid then begin
        if Computation.try_attach computation trigger then
          Trigger.on_signal trigger x y resume
          || begin
               Computation.detach computation trigger;
               false
             end
        else if Computation.is_canceled computation then begin
          Trigger.dispose trigger;
          false
        end
        else Trigger.on_signal trigger x y resume
      end
      else Trigger.on_signal trigger x y resume

    let[@inline] unsuspend (Fiber r : t) trigger =
      assert (Trigger.is_signaled trigger);
      r.forbid
      ||
      let (Packed computation) = r.packed in
      Computation.unsafe_unsuspend computation Backoff.default

    module FLS = struct
      type 'a key = { index : int; default : non_float; compute : unit -> 'a }

      let compute () = failwith "impossible"
      let counter = Atomic.make 0
      let unique = Sys.opaque_identity (Obj.magic counter : non_float)

      let ceil_pow_2_minus_1 n =
        let n = n lor (n lsr 1) in
        let n = n lor (n lsr 2) in
        let n = n lor (n lsr 4) in
        let n = n lor (n lsr 8) in
        let n = n lor (n lsr 16) in
        if Sys.int_size > 32 then n lor (n lsr 32) else n

      let grow old_fls i =
        let new_length = ceil_pow_2_minus_1 (i + 1) in
        let new_fls = Array.make new_length unique in
        Array.blit old_fls 0 new_fls 0 (Array.length old_fls);
        new_fls

      type 'a initial = Constant of 'a | Computed of (unit -> 'a)

      let new_key initial =
        let index = Atomic.fetch_and_add counter 1 in
        match initial with
        | Constant default ->
            let default = Sys.opaque_identity (Obj.magic default : non_float) in
            { index; default; compute }
        | Computed compute -> { index; default = unique; compute }

      let get (type a) (Fiber r : t) (key : a key) =
        let fls = r.fls in
        if key.index < Array.length fls then begin
          let value = Array.get fls key.index in
          if value != unique then Sys.opaque_identity (Obj.magic value : a)
          else
            let value = key.default in
            if value != unique then begin
              (* As the [fls] array was already large enough, we cache the default
                 value in the array. *)
              Array.set fls key.index value;
              Sys.opaque_identity (Obj.magic value : a)
            end
            else
              let value = key.compute () in
              Array.set fls key.index
                (Sys.opaque_identity (Obj.magic value : non_float));
              value
        end
        else
          let value = key.default in
          if value != unique then Sys.opaque_identity (Obj.magic value : a)
          else
            let value = key.compute () in
            let fls = grow fls key.index in
            r.fls <- fls;
            Array.set fls key.index
              (Sys.opaque_identity (Obj.magic value : non_float));
            value

      let set (type a) (Fiber r : t) (key : a key) (value : a) =
        let fls = r.fls in
        if key.index < Array.length fls then
          Array.set fls key.index
            (Sys.opaque_identity (Obj.magic value : non_float))
        else
          let fls = grow fls key.index in
          r.fls <- fls;
          Array.set fls key.index
            (Sys.opaque_identity (Obj.magic value : non_float))
    end

    let resume t k = Effect.Deep.continue k (canceled t)
    let resume_with t k h = Effect.Shallow.continue_with k (canceled t) h

    let continue t k v =
      match canceled t with
      | None -> Effect.Deep.continue k v
      | Some exn_bt -> Exn_bt.discontinue k exn_bt

    let continue_with t k v h =
      match canceled t with
      | None -> Effect.Shallow.continue_with k v h
      | Some exn_bt -> Exn_bt.discontinue_with k exn_bt h

    type _ Effect.t += Current : t Effect.t

    let current () = Effect.perform Current

    type _ Effect.t +=
      | Spawn : {
          forbid : bool;
          computation : 'a Computation.t;
          mains : (unit -> unit) list;
        }
          -> unit Effect.t

    let spawn ~forbid computation mains =
      Effect.perform @@ Spawn { forbid; computation; mains }

    type _ Effect.t += Yield : unit Effect.t

    let yield () = Effect.perform Yield

    module Maybe = struct
      type t = T : [< `Nothing | `Fiber ] tdt -> t [@@unboxed]

      let[@inline] to_fiber_or_current = function
        | T Nothing -> current ()
        | T (Fiber r) -> Fiber r

      let[@inline] or_current t = T (to_fiber_or_current t)
      let nothing = T Nothing
      let[@inline] equal x y = x == y || x == nothing || y == nothing
      let[@inline] unequal x y = x != y || x == nothing
      let[@inline] of_fiber t = T t

      let[@inline] current_if checked =
        match checked with
        | None | Some true -> of_fiber (current ())
        | Some false -> nothing

      let[@inline] current_and_check_if checked =
        match checked with
        | None | Some true ->
            let fiber = current () in
            check fiber;
            of_fiber fiber
        | Some false -> nothing

      let[@inline] check = function
        | T Nothing -> ()
        | T (Fiber r) -> check (Fiber r)
    end

    exception Done

    let done_bt = Exn_bt.get_callstack 0 Done

    let sleep ~seconds =
      let sleep = Computation.create ~mode:`LIFO () in
      Computation.cancel_after ~seconds sleep done_bt;
      let trigger = Trigger.create () in
      if Computation.try_attach sleep trigger then
        match Trigger.await trigger with
        | None -> ()
        | Some exn_bt ->
            Computation.finish sleep;
            Exn_bt.raise exn_bt
  end
end

module Picos_sync = struct
  module List_ext = struct
    let[@tail_mod_cons] rec drop_first_or_not_found x' = function
      | [] -> raise_notrace Not_found
      | x :: xs -> if x == x' then xs else x :: drop_first_or_not_found x' xs
  end

  module Mutex = struct
    open Picos

    let[@inline never] owner () = raise (Sys_error "Mutex: owner")
    let[@inline never] unlocked () = raise (Sys_error "Mutex: unlocked")
    let[@inline never] not_owner () = raise (Sys_error "Mutex: not owner")

    type entry = { trigger : Trigger.t; fiber : Fiber.Maybe.t }

    type state =
      | Unlocked
      | Locked of {
          fiber : Fiber.Maybe.t;
          head : entry list;
          tail : entry list;
        }

    type t = state Atomic.t

    let create ?(padded = false) () =
      let t = Atomic.make Unlocked in
      if padded then Multicore_magic.copy_as_padded t else t

    (* We try to avoid starvation of unlock by making it so that when, at the start
       of lock or unlock, the head is empty, the tail is reversed into the head.
       This way both lock and unlock attempt O(1) and O(n) operations at the same
       time. *)

    let locked_nothing =
      Locked { fiber = Fiber.Maybe.nothing; head = []; tail = [] }

    let rec unlock_as owner t backoff =
      match Atomic.get t with
      | Unlocked -> unlocked ()
      | Locked r as before ->
          if Fiber.Maybe.equal r.fiber owner then
            match r.head with
            | { trigger; fiber } :: rest ->
                let after = Locked { r with fiber; head = rest } in
                transfer_as owner t backoff before after trigger
            | [] -> begin
                match List.rev r.tail with
                | { trigger; fiber } :: rest ->
                    let after = Locked { fiber; head = rest; tail = [] } in
                    transfer_as owner t backoff before after trigger
                | [] ->
                    if not (Atomic.compare_and_set t before Unlocked) then
                      unlock_as owner t (Backoff.once backoff)
              end
          else not_owner ()

    and transfer_as owner t backoff before after trigger =
      if Atomic.compare_and_set t before after then Trigger.signal trigger
      else unlock_as owner t (Backoff.once backoff)

    let[@inline] unlock ?checked t =
      let owner = Fiber.Maybe.current_if checked in
      unlock_as owner t Backoff.default

    let rec cleanup_as entry t backoff =
      (* We have been canceled.  If we are the owner, we must unlock the mutex.
         Otherwise we must remove our entry from the queue. *)
      match Atomic.get t with
      | Locked r as before ->
          (* At this point we must use strict physical equality [==] rather than
             [Fiber.Maybe.equal]! *)
          if r.fiber == entry.fiber then unlock_as entry.fiber t backoff
          else if r.head != [] then
            match List_ext.drop_first_or_not_found entry r.head with
            | head ->
                let after = Locked { r with head } in
                cancel_as entry t backoff before after
            | exception Not_found ->
                let tail = List_ext.drop_first_or_not_found entry r.tail in
                let after = Locked { r with tail } in
                cancel_as entry t backoff before after
          else
            let tail =
              List_ext.drop_first_or_not_found entry r.tail (* wont raise *)
            in
            let after = Locked { r with tail } in
            cancel_as entry t backoff before after
      | Unlocked -> unlocked () (* impossible *)

    and cancel_as fiber t backoff before after =
      if not (Atomic.compare_and_set t before after) then
        cleanup_as fiber t (Backoff.once backoff)

    let rec lock_as fiber t backoff =
      match Atomic.get t with
      | Unlocked as before ->
          let after =
            if fiber == Fiber.Maybe.nothing then locked_nothing
            else Locked { fiber; head = []; tail = [] }
          in
          if not (Atomic.compare_and_set t before after) then
            lock_as fiber t (Backoff.once backoff)
      | Locked r as before ->
          let fiber = Fiber.Maybe.or_current fiber in
          if Fiber.Maybe.unequal r.fiber fiber then
            let trigger = Trigger.create () in
            let entry = { trigger; fiber } in
            let after =
              if r.head == [] then
                Locked
                  { r with head = List.rev_append r.tail [ entry ]; tail = [] }
              else Locked { r with tail = entry :: r.tail }
            in
            if Atomic.compare_and_set t before after then begin
              match Trigger.await trigger with
              | None -> ()
              | Some exn_bt ->
                  cleanup_as entry t Backoff.default;
                  Exn_bt.raise exn_bt
            end
            else lock_as fiber t (Backoff.once backoff)
          else owner ()

    let[@inline] lock ?checked t =
      let fiber = Fiber.Maybe.current_and_check_if checked in
      lock_as fiber t Backoff.default

    let try_lock ?checked t =
      let fiber = Fiber.Maybe.current_and_check_if checked in
      Atomic.get t == Unlocked
      && Atomic.compare_and_set t Unlocked
           (if fiber == Fiber.Maybe.nothing then locked_nothing
            else Locked { fiber; head = []; tail = [] })

    let protect ?checked t body =
      let fiber = Fiber.Maybe.current_and_check_if checked in
      lock_as fiber t Backoff.default;
      match body () with
      | value ->
          unlock_as fiber t Backoff.default;
          value
      | exception exn ->
          let bt = Printexc.get_raw_backtrace () in
          unlock_as fiber t Backoff.default;
          Printexc.raise_with_backtrace exn bt
  end

  module Condition = struct
    open Picos

    type state =
      | Empty
      | Queue of { head : Trigger.t list; tail : Trigger.t list }

    type t = state Atomic.t

    let create ?(padded = false) () =
      let t = Atomic.make Empty in
      if padded then Multicore_magic.copy_as_padded t else t

    let broadcast t =
      if Atomic.get t != Empty then
        match Atomic.exchange t Empty with
        | Empty -> ()
        | Queue r ->
            List.iter Trigger.signal r.head;
            List.iter Trigger.signal (List.rev r.tail)

    (* We try to avoid starvation of signal by making it so that when, at the start
       of signal or wait, the head is empty, the tail is reversed into the head.
       This way both signal and wait attempt O(1) and O(n) operations at the same
       time. *)

    let rec signal t backoff =
      match Atomic.get t with
      | Empty -> ()
      | Queue r as before -> begin
          match r.head with
          | trigger :: head ->
              signal_cas t backoff before
                (if head == [] && r.tail == [] then Empty
                 else Queue { r with head })
                trigger
          | [] -> begin
              match List.rev r.tail with
              | trigger :: head ->
                  signal_cas t backoff before
                    (if head == [] then Empty else Queue { head; tail = [] })
                    trigger
              | [] -> failwith "impossible"
            end
        end

    and signal_cas t backoff before after trigger =
      if Atomic.compare_and_set t before after then Trigger.signal trigger
      else signal t (Backoff.once backoff)

    let signal t = signal t Backoff.default

    let rec cleanup backoff trigger t =
      (* We have been canceled.  If we can't drop our trigger from the variable, we
         signal the next trigger in queue to make sure each signal wakes up at least
         one non-canceled waiter if possible. *)
      match Atomic.get t with
      | Empty -> ()
      | Queue r as before -> begin
          if r.head != [] then
            match List_ext.drop_first_or_not_found trigger r.head with
            | head ->
                cleanup_cas backoff trigger t before
                  (if head == [] && r.tail == [] then Empty
                   else Queue { r with head })
            | exception Not_found -> begin
                match List_ext.drop_first_or_not_found trigger r.tail with
                | tail ->
                    cleanup_cas backoff trigger t before (Queue { r with tail })
                | exception Not_found -> signal t
              end
          else
            match List_ext.drop_first_or_not_found trigger r.tail with
            | tail ->
                cleanup_cas backoff trigger t before
                  (if tail == [] then Empty else Queue { head = []; tail })
            | exception Not_found -> signal t
        end

    and cleanup_cas backoff trigger t before after =
      if not (Atomic.compare_and_set t before after) then
        cleanup (Backoff.once backoff) trigger t

    let rec wait t mutex trigger fiber backoff =
      let before = Atomic.get t in
      let after =
        match before with
        | Empty -> Queue { head = [ trigger ]; tail = [] }
        | Queue r ->
            if r.head != [] then Queue { r with tail = trigger :: r.tail }
            else Queue { head = List.rev_append r.tail [ trigger ]; tail = [] }
      in
      if Atomic.compare_and_set t before after then begin
        Mutex.unlock_as (Fiber.Maybe.of_fiber fiber) mutex Backoff.default;
        let result = Trigger.await trigger in
        let forbid = Fiber.exchange fiber ~forbid:true in
        Mutex.lock_as (Fiber.Maybe.of_fiber fiber) mutex Backoff.default;
        Fiber.set fiber ~forbid;
        match result with
        | None -> ()
        | Some exn_bt ->
            cleanup Backoff.default trigger t;
            Exn_bt.raise exn_bt
      end
      else wait t mutex trigger fiber (Backoff.once backoff)

    let wait t mutex =
      let fiber = Fiber.current () in
      let trigger = Trigger.create () in
      wait t mutex trigger fiber Backoff.default
  end
end

module Picos_structured = struct
  module Finally = struct
    open Picos

    type 'a finally = ('a -> unit) * (unit -> 'a)

    let[@inline] finally release acquire = (release, acquire)

    (** This function is marked [@inline never] to ensure that there are no
    allocations between the [acquire ()] and the [match ... with] nor before
    [release].  Allocations here would mean that e.g. pressing Ctrl-C, i.e.
    [SIGINT], at the right moment could mean that [release] would not be called
    after [acquire]. *)
    let[@inline never] ( let@ ) (release, acquire) body =
      let x = acquire () in
      match body x with
      | y ->
          release x;
          y
      | exception exn ->
          release x;
          raise exn

    type ('a, _) tdt =
      | Nothing : ('a, [> `Nothing ]) tdt
      | Resource : {
          mutable resource : 'a;
          release : 'a -> unit;
          moved : Trigger.t;
        }
          -> ('a, [> `Resource ]) tdt

    type 'a moveable = ('a, [ `Nothing | `Resource ]) tdt Atomic.t

    let ( let^ ) (release, acquire) body =
      let moveable = Atomic.make Nothing in
      let acquire () =
        let (Resource r as state : (_, [ `Resource ]) tdt) =
          Resource
            { resource = Obj.magic (); release; moved = Trigger.create () }
        in
        r.resource <- acquire ();
        Atomic.set moveable state;
        moveable
      in
      let release moveable =
        match Atomic.get moveable with
        | Nothing -> ()
        | Resource r -> begin
            match Trigger.await r.moved with
            | None -> ()
            | Some exn_bt -> begin
                match Atomic.exchange moveable Nothing with
                | Nothing -> ()
                | Resource r ->
                    r.release r.resource;
                    Exn_bt.raise exn_bt
              end
          end
      in
      ( let@ ) (release, acquire) body

    let[@inline never] check_no_resource () =
      (* In case of cancelation this is not considered an error as the resource was
         (likely) released by the parent. *)
      Fiber.check (Fiber.current ());
      invalid_arg "no resource to move"

    let move moveable =
      match Atomic.get moveable with
      | Nothing -> check_no_resource ()
      | Resource r ->
          let acquire () =
            match Atomic.exchange moveable Nothing with
            | Nothing -> check_no_resource ()
            | Resource r ->
                Trigger.signal r.moved;
                r.resource
          in
          (r.release, acquire)
  end

  module Control = struct
    open Picos

    exception Terminate

    let terminate_bt = Exn_bt.get_callstack 0 Terminate

    let terminate_bt ?callstack () =
      match callstack with
      | None -> terminate_bt
      | Some n -> Exn_bt.get_callstack n Terminate

    exception Errors of Exn_bt.t list

    let () =
      Printexc.register_printer @@ function
      | Errors exn_bts ->
          let causes =
            List.map
              (fun exn_bt -> Printexc.to_string exn_bt.Exn_bt.exn)
              exn_bts
            |> String.concat "; "
          in
          Some (Printf.sprintf "Errors[%s]" causes)
      | _ -> None

    module Errors = struct
      type t = Exn_bt.t list Atomic.t

      let create () = Atomic.make []

      let rec check (exn_bts : Exn_bt.t list) exns =
        match exn_bts with
        | [] -> ()
        | [ exn_bt ] ->
            Printexc.raise_with_backtrace (Errors (exn_bt :: exns)) exn_bt.bt
        | exn_bt :: exn_bts -> check exn_bts (exn_bt :: exns)

      let check t =
        match Atomic.get t with
        | [] -> ()
        | [ exn_bt ] -> Exn_bt.raise exn_bt
        | exn_bts -> check exn_bts []

      let rec push t exn_bt backoff =
        let before = Atomic.get t in
        let after = exn_bt :: before in
        if not (Atomic.compare_and_set t before after) then
          push t exn_bt (Backoff.once backoff)

      let push t exn_bt = push t exn_bt Backoff.default
    end

    let raise_if_canceled () = Fiber.check (Fiber.current ())
    let yield = Fiber.yield
    let sleep = Fiber.sleep

    let block () =
      match Trigger.await (Trigger.create ()) with
      | None -> failwith "impossible"
      | Some exn_bt -> Exn_bt.raise exn_bt

    let protect thunk = Fiber.forbid (Fiber.current ()) thunk
  end

  module Bundle = struct
    open Picos

    type t = {
      num_fibers : int Atomic.t;
      bundle : unit Computation.t;
      errors : Control.Errors.t;
      finished : Trigger.t;
    }

    let terminate ?callstack t =
      let terminate_bt = Control.terminate_bt ?callstack () in
      Computation.cancel t.bundle terminate_bt

    let error ?callstack t (exn_bt : Exn_bt.t) =
      if exn_bt.Exn_bt.exn != Control.Terminate then begin
        terminate ?callstack t;
        Control.Errors.push t.errors exn_bt
      end

    let decr t =
      let n = Atomic.fetch_and_add t.num_fibers (-1) in
      if n = 1 then begin
        Computation.finish t.bundle;
        Trigger.signal t.finished
      end

    let await t fiber packed canceler =
      decr t;
      Fiber.set_computation fiber packed;
      let forbid = Fiber.exchange fiber ~forbid:true in
      Trigger.await t.finished |> ignore;
      Fiber.set fiber ~forbid;
      let (Packed parent) = packed in
      Computation.detach parent canceler;
      Control.Errors.check t.errors;
      Fiber.check fiber

    let join_after fn =
      let t =
        let num_fibers = Atomic.make 1 in
        let bundle = Computation.create () in
        let errors = Control.Errors.create () in
        let finished = Trigger.create () in
        { num_fibers; bundle; errors; finished }
      in
      let fiber = Fiber.current () in
      let (Packed parent as packed) = Fiber.get_computation fiber in
      let bundle = Computation.Packed t.bundle in
      let canceler = Computation.attach_canceler ~from:parent ~into:t.bundle in
      (* TODO: Ideally there should be no poll point betweem [attach_canceler] and
         the [match ... with] below. *)
      Fiber.set_computation fiber bundle;
      match fn t with
      | value ->
          await t fiber packed canceler;
          value
      | exception exn ->
          let exn_bt = Exn_bt.get exn in
          error t exn_bt;
          await t fiber packed canceler;
          Exn_bt.raise exn_bt

    let[@inline never] completed () = invalid_arg "already completed"

    let rec incr t backoff =
      let before = Atomic.get t.num_fibers in
      if before = 0 then completed ()
      else if not (Atomic.compare_and_set t.num_fibers before (before + 1)) then
        incr t (Backoff.once backoff)

    let fork_as_promise t thunk =
      incr t Backoff.default;
      let child = Computation.create () in
      try
        let canceler = Computation.attach_canceler ~from:t.bundle ~into:child in
        let main () =
          begin
            match thunk () with
            | value -> Computation.return child value
            | exception exn ->
                let exn_bt = Exn_bt.get exn in
                Computation.cancel child exn_bt;
                error t exn_bt
          end;
          Computation.detach t.bundle canceler;
          decr t
        in
        Fiber.spawn ~forbid:false child [ main ];
        child
      with canceled_exn ->
        decr t;
        raise canceled_exn

    let fork t thunk = fork_as_promise t thunk |> ignore

    (* *)

    let is_running t = Computation.is_running t.bundle
    let unsafe_incr t = Atomic.incr t.num_fibers
    let unsafe_reset t = Atomic.set t.num_fibers 1
  end

  module Run = struct
    open Picos

    let wrap_all t main =
      Bundle.unsafe_incr t;
      fun () ->
        if Bundle.is_running t then begin
          try main () with exn -> Bundle.error t (Exn_bt.get exn)
        end;
        Bundle.decr t

    let wrap_any t main =
      Bundle.unsafe_incr t;
      fun () ->
        if Bundle.is_running t then begin
          try
            main ();
            Bundle.terminate t
          with exn -> Bundle.error t (Exn_bt.get exn)
        end;
        Bundle.decr t

    let run actions wrap =
      Bundle.join_after @@ fun t ->
      try
        let mains = List.map (wrap t) actions in
        Fiber.spawn ~forbid:false t.bundle mains
      with exn ->
        Bundle.unsafe_reset t;
        raise exn

    let all actions = run actions wrap_all
    let any actions = run actions wrap_any
  end
end

module Picos_rc = struct
  let[@inline never] created () =
    invalid_arg "resource already previously created"

  let[@inline never] disposed () =
    invalid_arg "resource already previously disposed"

  let bt =
    if Printexc.backtrace_status () then None
    else Some (Printexc.get_callstack 0)

  let count_shift = 2
  let count_1 = 1 lsl count_shift
  let dispose_bit = 0b01
  let closed_bit = 0b10

  module type Resource = sig
    (** A resource that must be explicitly {{!val-dispose} disposed}. *)

    type t
    (** Represents a disposable resource. *)

    val equal : t -> t -> bool
    (** [equal resource1 resource2] determines whether [resource1] and [resource2]
      are one and the same. *)

    val hash : t -> int
    (** [hash resource] computes the hash value for [resource]. *)

    val dispose : t -> unit
    (** [dispose resource] releases the resource.

      ⚠️ The physical [resource] value may be reused only after [dispose] has
      been called on it. *)
  end

  module Make (Resource : Resource) () = struct
    module Resource = Resource

    type entry = { count_and_bits : int; bt : Printexc.raw_backtrace }

    let ht = Picos_htbl.create ~hashed_type:(module Resource) ()

    type t = Resource.t

    let create ?(dispose = true) t =
      let bt =
        match bt with Some bt -> bt | None -> Printexc.get_callstack 15
      in
      if
        Picos_htbl.try_add ht t
          (Atomic.make { count_and_bits = count_1 lor Bool.to_int dispose; bt })
      then t
      else begin
        (* We assume resources may only be reused after they have been
           disposed. *)
        created ()
      end

    let unsafe_get = Fun.id

    let rec incr t entry backoff =
      let before = Atomic.get entry in
      if
        before.count_and_bits < count_1
        || before.count_and_bits land closed_bit <> 0
      then disposed ()
      else
        let count_and_bits = before.count_and_bits + count_1 in
        let after = { before with count_and_bits } in
        if not (Atomic.compare_and_set entry before after) then
          incr t entry (Backoff.once backoff)

    let incr t =
      match Picos_htbl.find_exn ht t with
      | exception Not_found -> disposed ()
      | entry -> incr t entry Backoff.default

    let rec decr closed_bit t entry backoff =
      let before = Atomic.get entry in
      let count_and_bits = (before.count_and_bits - count_1) lor closed_bit in
      if count_and_bits < 0 then disposed ()
      else
        let after = { before with count_and_bits } in
        if not (Atomic.compare_and_set entry before after) then
          decr closed_bit t entry (Backoff.once backoff)
        else if count_and_bits < count_1 then begin
          Picos_htbl.try_remove ht t |> ignore;
          (* We must dispose the resource as the last step, because the value
             might be reused after it has been disposed. *)
          if after.count_and_bits land dispose_bit <> 0 then Resource.dispose t
        end

    let decr ?close t =
      match Picos_htbl.find_exn ht t with
      | exception Not_found -> disposed ()
      | entry ->
          decr
            (match close with
            | None | Some false -> 0
            | Some true -> closed_bit)
            t entry Backoff.default

    type info = {
      resource : Resource.t;
      count : int;
      closed : bool;
      dispose : bool;
      bt : Printexc.raw_backtrace;
    }

    let infos () =
      Picos_htbl.to_seq ht
      |> Seq.map @@ fun (resource, entry) ->
         let { count_and_bits; bt } = Atomic.get entry in
         let count = count_and_bits lsr count_shift in
         let closed = count_and_bits land closed_bit <> 0 in
         let dispose = count_and_bits land dispose_bit <> 0 in
         { resource; count; closed; dispose; bt }
  end
end

module Picos_fd = struct
  module File_descr = struct
    type t = Unix.file_descr

    let equal : t -> t -> bool = ( == )

    let hash (fd : t) =
      if Obj.is_int (Obj.repr fd) then Obj.magic fd else Hashtbl.hash fd

    let dispose = Unix.close
  end

  include Picos_rc.Make (File_descr) ()
end

module Picos_select = struct
  open Picos

  let handle_sigchld_bit = 0b01
  let select_thread_running_on_main_domain_bit = 0b10

  type config = {
    mutable bits : int;
    mutable intr_sig : int;
    mutable intr_sigs : int list;
  }

  let config = { bits = 0; intr_sig = 0; intr_sigs = [] }

  (* *)

  type return =
    | Return : {
        value : 'a;
        computation : 'a Computation.t;
        mutable alive : bool;
      }
        -> return

  (** We use random numbers as keys for the awaiters. *)
  module RandomInt = struct
    type t = int

    let equal = Int.equal
    let hash = Fun.id
  end

  let chld_awaiters = Picos_htbl.create ~hashed_type:(module RandomInt) ()

  (* *)

  type cancel_at =
    | Cancel_at : {
        time : Mtime.span;
        exn_bt : Exn_bt.t;
        computation : 'a Computation.t;
      }
        -> cancel_at

  module Q =
    Psq.Make
      (Int)
      (struct
        type t = cancel_at

        let compare (Cancel_at l) (Cancel_at r) =
          Mtime.Span.compare l.time r.time
      end)

  type return_on =
    | Return_on : {
        file_descr : Picos_fd.t;
        value : 'a;
        computation : 'a Computation.t;
        mutable alive : bool;
      }
        -> return_on

  type phase = Continue | Select | Waking_up | Process

  type state = {
    phase : phase Atomic.t;
    mutable state : [ `Initial | `Starting | `Alive | `Stopping | `Stopped ];
    mutable exn_bt : Exn_bt.t;
    mutable pipe_inn : Unix.file_descr;
    mutable pipe_out : Unix.file_descr;
    byte : Bytes.t;
    (* *)
    timeouts : Q.t Atomic.t;
    mutable next_id : int;
    (* *)
    new_rd : return_on list ref;
    new_wr : return_on list ref;
    new_ex : return_on list ref;
  }

  type intr_status = Cleared | Signaled

  type _ tdt =
    | Nothing : [> `Nothing ] tdt
    | Req : {
        state : state;
        mutable unused : bool;
        mutable computation : intr_status Computation.t;
      }
        -> [> `Req ] tdt

  type req = R : [< `Nothing | `Req ] tdt -> req [@@unboxed]
  type counter_state = { value : int; req : req }

  let intr_pending = Atomic.make { value = 0; req = R Nothing }
  let exit_exn_bt = Exn_bt.get_callstack 0 Exit

  let cleared =
    let computation = Computation.create () in
    Computation.return computation Cleared;
    computation

  let intr_key =
    Picos_thread.TLS.new_key @@ fun () : [ `Req ] tdt ->
    invalid_arg "has not been configured"

  let key =
    Domain.DLS.new_key @@ fun () ->
    {
      phase = Atomic.make Continue;
      state = `Initial;
      exn_bt = exit_exn_bt;
      pipe_inn = Unix.stdin;
      pipe_out = Unix.stdin;
      byte = Bytes.create 1;
      timeouts = Atomic.make Q.empty;
      next_id = 0;
      new_rd = ref [];
      new_wr = ref [];
      new_ex = ref [];
    }

  let[@poll error] [@inline never] try_transition s from into =
    s.state == from
    && begin
         s.state <- into;
         true
       end

  let[@poll error] [@inline never] transition s into =
    let from = s.state in
    s.state <- into;
    from

  let rec wakeup s from =
    match Atomic.get s.phase with
    | Process | Waking_up ->
        (* The thread will process the fds and timeouts before next select. *)
        ()
    | Continue ->
        if Atomic.compare_and_set s.phase Continue Process then
          (* We managed to signal the wakeup before the thread was ready to call
             select and the thread will notice this without us needing to write to
             the pipe. *)
          ()
        else
          (* Either the thread called select or another wakeup won the race.  We
             need to retry. *)
          wakeup s from
    | Select ->
        if Atomic.compare_and_set s.phase Select Waking_up then
          if s.state == from then
            (* We are now responsible for writing to the pipe to force the thread
               to exit the select. *)
            let n = Unix.write s.pipe_out s.byte 0 1 in
            assert (n = 1)

  type fos = {
    n : int;
    unique_fds : Unix.file_descr list;
    ops : return_on list;
  }

  let fos_empty = { n = 1; unique_fds = []; ops = [] }

  module Ht = Hashtbl.Make (Picos_fd.Resource)

  let rec process_fds ht unique_fds ops = function
    | [] ->
        if unique_fds == [] && ops == [] then fos_empty
        else { n = Ht.length ht; unique_fds; ops }
    | (Return_on r as op) :: ops_todo ->
        if Computation.is_running r.computation then begin
          let file_descr = Picos_fd.unsafe_get r.file_descr in
          match Ht.find ht file_descr with
          | `Return ->
              Picos_fd.decr r.file_descr;
              r.alive <- false;
              Computation.return r.computation r.value;
              process_fds ht unique_fds ops ops_todo
          | `Alive -> process_fds ht unique_fds (op :: ops) ops_todo
          | exception Not_found ->
              Ht.add ht file_descr `Alive;
              process_fds ht (file_descr :: unique_fds) (op :: ops) ops_todo
        end
        else begin
          Picos_fd.decr r.file_descr;
          process_fds ht unique_fds ops ops_todo
        end

  let process_fds unique_fds fos new_ops =
    if fos.ops == [] && new_ops == [] then fos_empty
    else
      let ht = Ht.create fos.n in
      unique_fds |> List.iter (fun fd -> Ht.add ht fd `Return);
      let r = process_fds ht [] [] fos.ops in
      if new_ops == [] then r else process_fds ht r.unique_fds r.ops new_ops

  let rec process_timeouts s =
    let before = Atomic.get s.timeouts in
    match Q.pop before with
    | None -> -1.0
    | Some ((_, Cancel_at e), after) ->
        let elapsed = Mtime_clock.elapsed () in
        if Mtime.Span.compare e.time elapsed <= 0 then begin
          if Atomic.compare_and_set s.timeouts before after then
            Computation.cancel e.computation e.exn_bt;
          process_timeouts s
        end
        else
          Mtime.Span.to_float_ns (Mtime.Span.abs_diff e.time elapsed)
          *. (1. /. 1_000_000_000.)

  let rec select_thread s timeout rd wr ex =
    if s.state == `Alive then (
      let rd_fds, wr_fds, ex_fds =
        if Atomic.compare_and_set s.phase Continue Select then begin
          try
            Unix.select
              (s.pipe_inn :: rd.unique_fds)
              wr.unique_fds ex.unique_fds timeout
          with Unix.Unix_error (EINTR, _, _) -> ([], [], [])
        end
        else ([], [], [])
      in
      begin
        match Atomic.exchange s.phase Continue with
        | Select | Process | Continue -> ()
        | Waking_up ->
            let n = Unix.read s.pipe_inn s.byte 0 1 in
            assert (n = 1)
      end;
      let rd =
        process_fds rd_fds rd (Picos_thread_atomic.exchange s.new_rd [])
      in
      let wr =
        process_fds wr_fds wr (Picos_thread_atomic.exchange s.new_wr [])
      in
      let ex =
        process_fds ex_fds ex (Picos_thread_atomic.exchange s.new_ex [])
      in
      let timeout = process_timeouts s in
      let timeout =
        let state = Atomic.get intr_pending in
        if state.value = 0 then timeout
        else begin
          assert (0 < state.value);
          Unix.kill (Unix.getpid ()) config.intr_sig;
          let idle = 0.000_001 (* 1μs *) in
          if timeout < 0.0 || idle <= timeout then idle else timeout
        end
      in
      select_thread s timeout rd wr ex)

  let select_thread s =
    if Domain.is_main_domain () then
      config.bits <- select_thread_running_on_main_domain_bit lor config.bits;
    if not Sys.win32 then begin
      Thread.sigmask SIG_BLOCK config.intr_sigs |> ignore;
      Thread.sigmask
        (if config.bits land handle_sigchld_bit <> 0 then SIG_UNBLOCK
         else SIG_BLOCK)
        [ Sys.sigchld ]
      |> ignore
    end;
    begin
      try
        let pipe_inn, pipe_out = Unix.pipe ~cloexec:true () in
        s.pipe_inn <- pipe_inn;
        s.pipe_out <- pipe_out;
        if try_transition s `Starting `Alive then
          select_thread s (-1.0) fos_empty fos_empty fos_empty
      with exn -> s.exn_bt <- Exn_bt.get exn
    end;
    transition s `Stopped |> ignore;
    if s.pipe_inn != Unix.stdin then Unix.close s.pipe_inn;
    if s.pipe_out != Unix.stdin then Unix.close s.pipe_out

  let[@poll error] [@inline never] try_configure ~intr_sig ~intr_sigs
      ~handle_sigchld =
    config.intr_sigs == []
    && begin
         config.bits <- Bool.to_int handle_sigchld;
         config.intr_sig <- intr_sig;
         config.intr_sigs <- intr_sigs;
         true
       end

  let is_sigchld signum = signum = Sys.sigchld
  let is_intr_sig signum = signum = config.intr_sig

  let rec configure ?(intr_sig = Sys.sigusr2) ?(handle_sigchld = true) () =
    if not (Picos_thread.is_main_thread ()) then
      invalid_arg "must be called from the main thread on the main domain";
    assert (Sys.sigabrt = -1 && Sys.sigxfsz < Sys.sigabrt);
    if intr_sig < Sys.sigxfsz || 0 <= intr_sig || intr_sig = Sys.sigchld then
      invalid_arg "invalid interrupt signal number";
    if not (try_configure ~intr_sig ~intr_sigs:[ intr_sig ] ~handle_sigchld)
    then invalid_arg "already configured";

    if not Sys.win32 then begin
      if config.bits land handle_sigchld_bit <> 0 then begin
        let previously_blocked = Thread.sigmask SIG_BLOCK [ Sys.sigchld ] in
        assert (not (List.exists is_sigchld previously_blocked));
        let old_behavior =
          Sys.signal Sys.sigchld (Sys.Signal_handle handle_signal)
        in
        assert (old_behavior == Signal_default)
      end;
      begin
        let previously_blocked = Thread.sigmask SIG_BLOCK config.intr_sigs in
        assert (not (List.exists is_intr_sig previously_blocked));
        let old_behavior =
          Sys.signal config.intr_sig (Sys.Signal_handle handle_signal)
        in
        assert (old_behavior == Signal_default)
      end
    end

  and handle_signal signal =
    if signal = Sys.sigchld then begin
      Picos_htbl.remove_all chld_awaiters
      |> Seq.iter @@ fun (_, Return r) ->
         r.alive <- false;
         Computation.return r.computation r.value
    end
    else if signal = config.intr_sig then
      let (Req r) = Picos_thread.TLS.get intr_key in
      Computation.return r.computation Signaled

  let check_configured () = if config.intr_sigs = [] then configure ()

  let[@inline never] init s =
    check_configured ();
    if try_transition s `Initial `Starting then begin
      match Thread.create select_thread s with
      | thread ->
          Domain.at_exit @@ fun () ->
          if try_transition s `Alive `Stopping then wakeup s `Stopping;
          Thread.join thread;
          if s.exn_bt != exit_exn_bt then Exn_bt.raise s.exn_bt
      | exception exn ->
          transition s `Stopped |> ignore;
          raise exn
    end;
    while s.state == `Starting do
      Thread.yield ()
    done;
    if s.state != `Alive then invalid_arg "domain has been terminated"

  let get () =
    let s = Domain.DLS.get key in
    if s.state != `Alive then init s;
    s

  (* *)

  let[@poll error] [@inline never] next_id t =
    let id = t.next_id in
    t.next_id <- id + 1;
    id

  let rec add_timeout s id entry =
    let before = Atomic.get s.timeouts in
    let after = Q.add id entry before in
    if Atomic.compare_and_set s.timeouts before after then
      match Q.min after with
      | Some (id', _) -> if id = id' then wakeup s `Alive
      | None -> ()
    else add_timeout s id entry

  let rec remove_action _trigger s id =
    let before = Atomic.get s.timeouts in
    let after = Q.remove id before in
    if not (Atomic.compare_and_set s.timeouts before after) then
      remove_action (Obj.magic ()) s id

  let to_deadline ~seconds =
    match Mtime.Span.of_float_ns (seconds *. 1_000_000_000.) with
    | None ->
        invalid_arg "seconds should be between 0 to pow(2, 53) nanoseconds"
    | Some span -> Mtime.Span.add (Mtime_clock.elapsed ()) span

  let[@alert "-handler"] cancel_after computation ~seconds exn_bt =
    let time = to_deadline ~seconds in
    let entry = Cancel_at { time; exn_bt; computation } in
    let s = get () in
    let id = next_id s in
    add_timeout s id entry;
    let remover = Trigger.from_action s id remove_action in
    if not (Computation.try_attach computation remover) then
      Trigger.signal remover

  (* *)

  let wakeup_action _trigger s (Return_on r) = if r.alive then wakeup s `Alive

  let[@alert "-handler"] rec insert_fd s fds (Return_on r as op) =
    let before = !fds in
    if Computation.is_running r.computation then
      if Picos_thread_atomic.compare_and_set fds before (Return_on r :: before)
      then
        let _ : bool =
          Computation.try_attach r.computation
            (Trigger.from_action s op wakeup_action)
        in
        wakeup s `Alive
      else insert_fd s fds op
    else Picos_fd.decr r.file_descr

  let return_on computation file_descr op value =
    Picos_fd.incr file_descr;
    let s = get () in
    insert_fd s
      (match op with `R -> s.new_rd | `W -> s.new_wr | `E -> s.new_ex)
      (Return_on { computation; file_descr; value; alive = true })

  let await_on file_descr op =
    let computation = Computation.create () in
    return_on computation file_descr op file_descr;
    try Computation.await computation
    with exn ->
      Computation.cancel computation exit_exn_bt;
      raise exn

  (* *)

  module Intr = struct
    type t = req

    let[@inline] use = function
      | R Nothing -> ()
      | R (Req r) -> r.unused <- false

    (** This is used to ensure that the [intr_pending] counter is incremented
      exactly once before the counter is decremented. *)
    let rec incr_once (Req r as req : [ `Req ] tdt) backoff =
      let before = Atomic.get intr_pending in
      (* [intr_pending] must be read before [r.unused]! *)
      r.unused && before.req != R req
      && begin
           use before.req;
           let after = { value = before.value + 1; req = R req } in
           if Atomic.compare_and_set intr_pending before after then
             after.value = 1
           else incr_once req (Backoff.once backoff)
         end

    let intr_action trigger (Req r as req : [ `Req ] tdt) id =
      match Computation.await r.computation with
      | Cleared ->
          (* No signal needs to be delivered. *)
          remove_action trigger r.state id
      | Signaled ->
          (* Signal was delivered before timeout. *)
          remove_action trigger r.state id;
          if incr_once req Backoff.default then
            (* We need to make sure at least one select thread will keep on
               triggering interrupts. *)
            wakeup r.state `Alive
      | exception Exit ->
          (* The timeout was triggered.  This must have been called from the
             select thread, which will soon trigger an interrupt. *)
          let _ : bool = incr_once req Backoff.default in
          ()

    let nothing = R Nothing

    let[@alert "-handler"] req ~seconds =
      if Sys.win32 then invalid_arg "not supported on Windows"
      else begin
        let time = to_deadline ~seconds in
        (* assert (not (Computation.is_running r.computation)); *)
        let state = get () in
        let id = next_id state in
        let (Req r as req : [ `Req ] tdt) =
          Req { state; unused = true; computation = cleared }
        in
        let computation = Computation.with_action req id intr_action in
        r.computation <- computation;
        Picos_thread.TLS.set intr_key req;
        let entry = Cancel_at { time; exn_bt = exit_exn_bt; computation } in
        add_timeout state id entry;
        let was_blocked : int list =
          Thread.sigmask SIG_UNBLOCK config.intr_sigs
        in
        assert (List.exists is_intr_sig was_blocked);
        R req
      end

    let rec decr backoff =
      let before = Atomic.get intr_pending in
      use before.req;
      let after = { value = before.value - 1; req = R Nothing } in
      assert (0 <= after.value);
      if not (Atomic.compare_and_set intr_pending before after) then
        decr (Backoff.once backoff)

    let clr = function
      | R Nothing -> ()
      | R (Req r as req) ->
          let was_blocked : int list =
            Thread.sigmask SIG_BLOCK config.intr_sigs
          in
          assert (not (List.exists is_intr_sig was_blocked));
          if not (Computation.try_return r.computation Cleared) then begin
            let _ : bool = incr_once req Backoff.default in
            (* We ensure that the associated increment has been done before we
               decrement so that the [intr_pending] counter is never too low. *)
            decr Backoff.default
          end
  end

  (* *)

  let rec insert return =
    let id = Random.bits () in
    if Picos_htbl.try_add chld_awaiters id return then id else insert return

  let[@alert "-handler"] return_on_sigchld computation value =
    if
      config.bits
      land (select_thread_running_on_main_domain_bit lor handle_sigchld_bit)
      = handle_sigchld_bit
    then
      (* Ensure there is at least one thread handling [Sys.sigchld] signals. *)
      get () |> ignore;
    let return = Return { value; computation; alive = true } in
    let id = insert return in
    let remover =
      Trigger.from_action id return
      @@ fun _trigger id (Return this_r as this) ->
      if this_r.alive then begin
        this_r.alive <- false;
        (* It should be extremely rare, but possible, that the return was already
           removed and another added just at this point and so we must account for
           the possibility and make sure that whatever we remove is completed. *)
        match Picos_htbl.remove_exn chld_awaiters id with
        | Return that_r as that ->
            if this != that then
              Computation.return that_r.computation that_r.value
        | exception Not_found -> ()
      end
    in
    if not (Computation.try_attach computation remover) then
      Trigger.signal remover
end

module Picos_stdio = struct
  open Picos

  let nonblock_fds =
    Picos_htbl.create ~hashed_type:(module Picos_fd.Resource) ()

  module Unix = struct
    include Unix

    type file_descr = Picos_fd.t

    let is_oob flag = MSG_OOB == flag
    let is_nonblock flag = O_NONBLOCK == flag

    (* The retry wrappers below are written to avoid closure allocations. *)

    (* [EAGAIN] (and [EWOULDBLOCK]) indicates that the operation would have
       blocked and so we await using the [select] thread for the file descriptor.

       [EINTR] indicates that the operation was interrupted by a signal, which
       usually shouldn't happen with non-blocking operations.  We don't want to
       block, so we do the same thing as with [EAGAIN]. *)

    let[@inline] intr_req fd =
      if Sys.win32 || Picos_htbl.mem nonblock_fds (Picos_fd.unsafe_get fd) then
        Picos_select.Intr.nothing
      else Picos_select.Intr.req ~seconds:0.000_01 (* 10μs - TODO *)

    let rec again_0 fd fn op =
      let intr = intr_req fd in
      match fn (Picos_fd.unsafe_get fd) with
      | result ->
          Picos_select.Intr.clr intr;
          result
      | exception Unix.Unix_error ((EAGAIN | EINTR | EWOULDBLOCK), _, _) ->
          Picos_select.Intr.clr intr;
          again_0 (Picos_select.await_on fd op) fn op
      | exception exn ->
          Picos_select.Intr.clr intr;
          raise exn

    let rec again_cloexec_0 ?cloexec fd fn op =
      let intr = intr_req fd in
      match fn ?cloexec (Picos_fd.unsafe_get fd) with
      | result ->
          Picos_select.Intr.clr intr;
          result
      | exception Unix.Unix_error ((EAGAIN | EINTR | EWOULDBLOCK), _, _) ->
          Picos_select.Intr.clr intr;
          again_cloexec_0 ?cloexec (Picos_select.await_on fd op) fn op
      | exception exn ->
          Picos_select.Intr.clr intr;
          raise exn

    let rec again_3 fd x1 x2 x3 fn op =
      let intr = intr_req fd in
      match fn (Picos_fd.unsafe_get fd) x1 x2 x3 with
      | result ->
          Picos_select.Intr.clr intr;
          result
      | exception Unix.Unix_error ((EAGAIN | EINTR | EWOULDBLOCK), _, _) ->
          Picos_select.Intr.clr intr;
          again_3 (Picos_select.await_on fd op) x1 x2 x3 fn op
      | exception exn ->
          Picos_select.Intr.clr intr;
          raise exn

    let rec again_4 fd x1 x2 x3 x4 fn op =
      let intr = intr_req fd in
      match fn (Picos_fd.unsafe_get fd) x1 x2 x3 x4 with
      | result ->
          Picos_select.Intr.clr intr;
          result
      | exception Unix.Unix_error ((EAGAIN | EINTR | EWOULDBLOCK), _, _) ->
          Picos_select.Intr.clr intr;
          again_4 (Picos_select.await_on fd op) x1 x2 x3 x4 fn op
      | exception exn ->
          Picos_select.Intr.clr intr;
          raise exn

    let rec again_5 fd x1 x2 x3 x4 x5 fn op =
      let intr = intr_req fd in
      match fn (Picos_fd.unsafe_get fd) x1 x2 x3 x4 x5 with
      | result ->
          Picos_select.Intr.clr intr;
          result
      | exception Unix.Unix_error ((EAGAIN | EINTR | EWOULDBLOCK), _, _) ->
          Picos_select.Intr.clr intr;
          again_5 (Picos_select.await_on fd op) x1 x2 x3 x4 x5 fn op
      | exception exn ->
          Picos_select.Intr.clr intr;
          raise exn

    (* [EINPROGRESS] indicates that a socket operation is being performed
       asynchronously.  We await using the [select] thread for the operation to
       complete and then get the error from the socket. *)

    let progress_1 fd x1 fn op name =
      let intr = intr_req fd in
      match fn (Picos_fd.unsafe_get fd) x1 with
      | () -> Picos_select.Intr.clr intr
      | exception
          Unix.Unix_error ((EAGAIN | EINPROGRESS | EINTR | EWOULDBLOCK), _, _)
        -> begin
          (* The documentation of [bind] and [connect] does not mention [EAGAIN]
             (or [EWOULDBLOCK]), but on Windows we do seem to get those errors
             from [connect].

             The documentation of [bind] does not mention [EINTR].  Matching on
             that shouldn't cause issues with [bind].

             For [connect] both [EINPROGRESS] and [EINTR] mean that connection
             will be established asynchronously and we use [select] to wait. *)
          Picos_select.Intr.clr intr;
          let fd = Picos_select.await_on fd op in
          match Unix.getsockopt_error (Picos_fd.unsafe_get fd) with
          | None -> ()
          | Some error -> raise (Unix.Unix_error (error, name, ""))
        end
      | exception exn ->
          Picos_select.Intr.clr intr;
          raise exn

    let stdin = Picos_fd.create ~dispose:false Unix.stdin
    and stdout = Picos_fd.create ~dispose:false Unix.stdout
    and stderr = Picos_fd.create ~dispose:false Unix.stderr

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/open.html *)
    let openfile path flags file_perm =
      let fd = Picos_fd.create (Unix.openfile path flags file_perm) in
      if List.exists is_nonblock flags then begin
        let if_not_added_fd_has_been_closed_outside =
          Picos_htbl.try_add nonblock_fds (Picos_fd.unsafe_get fd) ()
        in
        assert if_not_added_fd_has_been_closed_outside
      end;
      fd

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/close.html *)
    let close fd =
      let _ : bool =
        Picos_htbl.try_remove nonblock_fds (Picos_fd.unsafe_get fd)
      in
      Picos_fd.decr ~close:true fd

    let close_pair (fd1, fd2) =
      close fd1;
      close fd2

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/fsync.html *)
    let fsync fd = again_0 fd Unix.fsync `W

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/read.html *)
    let read fd bytes pos len = again_3 fd bytes pos len Unix.read `R

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/write.html *)
    let write fd bytes pos len = again_3 fd bytes pos len Unix.write `W

    let single_write fd bytes pos len =
      again_3 fd bytes pos len Unix.single_write `W

    let write_substring fd string pos len =
      again_3 fd string pos len Unix.write_substring `W

    let single_write_substring fd string pos len =
      again_3 fd string pos len Unix.single_write_substring `W

    (* *)

    (*let in_channel_of_descr _ = failwith "TODO"*)
    (*let out_channel_of_descr _ = failwith "TODO"*)
    (*let descr_of_in_channel _ = failwith "TODO"*)
    (*let descr_of_out_channel _ = failwith "TODO"*)

    (* *)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/lseek.html *)
    let lseek fd amount seek_command =
      Unix.lseek (Picos_fd.unsafe_get fd) amount seek_command

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/ftruncate.html *)
    let ftruncate fd size = Unix.ftruncate (Picos_fd.unsafe_get fd) size

    (* *)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/fstat.html *)
    let fstat fd = Unix.fstat (Picos_fd.unsafe_get fd)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/isatty.html *)
    let isatty fd = Unix.isatty (Picos_fd.unsafe_get fd)

    (* *)

    module LargeFile = struct
      include Unix.LargeFile

      (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/lseek.html *)
      let lseek fd amount seek_command =
        Unix.LargeFile.lseek (Picos_fd.unsafe_get fd) amount seek_command

      (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/ftruncate.html *)
      let ftruncate fd size =
        Unix.LargeFile.ftruncate (Picos_fd.unsafe_get fd) size

      (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/fstat.html *)
      let fstat fd = Unix.LargeFile.fstat (Picos_fd.unsafe_get fd)
    end

    (* *)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/mmap.html

       This can raise EAGAIN, but it probably should not be handled? *)
    let map_file fd ?pos kind layout shared dims =
      Unix.map_file (Picos_fd.unsafe_get fd) ?pos kind layout shared dims

    (* *)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/fchmod.html *)
    let fchmod fd file_perm = Unix.fchmod (Picos_fd.unsafe_get fd) file_perm

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/fchown.html *)
    let fchown fd uid gid = Unix.fchown (Picos_fd.unsafe_get fd) uid gid

    (* *)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/dup.html *)
    let dup ?cloexec fd =
      Picos_fd.create (Unix.dup ?cloexec (Picos_fd.unsafe_get fd))

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/dup.html *)
    let dup2 ?cloexec src dst =
      Unix.dup2 ?cloexec (Picos_fd.unsafe_get src) (Picos_fd.unsafe_get dst)

    let set_nonblock fd =
      Unix.set_nonblock (Picos_fd.unsafe_get fd);
      Picos_htbl.try_add nonblock_fds (Picos_fd.unsafe_get fd) () |> ignore

    let clear_nonblock fd =
      Unix.clear_nonblock (Picos_fd.unsafe_get fd);
      Picos_htbl.try_remove nonblock_fds (Picos_fd.unsafe_get fd) |> ignore

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/fcntl.html *)
    let set_close_on_exec fd = Unix.set_close_on_exec (Picos_fd.unsafe_get fd)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/fcntl.html *)
    let clear_close_on_exec fd =
      Unix.clear_close_on_exec (Picos_fd.unsafe_get fd)

    (* *)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/pipe.html *)
    let pipe ?cloexec () =
      let inn, out = Unix.pipe ?cloexec () in
      (Picos_fd.create inn, Picos_fd.create out)

    (* *)

    let create_process prog args stdin stdout stderr =
      Unix.create_process prog args
        (Picos_fd.unsafe_get stdin)
        (Picos_fd.unsafe_get stdout)
        (Picos_fd.unsafe_get stderr)

    let create_process_env prog args env stdin stdout stderr =
      Unix.create_process_env prog args env
        (Picos_fd.unsafe_get stdin)
        (Picos_fd.unsafe_get stdout)
        (Picos_fd.unsafe_get stderr)

    (*let open_process_in _ = failwith "TODO"*)
    (*let open_process_out _ = failwith "TODO"*)
    (*let open_process _ = failwith "TODO"*)
    (*let open_process_full _ = failwith "TODO"*)
    (*let open_process_args _ = failwith "TODO"*)
    (*let open_process_args_in _ = failwith "TODO"*)
    (*let open_process_args_out _ = failwith "TODO"*)
    (*let open_process_args_full _ = failwith "TODO"*)
    (*let process_in_pid _ = failwith "TODO"*)
    (*let process_out_pid _ = failwith "TODO"*)
    (*let process_pid _ = failwith "TODO"*)
    (*let process_full_pid _ = failwith "TODO"*)
    (*let close_process_in _ = failwith "TODO"*)
    (*let close_process_out _ = failwith "TODO"*)
    (*let close_process _ = failwith "TODO"*)
    (*let close_process_full _ = failwith "TODO"*)

    (* *)

    module Wait_flag = struct
      let nohang_bit = 0b10
      let untraced_bit = 0b01

      (* Note that this is optimized to the identity function. *)
      let to_int = function WNOHANG -> 0 | WUNTRACED -> 1
      let to_bit flag = nohang_bit - to_int flag
      let () = assert (to_bit WNOHANG = nohang_bit)
      let () = assert (to_bit WUNTRACED = untraced_bit)

      let rec to_bits flags bits =
        match flags with
        | [] -> bits
        | flag :: flags -> to_bits flags (bits lor to_bit flag)

      let to_bits flags = to_bits flags 0

      let to_flags =
        [| []; [ WUNTRACED ]; [ WNOHANG ]; [ WNOHANG; WUNTRACED ] |]

      let to_flags bits = Array.get to_flags bits
    end

    let rec waitpid_unix ~bits ~pid =
      if bits land Wait_flag.nohang_bit <> 0 then
        Unix.waitpid (Wait_flag.to_flags bits) pid
      else
        let computation = Computation.create () in
        Picos_select.return_on_sigchld computation ();
        match
          Unix.waitpid (Wait_flag.to_flags (bits lor Wait_flag.nohang_bit)) pid
        with
        | exception Unix_error (EINTR, _, _) -> waitpid_unix ~bits ~pid
        | (pid_or_0, _) as result ->
            if pid_or_0 = 0 then begin
              Computation.await computation;
              waitpid_unix ~bits ~pid
            end
            else begin
              Computation.finish computation;
              result
            end
        | exception exn ->
            Computation.finish computation;
            raise exn

    let waitpid_win32 ~bits ~pid =
      if bits land Wait_flag.nohang_bit <> 0 then
        Unix.waitpid (Wait_flag.to_flags bits) pid
      else
        (* One way to provide a scheduler friendly [waitpid] on Windows would be
           to use a thread pool to run blocking operations on.  PR for a thread
           pool implemented in Picos would be welcome! *)
        invalid_arg "currently not supported on Windows without WNOHANG"

    let waitpid flags pid =
      let bits = Wait_flag.to_bits flags in
      if Sys.win32 then
        if pid <> -1 then waitpid_win32 ~bits ~pid
        else begin
          (* This should raise? *)
          Unix.waitpid flags pid
        end
      else waitpid_unix ~bits ~pid

    let wait () =
      if not Sys.win32 then waitpid_unix ~bits:0 ~pid:(-1)
      else begin
        (* This should raise [Invalid_argument] *)
        Unix.wait ()
      end

    (* *)

    let sh = "/bin/sh"

    let system cmd =
      if Sys.win32 then
        (* One way to provide a scheduler friendly [system] on Windows would be to
           use a thread pool to run blocking operations on.  PR for a thread pool
           implemented in Picos would be welcome! *)
        invalid_arg "currently not supported on Windows"
      else
        create_process sh [| sh; "-c"; cmd |] stdin stdout stderr
        |> waitpid [] |> snd

    (* *)

    let sleepf seconds = Fiber.sleep ~seconds
    let sleep seconds = Fiber.sleep ~seconds:(Float.of_int seconds)

    (* *)

    exception Done

    let done_bt = Exn_bt.get_callstack 0 Done

    let[@alert "-handler"] select rds wrs exs seconds =
      let overall = Computation.create () in
      let canceler =
        Trigger.from_action overall () @@ fun _ overall _ ->
        Picos_select.cancel_after overall ~seconds:0.0 done_bt
      in
      let prepare op fd =
        let computation = Computation.create () in
        if Computation.try_attach computation canceler then
          Picos_select.return_on computation fd op true;
        computation
      in
      let rdcs = List.map (prepare `R) rds in
      let wrcs = List.map (prepare `W) wrs in
      let excs = List.map (prepare `E) exs in
      let finisher =
        Trigger.from_action rdcs wrcs @@ fun _ rdcs wrcs ->
        let return_false computation = Computation.return computation false in
        List.iter return_false rdcs;
        List.iter return_false wrcs;
        List.iter return_false excs
      in
      if not (Computation.try_attach overall finisher) then
        Trigger.signal finisher
      else if 0.0 <= seconds then
        Picos_select.cancel_after overall ~seconds done_bt;
      match Computation.await overall with
      | () -> assert false
      | exception Done ->
          let[@tail_mod_cons] rec zip_filter pred xs ys =
            match (xs, ys) with
            | x :: xs, y :: ys ->
                if pred y then x :: zip_filter pred xs ys
                else zip_filter pred xs ys
            | _, _ -> []
          in
          ( zip_filter Computation.await rds rdcs,
            zip_filter Computation.await wrs wrcs,
            zip_filter Computation.await exs excs )
      | exception cancelation_exn ->
          Computation.cancel overall done_bt;
          raise cancelation_exn

    (* *)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/lockf.html *)
    let lockf fd lock_command length =
      Unix.lockf (Picos_fd.unsafe_get fd) lock_command length

    (* *)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/socket.html *)
    let socket ?cloexec socket_domain socket_type protocol =
      Picos_fd.create (Unix.socket ?cloexec socket_domain socket_type protocol)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/socketpair.html *)
    let socketpair ?cloexec socket_domain socket_type mystery =
      let fst, snd =
        Unix.socketpair ?cloexec socket_domain socket_type mystery
      in
      (Picos_fd.create fst, Picos_fd.create snd)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/accept.html *)
    let accept ?cloexec fd =
      let fd, sockaddr = again_cloexec_0 ?cloexec fd Unix.accept `R in
      (Picos_fd.create fd, sockaddr)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/bind.html *)
    let bind fd sockaddr = progress_1 fd sockaddr Unix.bind `W "bind"

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/connect.html *)
    let connect fd sockaddr = progress_1 fd sockaddr Unix.connect `W "connect"

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/listen.html *)
    let listen fd max_pending = Unix.listen (Picos_fd.unsafe_get fd) max_pending

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/shutdown.html *)
    let shutdown fd shutdown_command =
      Unix.shutdown (Picos_fd.unsafe_get fd) shutdown_command

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/getsockname.html *)
    let getsockname fd = Unix.getsockname (Picos_fd.unsafe_get fd)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/getpeername.html *)
    let getpeername fd = Unix.getpeername (Picos_fd.unsafe_get fd)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/recv.html *)
    let recv fd bytes offset length flags =
      again_4 fd bytes offset length flags Unix.recv
        (if List.exists is_oob flags then `E else `R)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/recvfrom.html *)
    let recvfrom fd bytes offset length flags =
      again_4 fd bytes offset length flags Unix.recvfrom
        (if List.exists is_oob flags then `E else `R)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/send.html *)
    let send fd bytes offset length flags =
      again_4 fd bytes offset length flags Unix.send `W

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/send.html *)
    let send_substring fd string offset length flags =
      again_4 fd string offset length flags Unix.send_substring `W

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/sendto.html *)
    let sendto fd bytes offset length flags sockaddr =
      again_5 fd bytes offset length flags sockaddr Unix.sendto `W

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/sendto.html *)
    let sendto_substring fd string offset length flags sockaddr =
      again_5 fd string offset length flags sockaddr Unix.sendto_substring `W

    (* *)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/getsockopt.html *)
    let getsockopt fd option = Unix.getsockopt (Picos_fd.unsafe_get fd) option

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/setsockopt.html *)
    let setsockopt fd option bool =
      Unix.setsockopt (Picos_fd.unsafe_get fd) option bool

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/getsockopt.html *)
    let getsockopt_int fd option =
      Unix.getsockopt_int (Picos_fd.unsafe_get fd) option

    let setsockopt_int fd option int =
      Unix.setsockopt_int (Picos_fd.unsafe_get fd) option int

    let getsockopt_optint fd option =
      Unix.getsockopt_optint (Picos_fd.unsafe_get fd) option

    let setsockopt_optint fd option optint =
      Unix.setsockopt_optint (Picos_fd.unsafe_get fd) option optint

    let getsockopt_float fd option =
      Unix.getsockopt_float (Picos_fd.unsafe_get fd) option

    let setsockopt_float fd option float =
      Unix.setsockopt_float (Picos_fd.unsafe_get fd) option float

    let getsockopt_error fd = Unix.getsockopt_error (Picos_fd.unsafe_get fd)

    (* *)

    (*let open_connection _ = failwith "TODO"*)
    (*let shutdown_connection _ = failwith "TODO"*)
    (*let establish_server _ = failwith "TODO"*)

    (* *)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/tcgetattr.html *)
    let tcgetattr fd = Unix.tcgetattr (Picos_fd.unsafe_get fd)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/tcsetattr.html *)
    let tcsetattr fd setattr_when terminal_io =
      Unix.tcsetattr (Picos_fd.unsafe_get fd) setattr_when terminal_io

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/tcsendbreak.html *)
    let tcsendbreak fd duration =
      Unix.tcsendbreak (Picos_fd.unsafe_get fd) duration

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/tcdrain.html *)
    let tcdrain fd = Unix.tcdrain (Picos_fd.unsafe_get fd)

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/tcflush.html *)
    let tcflush fd flush_queue =
      Unix.tcflush (Picos_fd.unsafe_get fd) flush_queue

    (* https://pubs.opengroup.org/onlinepubs/9699919799/functions/tcflow.html *)
    let tcflow fd flow_action = Unix.tcflow (Picos_fd.unsafe_get fd) flow_action
  end
end

module Picos_fifos = struct
  open Picos
  module Queue = Picos_mpsc_queue

  (* As a minor optimization, we avoid allocating closures, which take slightly
     more memory than values of this type. *)
  type ready =
    | Spawn of Fiber.t * (unit -> unit)
    | Continue of Fiber.t * (unit, unit) Effect.Deep.continuation
    | Resume of Fiber.t * (Exn_bt.t option, unit) Effect.Deep.continuation

  type t = {
    ready : ready Queue.t;
    needs_wakeup : bool Atomic.t;
    num_alive_fibers : int Atomic.t;
    mutex : Mutex.t;
    condition : Condition.t;
    resume :
      Trigger.t ->
      Fiber.t ->
      (Exn_bt.t option, unit) Effect.Deep.continuation ->
      unit;
    retc : unit -> unit;
  }

  let rec spawn t n forbid packed = function
    | [] -> Atomic.fetch_and_add t.num_alive_fibers n |> ignore
    | main :: mains ->
        let fiber = Fiber.create_packed ~forbid packed in
        Queue.push t.ready (Spawn (fiber, main));
        spawn t (n + 1) forbid packed mains

  let continue = Some (fun k -> Effect.Deep.continue k ())

  let rec next t =
    match Queue.pop_exn t.ready with
    | Spawn (fiber, main) ->
        let current =
          (* The current handler must never propagate cancelation, but it would be
             possible to continue some other fiber and resume the current fiber
             later. *)
          Some (fun k -> Effect.Deep.continue k fiber)
        and yield =
          Some
            (fun k ->
              Queue.push t.ready (Continue (fiber, k));
              next t)
        and discontinue = Some (fun k -> Fiber.continue fiber k ()) in
        let[@alert "-handler"] effc (type a) :
            a Effect.t -> ((a, _) Effect.Deep.continuation -> _) option =
          function
          | Fiber.Current ->
              (* We handle [Current] first as it is perhaps the most latency
                 sensitive effect. *)
              current
          | Fiber.Spawn r ->
              (* We check cancelation status once and then either perform the
                 whole operation or discontinue the fiber. *)
              if Fiber.is_canceled fiber then discontinue
              else begin
                spawn t 0 r.forbid (Packed r.computation) r.mains;
                continue
              end
          | Fiber.Yield -> yield
          | Computation.Cancel_after r -> begin
              (* We check cancelation status once and then either perform the
                 whole operation or discontinue the fiber. *)
              if Fiber.is_canceled fiber then discontinue
              else
                match
                  Picos_select.cancel_after r.computation ~seconds:r.seconds
                    r.exn_bt
                with
                | () -> continue
                | exception exn ->
                    let exn_bt = Exn_bt.get exn in
                    Some (fun k -> Exn_bt.discontinue k exn_bt)
            end
          | Trigger.Await trigger ->
              Some
                (fun k ->
                  if Fiber.try_suspend fiber trigger fiber k t.resume then
                    next t
                  else Fiber.resume fiber k)
          | _ -> None
        in
        Effect.Deep.match_with main () { retc = t.retc; exnc = raise; effc }
    | Continue (fiber, k) -> Fiber.continue fiber k ()
    | Resume (fiber, k) -> Fiber.resume fiber k
    | exception Queue.Empty ->
        if Atomic.get t.num_alive_fibers <> 0 then begin
          if Atomic.get t.needs_wakeup then begin
            Mutex.lock t.mutex;
            match
              if Atomic.get t.needs_wakeup then
                (* We assume that there is no poll point after the above
                   [Mutex.lock] and before the below [Condition.wait] is ready to
                   be woken up by a [Condition.broadcast]. *)
                Condition.wait t.condition t.mutex
            with
            | () -> Mutex.unlock t.mutex
            | exception exn ->
                Mutex.unlock t.mutex;
                raise exn
          end
          else Atomic.set t.needs_wakeup true;
          next t
        end

  let run ?(forbid = false) main =
    Picos_select.check_configured ();
    let ready = Queue.create ()
    and needs_wakeup = Atomic.make false
    and num_alive_fibers = Atomic.make 1
    and mutex = Mutex.create ()
    and condition = Condition.create () in
    let rec t =
      { ready; needs_wakeup; num_alive_fibers; mutex; condition; resume; retc }
    and retc () =
      Atomic.decr t.num_alive_fibers;
      next t
    and resume trigger fiber k =
      let resume = Resume (fiber, k) in
      if Fiber.unsuspend fiber trigger then
        (* The fiber has not been canceled, so we queue the fiber normally. *)
        Queue.push t.ready resume
      else
        (* The fiber has been canceled, so we give priority to it in this
           scheduler. *)
        Queue.push_head t.ready resume;
      (* As the trigger might have been signaled from another domain or systhread
         outside of the scheduler, we check whether the scheduler needs to be
         woken up and take care of it if necessary. *)
      if
        Atomic.get t.needs_wakeup
        && Atomic.compare_and_set t.needs_wakeup true false
      then begin
        begin
          match Mutex.lock t.mutex with
          | () -> Mutex.unlock t.mutex
          | exception Sys_error _ ->
              (* This should mean that [resume] was called from a signal handler
                 running on the scheduler thread.  If the assumption about not
                 having poll points holds, the [Condition.broadcast] should now be
                 able to wake up the [Condition.wait] in the scheduler. *)
              ()
        end;
        Condition.broadcast t.condition
      end
    in
    let computation = Computation.create () in
    let fiber = Fiber.create ~forbid computation in
    let main = Computation.capture computation main in
    Queue.push t.ready (Spawn (fiber, main));
    next t;
    Computation.await computation
end

(* *)

open Picos_structured.Finally
open Picos_structured
open Picos_stdio
open Picos_sync

let main () =
  let n = 100 in

  let loopback_0 = Unix.(ADDR_INET (inet_addr_loopback, 0)) in
  let server_addr = ref loopback_0 in
  let mutex = Mutex.create () in
  let condition = Condition.create () in

  let server () =
    Printf.printf "  Looping server running\n%!";
    let@ socket =
      finally Unix.close @@ fun () ->
      Unix.socket ~cloexec:true PF_INET SOCK_STREAM 0
    in
    match Unix.bind socket loopback_0 with
    | () ->
        Mutex.protect mutex (fun () -> server_addr := Unix.getsockname socket);
        Condition.signal condition;
        Unix.listen socket 8;
        Printf.printf "  Server listening\n%!";
        Bundle.join_after @@ fun bundle ->
        while true do
          let^ client =
            finally Unix.close @@ fun () ->
            Printf.printf "  Server accepting\n%!";
            Unix.accept ~cloexec:true socket |> fst
          in
          Printf.printf "  Server accepted client\n%!";

          Bundle.fork bundle @@ fun () ->
          let@ client = move client in
          let bytes = Bytes.create n in
          let n = Unix.read client bytes 0 (Bytes.length bytes) in
          Printf.printf "  Server read %d\n%!" n;
          let n = Unix.write client bytes 0 (n / 2) in
          Printf.printf "  Server wrote %d\n%!" n
        done
    | exception Unix.Unix_error (EPERM, _, _) -> raise Exit
  in

  let client id () =
    Printf.printf "  Client %s running\n%!" id;
    let@ socket =
      finally Unix.close @@ fun () ->
      Unix.socket ~cloexec:true PF_INET SOCK_STREAM 0
    in
    Unix.connect socket !server_addr;
    Printf.printf "  Client %s connected\n%!" id;
    let bytes = Bytes.create n in
    let n = Unix.write socket bytes 0 (Bytes.length bytes) in
    Printf.printf "  Client %s wrote %d\n%!" id n;
    let n = Unix.read socket bytes 0 (Bytes.length bytes) in
    Printf.printf "  Client %s read %d\n%!" id n
  in

  begin
    Bundle.join_after @@ fun bundle ->
    Bundle.fork bundle server;
    ( Mutex.protect mutex @@ fun () ->
      while !server_addr == loopback_0 do
        Condition.wait condition mutex
      done );
    Run.all [ client "A"; client "B" ];
    Bundle.terminate bundle
  end;

  Printf.printf "Server and Client test: OK\n%!"

let () =
  Printf.printf "Using blocking sockets and fibers on OCaml 5:\n%!";
  try Picos_fifos.run main with
  | Exit -> Printf.printf "Server and Client test: SKIPPED\n%!"
  | exn -> Printf.printf "Error: %s\n%!" (Printexc.to_string exn)
