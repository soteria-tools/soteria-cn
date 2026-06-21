open Soteria_c_lib
open Soteria.Logs.Import
open Typed
module Sym = Symbol_std
module Ctype = Cerb_frontend.Ctype
module Impl_mem = Cerb_frontend.Impl_mem

type 'a or_unspec = Spec of 'a | Unspec
[@@deriving show { with_path = false }]

type obj =
  | Int of T.sint Typed.t
  | Float of T.sfloat Typed.t
  | Ptr of T.sptr Typed.t
  | Array of obj or_unspec list
  | Struct of { tag : Sym.t; members : obj or_unspec list }
  | Fn of Sym.t
[@@deriving show { with_path = false }]

type t =
  | Obj of obj
  | Loaded of obj or_unspec
  | Type of (Ctype.ctype[@printer Fmt_ail.pp_ty])
  | Unit
  | List of t list
  | Tuple of t list
  | Bool of T.sbool Typed.t
[@@deriving show { with_path = true }]

let true_ = Bool Typed.v_true
let false_ = Bool Typed.v_false

(* ── Conversion from [Usable_mucore] core values ─────────────────────────── *)

(* Width (in bits) of a Cerberus integer type. *)
let bits_of_ity ity =
  match Layout.size_of_int_ty ity with
  | Some bytes -> 8 * bytes
  | None -> L.failwith "Core_value: integer type of unknown size"

(* [iv] is masked to [bits], so a (two's complement) negative value is kept as
   its bit pattern. *)
let int_of_ival ~bits iv : T.sint Typed.t =
  Impl_mem.case_integer_value iv
    (fun z -> Typed.BitVec.mk_masked bits z)
    (fun () -> L.failwith "Core_value: unspecified integer value")

let float_of_fval fv : T.sfloat Typed.t =
  Impl_mem.case_fval fv
    (fun () -> L.failwith "Core_value: unspecified float value")
    (fun f -> Typed.Float.f64 f)

let ptr_of_ptr_value ptr : obj =
  Impl_mem.case_ptrval ptr
    (* Null *)
    (fun _ -> Ptr Typed.Ptr.null) (* Funptr *)
    (function
      | Some sym -> Fn sym
      | None -> L.failwith "Core_value: unspecified pointer value")
    (* Loc *)
    (fun _ ->
      L.failwith
        "Core_value: pointer values with known location are not supported")

(* A struct member is stored as a [mem_value], which may be unspecified, hence
   [obj or_unspec]. *)
let rec obj_of_mem mv : obj or_unspec =
  Impl_mem.case_mem_value mv
    (fun _ct -> Unspec)
    (fun _ity _sym -> L.failwith "Core_value: concurrency-read mem value")
    (fun ity iv -> Spec (Int (int_of_ival ~bits:(bits_of_ity ity) iv)))
    (fun _fty fv -> Spec (Float (float_of_fval fv)))
    (fun _ct ptr -> Spec (ptr_of_ptr_value ptr))
    (fun mvs -> Spec (Array (List.map obj_of_mem mvs)))
    (fun tag members ->
      let members = List.map (fun (_, _, mv) -> obj_of_mem mv) members in
      Spec (Struct { tag; members }))
    (fun _tag _id _mv -> L.failwith "Core_value: union mem value")

(* [OVinteger] carries no type, so its width defaults to [int]. *)
let rec obj_of_mu (ov : Usable_mucore.object_value) : obj =
  let open Usable_mucore in
  match ov with
  | OVinteger iv -> Int (int_of_ival ~bits:Typed.c_int_bits iv)
  | OVfloating fv -> Float (float_of_fval fv)
  | OVarray lvs -> Array (List.map loaded_of_mu lvs)
  | OVstruct { tag; members } ->
      let members = List.map (fun (_, _, mv) -> obj_of_mem mv) members in
      Struct { tag; members }
  | OVpointer ptr -> ptr_of_ptr_value ptr
  | OVunion _ -> L.failwith "obj_of_mu: union values are not supported"

and loaded_of_mu (lv : Usable_mucore.loaded_value) : obj or_unspec =
  let open Usable_mucore in
  match lv with
  | LVspecified ov -> Spec (obj_of_mu ov)
  | LVunspecified _ -> Unspec

let rec of_mu (v : Usable_mucore.value) : t =
  let open Usable_mucore in
  match v with
  | Vobject ov -> Obj (obj_of_mu ov)
  | Vctype ct -> Type ct
  | Vunit -> Unit
  | Vtrue -> true_
  | Vfalse -> false_
  | Vtuple vs -> Tuple (List.map of_mu vs)
  | Vlist (_, vs) -> List (List.map of_mu vs)
  | Vloaded lv -> Loaded (loaded_of_mu lv)

let cast_int (v : t) : (T.sint Typed.t, string, _) Csymex.Result.t =
  match v with
  | Obj (Int i) | Loaded (Spec (Int i)) -> Csymex.Result.ok i
  | _ -> Csymex.Result.error "cast_int: value is not an integer"

let cast_type (v : t) : (Ctype.ctype, string, _) Csymex.Result.t =
  match v with
  | Type ct -> Csymex.Result.ok ct
  | _ -> Csymex.Result.error "cast_type: value is not a type"

let c_int (i : int) : t =
  Obj (Int (Typed.BitVec.mk_masked Typed.c_int_bits (Z.of_int i)))

let c_int_of_bool b = if b then c_int 1 else c_int 0

module Bool = struct
  let not b =
    match b with
    | Bool b -> Bool (Typed.Bool.not b)
    | _ -> L.failwith "not: not a boolean %a" pp b

  let of_bool b = Bool (Typed.Bool.of_bool b)

  let to_sbool v =
    match v with
    | Bool b -> b
    | _ ->
        L.failwith "Core_value.Bool.to_sbool: value is not a boolean: %a" pp v

  let or_ b1 b2 =
    match (b1, b2) with
    | Bool b1, Bool b2 -> Bool (Typed.Bool.or_ b1 b2)
    | _ -> L.failwith "or_: not booleans: %a, %a" pp b1 pp b2
end

let cfunction (fn_sig : Cn.Sctypes.c_concrete_sig) : t =
  (* Cerberus implementation: *)
  (* ATtuple
       [Vctype ret;
        Vlist BTy_ctype (List.map (fun (_, ty) -> Vctype ty) params);
        if is_variadic then Vtrue else Vfalse;
        if has_proto then Vtrue else Vfalse; ]
  *)
  Tuple
    [
      Type fn_sig.sig_return_ty;
      Tuple (List.map (fun t -> Type t) fn_sig.sig_arg_tys);
      Bool.of_bool fn_sig.sig_variadic;
      Bool.of_bool fn_sig.sig_has_proto;
    ]

let sem_eq_or_unspec (sem_eq_a : 'a -> 'a -> T.sbool Typed.t)
    (v1 : 'a or_unspec) (v2 : 'a or_unspec) : T.sbool Typed.t =
  match (v1, v2) with
  | Spec a1, Spec a2 -> sem_eq_a a1 a2
  | Unspec, Unspec -> Typed.v_true
  | _ -> Typed.v_false

let rec sem_eq_obj o1 o2 =
  let open Typed.Infix in
  let sem_eq_ooul l1 l2 =
    try
      List.fold_left2
        (fun acc v1 v2 -> acc &&@ sem_eq_or_unspec sem_eq_obj v1 v2)
        Typed.v_true l1 l2
    with Invalid_argument _ -> Typed.v_false
  in
  match (o1, o2) with
  | Int i1, Int i2 -> i1 ==@ i2
  | Float f1, Float f2 -> f1 ==@ f2
  | Ptr p1, Ptr p2 -> p1 ==@ p2
  | Array a1, Array a2 -> sem_eq_ooul a1 a2
  | Struct { tag = t1; members = m1 }, Struct { tag = t2; members = m2 } ->
      let tag_eq = Typed.Bool.of_bool @@ Sym.equal t1 t2 in
      tag_eq &&@ sem_eq_ooul m1 m2
  | Fn s1, Fn s2 -> Typed.Bool.of_bool @@ Sym.equal s1 s2
  | _ -> Typed.v_false

let rec sem_eq v1 v2 =
  let open Typed.Infix in
  let sem_eq_list l1 l2 =
    try
      List.fold_left2 (fun acc v1 v2 -> acc &&@ sem_eq v1 v2) Typed.v_true l1 l2
    with Invalid_argument _ -> Typed.v_false
  in
  match (v1, v2) with
  | Obj o1, Obj o2 -> sem_eq_obj o1 o2
  | Loaded l1, Loaded l2 -> sem_eq_or_unspec sem_eq_obj l1 l2
  | Type t1, Type t2 -> Typed.Bool.of_bool @@ Ctype.ctypeEqual t1 t2
  | Unit, Unit -> Typed.v_true
  | List l1, List l2 -> sem_eq_list l1 l2
  | Tuple t1, Tuple t2 -> sem_eq_list t1 t2
  | Bool b1, Bool b2 -> b1 ==@ b2
  | _ -> Typed.v_false

module Syntax = struct
  module Sym_int_syntax = struct
    open Typed.Syntax

    let zero = Obj (Int CInt.(0s))
    let one = Obj (Int CInt.(1s))
    let nonzero i = Obj (Int (CInt.Sym_int_syntax.mk_nonzero i))
  end
end
