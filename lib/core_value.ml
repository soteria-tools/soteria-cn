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
  | Fn of Sym.t
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

module Syntax = struct
  module Sym_int_syntax = struct
    open Typed.Syntax

    let zero = Obj (Int CInt.(0s))
    let one = Obj (Int CInt.(1s))
    let nonzero i = Obj (Int (CInt.Sym_int_syntax.mk_nonzero i))
  end
end
