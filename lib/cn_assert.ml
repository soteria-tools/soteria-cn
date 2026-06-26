module SState = State
open Soteria.Soteria_std
open Soteria.Logs.Import
open Soteria_c_lib
module State = SState
module Mu = Usable_mucore
open Csymex
open Syntax
open Soteria_c_helpers

type term = Cn.(BaseTypes.t Terms.term)
type annot = Cn.(BaseTypes.t Terms.annot)

let pp_rname = Mu.(pp_pp @@ Request.pp_name ~no_nums:true)

let pp_okind ft = function
  | Mu.Request.Init -> Fmt.pf ft "Init"
  | Uninit -> Fmt.pf ft "Uninit"

(* Sound only in OX mode, of course *)
let logic_assert v =
  let*- err = Csymex.assert_or_error v (`Lfail v :> Cn_error.t) in
  let* loc = get_loc () in
  let err =
    ( err,
      Soteria.Terminal.Call_trace.singleton ~loc
        ~msg:"Could not prove this holds" () )
  in
  Result.error err

(* This is [Symex.Producer.apply_subst], but re-implemented for the needs of CN. *)
let subst_or_extend ~ty sym subst =
  match Subst.find_opt sym subst with
  | Some v -> return (v, subst)
  | None ->
      let* v = Core_value.nondet_bt ty in
      let subst = Subst.add sym v subst in
      return (v, subst)

let produce_computational_arg (subst, state)
    ((arg, _loc) : Mu.computational_arg * Cn.Locations.info) :
    (Subst.t * State.t option) Csymex.t =
  [%l.trace "Producing computational argument: %a" Mu.pp_computational_arg arg];
  let (Computational (sym, ty) | Ghost (sym, ty)) = arg in
  let+ v = Core_value.nondet_bt ty in
  let subst = Subst.add sym v subst in
  [%l.trace "New substitution: %a" Subst.pp subst];
  (subst, state)

let produce_pure (subst, state) (annot : annot) :
    (Subst.t * State.t option) Csymex.t =
  let* v = Subst.eval_annot subst annot in
  let* v =
    Core_value.cast_bool v |> of_opt_not_impl ~msg:"produce_pure: not a boolean"
  in
  let+ () = assume [ v ] in
  (subst, state)

let produce_logical_constraint (subst, state) (lc : Cn.LogicalConstraints.t) :
    (Subst.t * State.t option) Csymex.t =
  match lc with
  | T it -> produce_pure (subst, state) it
  | Forall _ -> not_impl "consume_logical_constraint: Forall"

let produce_p_resource (subst, state) (name : Mu.Request.name) ptr iargs ty =
  match (name, iargs) with
  | Owned (cty, Init), [] ->
      let* ptr = Subst.eval_annot subst ptr in
      let* ptr =
        Core_value.cast_ptr ptr
        |> of_opt_not_impl ~msg:"produce_p_resource: not a pointer"
      in
      let* v = Core_value.nondet_bt ty in
      let+ state = State.produce_owned ptr cty v state in
      (v, (subst, state))
  | Owned (cty, Uninit), [] ->
      let* ptr = Subst.eval_annot subst ptr in
      let* ptr =
        Core_value.cast_ptr ptr
        |> of_opt_not_impl ~msg:"produce_p_resource: not a pointer"
      in
      let loc = Typed.Ptr.loc ptr in
      let ofs = Typed.Ptr.ofs ptr in
      let* len = Layout.size_of_s (Cn.Sctypes.to_ctype cty) in
      let+ state = State.produce_any' loc ofs len state in
      (Core_value.Loaded Unspec, (subst, state))
  | PName sym, iargs ->
      let def = Ctx.get_pred_def sym in
      let ret_ty = snd def.oarg in
      let* v = Core_value.nondet_bt ret_ty in
      let* iargs = map_list ~f:(Subst.eval_annot subst) iargs in
      let+ state = State.produce_pred sym iargs [ v ] state in
      (v, (subst, state))
  | Owned _, _ :: _ -> not_impl "produce_p_resource: Owned with iargs"

let produce_resource (subst, state) (req : Cn.Request.t) (ty : Cn.BaseTypes.t) :
    (Core_value.t * (Subst.t * State.t option)) Csymex.t =
  match req with
  | P { name; pointer; iargs } ->
      produce_p_resource (subst, state) name pointer iargs ty
  | Q _ -> not_impl "produce_resource: Q"

let produce_logical_arg (subst, state)
    ((arg, loc) : Mu.logical_arg * Cn.Locations.info) :
    (Subst.t * State.t option) Csymex.t =
  let@@ () = Csymex.with_loc ~loc:(fst loc) in
  match arg with
  | Define (sym, annot) ->
      let+ v = Subst.eval_annot subst annot in
      let subst = Subst.add sym v subst in
      (subst, state)
  | Resource (sym, (req, ty)) ->
      (* FIXME: Are we allowed to say take `P = ...; take P = ...`
         as a pre-condition to imply that both pointers point to the same data?
         The syntax seems to imply that it's not the case, so I'm assuming
         we can't.  *)
      let+ v, (subst, state) = produce_resource (subst, state) req ty in
      let subst = Subst.add sym v subst in
      (subst, state)
  | Constraint lc -> produce_logical_constraint (subst, state) lc

let produce_arguments (args : Mu.arguments) :
    (Subst.t * State.t option) Csymex.t =
  let subst = Subst.empty in
  let state = State.empty in
  let* subst, state =
    fold_list ~init:(subst, state) ~f:produce_computational_arg args.comp
  in
  fold_list ~init:(subst, state) ~f:produce_logical_arg args.logic

let produce_return_type (ret_ty : Mu.return_type) subst state =
  let@@ () = Csymex.with_loc ~loc:(fst ret_ty.ret_info) in
  [%l.trace "@[Producing post condition:@ %a@]" Mu.pp_return_type ret_ty];
  let rsym, bty = ret_ty.ret in
  let* r = Core_value.nondet_bt bty in
  let subst = Subst.add rsym r subst in
  fold_list ret_ty.logic ~f:produce_logical_arg ~init:(subst, state)

let consume_pure (subst, state) (annot : annot) =
  let (IT (_, _, loc)) = annot in
  let@@ () = Csymex.with_loc ~loc in
  let* v = Subst.eval_annot subst annot in
  let* v =
    Core_value.cast_bool v
    |> of_opt_not_impl ~msg:"consume_annot: not a boolean"
  in
  let++ () = logic_assert v in
  (subst, state)

let consume_logical_constraint (subst, state) (lc : Cn.LogicalConstraints.t) :
    ( Subst.t * State.t option,
      Cn_error.with_trace,
      State.syn list )
    Csymex.Result.t =
  match lc with
  | T it -> consume_pure (subst, state) it
  | Forall _ -> not_impl "consume_logical_constraint: Forall"

let consume_owned_pred cty (kind : Mu.Request.init) ptr subst state =
  let* ptr = Subst.eval_annot subst ptr in
  let* ptr =
    Core_value.cast_ptr ptr
    |> of_opt_not_impl ~msg:"consume_p_resource: not a pointer"
  in
  [%l.trace
    "@[Consuming Owned %a at %a@.@[with state:@ %a@]@]" pp_okind kind Typed.ppa
      ptr
      (Fmt.Dump.option @@ State.pp_pretty ~ignore_freed:true)
      state];
  let++ v, state =
    match kind with
    | Init ->
        State.SM.Result.run_with_state ~state (State.consume_owned ptr cty)
    | Uninit ->
        State.SM.Result.run_with_state ~state (State.consume_any ptr cty)
  in
  (v, (subst, state))

let consume_p_resrouce (subst, state) (name : Mu.Request.name) ptr iargs :
    (Core_value.t * (Subst.t * State.t option), _, _) Csymex.Result.t =
  let* loc = Csymex.get_loc () in
  match (name, iargs) with
  | Owned (cty, kind), [] ->
      consume_owned_pred cty kind ptr subst state
      |> Result.map_error (fun (e, _st) ->
          let trace =
            Soteria.Terminal.Call_trace.singleton ~loc
              ~msg:"Could not consume resource" ()
          in
          (e, trace))
  | Owned _, _ :: _ -> not_impl "consume_p_resource: Owned with iargs"
  | _ -> not_impl "consume_p_resource: not Owned(Init)"

let consume_resource (subst, state) (req : Cn.Request.t) :
    (Core_value.t * (Subst.t * State.t option), _, _) Csymex.Result.t =
  match req with
  | P { name; pointer; iargs } ->
      consume_p_resrouce (subst, state) name pointer iargs
  | Q _ -> not_impl "consume_resource: Q"

let consume_logical_arg (subst, state)
    ((arg, (loc, _)) : Mu.logical_arg * Cn.Locations.info) :
    ( Subst.t * State.t option,
      Cn_error.with_trace,
      State.syn list )
    Csymex.Result.t =
  let@@ () = Csymex.with_loc ~loc in
  match arg with
  | Define (sym, annot) ->
      let+ v = Subst.eval_annot subst annot in
      let subst = Subst.add sym v subst in
      Compo_res.Ok (subst, state)
  | Resource (sym, (req, _ty)) ->
      let++ v, (subst, state) = consume_resource (subst, state) req in
      let subst = Subst.add sym v subst in
      (subst, state)
  | Constraint lc -> consume_logical_constraint (subst, state) lc

let consume_arguments (args : Mu.arguments) subst state :
    ( Subst.t * State.t option,
      Cn_error.with_trace,
      State.syn list )
    Csymex.Result.t =
  let open Csymex.Result in
  (* I'm assuming the type Cn base type checker already went through code,
in which case there's nothing else to do about computational args. *)
  fold_list ~init:(subst, state) ~f:consume_logical_arg args.logic

let consume_return_type (ty : Mu.return_type) (ret : Core_value.t) subst state :
    ( Subst.t * State.t option,
      Cn_error.with_trace,
      State.syn list )
    Csymex.Result.t =
  [%l.trace "Consuming return type: %a" Mu.pp_return_type ty];
  let subst = Subst.add (fst ty.ret) ret subst in
  Result.fold_list ~init:(subst, state) ~f:consume_logical_arg ty.logic
